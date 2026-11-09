/-
Copyright (c) 2026 Carter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter
-/
module

public import Determinant.Tactic.CharZero
public meta import Determinant.Tactic.CharZero
public meta import Lean.Util.Path

/-! # Project-local, strictly checked determinant witnesses -/

public section

namespace Determinant.Tactic

inductive CachePolicy where
  | readWrite
  | readOnly
  | cacheOnly
  | disabled
  deriving Inhabited, Repr

/-- Per-invocation settings override the directory option. All inherited producer
settings have the same meaning as for `det_ne_zero`. Helper arguments are OS arguments,
never shell source. An empty array locates the bundled helper through Lean's source path. -/
structure CacheConfig extends ProducerConfig where
  directory : String := ""
  projectRoot : Option String := none
  policy : CachePolicy := .readWrite
  refresh : Bool := false
  lookupExecutable : String := "python3"
  lookupArguments : Array String := #[]
  lookupTimeoutMs : Nat := 10000
  deriving Inhabited, Repr

end Determinant.Tactic

public meta section

register_option determinant.witnessDirectory : String := {
  defValue := "det_ne_zero_witnesses"
  descr := "project-local directory for det_ne_zero! witnesses" }

open Lean Meta Elab Tactic Qq

namespace Determinant.Tactic

instance : BEq CachePolicy where
  beq
    | .readWrite, .readWrite | .readOnly, .readOnly
    | .cacheOnly, .cacheOnly | .disabled, .disabled => true
    | _, _ => false

initialize registerTraceClass `Determinant.cache

private def helperConfig (config : CacheConfig) : CoreM ProducerConfig := do
  let arguments ← if config.lookupArguments.isEmpty then do
    let sourcePath := (← getSrcSearchPath) ++ [← IO.Process.getCurrentDir]
    let source ← findLean sourcePath `Determinant.Tactic.Cache
    let some root := source.parent >>= System.FilePath.parent >>= System.FilePath.parent
      | throwError "cannot locate scripts/cache_lookup.py; set lookupArguments explicitly"
    let script ← IO.FS.realPath (root / "scripts" / "cache_lookup.py")
    pure #[script.toString]
  else pure config.lookupArguments
  return { config.toProducerConfig with
    executable := config.lookupExecutable
    arguments
    workingDirectory := none
    timeoutMs := config.lookupTimeoutMs
    maxAttempts := 1 }

private def cacheRequest (config : CacheConfig) (n : Nat) (values : Array Int)
    (action : String) (response : Json := Json.null) : CoreM Json := do
  let options ← getOptions
  let directory := if config.directory.isEmpty then
    determinant.witnessDirectory.get options else config.directory
  return Json.mkObj [
    ("action", toJson action), ("source_file", toJson (← getFileName)),
    ("project_root", toJson config.projectRoot), ("directory", toJson directory),
    ("dimension", toJson n), ("entries", toJson (values.map toString)),
    ("kind", toJson config.kind), ("response", response),
    ("max_bytes", toJson config.maxResponseBytes)]

private def callCache (config : CacheConfig) (request : Json) : CoreM Json := do
  let started ← IO.monoMsNow
  let output ← runProducer (← helperConfig config) request.compress
  let action ← IO.ofExcept ((request.getObjVal? "action").bind Json.getStr?)
  trace[Determinant.timing] "cache {action}: {(← IO.monoMsNow) - started} ms"
  unless output.exitCode == 0 do
    throwError "witness lookup failed: {output.stdout}\n{output.stderr}"
  match Json.parse output.stdout with
  | .ok result => return result
  | .error message => throwError "invalid witness lookup response: {message}"

private def parseCached (config : CacheConfig) (n : Nat) (values : Array Int)
    (result : Json) : Except String RawCertificate := do
  let record ← result.getObjVal? "record"
  unless (← (← record.getObjVal? "schema").getStr?) == "det-ne-zero-witness" &&
      (← (← record.getObjVal? "version").getNat?) == 1 do
    throw "incompatible witness schema/version"
  let matrix ← record.getObjVal? "matrix"
  unless (← (← matrix.getObjVal? "encoding").getStr?) == "det-ne-zero-matrix-v1" &&
      (← (← matrix.getObjVal? "dimension").getNat?) == n &&
      (← (← matrix.getObjVal? "entries").getArr?) == values.map (toJson ∘ toString) do
    throw "stored full integer matrix does not match the current matrix"
  parseProducerResponse n config.kind (← record.getObjVal? "response").compress

/-- Add persistence around either dispatcher. Only a successful modular proof is
stored. A bad cached candidate is retried once with fresh discovery, unless cache-only.
The saved tactic state also rolls back any auxiliary lemmas from failed replay. -/
def withWitnessCache (config : CacheConfig)
    (run : CertificateProducer → TacticM Unit) : TacticM Unit := withMainContext do
  if config.policy == .disabled then
    run (processProducer config.toProducerConfig)
    return
  let pending ← IO.mkRef (none : Option Json)
  let usedHit ← IO.mkRef false
  let fresh : CertificateProducer := fun n values => do
    if config.policy == .cacheOnly then
      throwError "det_ne_zero!: no usable cached witness (cache-only policy; producer disabled)"
    let (raw, response) ← processProducerWithMetadata config.toProducerConfig n values
    if config.policy == .readWrite then
      pending.set (some (← cacheRequest config n values "store" response))
    return raw
  let producer : CertificateProducer := fun n values => do
    if config.refresh then
      if config.policy == .cacheOnly then
        throwError "det_ne_zero!: refresh is incompatible with cache-only policy"
      trace[Determinant.cache] "refresh: bypassing witness lookup"
      return ← fresh n values
    let result ← callCache config (← cacheRequest config n values "lookup")
    let status ← IO.ofExcept ((result.getObjVal? "status").bind Json.getStr?)
    trace[Determinant.cache] "{status}: {(result.getObjVal? "path").toOption}"
    if status == "hit" then
      match parseCached config n values result with
      | .ok raw => usedHit.set true; return raw
      | .error message =>
        trace[Determinant.cache] "rejected: {message}"
        if config.policy == .cacheOnly then throwError "cached witness rejected: {message}"
    else if status == "rejected" then
      if config.policy == .cacheOnly then
        throwError "cached witness rejected: {(result.getObjVal? "message").toOption}"
    else unless status == "miss" do
      throwError "unexpected witness lookup status: {status}"
    return ← fresh n values
  let goal ← getMainGoal
  let saved ← saveState
  try
    run producer
  catch error =>
    if error.isInterrupt then throw error
    unless (← usedHit.get) && config.policy != .cacheOnly do throw error
    saved.restore
    trace[Determinant.cache] "cached verification failed; recomputing: {error.toMessageData}"
    run fresh
  if let some request ← pending.get then
    -- Misses are published only after kernel checking the assembled proof. Large
    -- row certificates already reference checked lemmas, so this stays inexpensive.
    let started ← IO.monoMsNow
    checkWithKernel (← instantiateMVars (mkMVar goal))
    trace[Determinant.timing] "cache verification: {(← IO.monoMsNow) - started} ms"
    let result ← callCache config request
    unless (← IO.ofExcept ((result.getObjVal? "status").bind Json.getStr?)) == "stored" do
      throwError "witness helper did not publish the checked certificate"
    trace[Determinant.cache] "stored: {(result.getObjVal? "path").toOption}"

/-- `det_ne_zero` with project-local, untrusted witness persistence and strict replay. -/
elab "det_ne_zero!" config:(ppSpace term)? : tactic => do
  let config ← match config with
    | none => pure ({} : CacheConfig)
    | some config => unsafe Term.evalTerm CacheConfig q(CacheConfig) config
  withWitnessCache config detNeZero

/-- Integer-only spelling of the persistent dispatcher. -/
elab "det_ne_zero_int!" config:(ppSpace term)? : tactic => do
  let config ← match config with
    | none => pure ({} : CacheConfig)
    | some config => unsafe Term.evalTerm CacheConfig q(CacheConfig) config
  withWitnessCache config detNeZeroInt

end Determinant.Tactic
