/-
Copyright (c) 2026 Carter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter
-/
module

public import Determinant.Tactic.Modular
public import Lean.Data.Json

/-! # Data-only certificate producers and bounded process execution

The process supplies candidates only. Every result goes through the same strict
checker as offline replay. Importing this module performs no external work.
-/

public section

namespace Determinant.Tactic

/-- Arguments are separate OS arguments, never shell source. Relative paths are
relative to `workingDirectory`, or Lean's current directory if it is omitted. -/
structure ProducerConfig where
  executable : String := "python3"
  arguments : Array String := #["scripts/det_certificate.py"]
  workingDirectory : Option String := none
  preferredPrimes : List Nat := [2, 3, 5, 7]
  maxAttempts : Nat := 16
  timeoutMs : Nat := 30000
  kind : String := "full-inverse"
  verifyProduct : Bool := false
  maxRequestBytes : Nat := 67108864
  maxResponseBytes : Nat := 67108864
  maxStderrBytes : Nat := 65536
  deriving Inhabited, Repr

end Determinant.Tactic

public meta section

open Lean Meta Elab Tactic Qq
open Mathlib.Tactic.Echelon

namespace Determinant.Tactic

initialize registerTraceClass `Determinant.producer

private def protocol : String := "determinant-certificate"

/-- Versioned row-major protocol; no expressions or executable source cross the boundary. -/
def producerRequest (n : Nat) (values : Array Int) (config : ProducerConfig) : Json :=
  Json.mkObj [
    ("protocol", toJson protocol), ("version", toJson (1 : Nat)),
    ("dimension", toJson n), ("entries", toJson (values.map toString)),
    ("kind", toJson config.kind),
    ("preferred_primes", toJson (config.preferredPrimes.map toString)),
    ("max_attempts", toJson config.maxAttempts), ("timeout_ms", toJson config.timeoutMs),
    ("verify_product", toJson config.verifyProduct)]

private def decimalInt (j : Json) : Except String Int := do
  let s ← j.getStr?
  let some value := s.toInt? | throw "invalid decimal integer string"
  unless toString value == s do throw "expected a canonical decimal integer string"
  return value

private def decimalNat (j : Json) : Except String Nat := do
  let value ← decimalInt j
  if value < 0 then throw "expected a nonnegative decimal integer string"
  return value.toNat

/-- Strict protocol decoding and exact shape validation precede all arithmetic.
Producer metadata is diagnostic and carries no mathematical authority. -/
def parseProducerResponse (n : Nat) (kind : String) (output : String) :
    Except String RawCertificate := do
  let response ← Json.parse output
  unless (← (← response.getObjVal? "protocol").getStr?) == protocol do
    throw "unsupported producer protocol"
  unless (← (← response.getObjVal? "version").getNat?) == 1 do
    throw "unsupported producer protocol version"
  let status ← (← response.getObjVal? "status").getStr?
  if status == "error" then
    let error ← response.getObjVal? "error"
    throw s!"{← (← error.getObjVal? "code").getStr?}: {← (← error.getObjVal? "message").getStr?}"
  unless status == "ok" do throw "unsupported producer status"
  let cert ← response.getObjVal? "certificate"
  let version ← (← cert.getObjVal? "version").getNat?
  let dimension ← (← cert.getObjVal? "dimension").getNat?
  let modulus ← decimalNat (← cert.getObjVal? "modulus")
  let actualKind ← (← cert.getObjVal? "kind").getStr?
  unless actualKind == kind do throw "producer returned an unexpected certificate kind"
  let rows ← (← cert.getObjVal? "inverse").getArr?
  let inverse ← rows.toList.mapM fun row => do
    (← row.getArr?).toList.mapM fun entry => do
      let value ← decimalInt entry
      unless 0 ≤ value && value < (modulus : Int) do
        throw "inverse entry is not a canonical residue representative"
      return value
  let raw : RawCertificate := { version, dimension, modulus, kind := actualKind, inverse }
  let _ ← raw.validate n
  return raw

private partial def readBounded (handle : IO.FS.Handle) (limit : Nat)
    (label : String) (buffer : ByteArray := {}) : IO String := do
  let chunk ← handle.read (min 4096 (limit + 1 - buffer.size)).toUSize
  let buffer := buffer ++ chunk
  if buffer.size > limit then throw <| IO.userError s!"producer {label} exceeds byte limit {limit}"
  if chunk.isEmpty then
    let some text := String.fromUTF8? buffer
      | throw <| IO.userError s!"producer {label} is not valid UTF-8"
    return text
  readBounded handle limit label buffer

private def taskError {α : Type} (task : Task (Except IO.Error α)) : IO Unit := do
  if ← IO.hasFinished task then
    if let .error error := task.get then throw error

/-- Use the platform's process-tree termination utility, with bounded cleanup.
The Windows supervisor's worker must be terminated before its parent is lost. -/
private def terminateTree {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) :
    IO Unit := do
  try
    let (cmd, args) := if System.Platform.isWindows then
      ("taskkill.exe", #["/PID", toString child.pid, "/T", "/F"])
    else
      ("/bin/kill", #["-KILL", "--", s!"-{child.pid}"])
    let killer ← IO.Process.spawn {
      cmd, args, stdin := .null, stdout := .piped, stderr := .piped }
    let started ← IO.monoMsNow
    repeat
      if (← killer.tryWait).isSome then break
      if (← IO.monoMsNow) - started ≥ 2000 then
        try killer.kill catch _ => pure ()
        discard <| IO.asTask killer.wait .dedicated
        break
      IO.sleep 10
  catch _ => pure ()
  try child.kill catch _ => pure ()
  discard <| IO.asTask child.wait .dedicated

/-- Run a producer with concurrent bounded pipe readers and writer, polling cancellation
and the wall clock even when the child never reads stdin or closes its output pipes. -/
def runProducer (config : ProducerConfig) (request : String) : CoreM IO.Process.Output := do
  unless config.timeoutMs > 0 && config.maxAttempts > 0 do
    throwError "producer timeoutMs and maxAttempts must be positive"
  unless request.utf8ByteSize ≤ config.maxRequestBytes do
    throwError "producer request exceeds byte limit {config.maxRequestBytes}"
  let started ← IO.monoMsNow
  let spawned ← (IO.Process.spawn {
    cmd := config.executable, args := config.arguments
    cwd := config.workingDirectory.map System.FilePath.mk
    stdin := .piped, stdout := .piped, stderr := .piped, setsid := true }).toBaseIO
  let child ← match spawned with
    | .ok child => pure child
    | .error error =>
      throwError "could not start certificate producer '{config.executable}': {error}"
  -- Cleanup must retain the stdin-free child. Retaining the original child in
  -- `finally` would keep the pipe open and prevent the producer from seeing EOF.
  let (stdin, child) ← child.takeStdin
  let mut completed := false
  try
    let writer ← IO.asTask (do stdin.putStr request; stdin.flush) .dedicated
    let stdout ← IO.asTask (readBounded child.stdout config.maxResponseBytes "stdout") .dedicated
    let stderr ← IO.asTask (readBounded child.stderr config.maxStderrBytes "stderr") .dedicated
    let mut exitCode := none
    repeat
      Core.checkInterrupted
      if (← IO.monoMsNow) - started ≥ config.timeoutMs then
        throwError "certificate producer timed out after {config.timeoutMs} ms"
      taskError stdout
      taskError stderr
      -- A nonzero exit may close stdin early; retain its stderr instead of a pipe error.
      -- POSIX waitpid reaps the child: never call it twice after an exit is observed.
      if exitCode.isNone then exitCode ← child.tryWait
      if let some code := exitCode then
        if (← IO.hasFinished stdout) && (← IO.hasFinished stderr) then
          if code == 0 then taskError writer
          completed := true
          let out ← IO.ofExcept stdout.get
          let err ← IO.ofExcept stderr.get
          return { exitCode := code, stdout := out, stderr := err }
      IO.sleep 10
    throwError "unreachable producer state"
  finally
    unless completed do
      terminateTree child

/-- The backend interface produces data, with no access to goal assignment. A replacement
producer can implement this signature and use `proveCertificateForEntries` unchanged. -/
abbrev CertificateProducer := Nat → Array Int → CoreM RawCertificate

/-- Preserve diagnostic provenance for persistent witnesses. -/
def processProducerWithMetadata (config : ProducerConfig) (n : Nat) (values : Array Int) :
    CoreM (RawCertificate × Json) := do
  let started ← IO.monoMsNow
  let request := (producerRequest n values config).compress
  trace[Determinant.timing] "serialization: {(← IO.monoMsNow) - started} ms"
  trace[Determinant.producer] "starting {config.executable} with {config.arguments}"
  let started ← IO.monoMsNow
  let output ← runProducer config request
  trace[Determinant.producer]
    "producer completed in {(← IO.monoMsNow) - started} ms\n{output.stderr}"
  trace[Determinant.timing] "producer transport: {(← IO.monoMsNow) - started} ms"
  -- POSIX spawn can return after fork but before exec fails. Lean then reports
  -- the missing executable through the child's stderr and exit status 255.
  if output.exitCode == 255 &&
      (output.stderr.splitOn "could not execute external process").length > 1 then
    throwError "could not start certificate producer '{config.executable}': {output.stderr}"
  unless output.exitCode == 0 do
    throwError "certificate producer exited with code {output.exitCode}\n\
      stdout: {output.stdout}\nstderr: {output.stderr}"
  let started ← IO.monoMsNow
  match parseProducerResponse n config.kind output.stdout with
  | .ok raw =>
    trace[Determinant.timing] "parsing: {(← IO.monoMsNow) - started} ms"
    let response ← IO.ofExcept (Json.parse output.stdout)
    if let .ok metadata := response.getObjVal? "producer" then
      trace[Determinant.producer] "metadata: {metadata.compress}"
    return (raw, response)
  | .error message =>
    throwError "invalid certificate producer response: {message}\nstderr: {output.stderr}"

def processProducer (config : ProducerConfig) : CertificateProducer := fun n values => do
  return (← processProducerWithMetadata config n values).1

/-- Extract the matrix once, serialize closed integer values, and replay a candidate
against those original expressions. The checker's congruence proofs bind data to the goal. -/
def proveWithProducer (A : Expr) (producer : CertificateProducer) : MetaM Expr := do
  let started ← IO.monoMsNow
  let (n, entries) ← integerEntries A
  let mut values := #[]
  for i in [:n] do
    for j in [:n] do
      let entry := (entries[i]!)[j]!
      let value ← try integerValue entry catch _ =>
        throwError "certificate producer: entry ({i}, {j}) is not a closed integer: {entry}"
      values := values.push value
  trace[Determinant.timing] "extraction: {(← IO.monoMsNow) - started} ms"
  let raw ← producer n values
  proveCertificateForEntries A n entries raw

/-- Close the current determinant goal using an interchangeable data-only producer. -/
def certifyWithProducer (producer : CertificateProducer) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let_expr Ne R lhs rhs := target
    | throwError "expected a goal A.det ≠ 0 or 0 ≠ A.det"
  let (det, zero, reversed) ← if lhs.isAppOf ``Matrix.det then pure (lhs, rhs, false)
    else if rhs.isAppOf ``Matrix.det then pure (rhs, lhs, true)
    else throwError "expected a determinant-nonzero goal"
  unless ← isDefEq R q(ℤ) do throwError "certificate producer supports integer matrices"
  unless ← isDefEq zero q((0 : ℤ)) do throwError "expected comparison with zero"
  let proof ← proveWithProducer det.getAppArgs.back! producer
  let proof ← if reversed then mkAppM ``Ne.symm #[proof] else pure proof
  unless ← isDefEq (← inferType proof) target do
    throwError "producer certificate does not prove the current goal"
  goal.assign proof
  replaceMainGoal []

/-- Discover a Sage certificate and check it strictly. Configuration is a data-only term. -/
elab "certify_det_ne_zero_sage" config:(ppSpace term)? : tactic => do
  let config ← match config with
    | none => pure ({} : ProducerConfig)
    | some config => unsafe Term.evalTerm ProducerConfig q(ProducerConfig) config
  certifyWithProducer (processProducer config)

end Determinant.Tactic
