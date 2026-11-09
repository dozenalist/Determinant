/-
Copyright (c) 2026 Carter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter
-/
module

public import Determinant.Tactic.Triangular
public import Determinant.Tactic.Bridge
public meta import Determinant.Tactic.Bridge

/-! # The public, uncached determinant tactic -/

public meta section

open Lean Elab Tactic Qq

namespace Determinant.Tactic

initialize registerTraceClass `Determinant.dispatch

/-- Try the hypothesis/triangular route transactionally, then the shared producer and
strict replay path. No persistent files are read or written by the dispatcher. -/
def detNeZeroInt (producer : CertificateProducer) : TacticM Unit := do
  let started ← IO.monoMsNow
  let saved ← saveState
  try
    evalTactic (← `(tactic| certify_det_ne_zero_triangular))
    trace[Determinant.timing] "triangular route: {(← IO.monoMsNow) - started} ms"
    trace[Determinant.dispatch] "proved by the triangular route"
    return
  catch error =>
    if error.isInterrupt then throw error
    saved.restore
    trace[Determinant.dispatch] "triangular route unavailable: {error.toMessageData}"
  trace[Determinant.dispatch] "trying modular certificate discovery"
  trace[Determinant.timing] "triangular attempt: {(← IO.monoMsNow) - started} ms"
  certifyWithProducer producer

/-- Prove `A.det ≠ 0` (or its reversal), trying triangularity before Sage.
The optional data-only term has type `ProducerConfig`. -/
elab "det_ne_zero_int" config:(ppSpace term)? : tactic => do
  let config ← match config with
    | none => pure ({} : ProducerConfig)
    | some config => unsafe Term.evalTerm ProducerConfig q(ProducerConfig) config
  detNeZeroInt (processProducer config)

end Determinant.Tactic
