-- Run after Cache.lean, in a fresh Lean process. No producer can be launched.
import Determinant

set_option trace.Determinant.cache true
set_option trace.Determinant.producer true

theorem freshCacheReplay : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! {
    directory := ".lake/det-ne-zero-tests/witnesses"
    policy := .cacheOnly
    executable := "sage-is-unavailable-in-this-process" }

run_cmd do
  for dependency in ← Lean.collectAxioms ``freshCacheReplay do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "unexpected axiom {dependency}"
