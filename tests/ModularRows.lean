import Determinant

open Lean Determinant

namespace ModularRowTests

macro "cycleMatrix20With " one:term : term => do
  let rows ← (List.range 20).toArray.mapM fun i => do
    let cells ← (List.range 20).toArray.mapM fun j =>
      if j == (i + 1) % 20 then pure one else `(term| 0)
    `(term| [$cells,*])
  `(term| Mathlib.Tactic.Matrix.ofLists 20 20 [$rows,*])

macro "cycleMatrix20" : term => `(term| cycleMatrix20With (1 : ℤ))

def A := cycleMatrix20

def witness : RawCertificate := {
  dimension := 20, modulus := 2
  inverse := List.ofFn fun i : Fin 20 => List.ofFn fun j : Fin 20 =>
    if i.val = (j.val + 1) % 20 then 1 else 0 }

-- Dimension 20 exercises separate, synchronous kernel checks of row lemmas.
theorem full : A.det ≠ 0 := by certify_det_ne_zero_modular witness
theorem upper : A.det ≠ 0 := by
  certify_det_ne_zero_modular { witness with kind := "unit-upper-product" }

-- Checked normalization lemmas must close over local entry definitions.
theorem localEntry : A.det ≠ 0 := by
  let one : ℤ := 1
  have : (cycleMatrix20With one).det ≠ 0 := by
    certify_det_ne_zero_modular witness
  exact this

-- Literal discovery cannot override the actual numeral instance in the goal.
-- This dimension exercises the separately kernel-checked normalization bridge.
set_option linter.style.haveILetI false in
example : True := by
  letI : OfNat ℤ 1 := ⟨0⟩
  fail_if_success
    have : (cycleMatrix20With (1 : ℤ)).det ≠ 0 := by
      certify_det_ne_zero_modular witness
  trivial

example : True := by
  fail_if_success
    have : A.det ≠ 0 := by
      certify_det_ne_zero_modular {
        witness with inverse := List.replicate 20 (List.replicate 20 0) }
  trivial

run_cmd do
  for decl in [``full, ``upper, ``localEntry] do
    for dependency in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "unexpected axiom {dependency} in {decl}"

end ModularRowTests
