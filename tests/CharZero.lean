import Determinant
import Mathlib.Basic.Complex.Basic

open Lean Elab Tactic Determinant Determinant.Tactic

namespace CharZeroTests

-- Determinant 5, with inverse modulo 3. Verify the actual signed table sent out.
elab "example_certificate" : tactic =>
  detNeZero fun n entries => do
    unless n == 2 && entries == #[2, 3, 1, 4] do throwError "incorrect integer lift"
    return { dimension := 2, modulus := 3, inverse := [[2, 0], [1, 1]] }

theorem complex : (!![2, 3; 1, 4] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
  example_certificate

theorem abstractRing {R : Type*} [CommRing R] [CharZero R] :
    (!![2, 3; 1, 4] : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
  example_certificate

theorem reversed : 0 ≠ (!![2, 3; 1, 4] : Matrix (Fin 2) (Fin 2) ℂ).det := by
  example_certificate

def named : Matrix (Fin 2) (Fin 2) ℂ := !![2, 3; 1, 4]
theorem namedGoal : named.det ≠ 0 := by example_certificate

theorem arithmetic : (!![1 + 1, 3 * 1; -(-1), 2 ^ 2] :
    Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by example_certificate

theorem lists : (Mathlib.Tactic.Matrix.ofLists 2 2 ([[2, 3], [1, 4]] :
    List (List ℂ))).det ≠ 0 := by example_certificate

example : True := by
  let x : ℂ := 2
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![x, 3; 1, 4]
  have : A.det ≠ 0 := by example_certificate
  trivial

-- Public syntax, including configuration, must avoid launching a producer here.
theorem triangular {R : Type*} [CommRing R] [CharZero R] :
    (!![-2, 3; 0, 4] : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
  det_ne_zero { executable := "must-not-launch" }

theorem empty {R : Type*} [CommRing R] [CharZero R] :
    (!![] : Matrix (Fin 0) (Fin 0) R).det ≠ 0 := by det_ne_zero

theorem singleton : (!![-7] : Matrix (Fin 1) (Fin 1) ℂ).det ≠ 0 := by det_ne_zero

theorem integer : (!![-2, 3; 0, 4] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero

theorem integerRenamed : (!![-2, 3; 0, 4] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero_int

macro "diagonalTwo17" : term => do
  let rows ← (List.range 17).toArray.mapM fun i => do
    let cells ← (List.range 17).toArray.mapM fun j =>
      if i == j then `(term| 2) else `(term| 0)
    `(term| [$cells,*])
  `(term| Mathlib.Tactic.Matrix.ofLists 17 17 [$rows,*])

theorem checkedLargeCast : (diagonalTwo17 : Matrix (Fin 17) (Fin 17) ℂ).det ≠ 0 := by
  det_ne_zero { executable := "must-not-launch" }

example (_x : ℂ) : True := by
  fail_if_success
    have : (!![_x, 3; 1, 4] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by example_certificate
  fail_if_success
    have : (!![2, 4; 1, 2] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
      run_tac do
        detNeZero fun _ _ =>
          return { dimension := 2, modulus := 3, inverse := [[2, 0], [1, 1]] }
  fail_if_success
    have : (!![2, 3; 1, 4] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 1 := by example_certificate
  fail_if_success
    have : (!![(1 / 2 : ℂ), 3; 1, 4] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
      example_certificate
  trivial

-- A local, nonstandard numeral instance must be checked against the actual goal.
example : True := by
  let : OfNat ℂ 2 := ⟨0⟩
  fail_if_success
    have : (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
      det_ne_zero { executable := "must-not-launch" }
  fail_if_success
    have : (diagonalTwo17 : Matrix (Fin 17) (Fin 17) ℂ).det ≠ 0 := by
      det_ne_zero { executable := "must-not-launch" }
  trivial

run_cmd do
  for decl in [``complex, ``abstractRing, ``reversed, ``namedGoal, ``arithmetic, ``lists,
      ``triangular, ``empty, ``singleton, ``integer, ``integerRenamed, ``checkedLargeCast] do
    for dependency in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "unexpected axiom {dependency} in {decl}"

end CharZeroTests
