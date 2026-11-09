import Determinant

open Lean Elab Tactic Determinant Determinant.Tactic

namespace DispatchTests

-- Any call of this producer is a test failure, including on the empty case.
elab "triangular_only" : tactic =>
  detNeZeroInt fun _ _ => throwError "triangular route launched a producer"

theorem empty : (!![] : Matrix (Fin 0) (Fin 0) ℤ).det ≠ 0 := by triangular_only
theorem singleton : (!![-7] : Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by triangular_only
theorem triangular : (!![-2, 5; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero_int { executable := "must-not-launch" }
theorem reversed : 0 ≠ (!![-2, 5; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ).det := by
  triangular_only

theorem symbolic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (ht : A.IsUpperTriangular) (hd : ∀ i, A i i ≠ 0) : A.det ≠ 0 := by
  det_ne_zero_int

def inverseFive : RawCertificate := {
  dimension := 2, modulus := 5, inverse := [[2, 2], [4, 2]] }

-- The producer sees the actual signed table. Successful replay must still check it.
elab "dense_certificate" : tactic =>
  detNeZeroInt fun n entries => do
    unless n == 2 && entries == #[2, 3, 1, 2] do throwError "incorrect extraction"
    return inverseFive

def named : Matrix (Fin 2) (Fin 2) ℤ := !![2, 3; 1, 2]
theorem dense : named.det ≠ 0 := by dense_certificate
theorem denseReversed : 0 ≠ named.det := by dense_certificate

def listMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  Mathlib.Tactic.Matrix.ofLists 2 2 [[2, 3], [1, 2]]
theorem denseLists : listMatrix.det ≠ 0 := by dense_certificate

def matrixAlias := listMatrix
theorem aliasLists : matrixAlias.det ≠ 0 := by dense_certificate

def letRows : Matrix (Fin 2) (Fin 2) ℤ :=
  Mathlib.Tactic.Matrix.ofLists 2 2 (let tail := [[1, 2]]; [2, 3] :: tail)
theorem denseLetRows : letRows.det ≠ 0 := by dense_certificate

-- Lean changes the list literal expansion at length 32, introducing balanced lets.
macro "identityLists40" : term => do
  let rows ← (List.range 40).toArray.mapM fun i => do
    let cells ← (List.range 40).toArray.mapM fun j =>
      if i == j then `(term| (1 : Int)) else `(term| (0 : Int))
    `(term| [$cells,*])
  `(term| Mathlib.Tactic.Matrix.ofLists 40 40 [$rows,*])

theorem largeListNotation : (identityLists40).det ≠ 0 := by triangular_only

example : int_matrix% [[2, -3], [-1, 2]] =
    (!![2, -3; -1, 2] : Matrix (Fin 2) (Fin 2) ℤ) := rfl

theorem quotedDense : (int_matrix% [[2, 3], [1, 2]]).det ≠ 0 := by dense_certificate
theorem quotedEmpty : (int_matrix% []).det ≠ 0 := by triangular_only
theorem jsonDense : (int_matrix% r#"[["2","3"],["1","2"]]"#).det ≠ 0 := by dense_certificate
example : int_matrix% r#"[["2","-3"],["-1","2"]]"# =
    (!![2, -3; -1, 2] : Matrix (Fin 2) (Fin 2) ℤ) := rfl
theorem quotedSigned : (int_matrix% [[-99999999999999999999999999999999999998, 33],
    [-4, 100000000000000000000000000000000000002]]).det ≠ 0 := by
  run_tac detNeZeroInt fun _ _ => pure inverseFive

set_option linter.unreachableTactic false in
example (_x : ℤ) : True := by
  fail_if_success
    have : (int_matrix% [[1, 0], [0]]).det ≠ 0 := by triangular_only
  fail_if_success
    have : (int_matrix% [[_x]]).det ≠ 0 := by triangular_only
  fail_if_success
    have : (int_matrix% r#"[["01"]]"#).det ≠ 0 := by triangular_only
  fail_if_success
    have : (int_matrix% r#"[[2]]"#).det ≠ 0 := by triangular_only
  fail_if_success
    have : (int_matrix% r#"[["1","0"],["0"]]"#).det ≠ 0 := by triangular_only
  fail_if_success
    have : (int_matrix% r#"[["-0"]]"#).det ≠ 0 := by triangular_only
  trivial

example : True := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![2, 3; 1, 2]
  have : A.det ≠ 0 := by dense_certificate
  trivial

example : True := by
  let A := named
  have : A.det ≠ 0 := by dense_certificate
  trivial

theorem emptyLists : (Mathlib.Tactic.Matrix.ofLists 0 0 ([] : List (List ℤ))).det ≠ 0 := by
  triangular_only

example : True := by
  fail_if_success
    have : (Mathlib.Tactic.Matrix.ofLists 2 2 ([[1, 0], [0, 1, 9]] : List (List ℤ))).det ≠ 0 := by
      triangular_only
  trivial

-- Backtracking restores the reversed target and all metavariables.
set_option linter.unusedTactic false in
example : 0 ≠ named.det := by
  first
  | det_ne_zero_int { executable := "determinant-producer-does-not-exist" }
  | dense_certificate

example (_A : Matrix (Fin 2) (Fin 2) ℤ) (_x : ℤ) : True := by
  fail_if_success
    have : _A.det ≠ 0 := by dense_certificate
  fail_if_success
    have : (!![_x, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by dense_certificate
  fail_if_success
    have : named.det ≠ 1 := by dense_certificate
  fail_if_success
    have : (1 : ℤ) ≠ 0 := by dense_certificate
  fail_if_success
    have : (!![2, 4; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      run_tac detNeZeroInt fun _ _ => pure inverseFive
  trivial

run_cmd do
  for decl in [``empty, ``singleton, ``triangular, ``reversed, ``symbolic, ``dense,
      ``denseReversed, ``denseLists, ``aliasLists, ``denseLetRows, ``largeListNotation,
      ``emptyLists, ``quotedDense, ``quotedEmpty, ``quotedSigned, ``jsonDense] do
    for dependency in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "unexpected axiom {dependency} in {decl}"

end DispatchTests
