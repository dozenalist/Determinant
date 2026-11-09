import Determinant

open Matrix

namespace DeterminantTests

open Lean in
macro "testUpper%" n:num : term => do
  let size := n.getNat
  let mut rows : Array (Array (TSyntax `term)) := #[]
  for i in [:size] do
    let mut row := #[]
    for j in [:size] do
      let value := quote (if j < i then 0 else 100000 + i * 131 + j * 17)
      let entry ← if i == j && i % 2 == 1 then `(term| -$value) else pure value
      row := row.push entry
    rows := rows.push row
  `(!![$[$[$rows],*];*])

theorem positive : (!![2, 3; 0, 5] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_triangular

theorem negative : (!![-2, 17, -31; 0, 5, 9; 0, 0, -7] :
    Matrix (Fin 3) (Fin 3) ℤ).det ≠ 0 := by
  certify_det_ne_zero_triangular

theorem empty (A : Matrix (Fin 0) (Fin 0) ℤ) : A.det ≠ 0 := by
  certify_det_ne_zero_triangular

example : (!![] : Matrix (Fin 0) (Fin 0) ℤ).det ≠ 0 := by
  certify_det_ne_zero_triangular

theorem singleton : (!![-123456789012345678901234567890123456789] :
    Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by
  certify_det_ne_zero_triangular

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hundred : (testUpper% 100 : Matrix (Fin 100) (Fin 100) ℤ).det ≠ 0 := by
  certify_det_ne_zero_triangular

def named : Matrix (Fin 3) (Fin 3) ℤ := !![3, 4, -5; 0, -7, 8; 0, 0, 11]

theorem named_ok : named.det ≠ 0 := by
  certify_det_ne_zero_triangular

example : 0 ≠ named.det := by
  certify_det_ne_zero_triangular

example : (let A : Matrix (Fin 2) (Fin 2) ℤ := !![2, 9; 0, -3]; A.det ≠ 0) := by
  dsimp only
  certify_det_ne_zero_triangular

example : True := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![2, 9; 0, -3]
  have : A.det ≠ 0 := by certify_det_ne_zero_triangular
  trivial

example : (!![2 + 3, 9; 7 - 7, -(4 * 5)] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_triangular

example (x : ℤ) : (!![2, x; 0, -3] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_triangular

example (a b x : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (!![a, x; 0, b] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_triangular

example (a b x y : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hy : y = 0) :
    (!![a, x; y, b] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_triangular

theorem symbolic {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CommRing R] [IsDomain R] (A : Matrix ι ι R) (htri : A.IsUpperTriangular)
    (hdiag : ∀ i, A i i ≠ 0) : A.det ≠ 0 := by
  certify_det_ne_zero_triangular

example {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CommRing R] [IsDomain R] (A : Matrix ι ι R) (htri : A.IsUpperTriangular)
    (hdiag : ∀ i, A.diag i ≠ 0) : 0 ≠ A.det := by
  certify_det_ne_zero_triangular

example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (htri : ∀ ⦃i j⦄, j < i → A i j = 0) (hdiag : ∀ i, A.diag i ≠ 0) : A.det ≠ 0 := by
  certify_det_ne_zero_triangular

-- Expected failures must leave the goal intact so that callers can try another route.
example : True := by
  fail_if_success
    have : (!![2, 3; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      certify_det_ne_zero_triangular
  fail_if_success
    have : (!![2, 3; 4, 5] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      certify_det_ne_zero_triangular
  fail_if_success
    have : (!![0] : Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by
      certify_det_ne_zero_triangular
  fail_if_success
    have : (1 : ℤ) ≠ 0 := by
      certify_det_ne_zero_triangular
  trivial

#print axioms positive
#print axioms negative
#print axioms empty
#print axioms singleton
#print axioms hundred
#print axioms named_ok
#print axioms symbolic

-- Reject all dependencies beyond ordinary Mathlib logical axioms automatically.
run_cmd do
  for decl in [``positive, ``negative, ``empty, ``singleton, ``hundred, ``named_ok, ``symbolic] do
    for dependency in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "unexpected axiom {dependency} in {decl}"

end DeterminantTests
