/-
Copyright (c) 2026 Carter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.Echelon.Reflection

/-!
# Triangular determinant certificates

The determinant criterion is Mathlib's, over any integral domain. The list bridge
reuses its lower triangular certificate on the transpose; no determinant is evaluated.
-/

public section

namespace Determinant

/-- An upper triangular matrix over an integral domain has nonzero determinant
when its diagonal is nonzero. -/
theorem det_ne_zero_of_upperTriangular {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [CommRing R] [IsDomain R] {A : Matrix ι ι R}
    (htri : A.IsUpperTriangular) (hdiag : ∀ i, A i i ≠ 0) : A.det ≠ 0 :=
  htri.det_ne_zero_iff.mpr hdiag

open Mathlib.Tactic.Matrix Mathlib.Tactic.Echelon

/-- Replay a Mathlib lower triangular certificate on the transpose of a list matrix.
The equality connects the candidate transpose to the original rows in the kernel. -/
theorem det_ne_zero_of_transpose_certificate {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} {rows transposed : List (List R)}
    (heq : ListMatrix.transpose n rows = transposed)
    (h : IsLowerTriangularDiagList 0 n transposed) : (ofLists n n rows).det ≠ 0 := by
  have hdet := (isLowerTriangular_ofLists h).det_ne_zero_iff.mpr (diag_ofLists_ne_zero h)
  rw [← heq, ofLists_transpose, Matrix.det_transpose] at hdet
  exact hdet

end Determinant
