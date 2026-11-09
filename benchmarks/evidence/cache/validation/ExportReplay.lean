import Determinant
example : (!![2,3;1,2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular { version := 1, dimension := 2, modulus := 5, kind := "full-inverse", inverse := [[2, 2], [4, 2]] }
