/-
Copyright (c) 2026 Carter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter
-/
module

public import Determinant.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Modular determinant certificates

Only `1 < p` is required. Primality is a policy for a future certificate producer,
not a trusted assertion or an assumption of the checker.
-/

public section

namespace Determinant

/-- Determinant nonvanishing lifts along any ring homomorphism; injectivity is unnecessary. -/
theorem det_ne_zero_of_map {ι R S : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] (f : R →+* S) {A : Matrix ι ι R}
    (h : (A.map f).det ≠ 0) : A.det ≠ 0 := by
  intro hz
  apply h
  change (f.mapMatrix A).det = 0
  rw [← f.map_det, hz, map_zero]

/-- Lift nonvanishing from the modular image of an integer matrix. -/
theorem det_ne_zero_of_modular_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} {A : Matrix ι ι ℤ}
    (h : (A.map (Int.castRingHom (ZMod p))).det ≠ 0) : A.det ≠ 0 :=
  det_ne_zero_of_map (Int.castRingHom (ZMod p)) h

/-- A checked right inverse modulo any `p > 1` certifies the integer determinant. -/
theorem det_ne_zero_of_modular_right_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (hp : 1 < p) {A : Matrix ι ι ℤ} {B : Matrix ι ι (ZMod p)}
    (h : A.map (Int.castRingHom (ZMod p)) * B = 1) : A.det ≠ 0 := by
  let : Fact (1 < p) := ⟨hp⟩
  exact det_ne_zero_of_modular_image (Matrix.det_ne_zero_of_right_inverse h)

/-- The reduced certificate works over nontrivial commutative rings, even with zero divisors.
Diagonal entries must be one, rather than merely nonzero. -/
theorem det_ne_zero_of_unit_upper_product {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [CommRing R] [Nontrivial R] {A B : Matrix ι ι R}
    (htri : (A * B).IsUpperTriangular) (hdiag : ∀ i, (A * B) i i = 1) : A.det ≠ 0 := by
  have hprod : (A * B).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular htri]
    simp [hdiag]
  intro hz
  rw [Matrix.det_mul, hz, zero_mul] at hprod
  exact zero_ne_one hprod

/-- Lift the reduced unit-upper-product certificate from a modular ring. -/
theorem det_ne_zero_of_modular_unit_upper_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] {p : ℕ} (hp : 1 < p) {A : Matrix ι ι ℤ}
    {B : Matrix ι ι (ZMod p)}
    (htri : (A.map (Int.castRingHom (ZMod p)) * B).IsUpperTriangular)
    (hdiag : ∀ i, (A.map (Int.castRingHom (ZMod p)) * B) i i = 1) : A.det ≠ 0 := by
  let : Fact (1 < p) := ⟨hp⟩
  exact det_ne_zero_of_modular_image (det_ne_zero_of_unit_upper_product htri hdiag)

end Determinant
