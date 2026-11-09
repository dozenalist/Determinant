/-
Copyright (c) 2026 Carter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter
-/
module

public import Determinant.Modular
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.Matrix.OfLists

/-!
# Data and soundness of offline modular certificates

Raw data is validated before arithmetic. All successful replay paths require a
checked equality connecting the extracted integer rows with the current goal.
The executable checkers are ordinary Lean definitions, with proved soundness;
their concrete acceptance must itself be proved (never asserted by a producer).
-/

@[expose] public section

namespace Determinant

/-- Version 1 has two deterministic certificate kinds with different obligations. -/
inductive CertificateKind where
  | fullInverse
  | unitUpperProduct
  deriving Repr, DecidableEq, Inhabited

/-- Untrusted, data-only candidate. Integers and the modulus have arbitrary precision.
String kind tags allow a parser to report unsupported formats rather than reinterpret them. -/
structure RawCertificate where
  version : ℕ := 1
  dimension : ℕ
  modulus : ℕ
  kind : String := "full-inverse"
  inverse : List (List ℤ)
  deriving Repr, Inhabited

/-- Shape-validated data, independent of any proof about matrix arithmetic. -/
structure Certificate where
  dimension : ℕ
  modulus : ℕ
  kind : CertificateKind
  inverse : List (List ℤ)
  modulus_gt_one : 1 < modulus
  row_count : inverse.length = dimension
  row_lengths : ∀ row ∈ inverse, row.length = dimension

/-- Validate the version, kind, modulus and exact shape against the actual goal dimension.
Neither padding nor truncation by `ofLists` is permitted at this boundary. -/
def RawCertificate.validate (expectedDimension : ℕ) (raw : RawCertificate) :
    Except String Certificate := do
  unless raw.version == 1 do throw "unsupported certificate version"
  let kind ← match raw.kind with
    | "full-inverse" => pure CertificateKind.fullInverse
    | "unit-upper-product" => pure CertificateKind.unitUpperProduct
    | _ => throw "unsupported certificate kind"
  unless raw.dimension == expectedDimension do throw "certificate dimension does not match goal"
  if hp : 1 < raw.modulus then
    if hr : raw.inverse.length = raw.dimension then
      if hc : ∀ row ∈ raw.inverse, row.length = raw.dimension then
        return ⟨raw.dimension, raw.modulus, kind, raw.inverse, hp, hr, hc⟩
      else throw "certificate has a ragged or incorrectly sized row"
    else throw "certificate has an incorrect row count"
  else throw "certificate modulus must be greater than one"

open Mathlib.Tactic.Matrix

/-- Row-major reduction, used once before checking products. -/
def residueRows (p : ℕ) (rows : List (List ℤ)) : List (List ℤ) :=
  rows.map (List.map (fun x => x % (p : ℤ)))

/-- Integer rows of the identity, including the empty identity. -/
def identityRows (n : ℕ) : List (List ℤ) :=
  List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => if i = j then 1 else 0

theorem ofLists_identityRows (n : ℕ) : ofLists n n (identityRows n) = 1 := by
  ext i j
  simp [identityRows, ofLists_apply, ofList_apply, List.getD, Matrix.one_apply]

/-- Reduction of signed entries preserves their modular images. -/
theorem map_residueRows (p n : ℕ) (rows : List (List ℤ)) :
    (ofLists n n (residueRows p rows)).map (Int.castRingHom (ZMod p)) =
      (ofLists n n rows).map (Int.castRingHom (ZMod p)) := by
  ext i j
  simp only [Matrix.map_apply, ofLists_apply, ofList_apply, residueRows]
  rw [← show List.map (fun x : ℤ => x % (p : ℤ)) [] = [] from rfl, List.getD_map]
  rw [← Int.zero_emod (p : ℤ), List.getD_map]
  exact ZMod.intCast_mod _ _

/-- The full list-product bridge. Its hypotheses can be built by dot-product expansion
and certified arithmetic, or proved by kernel evaluation of `checkFull`. -/
theorem modular_right_inverse_of_lists {n p : ℕ} {a b c : List (List ℤ)}
    (hmul : ListMatrix.mul n n n a b = c)
    (hmod : residueRows p c = identityRows n) :
    (ofLists n n a).map (Int.castRingHom (ZMod p)) *
      (ofLists n n b).map (Int.castRingHom (ZMod p)) = 1 := by
  rw [← Matrix.map_mul, ofLists_mul hmul, ← map_residueRows p n c, hmod,
    ofLists_identityRows]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- Full-product replay against the original integer table. The normalization equality
is proof evidence, not a runtime comparison of extracted data. -/
theorem det_ne_zero_of_full_certificate {n p : ℕ} (hp : 1 < p)
    {original a b c : List (List ℤ)} (ha : residueRows p original = a)
    (hmul : ListMatrix.mul n n n a b = c)
    (hmod : residueRows p c = identityRows n) : (ofLists n n original).det ≠ 0 := by
  apply det_ne_zero_of_modular_right_inverse hp
    (B := (ofLists n n b).map (Int.castRingHom (ZMod p)))
  rw [← map_residueRows p n original, ha]
  exact modular_right_inverse_of_lists hmul hmod

/-- Strict executable full-product checker. An equality to `true` must be kernel checked. -/
def checkFull (n p : ℕ) (a b : List (List ℤ)) : Bool :=
  decide (residueRows p (ListMatrix.mul n n n a b) = identityRows n)

theorem checkFull_sound {n p : ℕ} (hp : 1 < p) {original a b : List (List ℤ)}
    (ha : residueRows p original = a) (h : checkFull n p a b = true) :
    (ofLists n n original).det ≠ 0 :=
  det_ne_zero_of_full_certificate hp ha rfl (of_decide_eq_true h)

/-- The reduced certificate's exact obligations. The implication is tested before the dot
product, so no above-diagonal product entry is constructed or evaluated. -/
def UnitUpperConditions (n p : ℕ) (a b : List (List ℤ)) : Prop :=
  ∀ i j : Fin n, j ≤ i →
    ListMatrix.dotProduct n (a.getD i []) ((ListMatrix.transpose n b).getD j []) % (p : ℤ) =
      if i = j then 1 else 0

instance (n p : ℕ) (a b : List (List ℤ)) : Decidable (UnitUpperConditions n p a b) :=
  inferInstanceAs (Decidable (∀ i j : Fin n, j ≤ i → _))

/-- The reduced executable checker tests exactly `n(n+1)/2` dot products on success.
It does not build the full product. Column lookup uses Mathlib's shared transpose. -/
def checkUnitUpper (n p : ℕ) (a b : List (List ℤ)) : Bool :=
  decide (UnitUpperConditions n p a b)

private theorem modular_product_entry {n p : ℕ} (a b : List (List ℤ)) (i j : Fin n) :
    ((ofLists n n a).map (Int.castRingHom (ZMod p)) *
        (ofLists n n b).map (Int.castRingHom (ZMod p))) i j =
      (ListMatrix.dotProduct n (a.getD i []) ((ListMatrix.transpose n b).getD j []) : ℤ) := by
  have hmul : ofLists n n a * ofLists n n b =
      ofLists n n (ListMatrix.mul n n n a b) := ofLists_mul rfl
  rw [← Matrix.map_mul, hmul]
  simp only [Matrix.map_apply, ofLists_apply, ofList_apply]
  rw [ListMatrix.getD_mul a b i.isLt j.isLt]
  rfl

/-- Separate soundness for the weaker format. No full inverse equation is claimed. -/
theorem det_ne_zero_of_unit_upper_certificate {n p : ℕ} (hp : 1 < p)
    {original a b : List (List ℤ)} (ha : residueRows p original = a)
    (h : UnitUpperConditions n p a b) : (ofLists n n original).det ≠ 0 := by
  apply det_ne_zero_of_modular_unit_upper_product hp
    (B := (ofLists n n b).map (Int.castRingHom (ZMod p)))
  · rw [← map_residueRows p n original, ha]
    intro i j hij
    have hne : i ≠ j := ne_of_gt hij
    rw [modular_product_entry, ← ZMod.intCast_mod _ p, h i j (le_of_lt hij)]
    simp [hne]
  · rw [← map_residueRows p n original, ha]
    intro i
    rw [modular_product_entry, ← ZMod.intCast_mod _ p, h i i le_rfl]
    simp

theorem checkUnitUpper_sound {n p : ℕ} (hp : 1 < p) {original a b : List (List ℤ)}
    (ha : residueRows p original = a) (h : checkUnitUpper n p a b = true) :
    (ofLists n n original).det ≠ 0 :=
  det_ne_zero_of_unit_upper_certificate hp ha (of_decide_eq_true h)

end Determinant
