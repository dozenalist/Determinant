/-
Copyright (c) 2026 Carter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter
-/
module

public import Determinant.Certificate

/-! # Strict arithmetic on nonnegative residue representatives

Natural arithmetic uses the kernel's literal arithmetic directly. The bridge below
relates it to Mathlib's padded list dot products; no machine arithmetic is trusted.
-/

@[expose] public section

namespace Determinant

open Mathlib.Tactic.Matrix

def intRows (rows : List (List ℕ)) : List (List ℤ) := rows.map (List.map Int.ofNat)

def natDot : ℕ → List ℕ → List ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, a :: as, b :: bs => Nat.add (Nat.mul a b) (natDot n as bs)
  | _ + 1, _, _ => 0

theorem natDot_nil_left (n : ℕ) (b : List ℕ) : natDot n [] b = 0 := by
  cases n <;> rfl

theorem natDot_nil_right (n : ℕ) (a : List ℕ) : natDot n a [] = 0 := by
  cases n <;> cases a <;> rfl

theorem natDot_cast (n : ℕ) (a b : List ℕ) :
    (natDot n a b : ℤ) = ListMatrix.dotProduct n (a.map Int.ofNat) (b.map Int.ofNat) := by
  induction n generalizing a b with
  | zero => simp only [natDot, ListMatrix.dotProduct_zero, Nat.cast_zero]
  | succ n ih =>
    cases a <;> cases b <;>
      simp only [natDot, List.map_nil, List.map_cons, ListMatrix.dotProduct_add_one,
        List.headD_nil, List.headD_cons, List.tail_nil, List.tail_cons,
        Int.natCast_zero, zero_mul, mul_zero, zero_add]
    · simpa only [List.map_nil, natDot_nil_left, Nat.cast_zero] using (ih [] [])
    · simpa only [List.map_nil, natDot_nil_left, Nat.cast_zero] using (ih [] _)
    · simpa only [List.map_nil, natDot_nil_right, Nat.cast_zero] using (ih _ [])
    · rename_i a as b bs
      change (↑(a * b + natDot n as bs) : ℤ) = _
      rw [Int.natCast_add, Int.natCast_mul, ih]
      rfl

/-- Use the library's structural list operations without a dimension argument in
each recursive call. The row-width proof below supplies the padded specification. -/
def natDotZip (a b : List ℕ) : ℕ :=
  (a.zipWith Nat.mul b).foldr Nat.add 0

theorem natDotZip_eq (a b : List ℕ) : natDotZip a b = natDot a.length a b := by
  induction a generalizing b with
  | nil => rfl
  | cons x xs ih =>
    cases b with
    | nil => simp [natDotZip, natDot_nil_right]
    | cons y ys =>
      change Nat.add (Nat.mul x y) (natDotZip xs ys) =
        Nat.add (Nat.mul x y) (natDot xs.length xs ys)
      rw [ih]

/-- Fuse the structural zip and sum, avoiding an intermediate list during kernel reduction. -/
def natDotFused : List ℕ → List ℕ → ℕ
  | a :: as, b :: bs => Nat.add (Nat.mul a b) (natDotFused as bs)
  | _, _ => 0

theorem natDotFused_eq (a b : List ℕ) : natDotFused a b = natDotZip a b := by
  induction a generalizing b with
  | nil => rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      change Nat.add (Nat.mul x y) (natDotFused xs ys) =
        Nat.add (Nat.mul x y) (natDotZip xs ys)
      rw [ih]

def checkNatRow (upper : Bool) (n p i : ℕ) (row : List ℕ) (bt : List (List ℕ)) : Bool :=
  bt.zipIdx.all fun (col, j) =>
    if upper && i < j then true
    else natDotFused row col % p == if i == j then 1 else 0

def checkNatRows (upper : Bool) (n p start : ℕ) (a bt : List (List ℕ)) : Bool :=
  (a.zipIdx start).all fun (row, i) => checkNatRow upper n p i row bt

def checkNat (upper : Bool) (n p : ℕ) (a bt : List (List ℕ)) : Bool :=
  checkNatRows upper n p 0 a bt

theorem checkNatRows_nil (upper : Bool) (n p i : ℕ) (bt : List (List ℕ)) :
    checkNatRows upper n p i [] bt = true := rfl

theorem checkNatRows_cons {upper : Bool} {n p i : ℕ} {row : List ℕ}
    {rows bt : List (List ℕ)} (hr : checkNatRow upper n p i row bt = true)
    (ht : checkNatRows upper n p (i + 1) rows bt = true) :
    checkNatRows upper n p i (row :: rows) bt = true := by
  change (checkNatRow upper n p i row bt && checkNatRows upper n p (i + 1) rows bt) = true
  exact Bool.and_eq_true_iff.mpr ⟨hr, ht⟩

theorem checkNat_entry {upper : Bool} {n p : ℕ} {a bt : List (List ℕ)}
    (ha : a.length = n) (hw : a.all (fun row => row.length == n) = true)
    (ht : bt.length = n) (h : checkNat upper n p a bt = true)
    (i j : Fin n) (hij : j ≤ i) :
    natDot n (a.getD i []) (bt.getD j []) % p = if i = j then 1 else 0 := by
  have hi : i.val < a.length := by simp [ha]
  have hj : j.val < bt.length := by simp [ht]
  have hmi : (a[i.val], i.val) ∈ a.zipIdx := by
    simp [List.mk_mem_zipIdx_iff_getElem?, hi]
  have hmj : (bt[j.val], j.val) ∈ bt.zipIdx := by
    simp [List.mk_mem_zipIdx_iff_getElem?, hj]
  have hrow := List.all_eq_true.mp h _ hmi
  have hcell := List.all_eq_true.mp hrow _ hmj
  have hwidth : (a[i.val]).length = n := by
    simpa using List.all_eq_true.mp hw _ (List.getElem_mem hi)
  have hnot : ¬ i.val < j.val := Nat.not_lt.mpr hij
  simpa [natDotFused_eq, natDotZip_eq, hwidth, hnot,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Fin.ext_iff] using hcell

theorem intRows_getD (rows : List (List ℕ)) (i : ℕ) :
    (intRows rows).getD i [] = (rows.getD i []).map Int.ofNat := by
  simpa [intRows] using (List.getD_map (f := List.map Int.ofNat) (l := rows) (n := i)
    (d := []))

/-- Both formats are deterministic: `upper = false` checks every dot product;
`upper = true` skips exactly those above the diagonal. -/
theorem checkNat_sound {upper : Bool} {n p : ℕ} {original : List (List ℤ)}
    {a b bt : List (List ℕ)} (hp : 1 < p)
    (ha : residueRows p original = intRows a)
    (hat : a.length = n) (hw : a.all (fun row => row.length == n) = true) (hbt : bt.length = n)
    (ht : ListMatrix.transpose n (intRows b) = intRows bt)
    (h : checkNat upper n p a bt = true) : (ofLists n n original).det ≠ 0 := by
  apply det_ne_zero_of_unit_upper_certificate hp ha (b := intRows b)
  intro i j hij
  rw [ht, intRows_getD, intRows_getD, ← natDot_cast, ← Int.natCast_emod]
  rw [checkNat_entry hat hw hbt h i j hij]
  split <;> rfl

end Determinant
