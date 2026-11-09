/-
Copyright (c) 2026 Carter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter
-/
module

public import Determinant.Tactic.Dispatch
public meta import Determinant.Tactic.Dispatch
public meta import Mathlib.Tactic.Echelon.Cert

/-! # Integer-entry determinant certification in characteristic zero -/

public section

namespace Determinant

open Mathlib.Tactic.Matrix

/-- Transport integer determinant nonvanishing through the injective integer cast.
No domain assumption on the target ring is needed. -/
theorem det_ne_zero_of_int_cast {R ι : Type*} [CommRing R] [CharZero R]
    [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ} {B : Matrix ι ι R}
    (heq : B = A.map (Int.castRingHom R)) (h : A.det ≠ 0) : B.det ≠ 0 := by
  rw [heq]
  change (A.map fun x => (x : R)).det ≠ 0
  rw [← Int.cast_det]
  exact_mod_cast h

/-- A structural cast bridge, avoiding expansion into individual matrix indices. -/
theorem ofLists_int_cast {R : Type*} [CommRing R] (m n : ℕ) (rows : List (List ℤ)) :
    (ofLists m n rows).map (Int.castRingHom R) =
      ofLists m n (rows.map (List.map (Int.castRingHom R))) := by
  ext i j
  simp only [Matrix.map_apply, ofLists_apply, ofList_apply]
  have hrows := List.getD_map (l := rows) (d := [])
    (n := i.val) (List.map (Int.castRingHom R))
  rw [List.map_nil] at hrows
  rw [hrows]
  simpa using (List.getD_map (l := rows.getD i.val []) (d := 0)
    (n := j.val) (Int.castRingHom R)).symm

/-- Numeral interpretation with definitionally canonical zero and one. -/
@[expose] def literalNatCast (R : Type*) [CommRing R] : ℕ → R
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 2 : ℕ)

theorem literalNatCast_eq {R : Type*} [CommRing R] (n : ℕ) :
    literalNatCast R n = (n : R) := by
  cases n with
  | zero => exact Nat.cast_zero.symm
  | succ n =>
    cases n with
    | zero => exact Nat.cast_one.symm
    | succ n => rfl

/-- A numeral interpreter whose connection to integer casting is proved once. -/
@[expose] def literalIntCast (R : Type*) [CommRing R] : ℤ → R
  | .ofNat n => literalNatCast R n
  | .negSucc n => -literalNatCast R (n + 1)

theorem literalIntCast_eq {R : Type*} [CommRing R] (z : ℤ) :
    literalIntCast R z = (z : R) := by
  cases z <;> simp [literalIntCast, literalNatCast_eq, Int.cast_negSucc]

/-- Reflect whole numeral tables, avoiding a separate cast proof for every entry. -/
theorem ofLists_literalIntCast {R : Type*} [CommRing R] (m n : ℕ)
    (rows : List (List ℤ)) :
    ofLists m n (rows.map (List.map (literalIntCast R))) =
      (ofLists m n rows).map (Int.castRingHom R) := by
  simpa only [show literalIntCast R = Int.castRingHom R from
    funext literalIntCast_eq] using (ofLists_int_cast (R := R) m n rows).symm

end Determinant

public meta section

open Lean Meta Elab Tactic Qq
open Mathlib.Tactic.Matrix Mathlib.Tactic.Echelon

namespace Determinant.Tactic

/-- Candidate numeral data only; the reflected table is checked against the actual
entries before it is used. Custom instances therefore cannot change the goal silently. -/
private def literalIntegerEntries? (entries : Array (Array Expr)) :
    MetaM (Option (Array (Array Expr))) := OptionT.run do
  entries.mapM fun row => row.mapM fun e => do
    let (base, negative) := if e.isAppOf ``Neg.neg then (e.appArg!, true) else (e, false)
    if negative && e.getAppArgs[1]!.isFVar then failure
    let_expr OfNat.ofNat _ number inst := base | failure
    -- Reject noncanonical instances before attempting conversion in concrete rings:
    -- reducing distinct real/complex numerals can be much more expensive than failing.
    if inst.isAppOf ``instOfNatAtLeastTwo then
      if inst.getAppArgs[2]!.isFVar then failure
    else if inst.isAppOf ``Zero.toOfNat0 || inst.isAppOf ``One.toOfNat1 then
      if inst.getAppArgs[1]!.isFVar then failure
    else failure
    let n ← getNatValue? number
    let magnitude := mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
    return if negative then mkIntNeg magnitude else magnitude

/-- Proof-producing fallback for arithmetic expressions. -/
private def integerCastBridge {u : Level} (R : Q(Type u)) (_inst : Q(CommRing $R))
    (n : Nat) (entries : Array (Array Expr)) (originalRows : Q(List (List $R))) :
    MetaM ((rows : Q(List (List ℤ))) × Q(ofLists $n $n $originalRows =
      (ofLists $n $n $rows).map (Int.castRingHom $R))) := do
  let instRing : Q(Ring $R) ← synthInstanceQ q(Ring $R)
  let mut ints := #[]
  let mut rowProofs := []
  -- Repeated literals (especially 0/1) share both normalization work and proof terms.
  let mut cache : ExprMap (Expr × Expr) := {}
  for i in [:n] do
    let mut intRow := #[]
    let mut proofs := []
    for j in [:n] do
      have e : Q($R) := (entries[i]!)[j]!
      let result : Expr × Expr ← match cache.get? e with
        | some result => pure result
        | none => do
          let evaluated ← try Mathlib.Meta.NormNum.derive e catch _ =>
            throwError "det_ne_zero: entry ({i}, {j}) is not a closed integer: {e}"
          let some ⟨value, z, h⟩ := evaluated.toInt instRing
            | throwError "det_ne_zero: entry ({i}, {j}) is not an integer: {e}"
          have h : Q($e = ($z : $R)) := q(($h).out)
          -- Keep the fast literal path in downstream extraction/normalization.
          let magnitude := mkApp (mkConst ``Int.ofNat) (mkRawNatLit value.natAbs)
          let canonical := if value < 0 then mkIntNeg magnitude else magnitude
          cache := cache.insert e (canonical, h)
          pure (canonical, h)
      have z : Q(ℤ) := result.1
      have h : Q($e = ($z : $R)) := result.2
      intRow := intRow.push z
      proofs := ⟨e, q(($z : $R)), h⟩ :: proofs
    ints := ints.push intRow
    rowProofs := mkListCongr (α := R) proofs.reverse :: rowProofs
  let integral := ListMatrixLit.ofArray (α := q(ℤ)) q(inferInstance) n n ints
  have rows : Q(List (List ℤ)) := integral.lit
  have hrows : Q($originalRows = List.map (List.map (Int.castRingHom $R)) $rows) :=
    (mkListCongr (α := q(List $R)) rowProofs.reverse).2.2
  have heq : Q(ofLists $n $n $originalRows =
      (ofLists $n $n $rows).map (Int.castRingHom $R)) :=
    q((congrArg (ofLists $n $n) $hrows).trans (ofLists_int_cast $n $n $rows).symm)
  return ⟨rows, heq⟩

/-- Reflect numeral tables or normalize arithmetic, certify the integer matrix using
the same dispatcher, and transport the result to the target ring. -/
def detNeZero (producer : CertificateProducer) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let_expr Ne _ lhs rhs := target
    | throwError "det_ne_zero: expected A.det ≠ 0 or 0 ≠ A.det"
  let (det, zero, reversed) ← if lhs.isAppOf ``Matrix.det then pure (lhs, rhs, false)
    else if rhs.isAppOf ``Matrix.det then pure (rhs, lhs, true)
    else throwError "det_ne_zero: expected a determinant-nonzero goal"
  let ⟨u, R, _⟩ ← inferTypeQ' lhs
  let _instCommRing : Q(CommRing $R) ← synthInstanceQ q(CommRing $R)
  let _instCharZero : Q(CharZero $R) ← try synthInstanceQ q(CharZero $R) catch _ =>
    throwError "det_ne_zero: the coefficient ring must have characteristic zero (CharZero)"
  unless ← isDefEq zero q((0 : $R)) do
    throwError "det_ne_zero: expected comparison with zero"
  if ← isDefEq R q(ℤ) then
    detNeZeroInt producer
    return
  let started ← IO.monoMsNow
  let A := det.getAppArgs.back!
  let (n, _, entries) ← matrixEntries A
  let original := ListMatrixLit.ofArray (α := R) q(inferInstance) n n entries
  have originalRows : Q(List (List $R)) := original.lit
  let fastBridge? : Option ((rows : Q(List (List ℤ))) ×
      Q(ofLists $n $n $originalRows =
        (ofLists $n $n $rows).map (Int.castRingHom $R))) ←
    match ← literalIntegerEntries? entries with
    | none => pure none
    | some ints => do
      let integral := ListMatrixLit.ofArray (α := q(ℤ)) q(inferInstance) n n ints
      have rows : Q(List (List ℤ)) := integral.lit
      if n > 16 then
        -- Check the large conversion once, with the kernel, and reference its
        -- theorem during final assembly instead of reducing the table again.
        let saved ← saveState
        try
          let h ← withOptions (fun options => options.setBool `Elab.async false) <|
            mkAuxTheorem q(ofLists $n $n $originalRows =
              (ofLists $n $n $rows).map (Int.castRingHom $R))
              q(ofLists_literalIntCast (R := $R) $n $n $rows)
              (zetaDelta := true) (cache := false)
          pure (some ⟨rows, h⟩)
        catch error =>
          if error.isInterrupt then throw error
          saved.restore
          pure none
      else if ← isDefEq originalRows q(List.map (List.map (literalIntCast $R)) $rows) then
        -- Small conversions are also checked in the completed theorem.
        haveI' : $originalRows =Q List.map (List.map (literalIntCast $R)) $rows := ⟨⟩
        pure (some ⟨rows, q(ofLists_literalIntCast (R := $R) $n $n $rows)⟩)
      else pure none
  let ⟨rows, heq⟩ ← match fastBridge? with
    | some bridge => pure bridge
    | none => integerCastBridge R _instCommRing n entries originalRows
  trace[Determinant.timing] "integer cast bridge: {(← IO.monoMsNow) - started} ms"
  let intGoal ← mkFreshExprSyntheticOpaqueMVar q((ofLists $n $n $rows).det ≠ 0)
  let savedGoals ← getGoals
  try
    setGoals [intGoal.mvarId!]
    detNeZeroInt producer
  finally
    setGoals savedGoals
  have hi : Q((ofLists $n $n $rows).det ≠ 0) := ← instantiateMVars intGoal
  let proof : Expr := q(det_ne_zero_of_int_cast $heq $hi)
  let proof ← if reversed then mkAppM ``Ne.symm #[proof] else pure proof
  unless ← isDefEq (← inferType proof) target do
    throwError "det_ne_zero: integer cast does not match the original matrix"
  goal.assign proof
  replaceMainGoal []

/-- Prove determinant nonvanishing for concrete integer-entry matrices over a
commutative ring of characteristic zero, using `det_ne_zero_int` for certification.
The optional data-only term has type `ProducerConfig`. -/
elab "det_ne_zero" config:(ppSpace term)? : tactic => do
  let config ← match config with
    | none => pure ({} : ProducerConfig)
    | some config => unsafe Term.evalTerm ProducerConfig q(ProducerConfig) config
  detNeZero (processProducer config)

end Determinant.Tactic
