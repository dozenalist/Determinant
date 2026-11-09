/-
Copyright (c) 2026 Carter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter
-/
module

public import Determinant.Basic
public meta import Mathlib.Tactic.Echelon.Cert
public meta import Mathlib.Tactic.Echelon.Rat
public meta import Determinant.Tactic.Matrix
public import Mathlib.Tactic.NormNum

/-!
# `certify_det_ne_zero_triangular`

Use triangularity and diagonal hypotheses first. Otherwise parse a concrete integer
matrix once and reuse Mathlib's shared list certificate on its transpose.
-/

public meta section

open Lean Meta Elab Tactic Qq
open Mathlib.Tactic.Matrix Mathlib.Tactic.Echelon

namespace Determinant.Triangular

/-- Prove a proposition from the local context, allowing introduced indices. -/
private def fromContext (type : Expr) : TacticM Expr := do
  let g ← mkFreshExprSyntheticOpaqueMVar type
  let saved ← getGoals
  setGoals [g.mvarId!]
  try
    Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic| solve
      | assumption
      | (intros; assumption)
      | (intro i; exact isEmptyElim i)))
    instantiateMVars g
  finally
    setGoals saved

/-- Try the public criterion without enumerating indices or inspecting entries. -/
private def fromHypotheses (goal : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    let gs ← goal.apply (← mkConstWithFreshMVarLevels ``det_ne_zero_of_upperTriangular)
    for g in gs do
      g.assign (← fromContext (← g.getType))
    return true
  catch _ =>
    saved.restore
    return false

/-- Check the relevant entries and assemble a kernel-checked list certificate. -/
private def concreteProof (A : Expr) : TacticM Expr := do
  let (n, entries) ← Tactic.integerEntries A
  let mut normalized : Array (Array Expr) := #[]
  let mut rowProofs : List ((a : Q(List ℤ)) × (b : Q(List ℤ)) × Q($a = $b)) := []
  let arithmetic := normNumCertifier q(ℤ)
  let certifier : EntryCertifier q(ℤ) := {
    eq := fun a b => do
      if ← isDefEq a b then return ← mkEqRefl a
      if let some h ← findLocalDeclWithTypeQ? q($a = $b) then return h
      arithmetic.eq a b
    neZero := fun z a => do
      if let some h ← findLocalDeclWithTypeQ? q($a ≠ 0) then return h
      arithmetic.neZero z a }
  for i in [:n] do
    have d : Q(ℤ) := (entries[i]!)[i]!
    try
      discard <| certifier.neZero q(inferInstance) d
    catch _ =>
      throwError "certify_det_ne_zero_triangular: diagonal entry ({i}, {i}) is zero \
        or could not be proved nonzero: {d}"
    let mut entryProofs : List ((a : Q(ℤ)) × (b : Q(ℤ)) × Q($a = $b)) := []
    let mut normalizedRow := #[]
    for j in [:n] do
      have a : Q(ℤ) := (entries[i]!)[j]!
      if j < i then do
        let h ← do
          try certifier.eq a q((0 : ℤ)) catch _ =>
            throwError "certify_det_ne_zero_triangular: cannot establish upper triangularity; \
              entry ({i}, {j}) below the diagonal is nonzero or could not be proved zero: {a}"
        entryProofs := ⟨a, q((0 : ℤ)), h⟩ :: entryProofs
        normalizedRow := normalizedRow.push q((0 : ℤ))
      else do
        entryProofs := ⟨a, a, q(rfl)⟩ :: entryProofs
        normalizedRow := normalizedRow.push a
    normalized := normalized.push normalizedRow
    rowProofs := mkListCongr (α := q(ℤ)) entryProofs.reverse :: rowProofs
  -- Retain the original rows: arithmetic expressions equal to zero need a proved bridge.
  let original := ListMatrixLit.ofArray (α := q(ℤ)) q(inferInstance) n n entries
  let canonical := ListMatrixLit.ofArray (α := q(ℤ)) q(inferInstance) n n normalized
  let rowEq := mkListCongr (α := q(List ℤ)) rowProofs.reverse
  let transposed := Array.ofFn (n := n) (fun j =>
    Array.ofFn (n := n) (fun i => (normalized[i.val]!)[j.val]!))
  let T := ListMatrixLit.ofArray (α := q(ℤ)) q(inferInstance) n n transposed
  have rows : Q(List (List ℤ)) := canonical.lit
  have ts : Q(List (List ℤ)) := T.lit
  let h' ← certifyLowerTriangularDiagList certifier q(inferInstance) 0 n q(0) q($n) ts
  have h : Q(IsLowerTriangularDiagList 0 $n $ts) := h'
  have : ListMatrix.transpose $n $rows =Q $ts := ⟨⟩
  have heq : Q(ListMatrix.transpose $n $rows = $ts) := q(rfl)
  have proof : Q((ofLists $n $n $rows).det ≠ 0) :=
    q(det_ne_zero_of_transpose_certificate $heq $h)
  have originalRows : Q(List (List ℤ)) := original.lit
  if ← isDefEq originalRows rows then return proof
  have hrows : Q($originalRows = $rows) := rowEq.2.2
  have proof : Q((ofLists $n $n $originalRows).det ≠ 0) :=
    q((Eq.symm $hrows) ▸ $proof)
  return proof

/-- Prove determinant nonvanishing from upper triangularity and a nonzero diagonal.
Uses local hypotheses first, then checks concrete `Fin n` integer literals/definitions.
All arithmetic evidence is checked by Lean's kernel; no native evaluation or Sage is used. -/
elab "certify_det_ne_zero_triangular" : tactic => withMainContext do
  let initialTarget ← instantiateMVars (← (← getMainGoal).getType)
  if initialTarget.isAppOfArity ``Ne 3 then
    let lhs := initialTarget.getAppArgs[1]!
    let rhs := initialTarget.getAppArgs[2]!
    if !lhs.isAppOf ``Matrix.det && rhs.isAppOf ``Matrix.det then
      evalTactic (← `(tactic| apply Ne.symm))
  let goal ← getMainGoal
  if ← fromHypotheses goal then
    replaceMainGoal []
    return
  let target ← instantiateMVars (← goal.getType)
  let_expr Ne R lhs rhs := target
    | throwError "certify_det_ne_zero_triangular: expected a goal \
        of the form A.det ≠ 0 or 0 ≠ A.det"
  let (det, reversed) ← if lhs.isAppOf ``Matrix.det then pure (lhs, false)
    else if rhs.isAppOf ``Matrix.det then pure (rhs, true)
    else throwError "certify_det_ne_zero_triangular: expected a determinant-nonzero goal"
  let zero := if reversed then lhs else rhs
  unless ← isDefEq R q(ℤ) do
    throwError "certify_det_ne_zero_triangular: concrete checking supports integer matrices; \
      provide hypotheses for other integral domains"
  unless ← isDefEq zero q((0 : ℤ)) do
    throwError "certify_det_ne_zero_triangular: expected comparison with zero"
  let A := det.getAppArgs.back!
  let proof ← concreteProof A
  let proof ← if reversed then mkAppM ``Ne.symm #[proof] else pure proof
  unless ← isDefEq (← inferType proof) target do
    throwError "certify_det_ne_zero_triangular: certificate matrix does not match the goal matrix"
  goal.assign proof
  replaceMainGoal []

end Determinant.Triangular
