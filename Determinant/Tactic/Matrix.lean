/-
Copyright (c) 2026 Carter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter
-/
module

public meta import Mathlib.LinearAlgebra.Matrix.Notation
public meta import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Tactic.Matrix.OfLists
public meta import Mathlib.Tactic.Echelon.Rat

/-! # Shared concrete matrix extraction -/

public meta section

open Lean Meta Qq
open Mathlib.Tactic.Matrix

namespace Determinant.Tactic

/-- The pinned high-level parser also imports analysis tactic infrastructure.
This integer-only adapter reuses its public vector matcher without those imports. -/
private def vectorEntries? (A : Expr) :
    MetaM (Option (Nat × Nat × Expr × Array (Array Expr))) := do
  let_expr Matrix finM finN R := ← inferType A | return none
  let_expr Fin mE := finM | return none
  let_expr Fin nE := finN | return none
  let some m ← getNatValue? mE | return none
  let some n ← getNatValue? nE | return none
  let_expr DFunLike.coe _ _ _ _ f v := A | return none
  let_expr Matrix.of _ _ _ := f | return none
  let (rows, _, _) ← Matrix.matchVecConsPrefix mE v
  unless rows.length == m do return none
  let entries ← rows.toArray.mapM fun row => do
    let (cells, _, _) ← Matrix.matchVecConsPrefix nE row
    return cells.toArray
  unless entries.all (·.size == n) do return none
  return some (m, n, R, entries)

/-- Fast literal recognition with Mathlib arithmetic evaluation as a fallback.
This discovers data only; replay proves normalization against the original terms. -/
def integerValue (entry : Expr) : MetaM Int := do
  if let some value ← getIntValue? entry then return value
  if entry.isAppOf ``Int.ofNat then
    if let some value ← getNatValue? entry.appArg! then return value
  if entry.isAppOf ``Int.negSucc then
    if let some value ← getNatValue? entry.appArg! then return -(value + 1 : Int)
  if entry.isAppOf ``Neg.neg then
    let magnitude := entry.appArg!
    if magnitude.isAppOf ``Int.ofNat then
      if let some value ← getNatValue? magnitude.appArg! then return -(value : Int)
  return (← Mathlib.Tactic.Echelon.evalRatEntry true entry).num

private def listEntries? (A : Expr) : MetaM (Option (Nat × Nat × Expr × Array (Array Expr))) := do
  let_expr ofLists R _ mE nE rows := A | return none
  let some m ← getNatValue? mE | return none
  let some n ← getNatValue? nE | return none
  -- Lean's list notation introduces balanced let bindings at length 32.
  -- Its literal reader expects cons/nil chains; zeta-reduce those bindings first.
  let rows ← zetaReduce rows (zetaDelta := false)
  let some entries ← getListLitOf? rows getListLit? | return none
  unless entries.size == m && entries.all (·.size == n) do
    throwError "ofLists inputs require exactly the declared rows and columns \
      (no padding or truncation)"
  return some (m, n, R, entries)

/-- Parse square matrix/list literals over any coefficient type, following up to 64 aliases.
Callers must check the resulting proof type against the original goal before assigning it. -/
def matrixEntries (A : Expr) : MetaM (Nat × Expr × Array (Array Expr)) := do
  let A ← instantiateMVars A
  let mut current := A
  let mut parsed := none
  for _ in [:64] do
    parsed ← vectorEntries? current
    if parsed.isNone then parsed ← listEntries? current
    if parsed.isSome then break
    let next ← withTransparency .default do
      if current.isFVar then
        if let some value := (← current.fvarId!.getDecl).value? then return some value
      unfoldDefinition? current
    let some next := next | break
    current := next
  let some (m, n, R, entries) := parsed
    | throwError "expected a square matrix literal or a reducible definition \
        indexed by a closed Fin n"
  unless m == n do
    throwError "concrete inputs must be square matrices indexed by Fin n"
  return (n, R, entries)

/-- The integer-only adapter used by certificate replay. -/
def integerEntries (A : Expr) : MetaM (Nat × Array (Array Expr)) := do
  let (n, R, entries) ← matrixEntries A
  unless ← isDefEq R q(ℤ) do
    throwError "concrete inputs must be square integer matrices indexed by Fin n"
  return (n, entries)

end Determinant.Tactic
