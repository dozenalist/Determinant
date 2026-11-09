/-
Copyright (c) 2026 Carter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter
-/
module

public import Mathlib.Tactic.Matrix.OfLists
public meta import Lean.Elab.Term
public meta import Mathlib.Data.List.Monad
public meta import Lean.Data.Json

/-! # Efficient concrete integer matrix input

`int_matrix% [[1, -2], [3, 4]]` elaborates signed numeral data directly to
Mathlib's `ofLists`, using Lean's existing `ToExpr Int` and list quotation.
It avoids per-entry typeclass elaboration and the vector notation's index terms.
There is no evaluation, proof assertion, process, or file access at this boundary.
-/

public meta section

open Lean Elab Term Meta

syntax (name := integerMatrixLiteral) "int_matrix% " "[" term,* "]" : term
syntax (name := integerMatrixJson) "int_matrix% " str : term

private def matrixExpression (rows : List (List Int)) : TermElabM Expr := do
  let n := rows.length
  unless rows.all (·.length == n) do throwError "expected a square integer table"
  let intType := Lean.mkConst ``Int
  let zero ← synthInstance (mkApp (Lean.mkConst ``Zero [0]) intType)
  let ofNat := Lean.mkConst ``Int.ofNat
  let literal := fun (value : Int) =>
    let magnitude := mkApp ofNat (mkRawNatLit value.natAbs)
    if value < 0 then mkIntNeg magnitude else magnitude
  let rowValues ← rows.mapM fun row => Lean.Meta.mkListLit intType (row.map literal)
  let values ← Lean.Meta.mkListLit (mkApp (Lean.mkConst ``List [0]) intType) rowValues
  return mkAppN (Lean.mkConst ``Mathlib.Tactic.Matrix.ofLists [0])
    #[intType, zero, mkRawNatLit n, mkRawNatLit n, values]

elab_rules : term
  | `(int_matrix% [$rowSyntax,*]) => do
    let n := rowSyntax.getElems.size
    let rows ← rowSyntax.getElems.toList.mapM fun row => do
      let `([$cells,*]) := row
        | throwErrorAt row "expected a row of signed integer numerals"
      unless cells.getElems.size == n do
        throwErrorAt row "expected {n} entries in this square matrix row"
      cells.getElems.toList.mapM fun entry => do
        match entry with
        | `($value:num) => return (value.getNat : Int)
        | `(-$value:num) => return -(value.getNat : Int)
        | _ => throwErrorAt entry "int_matrix% accepts signed integer numerals"
    matrixExpression rows
  | `(int_matrix% $data:str) => do
    let json ← Lean.ofExcept (Json.parse data.getString)
    let array ← Lean.ofExcept json.getArr?
    let rows ← array.toList.mapM fun (row : Json) => do
      let cells ← Lean.ofExcept row.getArr?
      cells.toList.mapM fun (cell : Json) => do
        let text ← Lean.ofExcept cell.getStr?
        let some value := text.toInt? | throwError "invalid decimal integer string"
        unless toString value == text do throwError "expected a canonical decimal integer string"
        return value
    matrixExpression rows
