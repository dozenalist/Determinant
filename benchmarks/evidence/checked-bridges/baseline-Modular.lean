/-
Copyright (c) 2026 Carter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter
-/
module

public import Determinant.Certificate
public import Determinant.NatCertificate
public meta import Determinant.NatCertificate
public meta import Determinant.Certificate
public meta import Determinant.Tactic.Matrix
public meta import Mathlib.Tactic.Echelon.Cert
public meta import Mathlib.Tactic.Echelon.Rat
public meta import Lean.Meta.Closure
public meta import Lean.Meta.Tactic.AuxLemma
public import Mathlib.Tactic.NormNum

/-! # Offline, strict modular certificate replay -/

public meta section

open Lean Meta Elab Tactic Qq
open Mathlib.Tactic.Matrix Mathlib.Tactic.Echelon

namespace Determinant.Tactic

initialize registerTraceClass `Determinant.timing

/-- Both routes produce ordinary kernel-checked proofs. `kernel` is not native evaluation. -/
inductive ProofRoute where
  | kernel
  | arithmetic
  | listKernel
  deriving Inhabited

/-- `mkDecideProof` constructs a term without checking that the Boolean reduces to true.
Check first so a rejected certificate fails inside the tactic, allowing safe backtracking. -/
private def checkedDecide (proposition : Q(Prop)) : MetaM Q($proposition) := do
  let decision ← mkDecide proposition
  let result ← ofExceptKernelException <| Kernel.whnf (← getEnv) (← getLCtx) decision
  unless result.isConstOf ``Bool.true do
    throwError "kernel computation rejected the certificate"
  mkDecideProofQ proposition

/-- Normalize each signed original entry once, retaining a checked congruence for it. -/
private def normalize (p n : Nat) (entries : Array (Array Expr)) :
    MetaM ((original : Q(List (List ℤ))) × (a : ListMatrixLit q(ℤ) n n) ×
      Q(residueRows $p $original = $(a.lit))) := do
  let mut normalized := #[]
  for i in [:n] do
    let mut normalizedRow := #[]
    for j in [:n] do
      have e : Q(ℤ) := (entries[i]!)[j]!
      let value ← try integerValue e catch _ =>
        throwError "modular certificate: entry ({i}, {j}) is not a closed integer: {e}"
      let r : Q(ℤ) := mkApp (mkConst ``Int.ofNat)
        (mkRawNatLit (value % (p : Int)).toNat)
      normalizedRow := normalizedRow.push r
    normalized := normalized.push normalizedRow
  let original := ListMatrixLit.ofArray (α := q(ℤ)) q(inferInstance) n n entries
  let a := ListMatrixLit.ofArray (α := q(ℤ)) q(inferInstance) n n normalized
  unless ← withTransparency .all <| isDefEq q(residueRows $p $(original.lit)) a.lit do
    throwError "modular certificate: normalization does not match the original integer entries"
  let h ← mkEqRefl a.lit
  return ⟨original.lit, a, h⟩

/-- Expand shared list dot products, then prove the required integer remainders. -/
private def fullArithmeticProof (n p : Nat) (hp : Q(1 < $p))
    (original a b : Q(List (List ℤ))) (ha : Q(residueRows $p $original = $a))
    (aRows bRows : List (List Q(ℤ))) : MetaM Expr := do
  let mul := proveMul (α := q(ℤ)) q(inferInstance) q(inferInstance) q(inferInstance)
    n n n aRows bRows
  let certifier := normNumCertifier q(ℤ)
  let mut rowProofs := []
  for (row, i) in mul.rows.zipIdx do
    let mut proofs := []
    for (e, j) in row.zipIdx do
      have target : Q(ℤ) := if i == j then q(1) else q(0)
      let h ← try certifier.eq q($e % ($p : ℤ)) target catch _ =>
        throwError "modular certificate rejected: product entry ({i}, {j}) \
          is not {if i == j then "one" else "zero"} modulo {p}"
      proofs := ⟨q($e % ($p : ℤ)), target, h⟩ :: proofs
    rowProofs := mkListCongr (α := q(ℤ)) proofs.reverse :: rowProofs
  let ⟨_, _, h⟩ := mkListCongr (α := q(List ℤ)) rowProofs.reverse
  have hmod : Q(residueRows $p $(mul.expr) = identityRows $n) := h
  have hmul : Q(ListMatrix.mul $n $n $n $a $b = $(mul.expr)) := mul.proof
  return q(det_ne_zero_of_full_certificate $hp $ha $hmul $hmod)

/-- Specialize the already-normalized residues to natural literals and share an explicit
transpose. The semantic bridge and every arithmetic check are kernel checked. -/
private def naturalProof (n p : Nat) (upper : Bool) (hp : Q(1 < $p))
    (original a : Q(List (List ℤ))) (ha : Q(residueRows $p $original = $a))
    (normalized : ListMatrixLit q(ℤ) n n) (inverse : List (List Int)) : MetaM Expr := do
  let values ← normalized.rows.toArray.mapM fun row => row.toArray.mapM fun e => do
    return (← integerValue e).toNat
  let rows := values.map (·.map mkRawNatLit)
  let bValues := inverse.toArray.map (fun row => row.toArray.map (fun x =>
    (x % (p : Int)).toNat))
  let bs := bValues.map (·.map mkRawNatLit)
  let ts := Array.ofFn (n := n) (fun j => Array.ofFn (n := n) (fun i => (bs[i.val]!)[j.val]!))
  let tValues := Array.ofFn (n := n) (fun j =>
    (Array.ofFn (n := n) (fun i => (bValues[i.val]!)[j.val]!)).toList)
  let A := ListMatrixLit.ofArray (α := q(ℕ)) q(inferInstance) n n rows
  let B := ListMatrixLit.ofArray (α := q(ℕ)) q(inferInstance) n n bs
  let T := ListMatrixLit.ofArray (α := q(ℕ)) q(inferInstance) n n ts
  have an : Q(List (List ℕ)) := A.lit
  have bn : Q(List (List ℕ)) := B.lit
  let columns ← if n > 16 then
      withOptions (fun options => options.setBool `Elab.async false) do
        mkAuxDefinitionFor (← mkAuxDeclName (kind := `_detColumns)) T.lit (compile := false)
    else pure T.lit
  have tn : Q(List (List ℕ)) := columns
  have ha' : Q(residueRows $p $original = intRows $an) := ha
  have hrows : Q(List.length $an = $n) := ← mkEqRefl (mkRawNatLit n)
  have hwidth : Q(($an).all (fun row => row.length == $n) = true) := Lean.reflBoolTrue
  have hbt : Q(List.length $tn = $n) := ← mkEqRefl (mkRawNatLit n)
  unless ← withTransparency .all <|
      isDefEq q(ListMatrix.transpose $n (intRows $bn)) q(intRows $tn) do
    throwError "modular certificate: transpose does not match the inverse entries"
  have ht : Q(ListMatrix.transpose $n (intRows $bn) = intRows $tn) :=
    ← mkEqRefl q(intRows $tn)
  -- This compiled preflight is only a rejection aid. Reflexivity proofs require
  -- the kernel to reduce each actual Boolean to true. No native axiom is used.
  unless checkNat upper n p (values.toList.map Array.toList) tValues.toList do
    throwError "modular certificate rejected: product is not \
      {if upper then "unit upper triangular" else "the identity"} modulo {p}"
  let h ← if n > 16 then do
      -- Bound each kernel reduction cache to one row. The column data is a
      -- checked definition, so each auxiliary theorem's type stays small.
      let started ← IO.monoMsNow
      let rowLits := rows.map fun row => mkListLitQ (α := q(ℕ)) row.toList
      let mut proofs := #[]
      for i in [:n] do
        have row : Q(List ℕ) := rowLits[i]!
        have index : Q(ℕ) := mkNatLit i
        let proposition := q(checkNatRow $upper $n $p $index $row $tn = true)
        let value := Lean.reflBoolTrue
        let name ← withOptions (fun options => options.setBool `Elab.async false) <|
          mkAuxLemma [] proposition value (cache := false)
        proofs := proofs.push (mkConst name)
      trace[Determinant.timing] "row kernel proofs: {(← IO.monoMsNow) - started} ms"
      have empty : Q(List (List ℕ)) := q([])
      let mut tail := empty
      let mut proof : Expr := q(checkNatRows_nil $upper $n $p $n $tn)
      for i in (List.range n).reverse do
        have row : Q(List ℕ) := rowLits[i]!
        have index : Q(ℕ) := mkNatLit i
        have hr : Q(checkNatRow $upper $n $p $index $row $tn = true) := proofs[i]!
        have ht : Q(checkNatRows $upper $n $p ($index + 1) $tail $tn = true) := proof
        proof := q(checkNatRows_cons $hr $ht)
        tail := q($row :: $tail)
      pure proof
    else pure Lean.reflBoolTrue
  have h : Q(checkNat $upper $n $p $an $tn = true) := h
  return q(checkNat_sound (upper := $upper) (n := $n) (p := $p)
    (original := $original) (a := $an) (b := $bn) (bt := $tn)
    $hp $ha' $hrows $hwidth $hbt $ht $h)

/-- Check candidate data against the actual matrix expression. Fresh, cached and manual
producers can all call this entry point. Evaluation extracts data only; the returned proof
must be accepted for the current matrix by definitional equality. -/
def proveCertificateForEntries (A : Expr) (n : Nat) (entries : Array (Array Expr))
    (raw : RawCertificate)
    (route : ProofRoute := .kernel) : MetaM Expr := do
  let started ← IO.monoMsNow
  let cert ← match raw.validate n with
    | .ok cert => pure cert
    | .error message => throwError "modular certificate rejected: {message}"
  let p : Nat := cert.modulus
  let hp : Q(1 < $p) ← checkedDecide q(1 < $p)
  let ⟨original, normalized, ha⟩ ← normalize p n entries
  trace[Determinant.timing] "normalization: {(← IO.monoMsNow) - started} ms"
  let started ← IO.monoMsNow
  have a : Q(List (List ℤ)) := normalized.lit
  have ha : Q(residueRows $p $original = $a) := ha
  let bEntries := cert.inverse.toArray.map fun row =>
    row.toArray.map fun x => mkApp (mkConst ``Int.ofNat) (mkRawNatLit (x % (p : Int)).toNat)
  let B := ListMatrixLit.ofArray (α := q(ℤ)) q(inferInstance) n n bEntries
  have b : Q(List (List ℤ)) := B.lit
  let proof ← match cert.kind, route with
    | .fullInverse, .arithmetic =>
      fullArithmeticProof n p hp original a b ha normalized.rows B.rows
    | .fullInverse, .kernel => naturalProof n p false hp original a ha normalized cert.inverse
    | .unitUpperProduct, .kernel => naturalProof n p true hp original a ha normalized cert.inverse
    | .fullInverse, .listKernel => do
      let h ← try checkedDecide q(checkFull $n $p $a $b = true) catch _ =>
        throwError "modular certificate rejected: full product is not the identity modulo {p}"
      pure q(checkFull_sound (n := $n) (original := $original) (a := $a) (b := $b) $hp $ha $h)
    | .unitUpperProduct, _ => do
      let h ← try checkedDecide q(checkUnitUpper $n $p $a $b = true) catch _ =>
        throwError "modular certificate rejected: product is not unit upper triangular modulo {p}"
      pure q(checkUnitUpper_sound
        (n := $n) (original := $original) (a := $a) (b := $b) $hp $ha $h)
  trace[Determinant.timing] "certificate proof: {(← IO.monoMsNow) - started} ms"
  let started ← IO.monoMsNow
  have A : Q(Matrix (Fin $n) (Fin $n) ℤ) := A
  unless ← isDefEq (← inferType proof) q(($A).det ≠ 0) do
    throwError "modular certificate: extracted matrix does not match the actual goal matrix"
  trace[Determinant.timing] "goal connection: {(← IO.monoMsNow) - started} ms"
  return proof

/-- Standalone replay, including extraction of the actual goal matrix. -/
def proveCertificate (A : Expr) (raw : RawCertificate)
    (route : ProofRoute := .kernel) : MetaM Expr := do
  let (n, entries) ← integerEntries A
  proveCertificateForEntries A n entries raw route

private def replay (data : Syntax) (route : ProofRoute) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let_expr Ne R lhs rhs := target
    | throwError "expected a goal A.det ≠ 0 or 0 ≠ A.det"
  let (det, zero, reversed) ← if lhs.isAppOf ``Matrix.det then pure (lhs, rhs, false)
    else if rhs.isAppOf ``Matrix.det then pure (rhs, lhs, true)
    else throwError "expected a determinant-nonzero goal"
  unless ← isDefEq R q(ℤ) do throwError "modular replay supports integer matrices"
  unless ← isDefEq zero q((0 : ℤ)) do throwError "expected comparison with zero"
  -- Untrusted evaluation produces data, never a proof or a success assertion.
  let raw ← unsafe Term.evalTerm RawCertificate q(RawCertificate) data
  let proof ← proveCertificate det.getAppArgs.back! raw route
  let proof ← if reversed then mkAppM ``Ne.symm #[proof] else pure proof
  unless ← isDefEq (← inferType proof) target do
    throwError "modular certificate does not prove the current goal"
  goal.assign proof
  replaceMainGoal []

/-- Replay a data-only certificate using the strict executable checker in Lean's kernel. -/
elab "certify_det_ne_zero_modular " data:term : tactic => replay data .kernel

/-- Alternative full-product route using shared dot products and certified integer arithmetic.
The reduced certificate kind uses the strict kernel checker with either route. -/
elab "certify_det_ne_zero_modular_arithmetic " data:term : tactic => replay data .arithmetic

/-- Replay with the strict executable checker evaluated by the kernel. -/
elab "certify_det_ne_zero_modular_kernel " data:term : tactic =>
  replay data .kernel

end Determinant.Tactic
