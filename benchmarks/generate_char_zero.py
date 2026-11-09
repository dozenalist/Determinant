#!/usr/bin/env python3
"""Compare the integer dispatcher with integer-entry characteristic-zero lifting.

Reuse tables from generate_dense.py, preserving their seeds and certificate mode.
Run the resulting manifest with run_linux.py. Both variants include fresh producer
startup and final kernel checking. The target is an arbitrary CommRing + CharZero.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


HEADER = '''module
public import Determinant
meta import Determinant.Tactic.CharZero
meta import Lean.Util.NumObjs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option trace.Determinant.timing true
set_option linter.style.longLine false

open Lean Meta Elab Tactic Qq Determinant.Tactic
open Mathlib.Tactic.Echelon

run_cmd do
  if let some started ← IO.getEnv "DETERMINANT_BENCHMARK_STARTED_MS" then
    if let some started := started.toNat? then
      Lean.logInfo m!"[Determinant.timing] startup and imports: {(← IO.monoMsNow) - started} ms"

-- Build ordinary ring numerals directly, keeping input elaboration inexpensive.
elab "ring_matrix% " ring:ident data:str : term => do
  let zero ← Term.elabTerm (← `(term| (0 : $ring))) none
  let ⟨u, R, _⟩ ← inferTypeQ' zero
  let _inst : Q(CommRing $R) ← synthInstanceQ q(CommRing $R)
  let json ← Lean.ofExcept (Json.parse data.getString)
  let rows ← Lean.ofExcept json.getArr?
  let entries ← rows.mapM fun row => do
    let cells ← Lean.ofExcept row.getArr?
    cells.mapM fun cell => do
      let text ← Lean.ofExcept cell.getStr?
      let some value := text.toInt? | throwError "invalid integer"
      mkIntNumeral R value
  return (ListMatrixLit.ofArray (α := R) q(inferInstance)
    rows.size rows.size entries).matrix

elab "timed_matrix " name:ident " : " type:term " := " value:term : command => do
  let started ← IO.monoMsNow
  Lean.Elab.Command.elabCommand (← `(public noncomputable def $name : $type := $value))
  Lean.logInfo m!"[Determinant.timing] input declaration: {(← IO.monoMsNow) - started} ms"

'''

TAIL = '''
#print axioms benchmark
run_cmd do
  for dependency in ← Lean.collectAxioms ``benchmark do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "unexpected axiom {dependency}"
  let some (.thmInfo info) := (← Lean.getEnv).find? ``benchmark
    | throwError "missing theorem"
  Lean.logInfo m!"proof nodes: {← Lean.Expr.numObjs info.value}"
  if let some started ← IO.getEnv "DETERMINANT_BENCHMARK_STARTED_MS" then
    if let some started := started.toNat? then
      Lean.logInfo m!"[Determinant.timing] pre-export elapsed: {(← IO.monoMsNow) - started} ms"
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--dimensions", type=int, nargs="+", default=[10, 50, 100])
    args = parser.parse_args()
    source = Path(args.input)
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((source / "manifest.json").read_text())
    cases = []
    for case in manifest["cases"]:
        if case["dimension"] not in args.dimensions:
            continue
        original = (source / (case["name"] + ".lean")).read_text(encoding="utf-8")
        match = re.search(r'int_matrix% (r#".*?"#)', original)
        if not match:
            raise ValueError("expected lossless JSON integer input")
        data = match[1]
        n = case["dimension"]
        for variant in ["int", "char-zero"]:
            ring = "Int" if variant == "int" else "R"
            variables = "" if variant == "int" else "variable (R : Type) [CommRing R]\n"
            literal = f"int_matrix% {data}" if variant == "int" else f"ring_matrix% R {data}"
            theorem_params = "" if variant == "int" else " [CharZero R]"
            matrix = "benchmarkMatrix" if variant == "int" else "(benchmarkMatrix R)"
            tactic = "det_ne_zero_int" if variant == "int" else "det_ne_zero"
            code = HEADER + f'''elab "benchmark_certify" : tactic => do
  let started ← IO.monoMsNow
  evalTactic (← `(tactic| {tactic} {{
    executable := "/usr/bin/python3"
    kind := "{case['kind']}" }}))
  IO.eprintln s!"benchmark tactic returned after {{(← IO.monoMsNow) - started}} ms"

{variables}timed_matrix benchmarkMatrix : Matrix (Fin {n}) (Fin {n}) {ring} := {literal}

set_option profiler true in
set_option profiler.threshold 1 in
public theorem benchmark{theorem_params} : {matrix}.det ≠ 0 := by benchmark_certify
''' + TAIL
            name = f"{case['name']}-{variant}"
            (output / (name + ".lean")).write_text(code, encoding="utf-8")
            cases.append(dict(case, name=name, coefficient_ring=ring,
                tactic=tactic, source_sha256=hashlib.sha256(code.encode()).hexdigest()))
    (output / "manifest.json").write_text(json.dumps(dict(manifest, cases=cases), indent=2) + "\n")


if __name__ == "__main__":
    main()
