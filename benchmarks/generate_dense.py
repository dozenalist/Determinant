#!/usr/bin/env python3
"""Generate reproducible Lean inputs using Sage's public exact matrix APIs.

Generation is outside the timed run. Every Lean run starts its own producer and
checks fresh evidence; this script does not supply a certificate to the tactic.
"""
import argparse
import hashlib
import json
from pathlib import Path

from sage.all import GF, GL, ZZ, matrix, set_random_seed
from sage.env import SAGE_VERSION


def generate(n, bits, variant, seed):
    set_random_seed(seed)
    if variant == "triangular":
        bound = (ZZ(2) ** bits - 1) // 2
        return matrix(ZZ, n, n, [
            0 if j < i else (2 * ZZ.random_element(-bound, bound) + 1 if i == j
                             else ZZ.random_element(-bound, bound))
            for i in range(n) for j in range(n)])
    p = 3 if variant == "retry" else 2
    bound = (ZZ(2) ** bits - 1) // (p * (2 if variant == "retry" else 1))
    residue = GL(n, GF(p)).random_element().matrix()
    result = matrix(ZZ, n, n, [ZZ(residue[i, j]) + p * ZZ.random_element(-bound, bound)
                               for i in range(n) for j in range(n)])
    if variant == "retry":
        # Zero row modulo 2; scaling by 2 preserves invertibility modulo 3.
        result.rescale_row(0, 2)
    return result


def source(a, kind, representation, entry_syntax):
    n = a.nrows()
    def entry(x):
        if entry_syntax == "numerals":
            return str(x)
        return f"Int.ofNat {x}" if x >= 0 else f"Int.negSucc {-x - 1}"
    rows = [", ".join(entry(x) for x in row) for row in a.rows()]
    literal = "!![\n" + ";\n".join(rows) + "]"
    if representation == "lists":
        literal = f"Mathlib.Tactic.Matrix.ofLists {n} {n} [\n" + ",\n".join("[" + r + "]" for r in rows) + "]"
    elif representation == "quoted":
        literal = "int_matrix% [\n" + ",\n".join("[" + r + "]" for r in rows) + "]"
    elif representation == "json":
        table = [[str(x) for x in row] for row in a.rows()]
        literal = 'int_matrix% r#"' + json.dumps(table, separators=(",", ":")) + '"#'
    return f'''module
public import Determinant
meta import Determinant.Tactic.Bridge
meta import Lean.Util.NumObjs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option trace.Determinant.timing true
set_option trace.Determinant.producer true
set_option linter.style.longLine false

open Lean Elab Tactic Determinant.Tactic

run_cmd do
  if let some started ← IO.getEnv "DETERMINANT_BENCHMARK_STARTED_MS" then
    if let some started := started.toNat? then
      Lean.logInfo m!"[Determinant.timing] startup and imports: {{(← IO.monoMsNow) - started}} ms"

elab "timed_matrix " name:ident " : " type:term " := " value:term : command => do
  let started ← IO.monoMsNow
  Lean.Elab.Command.elabCommand (← `(public noncomputable def $name : $type := $value))
  Lean.logInfo m!"[Determinant.timing] input declaration: {{(← IO.monoMsNow) - started}} ms"
  IO.eprintln "benchmark input elaborated"
  (← IO.getStderr).flush

elab "benchmark_certify" : tactic => do
  let started ← IO.monoMsNow
  let executable := (← IO.getEnv "DETERMINANT_TEST_PYTHON").getD "python3"
  let argumentPrefix ← match ← IO.getEnv "DETERMINANT_TEST_PREFIX" with
    | none => pure #[]
    | some value => IO.ofExcept do
      (← (← Json.parse value).getArr?).mapM Json.getStr?
  evalTactic (← `(tactic| det_ne_zero_int {{
    executable := $(quote executable)
    arguments := $(quote (argumentPrefix.push "scripts/det_certificate.py"))
    preferredPrimes := [2, 3, 5, 7]
    kind := "{kind}"
    timeoutMs := 30000 }}))
  IO.eprintln s!"benchmark tactic returned after {{(← IO.monoMsNow) - started}} ms"
  (← IO.getStderr).flush

timed_matrix benchmarkMatrix : Matrix (Fin {n}) (Fin {n}) Int := {literal}

set_option profiler true in
set_option profiler.threshold 1 in
public theorem benchmark : benchmarkMatrix.det ≠ 0 := by benchmark_certify

#print axioms benchmark

run_cmd do
  for dependency in ← Lean.collectAxioms ``benchmark do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "unexpected axiom {{dependency}}"
  let some (.thmInfo info) := (← Lean.getEnv).find? ``benchmark
    | throwError "missing benchmark theorem"
  Lean.logInfo m!"proof nodes: {{← Lean.Expr.numObjs info.value}}"
  if let some started ← IO.getEnv "DETERMINANT_BENCHMARK_STARTED_MS" then
    if let some started := started.toNat? then
      Lean.logInfo m!"[Determinant.timing] pre-export elapsed: {{(← IO.monoMsNow) - started}} ms"
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default=".lake/dense-benchmarks")
    parser.add_argument("--dimensions", nargs="+", type=int, default=[10, 50, 100, 128, 200])
    parser.add_argument("--bits", type=int, default=20)
    parser.add_argument("--representation", choices=["literal", "lists", "quoted", "json"], default="json")
    parser.add_argument("--entry-syntax", choices=["numerals", "constructors"])
    parser.add_argument("--variants", nargs="+", choices=["dense", "retry", "triangular"],
                        default=["dense"])
    parser.add_argument("--kind", choices=["full-inverse", "unit-upper-product"],
                        default="unit-upper-product")
    args = parser.parse_args()
    args.entry_syntax = args.entry_syntax or (
        "decimal-strings" if args.representation == "json" else
        "numerals" if args.representation == "quoted" else "constructors")
    if args.representation == "quoted" and args.entry_syntax != "numerals":
        parser.error("int_matrix% takes numeral syntax; use --entry-syntax numerals")
    if args.representation == "json" and args.entry_syntax != "decimal-strings":
        parser.error("JSON input always uses decimal strings; omit --entry-syntax")
    if args.bits < 3 or any(n < 1 for n in args.dimensions):
        parser.error("bits must be at least 3; dimensions must be positive")
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)
    cases = []
    for variant in args.variants:
        for n in args.dimensions:
            seed = 20261108 + n
            a = generate(n, args.bits, variant, seed)
            name = f"{variant}-{n}-{args.bits}bit-{args.kind}-{args.representation}-{args.entry_syntax}"
            text = source(a, args.kind, args.representation, args.entry_syntax)
            (out / f"{name}.lean").write_text(text, encoding="utf-8")
            cases.append(dict(name=name, dimension=n, entry_bits=args.bits,
                              max_actual_bits=max(abs(x).nbits() for x in a.list()),
                              variant=variant, seed=seed, kind=args.kind, representation=args.representation,
                              entry_syntax=args.entry_syntax,
                              source_sha256=hashlib.sha256(text.encode()).hexdigest()))
    manifest = dict(generator_sage_version=SAGE_VERSION,
                    method="GL(n, GF(p)).random_element(), lifted by signed multiples of p",
                    cases=cases)
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(manifest))


if __name__ == "__main__":
    main()
