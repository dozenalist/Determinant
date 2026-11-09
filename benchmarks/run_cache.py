#!/usr/bin/env python3
"""Paired uncached/miss/hit proofs in the prepared native Linux environment.

Input files are JSON-form int_matrix% cases from generate_dense.py. Each sample
forces Lean elaboration, kernel checking, an axiom audit, and artifact writing.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import time

import psutil

from run_linux import parse_log


def source(table):
    n = len(table)
    encoded = json.dumps(table, separators=(",", ":"))
    return f'''module
public import Determinant
meta import Determinant.Tactic.Cache
meta import Lean.Util.NumObjs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option trace.Determinant.timing true
set_option trace.Determinant.producer true
set_option trace.Determinant.cache true
set_option linter.style.longLine false
open Lean Elab Tactic Determinant.Tactic

public noncomputable def benchmarkMatrix := int_matrix% r#"{encoded}"#

elab "cache_benchmark" : tactic => do
  let started ← IO.monoMsNow
  let mode := (← IO.getEnv "DETERMINANT_CACHE_BENCH_MODE").getD "plain"
  let directory := (← IO.getEnv "DETERMINANT_CACHE_BENCH_DIRECTORY").getD ".lake/cache-benchmark"
  if mode == "plain" then
    evalTactic (← `(tactic| det_ne_zero {{ kind := "unit-upper-product" }}))
  else
    let executable := if mode == "hit" then "sage-must-not-launch" else "python3"
    let policy := if mode == "hit" then CachePolicy.cacheOnly else CachePolicy.readWrite
    let config : CacheConfig := {{ directory, executable, policy, kind := "unit-upper-product" }}
    withWitnessCache config detNeZero
  IO.eprintln s!"benchmark tactic returned after {{(← IO.monoMsNow) - started}} ms"

set_option profiler true in
set_option profiler.threshold 1 in
public theorem benchmark : (benchmarkMatrix : Matrix (Fin {n}) (Fin {n}) ℤ).det ≠ 0 := by
  cache_benchmark

#print axioms benchmark
run_cmd do
  for dependency in ← Lean.collectAxioms ``benchmark do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "unexpected axiom {{dependency}}"
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--environment", default="/tmp/determinant-linux/benchmark-environment.json")
    parser.add_argument("--input", required=True, nargs="+", type=Path)
    parser.add_argument("--output", default="/tmp/determinant-linux/results/cache", type=Path)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--deadline", type=float, default=600)
    args = parser.parse_args()
    if args.repeats < 1 or args.deadline <= 0:
        parser.error("budgets must be positive")
    config = json.loads(Path(args.environment).read_text())
    workspace = Path(config["workspace"])
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    (output / "environment.json").write_text(json.dumps(dict(
        platform=platform.platform(), python=platform.python_version(),
        logicalCPUs=os.cpu_count(), memoryBytes=psutil.virtual_memory().total,
        leanVersion=config.get("lean_version"),
        mathlibRevision=config.get("mathlib_revision")), indent=2) + "\n")
    inputs = workspace / "inputs/cache"
    inputs.mkdir(parents=True, exist_ok=True)
    records = []
    batch = str(time.time_ns())
    for input_path in args.input:
        match = re.search(r'int_matrix% r#"(.*?)"#', input_path.read_text(), re.DOTALL)
        if not match:
            raise ValueError(f"expected JSON int_matrix% in {input_path}")
        table = json.loads(match[1])
        n = len(table)
        lean_source = inputs / f"Dense{n}.lean"
        lean_source.write_text(source(table))
        (output / lean_source.name).write_text(lean_source.read_text())
        for repeat in range(1, args.repeats + 1):
            directory = f".lake/cache-benchmark/{batch}/{n}/run{repeat}"
            for mode in ["plain", "miss", "hit"]:
                name = f"dense{n}-{mode}-run{repeat}"
                log_path = output / (name + ".log")
                artifact = output / (name + ".olean")
                env = dict(os.environ, LEAN_PATH=":".join(config["lean_path"]),
                           DETERMINANT_CACHE_BENCH_MODE=mode,
                           DETERMINANT_CACHE_BENCH_DIRECTORY=directory)
                started = time.monotonic()
                peak = peak_combined = 0
                with log_path.open("w") as log:
                    child = subprocess.Popen([config["lean"], "-R", str(workspace), "-o", str(artifact), str(lean_source)],
                                             cwd=workspace, env=env, stdout=log, stderr=log)
                    process = psutil.Process(child.pid)
                    while child.poll() is None:
                        try:
                            rss = process.memory_info().rss
                            peak = max(peak, rss)
                            combined = rss
                            for descendant in process.children(recursive=True):
                                try:
                                    combined += descendant.memory_info().rss
                                except psutil.NoSuchProcess:
                                    pass
                            peak_combined = max(peak_combined, combined)
                        except psutil.NoSuchProcess:
                            pass
                        if time.monotonic() - started > args.deadline:
                            for descendant in process.children(recursive=True):
                                descendant.kill()
                            process.kill()
                            raise TimeoutError(name)
                        time.sleep(0.05)
                elapsed = time.monotonic() - started
                log = log_path.read_text()
                tactic = re.search(r"benchmark tactic returned after (\d+) ms", log)
                record = dict(dimension=n, mode=mode, run=repeat, wallSeconds=round(elapsed, 3),
                              tacticMs=int(tactic[1]) if tactic else None, peakLeanSampleBytes=peak,
                              peakCombinedSampleBytes=peak_combined,
                              exitCode=child.returncode, oleanBytes=artifact.stat().st_size if artifact.exists() else 0,
                              producerInvocations=log.count("[Determinant.producer] starting"),
                              log=log_path.name, directory=directory, **parse_log(log))
                records.append(record)
                (output / "results.json").write_text(json.dumps(records, indent=2) + "\n")
                print(f"{name}: {elapsed:.3f}s, exit={child.returncode}, producer={record['producerInvocations']}", flush=True)
                if child.returncode:
                    raise RuntimeError(log[-5000:])
                if mode == "hit" and record["producerInvocations"]:
                    raise AssertionError("cache hit invoked producer")


if __name__ == "__main__":
    main()
