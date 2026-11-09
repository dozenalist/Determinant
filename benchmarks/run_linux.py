#!/usr/bin/env python3
"""Fresh strict proofs in the prepared native Linux workspace, with process metrics."""
import argparse
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import time

import psutil


def parse_log(log):
    phases = {name: int(ms) for name, ms in re.findall(
        r"\[Determinant.timing\] ([^:\r\n]+): (\d+) ms", log)}
    kernels = re.findall(r"(?m)^\s*type checking ([0-9.]+)(ms|s)\s*$", log)
    kernel_ms = float(kernels[-1][0]) * (1000 if kernels[-1][1] == "s" else 1) if kernels else None
    individual = re.findall(r"(?m)^type checking took ([0-9.]+)(ms|s)\s*$", log)
    final_kernel_ms = (float(individual[-1][0]) * (1000 if individual[-1][1] == "s" else 1)
                       if individual else None)
    nodes = re.search(r"proof nodes: (\d+)", log)
    metadata = re.search(r"metadata: (\{[^\r\n]+\})", log)
    axioms = re.search(r"'benchmark' depends on axioms: ([^\r\n]+)", log)
    return dict(phasesMs=phases, kernelMs=kernel_ms, finalDeclarationKernelMs=final_kernel_ms,
                proofNodes=int(nodes[1]) if nodes else None,
                producer=json.loads(metadata[1]) if metadata else None,
                axiomReport=axioms[1] if axioms else None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--environment", default="/tmp/determinant-linux/benchmark-environment.json")
    parser.add_argument("--input", required=True)
    parser.add_argument("--output")
    parser.add_argument("--names", nargs="+", default=["*"])
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--deadline", type=float, default=600)
    parser.add_argument("--producer-python", default="/usr/bin/python3")
    args = parser.parse_args()
    if args.repeats < 1 or args.deadline <= 0:
        parser.error("budgets must be positive")
    config = json.loads(Path(args.environment).read_text())
    workspace = Path(config["workspace"])
    source_directory = Path(args.input).resolve()
    input_directory = workspace / "inputs" / source_directory.name
    shutil.copytree(source_directory, input_directory, dirs_exist_ok=True)
    output = Path(args.output).resolve() if args.output else workspace / "results" / source_directory.name
    output.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((input_directory / "manifest.json").read_text())
    env = dict(os.environ, LEAN_PATH=":".join(config["lean_path"]),
               DETERMINANT_TEST_PYTHON=args.producer_python, DETERMINANT_TEST_PREFIX="[]")
    environment = dict(config, platform=platform.platform(), processor=platform.processor(),
                       logical_cpus=psutil.cpu_count(), visible_ram=psutil.virtual_memory().total,
                       input_directory=str(input_directory),
                       project_source_sha256={str(p.relative_to(workspace)):
                           hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in sorted((workspace / "Determinant").rglob("*.lean"))},
                       psutil_version=psutil.__version__,
                       invocation="native lean -R WORKSPACE -o ARTIFACT SOURCE; dependencies built before timing")
    (output / "environment.json").write_text(json.dumps(environment, indent=2) + "\n")
    records = []
    for case in manifest["cases"]:
        if not any(fnmatch.fnmatch(case["name"], pattern) for pattern in args.names):
            continue
        source = input_directory / (case["name"] + ".lean")
        if hashlib.sha256(source.read_bytes()).hexdigest() != case["source_sha256"]:
            raise RuntimeError("input source does not match its manifest digest")
        for run in range(1, args.repeats + 1):
            stem = output / f"{case['name']}-run{run}"
            artifact = Path(str(stem) + ".olean")
            logfile = Path(str(stem) + ".log")
            command = [config["lean"], "-R", str(workspace), "-o", str(artifact), str(source)]
            peak_lean = peak_combined = 0
            timed_out = False
            started = time.monotonic()
            run_env = dict(env, DETERMINANT_BENCHMARK_STARTED_MS=str(int(started * 1000)))
            with logfile.open("w") as log:
                child = subprocess.Popen(command, cwd=workspace, env=run_env, stdout=log, stderr=log,
                                         start_new_session=True)
                process = psutil.Process(child.pid)
                while True:
                    pid, status, usage = os.wait4(child.pid, os.WNOHANG)
                    if pid:
                        child.returncode = os.waitstatus_to_exitcode(status)
                        break
                    try:
                        rss = process.memory_info().rss
                        peak_lean = max(peak_lean, rss)
                        combined = rss
                        for descendant in process.children(recursive=True):
                            try:
                                combined += descendant.memory_info().rss
                            except psutil.NoSuchProcess:
                                pass
                        peak_combined = max(peak_combined, combined)
                    except psutil.NoSuchProcess:
                        pass
                    if time.monotonic() - started >= args.deadline:
                        timed_out = True
                        for target in reversed(process.children(recursive=True)):
                            try:
                                target.kill()
                            except psutil.NoSuchProcess:
                                pass
                        try:
                            process.kill()
                        except psutil.NoSuchProcess:
                            pass
                    time.sleep(0.05)
            elapsed = time.monotonic() - started
            record = dict(case=case, run=run, wallSeconds=round(elapsed, 3), exitCode=child.returncode,
                          timedOut=timed_out, deadlineSeconds=args.deadline, peakLeanSampleBytes=peak_lean,
                          peakProcessRssWait4Bytes=usage.ru_maxrss * 1024,
                          peakCombinedSampleBytes=peak_combined, sourceBytes=source.stat().st_size,
                          oleanBytes=artifact.stat().st_size if artifact.exists() else 0,
                          allOleanPartsBytes=sum(p.stat().st_size for p in output.glob(artifact.name + "*")),
                          log=logfile.name, **parse_log(logfile.read_text()))
            if "pre-export elapsed" in record["phasesMs"]:
                record["exportAndExitMs"] = round(elapsed * 1000 - record["phasesMs"]["pre-export elapsed"], 3)
            records.append(record)
            (output / "results.json").write_text(json.dumps(records, indent=2) + "\n")
            (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
            print(f"{case['name']}, run {run}: {elapsed:.3f}s, exit={child.returncode}, "
                  f"peak={usage.ru_maxrss / 1024:.1f} MiB", flush=True)
            if child.returncode or timed_out:
                raise RuntimeError(f"benchmark failed; retained {logfile}")


if __name__ == "__main__":
    main()
