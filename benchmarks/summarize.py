#!/usr/bin/env python3
"""Summarize exported evidence without merging different benchmark configurations."""
import argparse
import json
from pathlib import Path
import statistics


def measurements(records, get):
    values = [value for row in records if (value := get(row)) is not None]
    if not values:
        return None
    return dict(median=statistics.median(values), worst=max(values), samples=values)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", default="benchmarks/evidence")
    parser.add_argument("--output", default="benchmarks/summary.json")
    args = parser.parse_args()
    groups = {}
    for path in sorted(Path(args.evidence).glob("*/results.json")):
        label = path.parent.name.removesuffix("-repeat")
        for record in json.loads(path.read_text()):
            case = record["case"]
            key = label, case["name"], case.get("source_sha256")
            groups.setdefault(key, []).append(record)
    result = []
    for (label, name, digest), records in groups.items():
        good = [r for r in records if r["exitCode"] == 0 and not r.get("timedOut")]
        phases = sorted({key for row in good for key in row["phasesMs"]})
        entry = dict(label=label, case=records[0]["case"], successfulRuns=len(good),
                     failedRuns=len(records) - len(good),
                     wallSeconds=measurements(good, lambda r: r["wallSeconds"]),
                     phasesMs={key: measurements(good, lambda r: r["phasesMs"].get(key)) for key in phases},
                     kernelMs=measurements(good, lambda r: r.get("kernelMs")),
                     finalDeclarationKernelMs=measurements(good, lambda r: r.get("finalDeclarationKernelMs")),
                     exportAndExitMs=measurements(good, lambda r: r.get("exportAndExitMs")),
                     allOleanPartsBytes=measurements(good, lambda r: r["allOleanPartsBytes"]),
                     peakLeanRssBytes=measurements(good, lambda r: r.get("peakProcessRssWait4Bytes",
                                                               r.get("peakLeanProcessBytes"))),
                     proofNodes=measurements(good, lambda r: r.get("proofNodes")))
        result.append(entry)
        timing = entry["wallSeconds"]
        print(f"{label}: {name}: {len(good)} successful runs; " +
              (f"median {timing['median']:.3f}s, worst {timing['worst']:.3f}s" if timing else "no successful timing"))
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
