#!/usr/bin/env python3
"""Export native benchmark evidence, without copying large theorem artifacts."""
import argparse
import json
from pathlib import Path
import shutil

from run_linux import parse_log


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    source, output = Path(args.results), Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    records = json.loads((source / "results.json").read_text())
    environment = json.loads((source / "environment.json").read_text())
    for record in records:
        log = source / record["log"]
        if log.exists():
            record.update(parse_log(log.read_text()))
            shutil.copy2(log, output / log.name)
        if environment.get("input_directory"):
            original = Path(environment["input_directory"]) / (record["case"]["name"] + ".lean")
            if original.exists():
                (output / "inputs").mkdir(exist_ok=True)
                shutil.copy2(original, output / "inputs" / original.name)
    for name in ["environment.json", "manifest.json"]:
        if (source / name).exists():
            shutil.copy2(source / name, output / name)
    (output / "results.json").write_text(json.dumps(records, indent=2) + "\n")
    print(f"Exported {len(records)} records to {output}")


if __name__ == "__main__":
    main()
