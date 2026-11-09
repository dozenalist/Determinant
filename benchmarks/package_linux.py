#!/usr/bin/env python3
"""Package required built dependencies with native filesystem access before WSL extraction."""
import argparse
import io
import json
from pathlib import Path
import tarfile

from prepare_linux import imports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default=".lake/linux-benchmark.tar")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    output = (root / args.output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = {p["name"]: root / ".lake/packages" / p["name"] for p in manifest["packages"]}
    todo, seen, copied = ["Determinant"], set(), 0
    with tarfile.open(output, "w") as bundle:
        for directory in ["Determinant", "scripts", "tests", "benchmarks"]:
            for source in sorted((root / directory).rglob("*")):
                if source.is_file() and "__pycache__" not in source.parts:
                    bundle.add(source, arcname=source.relative_to(root).as_posix(), recursive=False)
        for name in ["Determinant.lean", "lean-toolchain", "lake-manifest.json", "lakefile.toml"]:
            bundle.add(root / name, arcname=name)
        while todo:
            module = todo.pop()
            if module in seen or module.split(".")[0] in {"Lean", "Init", "Std", "Lake"}:
                continue
            seen.add(module)
            relative = Path(*module.split("."))
            candidates = [(None, root)] if module.split(".")[0] == "Determinant" else list(packages.items())
            located = next(((name, base) for name, base in candidates
                            if (base / relative.with_suffix(".lean")).exists()), None)
            if located is None:
                raise RuntimeError(f"cannot locate source for {module}")
            name, base = located
            todo.extend(imports(base / relative.with_suffix(".lean")))
            if name is None:
                continue
            for suffix in [".olean", ".olean.private", ".olean.server", ".ilean", ".ir", ".ir.sig"]:
                source = base / ".lake/build/lib/lean" / (str(relative) + suffix)
                if source.exists():
                    target = Path("dependencies") / name / (str(relative) + suffix)
                    bundle.add(source, arcname=target.as_posix(), recursive=False)
            copied += 1
            if copied % 200 == 0:
                print(f"Packaged {copied} dependency modules", flush=True)
        metadata = json.dumps(dict(dependency_modules=copied, source_root=str(root))).encode()
        entry = tarfile.TarInfo("benchmark-package.json")
        entry.size = len(metadata)
        bundle.addfile(entry, io.BytesIO(metadata))
    print(f"{output}: {output.stat().st_size} bytes, {copied} dependency modules", flush=True)


if __name__ == "__main__":
    main()
