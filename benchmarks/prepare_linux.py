#!/usr/bin/env python3
"""Prepare a native Linux benchmark workspace with built, pinned dependencies.

Run from the repository in WSL after `lake build` on Windows and setup_linux.py.
Only copies data into the explicit temporary workspace; no global install changes.
The project modules are recompiled with the Linux release before timing proofs.
"""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile


MODULES = [
    "Determinant/Basic", "Determinant/Modular", "Determinant/Certificate",
    "Determinant/NatCertificate", "Determinant/Tactic/Matrix",
    "Determinant/Tactic/Triangular", "Determinant/Tactic/Modular",
    "Determinant/Tactic/Bridge", "Determinant/Tactic/Dispatch",
    "Determinant/Tactic/CharZero",
    "Determinant/Tactic/Literal", "Determinant/Tactic/Cache",
    "Determinant/Tactic", "Determinant",
]


def imports(path):
    text = re.sub(r"/-.*?-/", "", path.read_text(encoding="utf-8"), flags=re.S)
    for line in text.splitlines():
        line = line.split("--", 1)[0].strip()
        if not line or line in {"module", "prelude"}:
            continue
        match = re.fullmatch(r"(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", line)
        if match:
            yield match[1]
        else:
            break


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", default=str(Path(tempfile.gettempdir()) / "determinant-linux"))
    parser.add_argument("--lean", default="/tmp/determinant-lean/lean-4.35.0-linux/bin/lean")
    parser.add_argument("--archive", help="archive made by package_linux.py using native filesystem access")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    workspace = Path(args.workspace).resolve()
    if workspace == root or root.is_relative_to(workspace):
        parser.error("use a separate benchmark workspace")
    workspace.mkdir(parents=True, exist_ok=True)
    lean = Path(args.lean).resolve()
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    pin = (root / "lean-toolchain").read_text().strip().split(":v")[-1]
    if f"version {pin}," not in version:
        parser.error("Linux compiler must match lean-toolchain")
    paths = [workspace / ".lake/build/lib/lean"]
    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = {p["name"]: root / ".lake/packages" / p["name"] for p in manifest["packages"]}
    for name in packages:
        paths.append(workspace / "dependencies" / name)
    if args.archive:
        print("Extracting native dependency archive", flush=True)
        with Path(args.archive).open("rb", buffering=4 * 1024 * 1024) as stream:
            with tarfile.open(fileobj=stream, mode="r|", bufsize=4 * 1024 * 1024) as bundle:
                bundle.extractall(workspace, filter="data")
    else:
        for name in ["Determinant", "scripts", "tests", "benchmarks"]:
            shutil.copytree(root / name, workspace / name, dirs_exist_ok=True)
        for name in ["Determinant.lean", "lean-toolchain", "lake-manifest.json", "lakefile.toml"]:
            shutil.copy2(root / name, workspace / name)
    todo = [] if args.archive else ["Determinant"]
    seen = set()
    copied = 0
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
            raise RuntimeError(f"cannot locate source for dependency {module}")
        name, base = located
        todo.extend(imports(base / relative.with_suffix(".lean")))
        if name is None:
            continue
        for suffix in [".olean", ".olean.private", ".olean.server", ".ilean", ".ir", ".ir.sig"]:
            source = base / ".lake/build/lib/lean" / (str(relative) + suffix)
            if source.exists():
                target = workspace / "dependencies" / name / (str(relative) + suffix)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, target)
        copied += 1
        if copied % 100 == 0:
            print(f"Copied {copied} required dependency modules", flush=True)
    print(f"Copied {copied} required dependency modules", flush=True)
    env = dict(os.environ, LEAN_PATH=":".join(str(p) for p in paths))
    for module in MODULES:
        source = workspace / (module + ".lean")
        output = paths[0] / (module + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        print(f"Building {module}", flush=True)
        subprocess.run([str(lean), "-R", str(workspace), "-o", str(output), str(source)],
                       cwd=workspace, env=env, check=True)
    configuration = dict(workspace=str(workspace), lean=str(lean), lean_version=version,
                         lean_path=[str(p) for p in paths], source_root=str(root),
                         mathlib_revision=next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"))
    (workspace / "benchmark-environment.json").write_text(json.dumps(configuration, indent=2) + "\n")
    print(workspace / "benchmark-environment.json", flush=True)


if __name__ == "__main__":
    main()
