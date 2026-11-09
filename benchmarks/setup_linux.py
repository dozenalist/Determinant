#!/usr/bin/env python3
"""Fetch the project's exact Linux Lean release into a temporary benchmark directory.

Requires Python 3.14's standard-library compression.zstd. Does not install elan,
change PATH, alter the project pin, or modify a global toolchain installation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import re
import subprocess
import tarfile
import tempfile
import urllib.request
import compression.zstd


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", default=str(Path(tempfile.gettempdir()) / "determinant-lean"))
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        parser.error("this benchmark setup targets x86-64 Linux")
    root = Path(__file__).resolve().parent.parent
    pin = (root / "lean-toolchain").read_text().strip()
    match = re.fullmatch(r"leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+)", pin)
    if not match:
        parser.error("expected an exact stable leanprover/lean4 version")
    version = match[1]
    directory = Path(args.directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    lean = directory / f"lean-{version}-linux" / "bin" / "lean"
    if not lean.exists():
        name = f"lean-{version}-linux.tar.zst"
        api = f"https://api.github.com/repos/leanprover/lean4/releases/tags/v{version}"
        with urllib.request.urlopen(api) as response:
            release = json.load(response)
        asset = next(a for a in release["assets"] if a["name"] == name)
        archive = directory / name
        print(f"Downloading {name} ({asset['size']} bytes)", flush=True)
        urllib.request.urlretrieve(asset["browser_download_url"], archive)
        digest = hashlib.file_digest(archive.open("rb"), "sha256").hexdigest()
        if asset.get("digest") and asset["digest"] != "sha256:" + digest:
            raise RuntimeError("release asset SHA-256 mismatch")
        print(f"SHA-256 {digest}; extracting", flush=True)
        with compression.zstd.open(archive, "rb") as stream:
            with tarfile.open(fileobj=stream, mode="r|") as bundle:
                bundle.extractall(directory, filter="data")
    result = subprocess.run([str(lean), "--version"], check=True, capture_output=True, text=True)
    if f"version {version}," not in result.stdout:
        raise RuntimeError("toolchain version does not match project pin")
    print(result.stdout.strip(), flush=True)
    print(lean, flush=True)


if __name__ == "__main__":
    main()
