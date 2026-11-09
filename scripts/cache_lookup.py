#!/usr/bin/env python3
"""Project-local, data-only witness lookup. Standard Python only; never imports Sage.

One JSON request on stdin, one JSON result on stdout. See CACHE.md for the public
record/identity formats. This helper indexes candidates; Lean checks the proof.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

SCHEMA = "det-ne-zero-witness"
ENCODING = "det-ne-zero-matrix-v1"
KINDS = {"full-inverse", "unit-upper-product"}
MAX_BYTES = 64 * 1024 * 1024


def matrix_identity(n, entries):
    if type(n) is not int or n < 0:
        raise ValueError("dimension must be a nonnegative integer")
    if not isinstance(entries, list) or len(entries) != n * n:
        raise ValueError("expected dimension squared row-major entries")
    if any(not isinstance(x, str) or re.fullmatch(r"0|-?[1-9][0-9]*", x, re.ASCII) is None
           for x in entries):
        raise ValueError("expected canonical signed decimal strings")
    # Newlines cannot occur in canonical decimals. A final newline is mandatory.
    canonical = ("\n".join([ENCODING, str(n), *entries]) + "\n").encode("ascii")
    return {"encoding": ENCODING, "dimension": n, "entries": entries}, hashlib.sha256(canonical).hexdigest()


def project_root(request):
    if request.get("project_root") is not None:
        root = Path(request["project_root"]).resolve()
        if not root.is_dir():
            raise ValueError("project_root must be an existing directory")
        return root
    source = request.get("source_file")
    start = Path(source).resolve().parent if source and not source.startswith("<") else Path.cwd().resolve()
    for root in (start, *start.parents):
        if (root / "lakefile.toml").is_file() or (root / "lakefile.lean").is_file():
            return root
    raise ValueError("cannot locate the source's Lake project; set projectRoot explicitly")


def witness_path(request, digest):
    root = project_root(request)
    directory = (root / request.get("directory", "det_ne_zero_witnesses")).resolve()
    if directory == root or not directory.is_relative_to(root):
        raise ValueError("witness directory must be inside the local project root")
    kind = request["kind"]
    if kind not in KINDS:
        raise ValueError("unsupported certificate kind")
    n = request["dimension"]
    path = directory / f"matrix-v1-{n}x{n}-{digest}-{kind}.json"
    if path.is_symlink():
        raise ValueError("witness files must not be symbolic links")
    return path


def validate_record(record, matrix, kind):
    if not isinstance(record, dict) or record.get("schema") != SCHEMA or type(record.get("version")) is not int or record["version"] != 1:
        raise ValueError("incompatible witness schema/version")
    if record.get("matrix") != matrix:
        raise ValueError("stored full integer matrix does not match the current matrix")
    response = record["response"]
    if response.get("protocol") != "determinant-certificate" or response.get("version") != 1 or response.get("status") != "ok":
        raise ValueError("invalid certificate response")
    cert = response["certificate"]
    if cert.get("kind") != kind or cert.get("dimension") != matrix["dimension"]:
        raise ValueError("incompatible certificate kind/dimension")
    # Lean performs strict decoding and all mathematical checks, on every replay.
    return record


def execute(request):
    matrix, digest = matrix_identity(request["dimension"], request["entries"])
    path = witness_path(request, digest)
    limit = request.get("max_bytes", MAX_BYTES)
    if type(limit) is not int or limit <= 0:
        raise ValueError("max_bytes must be positive")
    if request["action"] == "lookup":
        try:
            with path.open("rb") as stream:
                data = stream.read(limit + 1)
            if len(data) > limit:
                raise ValueError("witness exceeds byte limit")
            record = validate_record(json.loads(data), matrix, request["kind"])
            return {"status": "hit", "path": str(path), "record": record}
        except FileNotFoundError:
            return {"status": "miss", "path": str(path)}
        except (ValueError, KeyError, TypeError, AttributeError) as error:
            return {"status": "rejected", "path": str(path), "message": str(error)}
    if request["action"] != "store":
        raise ValueError("unsupported cache action")
    record = validate_record(dict(schema=SCHEMA, version=1, matrix=matrix,
                                  response=request["response"]), matrix, request["kind"])
    data = (json.dumps(record, ensure_ascii=True, separators=(",", ":")) + "\n").encode("ascii")
    if len(data) > limit:
        raise ValueError("witness exceeds byte limit")
    path.parent.mkdir(parents=True, exist_ok=True)
    # Unique staging files in the same directory; concurrent writers publish only
    # complete records. An interrupted staging file is never a lookup candidate.
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".staging-", suffix=".tmp", delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return {"status": "stored", "path": str(path)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export", type=Path, metavar="WITNESS", help="export a Lean RawCertificate term for offline replay")
    args = parser.parse_args()
    try:
        if args.export:
            record = json.loads(args.export.read_bytes())
            matrix = record["matrix"]
            matrix, _ = matrix_identity(matrix["dimension"], matrix["entries"])
            kind = record["response"]["certificate"]["kind"]
            validate_record(record, matrix, kind)
            cert = record["response"]["certificate"]
            p = cert["modulus"]
            if kind not in KINDS or type(cert["version"]) is not int or cert["version"] != 1:
                raise ValueError("unsupported certificate kind/version")
            if not isinstance(p, str) or re.fullmatch(r"[1-9][0-9]*", p, re.ASCII) is None or int(p) < 2:
                raise ValueError("invalid modulus")
            n, rows = matrix["dimension"], cert["inverse"]
            if not isinstance(rows, list) or len(rows) != n:
                raise ValueError("invalid inverse shape")
            for row in rows:
                if not isinstance(row, list) or len(row) != n:
                    raise ValueError("invalid inverse shape")
                for value in row:
                    if not isinstance(value, str) or re.fullmatch(r"0|[1-9][0-9]*", value, re.ASCII) is None or int(value) >= int(p):
                        raise ValueError("invalid inverse residue")
            inverse = "[" + ", ".join("[" + ", ".join(row) + "]" for row in rows) + "]"
            print(f'{{ version := 1, dimension := {n}, modulus := {p}, kind := "{kind}", inverse := {inverse} }}')
            return 0
        data = sys.stdin.buffer.read(MAX_BYTES + 1)
        if len(data) > MAX_BYTES:
            raise ValueError("cache request exceeds byte limit")
        result = execute(json.loads(data))
        code = 0
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        result, code = {"status": "error", "message": str(error)}, 1
    print(json.dumps(result, separators=(",", ":")), flush=True)
    return code


if __name__ == "__main__":
    sys.exit(main())
