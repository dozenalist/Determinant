"""Deliberately untrusted protocol/process fixture; contains no inversion algorithm."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

parser = argparse.ArgumentParser()
parser.add_argument("--mode", default="valid")
parser.add_argument("--literal", default="argument with spaces & $()")
parser.add_argument("--marker")
args = parser.parse_args()
assert args.literal == "argument with spaces & $()"
if args.mode == "no-read":
    time.sleep(60)
    sys.exit(0)
if args.mode == "wait":
    json.load(sys.stdin)
    time.sleep(60)
    sys.exit(0)
if args.mode == "child-tree":
    subprocess.Popen([sys.executable, "-c",
                      "import pathlib,sys,time; time.sleep(4); pathlib.Path(sys.argv[1]).touch()",
                      args.marker])
    Path(args.marker + ".started").touch()
    time.sleep(60)
    sys.exit(0)
data = json.load(sys.stdin)
if args.marker and args.mode != "child-tree":
    with Path(args.marker).open("a") as marker:
        marker.write("producer invoked\n")
if args.mode == "exit":
    print("deliberate producer diagnostic", file=sys.stderr)
    sys.exit(17)
if args.mode == "stdout-limit":
    print("x" * 100000, flush=True)
    time.sleep(60)
if args.mode == "stderr-limit":
    print("x" * 100000, file=sys.stderr, flush=True)
    time.sleep(60)
if args.mode == "invalid-utf8":
    os.write(sys.stdout.fileno(), b"\xff")
    sys.exit(0)
if args.mode == "malformed":
    print("not JSON")
    sys.exit(0)
if args.mode == "truncated":
    print('{"protocol":')
    sys.exit(0)
cert = dict(version=1, dimension=data["dimension"], modulus="5", kind=data["kind"],
            inverse=[["2", "2"], ["4", "2"]])
response = dict(protocol="determinant-certificate", version=1, status="ok", certificate=cert)
if args.mode == "bad-math":
    cert["inverse"][0][0] = "3"
if args.mode == "wrong-version":
    response["version"] = 2
if args.mode == "wrong-cert-version":
    cert["version"] = 2
if args.mode == "wrong-dimension":
    cert["dimension"] = 3
if args.mode == "wrong-modulus":
    cert["modulus"] = "1"
if args.mode == "wrong-kind":
    cert["kind"] = "producer-says-success"
if args.mode == "ragged":
    cert["inverse"][1].pop()
if args.mode == "noncanonical":
    cert["inverse"][0][0] = "02"
if args.mode == "numeric-integer":
    cert["inverse"][0][0] = 2
if args.mode == "residue-bound":
    cert["inverse"][0][0] = "7"
print(json.dumps(response), flush=True)
