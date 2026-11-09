#!/usr/bin/env python3
"""Data-only Sage adapter. Run with a Python interpreter that can import sage.all.

The standard-library supervisor bounds Sage import and inversion as well as search.
No linear algebra is implemented here: the worker uses Sage's public exact APIs.
"""

import argparse
import json
import re
import subprocess
import sys
import time

PROTOCOL = "determinant-certificate"
VERSION = 1
MAX_REQUEST_BYTES = 64 * 1024 * 1024
KINDS = {"full-inverse", "unit-upper-product"}

# Python 3.11's decimal conversion limit otherwise loses the arbitrary-size contract.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


class ProtocolError(ValueError):
    pass


def decimal(value, natural=False):
    pattern = r"0|[1-9][0-9]*" if natural else r"0|-?[1-9][0-9]*"
    if not isinstance(value, str) or re.fullmatch(pattern, value, re.ASCII) is None:
        raise ProtocolError("expected a canonical decimal integer string")
    return int(value)


def natural(value, name, positive=False):
    if type(value) is not int or value < (1 if positive else 0):
        raise ProtocolError(f"{name} must be {'positive' if positive else 'nonnegative'}")
    return value


def validate_request(request):
    if not isinstance(request, dict):
        raise ProtocolError("request must be an object")
    if request.get("protocol") != PROTOCOL or type(request.get("version")) is not int or request["version"] != VERSION:
        raise ProtocolError("unsupported protocol or version")
    n = natural(request.get("dimension"), "dimension")
    entries = request.get("entries")
    if not isinstance(entries, list) or len(entries) != n * n:
        raise ProtocolError("entries must contain exactly dimension squared integers in row-major order")
    values = [decimal(entry) for entry in entries]
    if request.get("kind") not in KINDS:
        raise ProtocolError("unsupported certificate kind")
    natural(request.get("max_attempts"), "max_attempts", positive=True)
    natural(request.get("timeout_ms"), "timeout_ms", positive=True)
    primes = request.get("preferred_primes")
    if not isinstance(primes, list) or any(decimal(p, natural=True) < 2 for p in primes):
        raise ProtocolError("preferred_primes must contain decimal integers greater than one")
    if type(request.get("verify_product")) is not bool:
        raise ProtocolError("verify_product must be a Boolean")
    return n, values


def failure(code, message, attempted=()):
    return {"protocol": PROTOCOL, "version": VERSION, "status": "error",
            "error": {"code": code, "message": message}, "attempted_primes": list(attempted)}


def produce(request):
    n, values = validate_request(request)
    started = time.monotonic()
    # Import only inside the supervised worker, never for protocol validation.
    from sage.all import GF, ZZ, identity_matrix, matrix, next_prime
    from sage.env import SAGE_VERSION

    imported = time.monotonic()
    integer_matrix = matrix(ZZ, n, n, values)
    constructed = time.monotonic()
    candidates = [ZZ(p) for p in request["preferred_primes"]]
    attempted = []
    previous = max(candidates, default=ZZ(1))
    for attempt in range(request["max_attempts"]):
        if (time.monotonic() - started) * 1000 >= request["timeout_ms"]:
            return failure("timeout", "certificate producer time budget exhausted", attempted), 3
        if attempt < len(candidates):
            p = candidates[attempt]
            if not p.is_prime(proof=True):
                raise ProtocolError(f"preferred candidate {p} is not prime")
        else:
            previous = next_prime(previous, proof=True)
            p = previous
        attempted.append(str(p))
        # Let the installed Sage release select its established backend.
        reduced = integer_matrix.change_ring(GF(p))
        try:
            inverse = reduced.inverse()
        except ZeroDivisionError:
            print(f"singular reduction modulo {p}; trying another prime", file=sys.stderr, flush=True)
            continue
        if request["verify_product"] and reduced * inverse != identity_matrix(GF(p), n):
            raise RuntimeError("Sage inverse failed the optional product check")
        inverted = time.monotonic()
        inverse_rows = [[str(ZZ(inverse[i, j]) % p) for j in range(n)] for i in range(n)]
        encoded = time.monotonic()
        try:
            import resource
            peak_rss_kib = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        except ImportError:
            peak_rss_kib = None
        response = {"protocol": PROTOCOL, "version": VERSION, "status": "ok",
                    "certificate": {"version": VERSION, "dimension": n, "modulus": str(p),
                                    "kind": request["kind"],
                                    "inverse": inverse_rows},
                    "producer": {"name": "SageMath", "sage_version": SAGE_VERSION,
                                 "backend": type(reduced).__module__ + "." + type(reduced).__name__,
                                 "attempted_primes": attempted,
                                 "import_ms": round((imported - started) * 1000),
                                 "matrix_ms": round((constructed - imported) * 1000),
                                 "search_inverse_ms": round((inverted - constructed) * 1000),
                                 "certificate_encode_ms": round((encoded - inverted) * 1000),
                                 "peak_rss_kib": peak_rss_kib,
                                 "elapsed_ms": round((time.monotonic() - started) * 1000)}}
        return response, 0
    return failure("search-exhausted", "no certificate found within the prime-attempt budget; "
                   "this does not establish integer singularity", attempted), 2


def emit(response):
    print(json.dumps(response, separators=(",", ":")), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    try:
        data = sys.stdin.buffer.read(MAX_REQUEST_BYTES + 1)
        if len(data) > MAX_REQUEST_BYTES:
            raise ProtocolError("request exceeds byte limit")
        request = json.loads(data)
        validate_request(request)
        if args.worker:
            response, code = produce(request)
            emit(response)
            return code
        # subprocess.run kills and reaps a worker which exceeds its deadline, even
        # during a Sage import or a single long-running public inverse call.
        try:
            result = subprocess.run([sys.executable, __file__, "--worker"], input=data,
                                    timeout=request["timeout_ms"] / 1000, check=False)
            return result.returncode
        except subprocess.TimeoutExpired:
            emit(failure("timeout", "certificate producer time budget exhausted"))
            return 3
    except (ProtocolError, ValueError, KeyError, TypeError) as error:
        emit(failure("invalid-request", str(error)))
        print(f"invalid certificate request: {error}", file=sys.stderr)
        return 4
    except ImportError as error:
        emit(failure("sage-unavailable", str(error)))
        print("SageMath is unavailable; use a Python environment containing sage.all", file=sys.stderr)
        return 5
    except Exception as error:
        emit(failure("producer-failed", str(error)))
        print(f"certificate producer failed: {error}", file=sys.stderr)
        return 6


if __name__ == "__main__":
    sys.exit(main())
