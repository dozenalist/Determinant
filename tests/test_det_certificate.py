"""Run: python3 -m unittest discover -s tests -p 'test_*.py' -v.

Protocol tests need only standard Python; Sage integration tests require sage.all.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "det_certificate.py"
spec = importlib.util.spec_from_file_location("det_certificate", SCRIPT)
producer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(producer)
try:
    import sage.all  # noqa: F401
    HAVE_SAGE = True
except ImportError:
    HAVE_SAGE = False


def request(entries=None, n=2, **overrides):
    result = dict(protocol=producer.PROTOCOL, version=1, dimension=n,
                  entries=entries if entries is not None else ["2", "1", "2", "2"],
                  kind="full-inverse", preferred_primes=["2", "3", "5"],
                  max_attempts=8, timeout_ms=30000, verify_product=True)
    result.update(overrides)
    return result


def run(data, *args):
    return subprocess.run([sys.executable, str(SCRIPT), *args], input=json.dumps(data),
                          text=True, capture_output=True, timeout=45)


class ProtocolTests(unittest.TestCase):
    def test_lossless_and_empty(self):
        huge = "-" + "9" * 5000
        self.assertEqual(producer.validate_request(request([huge], n=1))[1], [int(huge)])
        self.assertEqual(producer.validate_request(request([], n=0)), (0, []))

    def test_reject_bad_data(self):
        for patch in [dict(version=2), dict(version=True), dict(dimension=True),
                      dict(dimension=-1), dict(entries=["1"]), dict(kind="success"),
                      dict(max_attempts=0), dict(timeout_ms=0), dict(verify_product=1),
                      dict(preferred_primes=["1"]), dict(preferred_primes=[2])]:
            with self.subTest(patch=patch), self.assertRaises(producer.ProtocolError):
                producer.validate_request(request(**patch))
        for value in ["+1", "01", "-0", " 1", "1.0", "1e3", "١", 1, True, None]:
            with self.subTest(value=value), self.assertRaises(producer.ProtocolError):
                producer.decimal(value)

    def test_malformed_request_and_arguments(self):
        result = run(request(entries=["bad"]))
        self.assertEqual(result.returncode, 4)
        self.assertEqual(json.loads(result.stdout)["error"]["code"], "invalid-request")
        self.assertIn("invalid certificate request", result.stderr)
        result = run(request(), "--unknown-argument")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unrecognized arguments", result.stderr)

    def test_supervisor_timeout_includes_import(self):
        result = run(request(timeout_ms=1))
        self.assertEqual(result.returncode, 3)
        self.assertEqual(json.loads(result.stdout)["error"]["code"], "timeout")

    @unittest.skipIf(HAVE_SAGE, "this case needs a Python without Sage")
    def test_missing_sage_diagnostic(self):
        result = run(request())
        self.assertEqual(result.returncode, 5, result.stderr + result.stdout)
        self.assertEqual(json.loads(result.stdout)["error"]["code"], "sage-unavailable")
        self.assertIn("use a Python environment", result.stderr)


@unittest.skipUnless(HAVE_SAGE, "SageMath is not installed in this Python environment")
class SageTests(unittest.TestCase):
    def test_dense_bad_prime_retry(self):
        result = run(request())  # determinant = 2: bad at 2, good at 3.
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        data = json.loads(result.stdout)
        self.assertEqual(data["producer"]["attempted_primes"], ["2", "3"])
        self.assertEqual(data["certificate"]["modulus"], "3")
        self.assertEqual(data["certificate"]["inverse"], [["1", "1"], ["2", "1"]])
        self.assertIn("singular reduction modulo 2", result.stderr)
        self.assertTrue(data["producer"]["backend"].startswith("sage."))

    def test_singular_and_exhausted_are_not_integer_singularity(self):
        for entries in [["1", "2", "1", "2"], ["1", "2", "0", "0"],
                        ["2", "1", "2", "2"]]:
            with self.subTest(entries=entries):
                result = run(request(entries=entries, max_attempts=1))
                self.assertEqual(result.returncode, 2, result.stderr + result.stdout)
                data = json.loads(result.stdout)
                self.assertEqual(data["error"]["code"], "search-exhausted")
                self.assertIn("does not establish integer singularity", data["error"]["message"])

    def test_empty_singleton_signed_large_reduced_and_fallback(self):
        for data in [request([], n=0), request(["-3"], n=1),
                     request([str(-(10**100) + 1)], n=1),
                     request(kind="unit-upper-product"), request(preferred_primes=[])]:
            with self.subTest(data=data):
                result = run(data)
                self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
                cert = json.loads(result.stdout)["certificate"]
                self.assertEqual(cert["kind"], data["kind"])
                self.assertEqual(cert["dimension"], data["dimension"])
                p = int(cert["modulus"])
                for row in cert["inverse"]:
                    self.assertTrue(all(0 <= int(x) < p for x in row))

    def test_nonprime_candidate_is_configuration_error(self):
        result = run(request(preferred_primes=["4"]))
        self.assertEqual(result.returncode, 4, result.stderr + result.stdout)
        self.assertIn("not prime", json.loads(result.stdout)["error"]["message"])


if __name__ == "__main__":
    unittest.main()
