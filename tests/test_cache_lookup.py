"""Standard-library tests for witness identity, locality, and atomic persistence."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "scripts/cache_lookup.py"
spec = importlib.util.spec_from_file_location("cache_lookup", SCRIPT)
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)


def response(n=2, kind="full-inverse"):
    return dict(protocol="determinant-certificate", version=1, status="ok",
                certificate=dict(version=1, dimension=n, modulus="5", kind=kind,
                                 inverse=[["2", "2"], ["4", "2"]]),
                producer=dict(name="fixture", version="1"))


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "lakefile.toml").touch()
        (self.root / "src").mkdir()
        self.request = dict(action="lookup", source_file=str(self.root / "src/Goal.lean"),
                            directory="det_ne_zero_witnesses", dimension=2,
                            entries=["2", "3", "1", "2"], kind="full-inverse")

    def store(self, **overrides):
        return cache.execute(dict(self.request, action="store", response=response(), **overrides))

    def test_identity_and_single_entry_change(self):
        matrix, digest = cache.matrix_identity(2, self.request["entries"])
        expected = b"det-ne-zero-matrix-v1\n2\n2\n3\n1\n2\n"
        self.assertEqual(digest, hashlib.sha256(expected).hexdigest())
        self.assertEqual(matrix["entries"], self.request["entries"])
        miss = cache.execute(self.request)
        self.assertEqual(miss["status"], "miss")
        self.assertFalse(Path(miss["path"]).parent.exists())
        self.store()
        hit = cache.execute(self.request)
        self.assertEqual(hit["status"], "hit")
        self.assertEqual(hit["record"]["response"], response())
        self.assertIn(digest, Path(hit["path"]).name)
        self.assertEqual(cache.execute(dict(self.request, entries=["2", "4", "1", "2"]))["status"], "miss")
        self.assertEqual(cache.execute(dict(self.request, kind="unit-upper-product"))["status"], "miss")

    def test_lossless_large_signed_empty_and_invalid_integers(self):
        huge = "-" + "9" * 5000
        request = dict(self.request, dimension=1, entries=[huge])
        cache.execute(dict(request, action="store", response=response(1)))
        self.assertEqual(cache.execute(request)["record"]["matrix"]["entries"], [huge])
        self.assertEqual(cache.matrix_identity(0, [])[0]["entries"], [])
        for n, entries in [(True, ["1"]), (-1, []), (2, ["1"]), (1, ["01"]),
                           (1, ["-0"]), (1, ["+1"]), (1, [1]), (1, ["١"])]:
            with self.subTest(entries=entries), self.assertRaises(ValueError):
                cache.matrix_identity(n, entries)

    def test_source_root_overrides_cwd_and_no_directory_scanning(self):
        with patch("pathlib.Path.cwd", return_value=Path("/unrelated")):
            path = Path(self.store()["path"])
        self.assertEqual(path.parent, self.root / "det_ne_zero_witnesses")
        with patch("pathlib.Path.iterdir", side_effect=AssertionError("linear scan")):
            self.assertEqual(cache.execute(self.request)["status"], "hit")
        custom = self.store(directory="proofs/custom witnesses")
        self.assertEqual(Path(custom["path"]).parent, self.root / "proofs/custom witnesses")
        for directory in ["..", str(self.root.parent), "."]:
            with self.subTest(directory=directory), self.assertRaises(ValueError):
                cache.execute(dict(self.request, directory=directory))

    def test_corruption_migration_collision_and_size(self):
        path = Path(self.store()["path"])
        original = path.read_text()
        for text in ['{"schema":', '{"status":"ok"}',
                     original.replace('"version":1', '"version":2', 1),
                     original.replace('"entries":["2","3"', '"entries":["2","4"')]:
            path.write_text(text)
            self.assertEqual(cache.execute(self.request)["status"], "rejected")
        path.write_text(original)
        self.assertEqual(cache.execute(dict(self.request, max_bytes=1))["status"], "rejected")
        with self.assertRaises(ValueError):
            self.store(max_bytes=1)
        self.assertEqual(path.read_text(), original)

    def test_atomic_failure_concurrency_and_orphan_staging(self):
        path = Path(self.store()["path"])
        original = path.read_bytes()
        with patch("os.replace", side_effect=OSError("simulated interrupted publication")):
            with self.assertRaises(OSError):
                self.store()
        self.assertEqual(path.read_bytes(), original)
        self.assertEqual(list(path.parent.glob(".staging-*")), [])
        (path.parent / ".staging-abandoned.tmp").write_text("incomplete")
        with ThreadPoolExecutor(max_workers=8) as pool:
            results = list(pool.map(lambda _: self.store(), range(24)))
        self.assertTrue(all(x["status"] == "stored" for x in results))
        self.assertEqual(cache.execute(self.request)["status"], "hit")
        self.assertEqual(len(list(path.parent.glob("matrix-*.json"))), 1)

    def test_symlinks_cannot_escape_project(self):
        with tempfile.TemporaryDirectory() as external:
            link = self.root / "outside"
            try:
                link.symlink_to(external, target_is_directory=True)
            except OSError:
                self.skipTest("symlink creation unavailable")
            with self.assertRaises(ValueError):
                cache.execute(dict(self.request, directory="outside"))

    def test_fresh_process_without_sage(self):
        self.store()
        result = subprocess.run([sys.executable, "-S", str(SCRIPT)],
                                input=json.dumps(self.request), text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(result.stdout)["status"], "hit")
        result = subprocess.run([sys.executable, str(SCRIPT)], input="{", text=True, capture_output=True)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(json.loads(result.stdout)["status"], "error")

    def test_export_is_data_only(self):
        path = self.store()["path"]
        result = subprocess.run([sys.executable, str(SCRIPT), "--export", path],
                                text=True, capture_output=True, check=True)
        self.assertIn('dimension := 2, modulus := 5, kind := "full-inverse"', result.stdout)
        self.assertIn('inverse := [[2, 2], [4, 2]]', result.stdout)
        data = json.loads(Path(path).read_text())
        data["response"]["certificate"]["inverse"][0][0] = "by sorry"
        Path(path).write_text(json.dumps(data))
        result = subprocess.run([sys.executable, str(SCRIPT), "--export", path],
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 1)


if __name__ == "__main__":
    unittest.main()
