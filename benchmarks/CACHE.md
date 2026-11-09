# Milestone 6: project-local determinant witnesses

Implemented `det_ne_zero!` and `det_ne_zero_int!` with a configurable
`det_ne_zero_witnesses/` default at the local Lake project root. The cached route
uses the existing dispatcher and checker, preserving the triangular fast path,
strict arithmetic checking, and the connection to the actual goal. Configuration,
canonical identity bytes, JSON schema, directory confinement, atomic publication,
policies, and standalone export are specified in [scripts/CACHE.md](../scripts/CACHE.md).

The helper uses Python's standard `hashlib`, JSON, filesystem, and temporary-file
APIs. It computes one SHA-256 filename and opens only that candidate. There is no
directory scan or Sage import on a hit. Full integer A is checked for equality
before replay; the digest carries no mathematical authority. New records retain
full A, B, p and the complete producer response, including Sage version/backend
and timings. Only successfully kernel-checked candidates are published.

## Validation

`lake build` passes on native Windows with the pinned Lean 4.35.0 toolchain.
The final WSL regression pass covers `Cache`, fresh-process `CacheReplay`,
`Bridge`, `Dispatch`, `CharZero`, `Modular`, `ModularRows`, `Triangular`, `Sage`,
and import of the compiled Sage proof. All pass. The Python suite runs 17 tests;
16 pass and the missing-Sage diagnostic is skipped because Sage is installed.
Logs and exit codes are in [validation evidence](evidence/cache/validation/results.json).

The cache-specific checks cover:

- Initial miss and complete publication; repeat hit with the producer executable
  deliberately unavailable, including a second fresh Lean process.
- Exact full-A identity: a one-entry change creates a distinct witness, while
  arithmetic expressions and different characteristic-zero rings share the same
  integer table's candidate.
- Corrupted B and a changed modulus fail cache-only replay. Read/write mode can
  recover from invalid mathematical evidence. Singular candidates are not stored.
- Read/write, read-only, cache-only, disabled, refresh, directory option precedence,
  explicit directory overrides, and directory names containing spaces.
- Empty, singleton, and triangular goals require neither helper nor producer and
  create no modular record.
- Truncated/corrupt records, incompatible schemas, mismatched full matrices,
  canonical signed decimal strings, and integers with 5000 decimal digits.
- Concurrent writes, interrupted atomic replacement, abandoned staging files,
  and confinement of paths/symlinks to the configured local project.
- Lookup with directory listing disabled, demonstrating that cache size does not
  add a scan of other matrices.

All representative Lean declarations audit their axioms against `propext`,
`Classical.choice`, and `Quot.sound`. Importing a compiled cached theorem also
passes with no Python or Sage executable on PATH. Exporting a witness to a
`RawCertificate` term and replaying it through `certify_det_ne_zero_modular` works
with no Python or Sage on PATH. Cache-only replay itself requires standard Python
for lookup; it does not require Sage.

## Paired fresh-process measurements

Hardware: Intel Core Ultra 7 256V, eight logical CPUs; native WSL2 Linux
6.18.54.1, about 7.59 GiB visible memory, Python 3.14.10, SageMath 10.10. Lean and
Mathlib are pinned to 4.35.0; Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

Inputs reuse the archived dense 20-bit signed matrices at 100×100 and 128×128,
using `int_matrix%` JSON decimal strings and `unit-upper-product` certificates.
Each sample starts a new Lean process, elaborates the input, rebuilds the proof,
kernel checks and audits its axioms, and writes the artifact. It does not reuse
an up-to-date proof `.olean`. Each repeat runs ordinary `det_ne_zero`, a genuine
miss in a new empty configured directory, then a cache-only hit in another fresh
process with a nonexistent producer executable. No refresh shortcut is used to
simulate a miss. Runs are sequential, with the regression/build workload completed
before these final samples.

At 100×100, three samples per mode give the following median/worst seconds:

| Mode | End-to-end | Tactic | Producer calls per sample |
| --- | ---: | ---: | ---: |
| Ordinary `det_ne_zero` | 29.629 / 29.888 | 26.733 / 27.170 | 1 |
| `det_ne_zero!` miss | 29.058 / 29.392 | 26.402 / 26.713 | 1 |
| `det_ne_zero!` hit | 26.103 / 26.775 | 23.606 / 24.075 | 0 |

The miss shows no material end-to-end slowdown in this batch. Its measured cache
phases have medians of 115 ms for lookup, 635 ms for pre-publication kernel
verification, and 168 ms for atomic storage: about 0.92 seconds total, or 3.1% of
the ordinary median. Variability in the dominant kernel row checks offsets that
extra work in the paired totals; persistence does not itself accelerate those
checks. Hits need only a 118 ms median lookup and avoid the producer's roughly
1.5-second startup/transport path. The observed median end-to-end hit is 11.9%
faster than the ordinary route.

Worst sampled Lean RSS is 1588.5 MiB ordinary, 1594.6 MiB on a miss, and
1593.9 MiB on a hit. Worst sampled combined process-tree RSS is 1610.5,
1759.3, and 1593.9 MiB respectively. These are 50 ms samples, not guarantees about
unsampled peaks. [All nine samples, phases, and axiom reports](evidence/cache/final100/results.json)
and their [environment](evidence/cache/final100/environment.json) are retained.

At 128×128, one fresh sample per mode takes 55.978 seconds ordinary, 57.866 on a
miss, and 55.270 on a hit. The miss is 3.4% slower and the hit 1.3% faster in this
single pair, consistent with small persistence overhead relative to proof checking.
The hit again invokes no producer. [Raw 128×128 results](evidence/cache/final128/results.json)
retain phase timings, sampled memory, logs, and the witness used for replay.

The cache eliminates discovery and Sage startup; it still constructs and checks
the Lean proof on every use. Kernel arithmetic remains cubic and dominates these
inputs, so cache replay offers a modest speedup rather than eliminating proof cost.
The 128×128 sample is a scaling check, not a repeated timing distribution. These
measurements concern integer goals through `det_ne_zero`; characteristic-zero
transport uses the same cache, and its separate costs are documented in
[CHAR_ZERO.md](CHAR_ZERO.md).

## Reproduction

Build the library, then run correctness and fresh replay in this order:

```sh
lake build
python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean tests/Cache.lean
lake env lean tests/CacheReplay.lean
```

For timings, use the native workspace setup documented in [HANDOFF.md](HANDOFF.md).
`prepare_linux.py` now builds `Determinant/Tactic/Cache` before the public imports.
The standard helper must be available in the prepared project's `scripts/`.
The benchmark runner additionally requires the existing `psutil` dependency.

```sh
python3 benchmarks/run_cache.py \
  --input benchmarks/evidence/checked-bridges/final-dense/inputs/dense-100-20bit-unit-upper-product-json-decimal-strings.lean \
  --output /tmp/determinant-linux/results/cache100 --repeats 3
python3 benchmarks/run_cache.py \
  --input benchmarks/evidence/scale128/inputs/dense-128-20bit-unit-upper-product-json-decimal-strings.lean \
  --output /tmp/determinant-linux/results/cache128 --repeats 1
```

The runner records end-to-end and tactic time, per-phase traces, producer calls,
sampled Lean and combined process-tree RSS, artifact size, and axiom reports.
Raw sources, logs, environment data, and selected full witness records accompany
the final results under [evidence/cache](evidence/cache). Witness records can be
copied into another local project or exported as described in the cache guide.
