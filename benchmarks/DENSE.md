# Combined tactic and strict dense benchmarks

The latest [checked-bridge follow-up](BRIDGES.md) reduces repeated conversions
while preserving the checker and trust boundary. Its current measurements,
rejected block/arithmetic experiments, and machine-variation caveats are recorded
separately from the historical samples below.

The [fused dot-product follow-up](OPTIMIZATION.md) improves fresh 50×50 / 100×100
median totals from 7.134 / 36.586 seconds to 5.065 / 24.348 seconds against a
remeasured baseline, with unchanged proof obligations. This report retains the
earlier measurements and their execution-mode details.

`certify_det_ne_zero` first tries the hypothesis/triangular tactic transactionally.
It then uses the bounded process producer and the same offline certificate replay
API. It accepts the optional `ProducerConfig` used by `certify_det_ne_zero_sage`.
No persistent certificate cache is involved. Importing a compiled theorem needs
neither Sage nor the producer's files.

The measured mode is ordinary kernel checking. There is no `native_decide`, native
evaluation axiom, `sorry`, or external-result axiom. Every generated theorem audits
its dependencies against `propext`, `Classical.choice`, and `Quot.sound`.

The initial 50×50 strict checker baseline took 81.448 seconds for the full product
and 67.545 seconds for the reduced product, each in one exploratory fresh run.
Those data are retained in [results-checker-baseline.json](results-checker-baseline.json).
They are profiling evidence, not repeated performance guarantees. The previous
arithmetic/list-kernel comparisons remain in [MODULAR.md](MODULAR.md).

The following changes address those bottlenecks:

- Lean's literal readers discover signed literal values directly; Mathlib's
  `evalRatEntry` remains the fallback for arithmetic expressions. Replay proves
  the residue equality against the original entries even when custom numeral
  instances make literal recognition misleading.
- One kernel-checked table equality replaces thousands of separate `norm_num`
  congruence proofs. This reduced 50×50 normalization to about half a second in
  exploratory profiles and greatly reduced the normalization proof.
- `NatCertificate` specializes nonnegative residue arithmetic to the kernel's
  natural literals. Its cast theorem connects the specialized dot product to
  Mathlib's existing padded list dot product. It adds no elimination/inversion
  algorithm. An explicit transpose is constructed once and its equality proved.
- A compiled preflight rejects bad products without evaluating the product twice
  in the kernel. It cannot establish acceptance. Reflexivity of the Boolean check
  requires the kernel to evaluate the complete deterministic checker. Above
  dimension 16, synchronous auxiliary row lemmas bound each reduction cache.
  These are ordinary checked theorems, with a checked data definition for columns.
- Direct integer constructors and raw natural literals avoid unnecessary numeral
  wrappers. `List.zipWith Nat.mul` and `List.foldr Nat.add` perform residue dot
  products; a row-width proof and a proved cast bridge connect them to Mathlib's
  padded dot products. Normalization and transpose equations use checked
  conversion rather than an additional decidable-list equality traversal.
- The reduced format checks exactly the diagonal and below-diagonal dot products.
  Full inverse replay still checks every product entry; the two formats retain
  distinct obligations, including over composite moduli.
- `int_matrix% [[...], ...]` uses Lean's integer constructors and list quotation and
  Mathlib's `ofLists` to avoid per-entry typeclass elaboration. One exploratory
  100×100 input using ordinary `Int.ofNat`/`Int.negSucc` syntax spent 42.010 seconds
  in input declaration elaboration alone. The new adapter accepts signed numeral
  data, with no external evaluation or proof assertion.
- The lossless JSON form `int_matrix% r#"[["2","1"],["2","2"]]"#` avoids parsing
  thousands of individual Lean numeral terms. Use `noncomputable def` for matrix
  data intended only for proofs. The complete data and theorem are kernel checked;
  the definition simply has no generated executable code. A repeated 100×100
  computable-definition comparison took 63.410–65.095 seconds, including roughly
  eight seconds in unnecessary data compilation and much larger artifact output.
- Ordinary `ofLists` notation is supported too. Lean switches to balanced lets
  for long list literals; the extractor zeta-reduces those bindings before using
  the library literal reader. A 40×40 regression crosses that threshold. Exact
  shape validation, bounded aliases, and the final checked goal connection apply
  to all supported representations.

Mathlib's shared dot-product arithmetic certifier was retained as an alternative.
The integer/list executable checkers remain available through `checkFull_sound`
and `checkUnitUpper_sound` for theorem-level replay. Profiling justified
specializing residue arithmetic rather than
adding packed multiplication, custom finite-field inversion, or a new certificate
scheme. Sage still selects its established backend through public APIs.

## Reproduction

Reference hardware: Intel Core Ultra 7 256V (8 cores / 8 logical processors),
16,811,347,968 bytes visible RAM, Windows 11 Home 10.0.26300; native x86-64 Lean
4.35.0 release (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Mathlib 4.35.0
(`56a005855ea17e0b0958f73ec801ae140b0a1679`); WSL 3.0.3, distribution
`SageMath-10.10`, Sage 10.10, Linux Python 3.14.10. WSL is already running and
dependencies are built. The desktop is not CPU isolated. No builds or correctness
tests run concurrently with the reported primary samples. The primary optimized
measurements run the exact pinned **Linux** Lean release and Sage natively in WSL,
with source and built dependencies on WSL's native filesystem. The available WSL
RAM is recorded in each environment file. The Windows/mounted-filesystem profiles
are retained separately and are not combined with the native WSL samples.

Generate inputs with Sage, outside the timed interval:

```powershell
lake build
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/generate_dense.py
```

The default input representation is the lossless JSON spelling of `int_matrix%`
(`--representation json`), with a `noncomputable` matrix definition in a Lean
`module`. Module-interface imports avoid loading unnecessary private dependency
data. The performance claim is scoped to that input and execution form; generic
notation and Windows filesystem costs remain part of their own totals.

The generator uses `GL(n, GF(p)).random_element().matrix()` and lifts its entries
by random signed multiples of `p`, using the recorded seed and Sage's public exact
matrix APIs. Thus the integer matrix is nonsingular modulo the intended prime.
Generation supplies no certificate to the tactic. Retry cases scale the first
row of a lift from `GF(3)` by two, making prime 2 fail and prime 3 succeed.
Triangular cases use signed nonzero diagonal entries. Manifests record the seed,
actual entry magnitude bits, representation, certificate kind and source SHA-256.

Configure the producer as in [PROTOCOL.md](../scripts/PROTOCOL.md), then run:

```powershell
$env:DETERMINANT_TEST_PYTHON = 'C:\Windows\System32\WindowsPowerShell\v1.0\powershell.exe'
$env:DETERMINANT_TEST_PREFIX = '["-NoProfile","-ExecutionPolicy","Bypass","-File","scripts/Invoke-SageWSL.ps1","-Distribution","SageMath-10.10","-Python","/usr/bin/python3","-Script"]'
powershell -NoProfile -ExecutionPolicy Bypass -File benchmarks/Run-Dense.ps1
```

That Windows runner is retained for comparison. The primary native WSL route is:

```powershell
# Setup and dependency compilation are outside the timed proofs.
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/setup_linux.py
# Use native Windows Python to package built dependencies efficiently:
python3 benchmarks/package_linux.py
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/prepare_linux.py --archive .lake/linux-benchmark.tar
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/generate_dense.py --output .lake/dense-inputs
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/run_linux.py --input .lake/dense-inputs --repeats 3
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/export_results.py --results /tmp/determinant-linux/results/dense-inputs --output benchmarks/evidence/dense
```

Use an installed native Python executable in place of `python3` if that name is
unavailable on Windows. `setup_linux.py` requires Python 3.14 and verifies the
official release SHA-256 when GitHub supplies it. The exact pinned Linux Lean is
installed in `/tmp`, without changing elan or the project pin. The package includes
`.ir.sig`, `.ir`, and all `.olean` parts. `prepare_linux.py` recompiles project
modules in `/tmp/determinant-linux` before timing. The native runner uses the
already installed `psutil` 7.2.2 for descendant metrics. Its own Python startup
is outside the timer; spawned fresh Lean and every producer are inside. There
is no Lake wrapper in the native primary invocation. Compiler version, OS/kernel,
input/source hashes, and visible RAM are exported alongside the measurements.

Each run invokes Lean on source afresh (`lake env lean -o ...` on Windows; the
exact Linux `lean -R ... -o ...` executable natively in WSL). The timer includes
Lean startup, imports, source parsing, matrix elaboration, extraction,
serialization, launcher/supervisor/Sage startup, prime retries and inversion,
parsing, proof construction, kernel checking, axiom audit, and artifact writing.
Windows totals additionally include the Lake/elan wrapper.
It excludes input generation and dependency builds. It never reuses a compiled
benchmark declaration or a certificate. `Elab.async false` makes final declaration
kernel profiling synchronous; it does not change proof trust.

The input declaration and tactic phases have monotonic timers. Startup/imports
and pre-export elapsed time have markers tied to the runner's Linux monotonic
clock. The difference between process exit and the latter marker estimates
artifact writing and exit overhead. Lean's built-in profiler reports cumulative
kernel time and the final theorem check separately. Row checking is included in
both tactic execution and cumulative kernel time; do not add overlapping phases.
Producer metadata separates Sage import, matrix construction, search/inversion
and residue encoding. Subtracting reported worker time from transport approximates
launcher, supervisor and pipe overhead; it is not a separate inversion measurement.

The Windows runner samples fresh Lake/Lean processes every 100 ms and records
lifetime peak working set per process plus the maximum sampled combined working
set. Old editor servers are excluded. Sage's Linux worker reports its peak RSS
separately. These are component measurements, not a synchronized machine-wide
peak; WSL VM/launcher overhead is not included in those memory figures. Artifacts
include the main `.olean` and the sum of all its emitted parts. Proof size is
`Lean.Expr.numObjs` on the final theorem value, counting shared expression objects
without expanding auxiliary theorem bodies. All artifact parts include those
auxiliary declarations; the node count is not their expanded aggregate proof size.

Use `--dimensions`, `--bits`, `--variants`, `--kind`, `--representation`, and
`--output` on the generator for additional cases. The runner accepts separate
input/output directories, name patterns, repetitions, and a per-run deadline;
it retains unsuccessful measurements and logs instead of dropping them.

Correctness commands are in the README. They cover singular and corrupted
certificates, both formats, composite moduli, signed/large entries, empty and
singleton matrices, aliases, unsupported symbolic inputs, producer errors,
timeouts, cancellation and worker cleanup. `tests/Sage.lean` exercises the public
dispatcher against real Sage and audits its final declarations.

## Measurements

The primary strict native WSL samples use fresh source elaboration, `int_matrix%`
with decimal-string JSON, `noncomputable` data definitions, module imports and
the reduced certificate kind. The first three dimensions have three repetitions:

| Dimension | Entry magnitude bound | Median seconds | Worst seconds | All runs |
| --- | --- | ---: | ---: | --- |
| 10 | 20 bits, signed | 3.162 | 13.455 | 13.455, 3.162, 2.381 |
| 50 | 20 bits, signed | 6.318 | 7.390 | 7.390, 6.318, 5.711 |
| 100 | 20 bits, signed | **48.003** | **53.965** | 53.965, 48.003, 45.426 |
| 128 | 20 bits, signed | 94.777 | 95.018 | 94.536, 95.018 |
| 200 | 20 bits, signed | — (one run) | 384.988 | 384.988 |

All three 100×100 samples satisfy the 60-second target in this advertised mode.
This is not a claim about arbitrary notation, entries, primes, machines or sizes.
The 128×128 size is supported but did not meet the one-minute target.
Sage selected its established characteristic-two backend
`sage.matrix.matrix_mod2_dense.Matrix_mod2_dense`. Every axiom audit passed.
See [the complete primary records](evidence/dense/results.json), their logs,
input sources, manifest and exact environment in the same directory.
Larger-size records are exported separately under
[evidence/scale128](evidence/scale128/results.json).
The successful 200×200 scaling sample is in
[evidence/scale200](evidence/scale200/results.json). It is a single observation,
so no repeated-run median is claimed for that dimension.

At 100×100 the final theorem has 74,936 shared proof-expression objects and
3,350,544 bytes across all `.olean` parts (159,808 bytes for the main interface).
Maximum Lean peak RSS across the three runs was 1,800,654,848 bytes. Median row
kernel checking was 38.734 seconds; median final-theorem checking was 2.970 seconds.
Producer transport was 1.338 seconds at its median. These nested phases explain
why optimizing Sage inversion is not the main remaining scaling opportunity.

At 128×128 the proof has 122,503 shared expression objects, 5,131,400 bytes across
all artifact parts, and maximum Lean peak RSS of 2,033,242,112 bytes. Two samples
are sufficient to report their observed median/worst, not a uniform scaling law.
The single 200×200 proof has 297,386 objects in its final value, 11,672,760 bytes
across all artifact parts, and 2,902,986,752 bytes peak Lean RSS. Row kernel proofs
take 349.167 seconds, while producer transport takes 1.439 seconds. This directly
identifies strict arithmetic reduction as the next scaling bottleneck.

The timing mode uses ordinary desktop scheduling, warm WSL, and built dependencies.
Every process and Sage worker is fresh; filesystem pages may be warm. First-run
startup variation is retained (for example, the 10×10 first run takes 13.455 s).
The reports do not substitute a warm theorem artifact for a fresh declaration.
Sage's backend is chosen automatically: characteristic-two inversion is already
only milliseconds in these cases, so forcing FLINT/LinBox would not address the
dominant kernel reduction time. Modulus-three retry cases exercise Sage's selected
modular backend separately; the 100×100 case reports
`sage.matrix.matrix_modn_dense_float.Matrix_modn_dense_float`, while the earlier
2×2 example selected FLINT. Backend selection is dimension dependent in this setup.

The 50×50 pipeline is detailed in [HANDOFF.md](HANDOFF.md), including phase overlap,
memory/artifact sizes, the exact reproduction commands and future optimization
directions. Kernel checking dominates; producer inversion is a small fraction of
the total. The larger-size and additional-family results come from the same
sequential measurement batch.

The deliberately bad-prime 100×100 example also passes in **49.788 seconds**:
prime 2 is rejected and prime 3 succeeds using Sage's selected
`matrix_modn_dense_float` backend. See
[the retry record](evidence/retry/results.json). This is one additional matrix and
one fresh timing, not a repeated-run distribution.

A separate signed **256-bit** 100×100 matrix passes in **48.319 seconds**, with
the same strict reduced checker and a fresh producer. See
[the large-entry record](evidence/large256/results.json). This is a successful
large-entry example, not a guarantee for all arbitrary-precision entries.

The combined dispatcher selects the direct triangular route at 50×50 and 100×100:
fresh totals are **1.829 s** and **2.782 s**, with no producer metadata or invocation.
See [triangular evidence](evidence/triangular/results.json). The full inverse kind
at 50×50 takes **13.007 s** in its single comparison, versus a 6.318 s median for
reduced checking; see [full-product evidence](evidence/full50/results.json).

An optional second 200×200 repeat was stopped after the required families were
exported to preserve the user's time window. It is not counted as a successful
or complete sample. No repeated-run median is claimed at 200. Further repetitions
at that size are a follow-up, not evidence for a uniform larger-size bound.

The compiled 100×100 theorem was imported with the producer deliberately
unavailable: [import audit](evidence/import-large.json), 1.109 s, ordinary axioms
only. Its auxiliary row proofs and data are self-contained in the emitted parts.
All exported comparisons are summarized in [summary.json](summary.json).

Validation: the Windows `lake build` passes. The native Linux suites
`Modular.lean`, `ModularRows.lean`, `Dispatch.lean`, `Bridge.lean`, `Sage.lean`, and
`Triangular.lean` pass, including their strict axiom audits, composite moduli,
corrupted certificates, long list notation and process cleanup. Producer Python
tests pass both in native standard Python (Sage-specific cases skipped there) and
in Sage Python (the missing-Sage case skipped there). The malformed-JSON literal
rejection cases in `Dispatch.lean` also passed separately after timing. Benchmark
and producer helper scripts pass Python syntax compilation.

Retained comparisons: [computable input](evidence/computable-input/results.json)
missed the target at 100×100 (63.410, 64.007, 65.095 seconds);
[an earlier native checker](evidence/slow-native125/results.json) took 125.881
seconds and [an intermediate version](evidence/slow-native92/results.json) took
92.621 seconds. These include successful, audited proofs but do not establish the
target. Earlier Windows runs include an [aborted slow input](results-dense-slow.json),
a [long-list extraction failure](results-dense-shape-failure.json), and a
[kernel timeout](results-dense-kernel-timeout.json). Failed/aborted runs produced no
accepted theorem artifact and are excluded from successful-run statistics.
