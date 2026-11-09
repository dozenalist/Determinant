# Milestones 4–5: certification performance handoff

Characteristic-zero follow-up: the combined integer tactic is now `det_ne_zero_int`
(formerly `certify_det_ne_zero`). `det_ne_zero` lifts concrete integer-entry
matrices over `[CommRing R] [CharZero R]` to the same checker, including `ℂ`.
See [CHAR_ZERO.md](CHAR_ZERO.md) for the cast bridge, regressions, and paired
performance measurements. Final 100×100 median certification is 30.187 s versus
27.234 s for the integer tactic (10.8% overhead, including kernel checking).
Whole-process medians are 41.885 versus 29.584 s because ring-numeral input
elaboration also costs more. Historical evidence below keeps its original names.

Latest follow-up: [BRIDGES.md](BRIDGES.md) retains separately checked normalization
and transpose lemmas. Fresh confirmation medians improve from 10.630 to 9.728 s
at 50×50 and from 48.969 to 41.783 s at 100×100 against the fused checker
remeasured in that session. Machine speed varied substantially; the report keeps
the initial and confirmation batches separate. Row blocks and arithmetic
experiments were reverted. Milestone 6 remains untouched.

Performance follow-up: [OPTIMIZATION.md](OPTIMIZATION.md) records the retained
fused dot product, lowering fresh median certification from 7.134 to 5.065 seconds
at 50×50 and from 36.586 to 24.348 seconds at 100×100. Expression sharing was tested
and reverted. Milestone 6 remains untouched. The measurements below are the
earlier historical baseline; use the follow-up for the current checker.

Read [DENSE.md](DENSE.md) and its raw evidence first. `ROADMAP.md` is the authority
for milestone acceptance. Milestones 4 and 5 are complete for the documented
strict native WSL mode: the repeated 100×100 target and larger-size scaling
evidence are recorded below. This uses complete fresh declarations, including
kernel checks and producer startup. Persistent certificates (`certify_det_ne_zero!`) are Milestone 6
and have not been implemented in this work.

Useful entry points for the next agent: [the 50×50 phase table](#a-measured-5050-pipeline),
[native reproduction](#reproduce-and-continue-in-this-sessions-prepared-workspace),
and [measured optimization directions](#improvements-to-investigate-next). The
raw evidence is authoritative if a rounded prose statistic differs.

## Current implementation and trust boundary

- `Determinant/Tactic/Dispatch.lean`: public `certify_det_ne_zero`, optional
  `ProducerConfig`, transactional triangular-first route, then the bounded
  producer and the shared strict replay API. A throwing producer in
  `tests/Dispatch.lean` proves triangular goals do not launch external computation.
- `Determinant/Tactic/Matrix.lean`: integer-only vector parser using Mathlib's
  `Matrix.matchVecConsPrefix`, exact-shape `ofLists` parser, at most 64 aliases,
  and Lean's fast literal readers with Mathlib arithmetic evaluation as fallback.
  The higher-level Mathlib parser was inspected and replaced by this small adapter
  because its imports pulled in unrelated analysis tactics. Long list notation
  introduces balanced `let`s; zeta-reduction is required before list recognition.
- `Determinant/Tactic/Literal.lean`: `int_matrix% [[...], ...]` and lossless JSON
  `int_matrix% r#"[["2","3"],["1","2"]]"#` produce ordinary Mathlib `ofLists`
  terms with direct integer constructors. No process or proof assertion is involved.
- `Determinant/NatCertificate.lean`: natural residue dot products use the fused
  structural `natDotFused`, proved equal to the public `List.zipWith Nat.mul` /
  `List.foldr Nat.add` specification by `natDotFused_eq`. `natDotZip_eq`, `natDot_cast`,
  and `checkNat_sound` connect this to the existing padded integer-list checker
  and its determinant theorem. The row-width obligation is mandatory.
- `Determinant/Tactic/Modular.lean`: normalize original integer expressions once;
  above dimension 16, synchronously check their residue table equality in an
  auxiliary theorem, substituting local definitions before closure abstraction.
  Build an explicit transpose and check its connection in another auxiliary theorem.
  Small inputs retain direct conversion proofs. Compiled `checkNat` is
  only a rejection preflight. Accepted evidence is reflexivity of the actual
  Boolean check, requiring kernel reduction to `true`. Above dimension 16, each
  row is a separate synchronous checked auxiliary theorem; a shared checked
  definition holds the column table. The final theorem assembles those row proofs.
- Both full and reduced formats remain deterministic. Full checks all cells;
  reduced checks the diagonal and below it. No `native_decide`, generated native
  axiom, `sorry`, or producer assertion is accepted. Every benchmark and regression
  audits final declarations against `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/det_certificate.py`: Sage's public exact inversion APIs, no custom
  elimination. Metadata now measures import, matrix construction, search/inversion,
  residue encoding, and Linux worker peak RSS. Lean's transport trace includes
  supervisor/launcher overhead. POSIX exec failures can surface as child status
  255; `processProducer` normalizes that into a missing-executable diagnostic.

## A measured 50×50 pipeline

The final three fresh runs took **7.390, 6.318, and 5.711 seconds**: median
**6.318**, worst **7.390**. The exact sources, environment, hashes, logs and records
are in [evidence/dense](evidence/dense/results.json). This table reports the median
and worst observed time for each step across those three runs. Medians of separate
steps need not belong to the same run.

| Step | Median ms | Worst ms | Scope |
| --- | ---: | ---: | --- |
| Lean startup and imports | 910 | 930 | Fresh native Lean process through first command marker |
| Matrix input declaration | 14 | 15 | Lossless JSON parse and checked noncomputable matrix definition |
| Triangular attempt | 10 | 11 | Hypotheses/literal attempt, restored before modular fallback |
| Extraction | 6 | 8 | Actual goal matrix and closed integer entries |
| Serialization | 1 | 2 | Request JSON construction/compression |
| Producer transport | 951 | 1,262 | Supervisor, worker startup, I/O, computation, exit |
| Sage import (inside transport) | 664 | 891 | Fresh worker imports |
| Integer matrix construction (inside transport) | 1 | 1 | Public Sage matrix API |
| Search/inversion (inside transport) | 10 | 31 | Prime 2, exact characteristic-two inverse |
| Certificate encoding (inside transport) | 1 | 1 | Canonical residue strings |
| Response parsing | 2 | 2 | JSON and certificate validation |
| Normalization bridge construction | 300 | 437 | Residue literals and checked conversion against original expressions |
| Certificate proof, inclusive | 3,331 | 3,857 | Shared data, transpose, preflight, row checks, assembly |
| Row kernel proofs (inside preceding row) | 3,109 | 3,602 | All required deterministic dot products, synchronously checked |
| Other certificate preparation/assembly | 222 | 255 | Inclusive certificate phase minus row kernel phase |
| Goal connection | 1 | 2 | Proof type versus actual determinant goal |
| Final theorem kernel check | 419 | 422 | Assembly and conversion after row lemmas are checked |
| Cumulative kernel profiler | 3,490 | 3,970 | Overlaps row/final phases; not additive |
| Artifact export and process exit | 114.989 | 124.164 | Exit time minus pre-export monotonic marker |
| Remaining command elaboration/audit/scheduling | about 256 | about 320 | Residual, not a separately instrumented subsystem |
| Whole fresh process | **6,318** | **7,390** | Primary end-to-end result |

Each final theorem value has 19,012 shared expression objects (without expanding
auxiliary row lemmas); all `.olean` parts, including those lemmas, total
1,255,368 bytes. Maximum Lean process peak RSS is 1,519,665,152 bytes. Producer
worker peak RSS is at most 213,568 KiB. Measurements overlap as labelled: do not
add producer subphases, row kernel time, cumulative kernel time, and their parent
phases together. The step medians are not a partition of the median total.

For comparison, the following earlier isolated run used the same matrix and
checker before the additional startup/export instrumentation and took 9.220 s:

One isolated native WSL run of the current strict checker took **9.220 seconds**.
It used seed `20261158`, a random invertible matrix over `GF(2)` lifted by signed
multiples of two, maximum integer magnitude 20 bits, `unit-upper-product`, a
`noncomputable` matrix definition, JSON literal input, and a Lean `module`.
This is a successful fresh declaration, not an imported proof or replayed `.olean`.

| Step | Milliseconds | What the timer includes |
| --- | ---: | --- |
| Matrix input declaration | 17 | Parse lossless integer data and check the definition |
| Triangular attempt | 17 | Hypotheses/literal route, transactional failure before modular discovery |
| Extraction | 8 | Read the actual goal matrix and closed integer entries |
| Serialization | 2 | Build/compress the row-major protocol JSON |
| Producer transport | 1,386 | Spawn supervisor/Sage worker, I/O, inversion, exit |
| Sage import (inside transport) | 991 | Worker imports `sage.all` |
| Sage matrix construction (inside transport) | 1 | Public `matrix(ZZ, ...)` construction |
| Prime search/inversion (inside transport) | 13 | Reduction and public exact inverse; prime 2 succeeds |
| Certificate encoding (inside transport) | 1 | Canonical inverse residue strings |
| Response parsing | 2 | Lean JSON decode, exact shape/modulus/residue validation |
| Normalization/proof bridge construction | 619 | Residue data and conversion check against original expressions |
| Certificate proof, inclusive | 4,795 | Data/transpose preparation, preflight, row checks, assembly |
| Row kernel proofs (inside preceding row) | 4,427 | Synchronous kernel reductions of the checked dot products |
| Goal connection | 1 | Final proof type versus the original matrix goal |
| Cumulative kernel profiler | 5,050 | Overlaps row checks and final theorem checking; do not add it to total |
| Whole fresh process | 9,220 | Includes imports, all above work, final audit, export, exit |

The resulting proof has 19,012 shared expression objects. The main `.olean` is
159,832 bytes; all emitted parts total 1,253,168 bytes. Lean peak RSS was
1,519,542,272 bytes; Sage worker peak RSS was 213,568 KiB. The raw run is retained
with the final evidence. The later detailed 50×50 samples also measure startup/imports
and export/exit explicitly; use their median/worst values when comparing changes.
These timings are nested and rounded, so summing this table is incorrect.

The final 100×100 reference samples all pass below sixty seconds: **53.965,
48.003, 45.426 s** (median **48.003**, worst **53.965**). Row kernel checking
still dominates: median **38.734 s**; final assembly kernel checking **2.970 s**;
producer transport **1.338 s**. Data/proof artifacts total **3,350,544 bytes** and
peak Lean RSS is at most **1,800,654,848 bytes** in these runs. The two 128×128
samples take **94.536 and 95.018 s** and therefore exceed the one-minute target.
The 200×200 proof passed in **384.988 s** in one successful scaling sample:
**349.167 s** in row kernel proofs, **13.900 s** in final theorem checking,
**8.883 s** in normalization construction, and only **1.439 s** in producer
transport. Its proof value has 297,386 shared objects, all artifact parts total
11,672,760 bytes, and Lean peak RSS is 2,902,986,752 bytes. There is no repeated-run
median for 200×200. Additional-family measurements are in DENSE.md and the evidence.
The bad-prime 100×100 retry takes 49.788 s and a signed 256-bit 100×100 example
takes 48.319 s, each measured once. Triangular 50/100 examples take 1.829/2.782 s
without a producer. A full-product 50×50 comparison takes 13.007 s. The optional
second 200×200 repeat was stopped to preserve the requested work window, and is
not counted as a complete sample. All correctness suites and axiom audits pass.

## Reproduce and continue in this session's prepared workspace

The Windows project is at `C:\Users\carte\lean\ModularFormsBridge\Determinant`.
`ELAN_HOME` may need to be set to `C:\Users\carte\.elan` in sandboxed shells.
Windows Lean is available through `lake`. WSL distribution is `SageMath-10.10`.
Native Windows Python 3.11.9 is installed at
`C:\Program Files\WindowsApps\PythonSoftwareFoundation.Python.3.11_3.11.2544.0_x64__qbz5n2kfra8p0\python3.11.exe`.

The native workspace is `/tmp/determinant-linux`, exact Linux Lean is
`/tmp/determinant-lean/lean-4.35.0-linux/bin/lean`, and
`/tmp/determinant-linux/benchmark-environment.json` records `LEAN_PATH` and pins.
The primary benchmark copies source inputs into that native filesystem before
starting its timer. Importing thousands of artifacts directly through `/mnt/c`
was extremely slow and is not the advertised execution method.

From PowerShell at the project root:

```powershell
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/generate_dense.py --dimensions 50 --output .lake/recheck50
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/run_linux.py --input .lake/recheck50 --repeats 3
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/export_results.py --results /tmp/determinant-linux/results/recheck50 --output benchmarks/evidence/recheck50
```

`run_linux.py` records process start through successful exit and polls memory every
50 ms. Its `wait4` peak RSS is a component peak, not a synchronized whole-machine
peak. It records combined sampled descendant RSS and the producer's own peak too.
The source hash, matrix seed, Sage version, compiler version, kernel/OS, source
hashes and each axiom report accompany results. All `.olean` parts count toward
artifact size. `Elab.async false` keeps row/final kernel checks synchronous.

For a clean native setup, use `setup_linux.py`, `package_linux.py`, and
`prepare_linux.py --archive ...` as documented in DENSE.md. **Include `.ir.sig`**
alongside `.ir` and all `.olean` parts; omitting it gave misleading missing-data
errors even though `.olean` files existed. The package reads source import headers
to copy only the required pinned dependency closure. Recompile the project modules
with Linux Lean before timing. Toolchain setup and dependency builds are outside
the primary benchmark, but fresh Lean/Sage startup and every per-goal operation
remain inside it.

If changing implementation files in the Windows checkout, copy and recompile
them into the native workspace; otherwise a benchmark can silently measure old
code. The temporary helper `.lake/update_linux.py` does this for named modules.
Rebuild downstream modules when changing public declarations or signatures.
The helper is convenient in this session; the documented preparation script is
the reproducible route for a fresh environment. Do not mistake cached imports of
the benchmark theorem for a fresh elaboration.

## Improvements to investigate next

1. **Keep the row-kernel budget visible.** At 100×100 it dominates. Compare fresh
   50×50 and 100×100 declarations before and after a change. Report cumulative
   kernel time, row time, final-declaration kernel time, total time, memory, all
   artifact parts, and axioms. A faster producer alone is immaterial here.
2. **Preserve compact literal and module input.** For proof-only matrices,
   `noncomputable def` prevents pointless data compilation. One exploratory
   100×100 declaration using ordinary constructor syntax spent 42.010 seconds in
   input elaboration; a compact JSON noncomputable declaration took 87 ms. Avoid
   reverting to enormous function-index simplifications or per-cell numeral proofs.
3. **Measure sharing, then fuse only if justified.** Try Lean's public
   `ShareCommon.shareCommon` on shared column literals and theorem propositions.
   Follow-up: sharing did not improve the measured 50/100 cases and was reverted;
   the fused structural dot product did improve them and was retained, with a
   proved equality to the existing specification. See OPTIMIZATION.md. The earlier
   multi-branch zero-skipping/numeral specialization was slower than the current
   public `zipWith`/`foldr` route; do not reintroduce it without measurement.
4. **Tune checked block size.** Current threshold is `n > 16`, one checked row
   lemma per row. Test small blocks of rows versus one whole-check proof. The
   latter previously caused multi-gigabyte reduction caches and long pauses.
   Bound caches while avoiding repeated unfolding of the shared column definition.
   Follow-up: blocks of two and four rows did not establish a speedup and were
   reverted; one checked row remains. See BRIDGES.md and its rejected patches.
5. **Optimize conversion bridges separately.** Normalization and transpose are
   quadratic data traversals. Maintain a proof about the *actual original entry
   expressions*. A digest, native equality, or producer success cannot replace it.
   Custom numeral instances in `tests/Modular.lean` specifically test this boundary.
   Follow-up: separate checked normalization/transpose lemmas were retained.
   `tests/ModularRows.lean` also checks local entries and custom numeral instances
   above the splitting threshold. See BRIDGES.md for measurements and evidence.
6. **Use a proved compact representation only after profiling.** Packed binary
   arithmetic or a published elimination/decomposition certificate may help the
   cubic kernel bottleneck. Search the pinned public libraries first. Prove the
   semantic bridge and deterministic acceptance; do not substitute Freivalds,
   random spot checks, or native-evaluation axioms.
7. **Expand performance scope honestly.** The fast advertised path uses reduced
   checking and often prime 2. Full-product mode, bad-prime retries, composite
   moduli, very large entries, general notation, Windows/mounted-filesystem I/O,
   and larger dimensions have distinct costs. Retain slow/timeout records and
   never omit final kernel time to meet the target.
8. **Only then start Milestone 6.** Reuse `proveCertificateForEntries` and the
   current strict replay for persistent candidates. The cache must store full
   `A`, `B`, and `p`, compare actual matrix identity, and recheck all evidence.

Correctness checks: `lake build`, `tests/Triangular.lean`, `tests/Modular.lean`,
`tests/ModularRows.lean`, `tests/Dispatch.lean`, `tests/Bridge.lean`, real
`tests/Sage.lean`, and the Python producer suites in both native Python and Sage.
`tests/ImportSage.lean` audits import of a compiled result with discovery unavailable.
Keep tests for malformed shape/JSON, false success, corrupted checked entries,
wrong matrix/modulus/kind/version, singularity, retry, cancellation, worker cleanup,
long balanced list notation, local aliases and signed/large entries.
