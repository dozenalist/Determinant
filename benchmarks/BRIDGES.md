# Checked conversion bridges

This follow-up implements the conversion-bridge direction in [HANDOFF.md](HANDOFF.md).
It retains the fused dot product from [OPTIMIZATION.md](OPTIMIZATION.md), with one
checked row lemma per row above dimension 16. There is no persistent certificate
cache or change to the producer protocol.

## Implementation and trust

For dimensions above 16, `Determinant/Tactic/Modular.lean` now uses Lean's public
`mkAuxTheorem` to check two equalities as synchronous auxiliary theorems:

- Reduction of the **actual original integer expressions** to the residue table.
- Transposition of the supplied inverse table to the shared column table.

Each theorem uses reflexivity, so the kernel must compute and check its equality.
The final determinant proof references the checked theorem. Previously, these
conversions were checked by the metaprogram's `isDefEq` and repeated during the
final declaration's kernel check. `mkAuxTheorem` uses `zetaDelta := true` for
normalization so local entry definitions keep their values when the theorem is
closed. The small-matrix path is unchanged.

The pinned public adapter examined was `Lean.Meta.mkAuxTheorem` in
`Lean/Meta/Closure.lean`, which closes the type/value before calling
`Lean.Meta.mkAuxLemma`. `Elab.async false` keeps the checks synchronous, and
`cache := false` requests fresh auxiliary declarations instead of reusing a
theorem through the type-based lookup. This is ordinary proof checking, not
native evaluation.

The original matrix link, exact shape checks, row-width proof, transpose equation,
compiled rejection preflight, every required dot product, and final kernel check
remain mandatory. Full certificates still check every cell; reduced certificates
check every diagonal and below-diagonal cell. The axiom whitelist remains
`propext`, `Classical.choice`, and `Quot.sound`.

`tests/ModularRows.lean` adds coverage for entries containing a local definition
and a custom numeral instance at dimension 20. The latter must be rejected even
if literal discovery proposes different data.

## Repeated fresh measurements

The confirmation comparison uses the same saved signed 20-bit matrices, seeds
20261158 and 20261208, JSON `int_matrix%`, noncomputable data, module imports,
and reduced `unit-upper-product` checking. Each implementation has three fresh
declarations per dimension. These are comparisons with the fused checker
remeasured in this session, not with the older times in DENSE.md.

| Dimension | Original seconds | Checked bridges seconds | Median before → after | Reduction |
| --- | --- | --- | --- | ---: |
| 50×50 | 38.757, 10.630, 9.400 | 44.474, 7.527, 9.728 | **10.630 → 9.728** | **8.5%** |
| 100×100 | 48.969, 63.352, 42.806 | 34.788, 41.783, 44.964 | **48.969 → 41.783** | **14.7%** |

The 100×100 worst observed total falls from 63.352 to 44.964 seconds. The
50×50 worst total increases from 38.757 to 44.474 seconds: those first runs
include 26.772 and 34.444 seconds loading imports, respectively. No sample is
discarded. These are desktop observations, not a uniform runtime guarantee.

| Median phase, seconds | 50×50 original | 50×50 bridges | 100×100 original | 100×100 bridges |
| --- | ---: | ---: | ---: | ---: |
| Normalization, including its checked bridge | 0.749 | 0.266 | 3.318 | 1.884 |
| Row kernel proofs | 3.555 | 2.768 | 35.738 | 30.731 |
| Cumulative kernel profiler | 4.640 | 3.990 | 39.500 | 35.400 |
| Final declaration kernel check | 1.020 | 0.162 | 3.990 | 1.130 |

Kernel phases overlap and must not be added. Moving the two conversions into
checked auxiliary declarations removes the duplicate metaprogram/kernel work.
Row arithmetic is identical; its observed timing changes also reflect the
varying machine conditions. The cubic row checker remains the main bottleneck.

| Dimension | Maximum Lean peak RSS before → after, bytes | All `.olean` parts before → after, bytes | Final proof objects before → after |
| --- | --- | --- | --- |
| 50×50 | 1,516,224,512 → 1,476,165,632 | 1,255,344 → 1,256,496 | 19,012 → 16,636 |
| 100×100 | 1,798,041,600 → 1,659,768,832 | 3,350,528 → 3,351,680 | 74,936 → 65,273 |

Proof-object counts do not expand auxiliary theorem bodies. Artifact totals
include all auxiliary declarations. Peak RSS is a process/component measurement,
not synchronized whole-machine memory. The two extra checked theorems add
1,152 artifact bytes at either dimension.

Additional cases use the same saved input for each implementation:

| Case | Original seconds | Bridges seconds | Scope |
| --- | --- | --- | --- |
| Prime retry 100×100 | 52.827 | 41.720 | One each; prime 2 fails, prime 3 succeeds |
| Signed 256-bit entries, 100×100 | 57.999 | 37.354 | One each |
| Full inverse 50×50 | 11.928, 17.382, 15.518 | 12.214, 9.029, 12.704 | Three each; median **15.518 → 12.214** |

The initial full-inverse pair was slightly slower with bridges, so two more
samples per implementation were measured. All six remain in the comparison.
The retry and large-entry singles do not establish repeated-run distributions.

## Reproduction

Use the pinned native WSL setup and timing contract in [DENSE.md](DENSE.md).
Rebuild `Tactic/Modular` and its downstream modules before measuring a source
change. Rebuild `NatCertificate` too when reproducing the arithmetic experiments.
The evidence includes the exact baseline sources and retained/rejected patches.

```powershell
New-Item -ItemType Directory -Force .lake/bridge-recheck | Out-Null
Copy-Item benchmarks/evidence/checked-bridges/final-dense/manifest.json .lake/bridge-recheck/
Copy-Item benchmarks/evidence/checked-bridges/final-dense/inputs/*.lean .lake/bridge-recheck/
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/run_linux.py --input .lake/bridge-recheck --names '*-50-*' '*-100-*' --repeats 3
```

Every timed sample elaborates fresh source, starts a fresh Sage producer,
checks all auxiliary and final declarations, audits axioms, and writes theorem
artifacts. Dependency compilation and input generation are outside the timer.
No correctness suite or build runs concurrently with a timed sample.

## Exploratory comparisons

The first, faster-machine baseline had three samples per size: 50×50 took
5.859, 4.644, and 4.905 seconds; 100×100 took 23.739, 27.844, and 23.525 seconds.
The initial bridge experiment took 4.048 and 19.017 seconds respectively. That
experiment preceded the local-definition closure fix; final measurements use
the corrected implementation.

The other experiments were reverted:

| Experiment | 50×50 seconds | 100×100 seconds |
| --- | ---: | ---: |
| Two checked rows per block | 6.068 | 24.741 |
| Four checked rows per block | 5.150 | 28.643 |
| Accumulating tail-recursive dot product, with bridges | 11.697 | 42.957 |
| Fused column-index traversal, with bridges | 12.503 | 43.831 |

The block experiments proved assembly through `List.zipIdx_append` and
`List.all_append`. The accumulator had a proved equality to `natDotFused` using
associativity; the column traversal was proved equal to `zipIdx.all`. They did
not establish an improvement over the bridge implementation. The last two
experiments ran after startup, producer, and arithmetic timings all slowed,
so their totals alone cannot isolate an algorithmic regression. They are
retained as exploratory evidence, not repeated performance distributions.

Machine conditions changed substantially during this session. Rechecking the
**unchanged original** produced 50×50 totals of 38.757, 10.630, and 9.400 seconds
and 100×100 totals of 48.969, 63.352, and 42.806 seconds. The 38.757-second sample
included 26.772 seconds loading imports. All samples are retained. Initial and
confirmation measurements are kept in separate summary groups rather than
pooled across the change in machine speed.

## Evidence

The [summary](evidence/checked-bridges/summary.json) separates the initial,
confirmation, rejected, and additional-case groups. Its sibling directories
contain all **38 successful fresh declarations**, raw logs, exact input sources,
manifests, source hashes, pinned environments, kernel measurements, and axiom
reports. No benchmark theorem artifacts or certificates are reused during those timings.

The [retained patch](evidence/checked-bridges/retained.patch),
[baseline tactic](evidence/checked-bridges/baseline-Modular.lean), and
[baseline natural checker](evidence/checked-bridges/baseline-NatCertificate.lean)
allow exact reconstruction. Rejected patches are saved alongside them. The
[exploratory tactic](evidence/checked-bridges/exploratory-Modular.lean) records the
initial bridge variant before the local-definition fix. Source snapshots were
checked against the SHA-256 hashes recorded in their benchmark environments.

## Validation

All checks pass; the [validation records](evidence/checked-bridges/validation/results.json)
and sibling logs retain the native results and axiom audits:

- Windows `lake build` (1,913 jobs).
- Native Lean `Modular`, `ModularRows`, `Dispatch`, `Bridge`, `Sage`, and `Triangular`.
- Import of compiled `Sage` and the optimized 100×100 theorem with the producer
  deliberately unavailable.
- Producer tests under Windows standard Python (9 tests, 4 Sage-specific skips)
  and Sage Python (9 tests, 1 missing-Sage skip).

All 38 benchmark declarations and both import audits report only `propext`,
`Classical.choice`, and `Quot.sound`. The local-entry regression caught the need
for `zetaDelta := true`; the final implementation passes that regression and
the custom-numeral rejection check. Existing malformed-data, full/reduced,
composite-modulus, alias, cancellation, and process-cleanup coverage remains.

The retained production change is limited to `Determinant/Tactic/Modular.lean`.
`Determinant/NatCertificate.lean` is byte-for-byte identical to the starting
fused checker. Milestone 6 is unchanged.

## Direct comparison with the 19-second prototype

`benchmarks/compare_bridge_states.py` checks the archived prototype against the
current tactic directly. It verifies the prototype against the original
19.017-second run's recorded source hash, verifies that every other tactic source
is unchanged, and uses the exact same saved 100×100 signed 20-bit matrix.

The two versions are built into separate native temporary workspaces before any
timings. Shared dependency artifacts and unchanged project modules are identical;
the changed tactic module and all downstream modules are rebuilt separately.
There are no rebuilds between measured samples and no edits to the working tactic
or the original prepared native workspace.

The declared schedule is one complete warmup per version, retained separately,
followed by six counterbalanced pairs: prototype/current, current/prototype,
repeated three times. Each sample launches fresh Lean and Sage and includes
startup, discovery, proof construction, all kernel checks, axiom auditing,
artifact writing, and successful process exit. No benchmark theorem or certificate
is reused. Filesystem pages may be warm, as in the earlier native benchmarks.

The only executable source difference is `zetaDelta := true` for the normalization
auxiliary theorem. In the pinned `Lean/Meta/Closure.lean`, this also skips the
metaprogram's extra `check` in `preprocess`. Closed literal expressions take the
`visitExpr` fast path; the local-definition fix does not require expanding a
table of literal entries. Both versions still kernel-check the auxiliary theorem.

The [comparison evidence](evidence/prototype-current/summary.json) retains source
snapshots, individual logs, environments, exact inputs, sample order, warmups,
phase measurements, and descriptive paired statistics. Reproduce from the project
root in the prepared WSL environment, using a new output directory:

```powershell
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/compare_bridge_states.py --pairs 6 --output benchmarks/evidence/prototype-current-recheck
```
