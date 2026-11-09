# Fused dot-product certification follow-up

The newer [checked-bridge follow-up](BRIDGES.md) retains this fused checker and
removes repeated normalization/transpose conversion. Its fresh confirmation
100×100 median improves from 48.969 to 41.783 seconds under that session's slower
machine conditions. The historical fused-dot comparisons below remain separate.

The retained change replaces the intermediate `zipWith` product list and `foldr`
sum in the strict natural checker with one structural recursion. Fresh native
WSL certification became **29.0% faster at 50×50** and **33.4% faster at 100×100**
by the three-run medians below. These are comparisons against the original
checker remeasured in this session, not against the older, slower handoff samples.
Milestone 6 was not changed.

## Change and proof

`Determinant/NatCertificate.lean` adds `natDotFused` and proves
`natDotFused_eq : natDotFused a b = natDotZip a b` for arbitrary natural lists.
`checkNatRow` uses the fused function; `checkNat_entry` rewrites through this
equality and the existing `natDotZip_eq` and cast bridge. The original public
zip/fold implementation remains the specification and comparison point.

The pinned public implementations examined were `List.zipWith`, `List.foldr`,
`List.zipWith_foldr_eq_zip_foldr`, and Mathlib's padded `ListMatrix.dotProduct`.
The zip/fold theorem still leaves an intermediate list. The small fused adapter
removes that allocation and second traversal while retaining a proved connection
to those operations. It has no zero-skipping branches or modulus-specific cases.

The original matrix normalization, row-width obligation, transpose proof,
compiled rejection preflight, synchronous checked row lemmas, and final kernel
check remain in place. Full inverse checking still checks every entry; reduced
checking still checks exactly the diagonal and below it. The tests audit the new
equality theorem as well as the existing soundness and final determinant proofs.

## Measurements

Same pinned Lean 4.35.0, Mathlib, Sage 10.10, native WSL filesystem, hardware, and
timing contract as [DENSE.md](DENSE.md). Every sample elaborates fresh source,
starts a fresh producer, kernel-checks the proof and its auxiliary declarations,
audits axioms, and writes artifacts. No build or regression suite ran concurrently
with these measurements. No certificate cache or benchmark theorem import is used.

The dense cases use the exact previously saved signed 20-bit matrices, seeds
20261158 and 20261208, JSON `int_matrix%`, noncomputable data, module imports, and
`unit-upper-product`. Each implementation has three samples per dimension:
two initially, then a third after switching back to the original checker and
restoring the candidate. The intervening sharing experiment was discarded.

| Case | Original seconds | Fused seconds | Median before → after |
| --- | --- | --- | --- |
| Dense 50×50 | 7.134, 5.776, 16.764 | 4.950, 5.065, 5.422 | **7.134 → 5.065** |
| Dense 100×100 | 35.661, 36.586, 38.311 | 24.120, 24.348, 26.143 | **36.586 → 24.348** |
| Full inverse 50×50, one each | 10.725 | 7.689 | Single comparison |
| Prime retry 100×100, one each | 39.414 | 26.407 | Single comparison |

The retry case rejects prime 2 and succeeds at prime 3. The full-inverse case
exercises the public dispatcher's default certificate kind. These single samples
support the additional formats but do not establish repeated-run distributions.

The 16.764-second original 50×50 sample includes 10.015 seconds of startup/imports
and 2.216 seconds of producer transport. It is retained, not omitted. Desktop
scheduling and startup variation remain part of the totals. Row-kernel reduction
also improves independently of that variation:

| Median phase, seconds | 50×50 original | 50×50 fused | 100×100 original | 100×100 fused |
| --- | ---: | ---: | ---: | ---: |
| Row kernel proofs | 2.838 | 1.913 | 28.791 | 16.736 |
| Cumulative kernel profiler | 3.230 | 2.350 | 30.800 | 18.900 |
| Final declaration kernel check | 0.420 | 0.467 | 2.340 | 2.320 |

These kernel measurements overlap; do not add them. At 100×100 the median row
phase is 41.9% shorter. Final theorem checking is essentially unchanged.

There is no meaningful measured memory or proof-size improvement. Maximum Lean
peak RSS before/after is 1,520,009,216 / 1,519,816,704 bytes at 50×50 and
1,797,632,000 / 1,801,076,736 bytes at 100×100. All emitted `.olean` parts total
1,255,336 bytes at 50×50 and 3,350,512 bytes at 100×100 for both implementations.
Final proof values contain 19,012 and 74,936 shared expression objects respectively;
these counts do not expand auxiliary theorem bodies. Every benchmark audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Rejected experiment and evidence

Applying `Lean.ShareCommon.shareCommon` to the column literal and each row
proposition did not improve certification: 100×100 took 37.589 and 37.560 seconds,
with median row checking 29.581 seconds. Its 50×50 samples were 17.878 and 6.379
seconds (the first included 11.257 seconds of startup/imports). This change was
fully reverted. `Determinant/Tactic/Modular.lean` is identical to the starting file.

The [summary](evidence/fused-dot/summary.json) contains all aggregates. Its sibling
directories contain all 20 raw records, logs, input sources, manifests, and source
hashes: `baseline` plus `baseline-confirm-dense`, `fused` plus `final-dense`,
`sharing`, and the four full/retry comparisons. The
[retained patch](evidence/fused-dot/retained.patch) and
[rejected patch](evidence/fused-dot/rejected-sharing.patch) record both experiments.
The [original checker](evidence/fused-dot/baseline-NatCertificate.lean) allows exact
restoration of the measured baseline without relying on temporary session files.

## Reproduction and validation

Rebuild the changed project modules into the native WSL workspace before timing;
see the clean preparation procedure in [DENSE.md](DENSE.md). Rebuild
`NatCertificate` and its downstream tactic modules after each implementation switch.
Use the saved identical inputs for a recheck, from PowerShell at the project root:

```powershell
New-Item -ItemType Directory -Force .lake/fused-dot-recheck | Out-Null
Copy-Item benchmarks/evidence/fused-dot/final-dense/manifest.json .lake/fused-dot-recheck/
Copy-Item benchmarks/evidence/fused-dot/final-dense/inputs/*.lean .lake/fused-dot-recheck/
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/run_linux.py --input .lake/fused-dot-recheck --names '*-50-*' '*-100-*' --repeats 3
```

Correctness validation: Windows `lake build`; native Lean `Modular`, `ModularRows`,
`Dispatch`, `Bridge`, `Sage`, and `Triangular` suites; compiled `Sage` and optimized
100×100 theorem imports with the producer deliberately unavailable. The
[validation logs](evidence/fused-dot/validation/results.json) retain the suite results
and axiom audits. Existing rejection, composite-modulus, custom-numeral, shape,
alias, cancellation, process-cleanup, and full/reduced distinction tests remain.
