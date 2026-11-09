# Characteristic-zero determinant tactics

`det_ne_zero_int` is the renamed `certify_det_ne_zero` dispatcher. Its public
meta entry point is `Determinant.Tactic.detNeZeroInt`; the triangular-first
strategy, producer configuration, and strict modular replay are unchanged.
Generated benchmark sources and current examples use the new name. Archived
benchmark evidence retains the spelling used when it was measured.

`det_ne_zero` accepts concrete integer-entry matrices over `[CommRing R] [CharZero R]`.
It supports the existing square `Fin n` vector/list literals, reducible aliases,
local definitions, both orientations of the nonzero goal, signed numerals, and
closed arithmetic recognized as integer-valued by `norm_num`. No `IsDomain R`
assumption is needed. It takes the same optional `ProducerConfig` as the integer
tactic. Dense goals use the same Sage setup described in [PROTOCOL.md](../scripts/PROTOCOL.md).

```lean
import Determinant
import Mathlib.Basic.Complex.Basic

example : (!![2, 3; 1, 4] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
  det_ne_zero
```

## Checked cast bridge

The tactic parses the matrix once and constructs an integer matrix `A` together
with a proof that the original matrix is `A.map (Int.castRingHom R)`. Ordinary
signed numeral tables use `literalIntCast`, an interpreter proved equal to integer
casting once for every entry value. A whole-table conversion check connects this
interpretation to the actual original expressions. Above dimension 16, this is a
synchronous checked auxiliary theorem; final assembly references it. Small inputs
use direct conversion, checked again in the final theorem. This avoids thousands
of individual scalar cast proofs. Nonstandard numeral instances bypass this fast
path before conversion, avoiding expensive failed reduction in concrete rings.

Arithmetic expressions retain a proof-producing `norm_num` fallback. List congruence
and the proved `ofLists_int_cast` lemma give its structural bridge without enumerating
matrix indices. Repeated entry expressions share normalization results and proofs.
Negative integer entries use the same fast constructor format as `int_matrix%`.

The integer subgoal goes through `detNeZeroInt`. The theorem
`det_ne_zero_of_int_cast` transports its result using `Int.cast_det` and the
injectivity of integer casts in characteristic zero. The completed proof is
checked against the original goal, including its actual numeral instances.
For integer goals, `det_ne_zero` calls the integer dispatcher directly.
The extra work is quadratic in the number of rows for fixed-size entry expressions;
the certificate checker retains its cubic dot-product work.

## Performance method

The paired inputs reuse the signed 20-bit dense tables and seeds from the existing
dense suite, with `kind := "unit-upper-product"`. The new target is an arbitrary
type `R` with `CommRing R` and `CharZero R` instances. This checks that the bridge
works without evaluating arithmetic in the target ring. The benchmark-only
`ring_matrix%` elaborator constructs ordinary ring numerals; it adds no proof or
trusted assertion and is not a new public tactic input syntax.

Each sample starts a fresh native Linux Lean process and Sage producer in the
prepared WSL workspace, proves a new theorem with synchronous kernel checking,
audits axioms, and writes all theorem artifacts. No benchmark theorem or
certificate is reused. Dependencies are built before timing. Three fresh samples
are retained for each variant and size. Certification time is the elapsed tactic
invocation plus the final theorem kernel check; it includes the cast bridge,
Sage startup, integer replay, and all auxiliary row checks. Whole-process time
also includes imports, matrix declaration, command overhead, audits, and export.

## Final measurements

All eighteen final-source proofs succeeded with only the standard audited axioms.
The exported implementation hashes were checked against the final Windows source.
Medians below are from three fresh runs per case, in seconds:

| Size | Integer certification | Characteristic-zero certification | Cast bridge, included | Integer whole process | Characteristic-zero whole process |
| --- | ---: | ---: | ---: | ---: | ---: |
| 10×10 | 1.573 | 1.484 | 0.031 | 3.301 | 3.257 |
| 50×50 | 4.720 | 5.480 | 0.345 | 6.445 | 9.876 |
| 100×100 | 27.234 | 30.187 | 1.720 | 29.584 | 41.885 |

The observed certification overhead is **16.1% at 50×50 and 10.8% at 100×100**.
The 10×10 difference is within producer/startup variation; it does not establish
a speedup. Integer goals sent to `det_ne_zero` use the integer dispatcher directly.

Whole-process times have a larger difference because ordinary ring-numeral input
is more expensive to declare than the optimized `int_matrix%` integer input.
Median input-declaration times are 0.021 versus 1.941 s at 50×50 and 0.085 versus
8.282 s at 100×100. Thus the 10.8% figure is a certification-time comparison,
not a whole-file runtime claim. The 100×100 characteristic-zero whole-process
samples are 53.008, 41.885, and 41.749 s. The first integer 10×10 run also has a
13.670 s startup/import phase and takes 17.824 s overall; it is retained in the
evidence. Desktop load and startup conditions varied. These are measurements for
the documented mode, not a uniform bound for every ring or arithmetic expression.

At 100×100, median final theorem kernel time is 0.613 s for integers and 1.050 s
for the new tactic; the cast bridge's synchronous kernel check is already inside
the 1.720 s bridge phase and certification time. All emitted `.olean` parts total
3,457,752 versus 15,154,072 bytes, including matrix data and cast auxiliary
declarations. Maximum wait4 process peak RSS is 1,662,001,152 versus 1,723,764,736
bytes. These memory peaks are not synchronized whole-machine totals.

The [summary](evidence/char-zero/summary.json) contains individual samples and
medians; [raw results](evidence/char-zero/results.json), logs, exact input sources,
and [environment and source hashes](evidence/char-zero/environment.json) are
retained alongside it. Certification samples are calculated from each log's
`benchmark tactic returned after ... ms` plus `finalDeclarationKernelMs` in the
corresponding record. Each per-sample sum is formed before taking its median.

Earlier experiments are retained separately in `baseline`, `per-entry`,
`table-conversion`, and `checked-pre-guard` under the evidence directory. Their
samples are not pooled into the final table. Per-entry numeral proofs and repeated
table conversion were replaced by the once-checked table bridge. Keep the
canonical-instance guard: the large custom-numeral regression exposed an expensive
failed conversion in complex numbers before that guard was added.

## Verification

`lake build`, `tests/CharZero.lean`, `tests/Dispatch.lean`, `tests/Triangular.lean`,
`tests/Modular.lean`, `tests/ModularRows.lean`, and `tests/Bridge.lean` pass.
`tests/Sage.lean` also passes through the real Windows/WSL Sage launcher, including
the requested complex example and an abstract characteristic-zero ring.
The Python suite passes eight applicable tests in Sage, with the missing-Sage
diagnostic test skipped. Audited declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The new regression suite covers aliases, local entries and matrices, arithmetic,
list input, empty/singleton/triangular matrices, reversed goals, integer delegation,
the renamed public syntax, rejection of symbolic/fractional entries and singular
certificates, and nonstandard local numeral instances both below and above the
checked-bridge threshold. CI includes the new suite.

## Reproduction

Prepare the pinned native workspace as described in [HANDOFF.md](HANDOFF.md),
including the new `Determinant/Tactic/CharZero` module and downstream imports.
From the Windows project directory:

```powershell
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/generate_dense.py --dimensions 10 50 100 --output .lake/char-zero-tables
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/generate_char_zero.py --input .lake/char-zero-tables --output .lake/char-zero-comparison --dimensions 10 50 100
wsl --distribution SageMath-10.10 --exec /usr/bin/python3 benchmarks/run_linux.py --input .lake/char-zero-comparison --repeats 3
```

The generator records exact source hashes in its manifest; `run_linux.py` checks
them and records implementation hashes, compiler pins, phase times, artifact
sizes, process memory, and axiom reports. Raw evidence for this run is retained in
[evidence/char-zero](evidence/char-zero/results.json).
