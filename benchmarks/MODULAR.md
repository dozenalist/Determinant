# Modular replay interface and reuse

Milestone 2 accepts closed square integer literals indexed by `Fin n`, including
definitions reducible to literals, and direct or reversed determinant inequalities.
The standalone replay API accepts versioned data with dimension, modulus, kind tag
and a rectangular integer table. It rejects unsupported metadata and incorrect
dimensions before arithmetic. No external process or persistent storage is involved.

The mathematical modules are `Determinant/Modular.lean` and
`Determinant/Certificate.lean`. Every project tactic lives under `Determinant/Tactic/`;
`Determinant/Tactic.lean` is the public import aggregator. The shared extractor is
`Tactic/Matrix.lean`, and `Tactic/Modular.lean` exposes `proveCertificate A raw route`.
It returns a proof about the supplied expression `A`, so producer discovery and cache
lookup can later supply data without changing the proof layer.

## Data contract and normalization

`RawCertificate` has `version` (default 1), `dimension`, `modulus`, `kind` (default
`"full-inverse"`), and `inverse : List (List Int)`. The other supported kind is
`"unit-upper-product"`. Unsupported versions/kinds, wrong dimensions, modulus zero
or one, wrong row counts, ragged rows, and excess columns are rejected before matrix
arithmetic. `RawCertificate.validate expectedDimension` returns an `Except` containing
a `Certificate` with proofs of its modulus bound and exact rectangular shape.
There is no JSON/process protocol at this milestone; that belongs to Milestone 3.

The goal matrix is parsed once with Mathlib's `matchMatrixLit?` and reconstructed
with `ListMatrixLit` / `ofLists`. The final proof type must be definitionally equal
to the actual matrix determinant goal. Parsing does not make an asserted equality.

Original signed entries are reduced once to canonical integer residues. Every
normalization has a `norm_num` proof that the original expression modulo `p` equals
the proposed residue, assembled with `mkListCongr`. `map_residueRows` then uses
`ZMod.intCast_mod` to transport the certificate back to the original integer table.
Inverse entries are reduced as untrusted witness data; the normalized witness is
checked independently against the current matrix. No statement about a caller's
proof term or a producer's success flag is accepted as evidence.

## Library reuse and proof routes

The proof uses `Matrix.det_ne_zero_of_right_inverse`, `RingHom.map_det`,
`ZMod.nontrivial`, `ZMod.intCast_mod`, `Matrix.map_mul`, and `ofLists_mul`.
A modulus needs only be greater than one. The unit-upper-product proof also uses
`Matrix.det_of_isUpperTriangular` and `Matrix.det_mul`, over nontrivial commutative
rings. It requires diagonal ones, avoiding the zero-divisor problem of a merely
nonzero diagonal over composite moduli.

The full arithmetic route reuses `proveMul`, `proveDotProduct` (through `proveMul`),
and `mkListCongr`. It proves exact integer dot products modulo `p` with Mathlib's
`normNumCertifier`. Rows and columns are shared by the library helpers. Performing
the arithmetic over integers allows reuse of `norm_num`'s integer remainder proofs;
there is no custom multiplication, elimination, modular inversion or primality test.
`certifyProductEq` was inspected, but its equality certifier checks equality in the
coefficient ring. Here integer products need only agree modulo `p`, so the small
`modular_right_inverse_of_lists` adapter connects the existing integer product bridge
to modular equality instead. The echelon decomposition assembler is not used because
an inverse certificate is not an echelon decomposition.

The alternative full route uses `checkFull`, a proved executable list checker.
Its concrete acceptance is proved by ordinary kernel reduction. Before constructing
the proof, `checkedDecide` also reduces the decision using `Kernel.whnf` and rejects
false results. This is necessary because `mkDecideProof` alone constructs a proof
candidate without checking its reduction; otherwise rejection could be deferred
until the enclosing declaration's kernel check and break tactic backtracking.

The reduced `checkUnitUpper` has its own `checkUnitUpper_sound` theorem. On success
it checks `n(n+1)/2` dot products, testing `j ≤ i` before evaluating a dot product.
No above-diagonal product entry or full product is built. It currently uses the
kernel route with either tactic spelling. Its quantified index checks and list
lookups can offset the saved dot products; a speedup is not assumed.

`certify_det_ne_zero_modular` defaults to the executable kernel route;
`certify_det_ne_zero_modular_kernel` is its explicit spelling. The arithmetic route
is available as `certify_det_ne_zero_modular_arithmetic`. `proveCertificate` accepts
the corresponding `.kernel` or `.arithmetic` argument and defaults to `.kernel`.

Both strict routes produce ordinary proof terms. Candidate terms are evaluated as
untrusted data with `Term.evalTerm`; arithmetic correctness still requires checked
proofs. No `native_decide`, `decide +native`, new axioms, Sage, subprocess or persistent
cache is used. The suite audits representative final theorem dependencies and both
checker soundness theorems, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
It also demonstrates direct theorem-level replay without the tactic evaluator.

## Measurements

Run `lake build`, then `./benchmarks/Run-Modular.ps1` (or use the process-local
PowerShell execution policy shown in the main README). This regenerates small dense
`A = I + J` examples and certificates `B = I - (n+1)⁻¹ J` modulo 101. Witness discovery
uses .NET's standard `BigInteger.ModPow`; Lean still checks the candidate products.
Entries of `A` are 1 or 2; entries of `B` are residues in `[0, 100]`. This is a
deterministic checker comparison, not representative general-matrix discovery.

Each timing includes fresh Lake/Lean startup, imports, elaboration, data evaluation,
normalization, proof construction, kernel checking, axiom audit and `.olean` writing.
Dependencies and matrix/certificate source generation are outside the timer. Artifact
sizes include the source's matrix and certificate definitions. Proof node counts
use Lean's `Expr.numObjs` on the theorem value (distinct allocated expression nodes,
excluding imported theorem bodies). Internal phases and peak memory are not measured.

Reference environment (2026-11-08): Intel Core Ultra 7 256V, x86-64 Windows
NT 10.0.26300.0, Lean 4.35.0 release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Mathlib 4.35.0 commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The existing Elan installation was
selected with `ELAN_HOME` in this restricted shell. No CPU isolation; total RAM
and peak process memory were not collected. All 27 fresh elaborations passed,
with only the three allowed logical axioms.

Three runs per route and dimension; complete samples are in
[results-modular.json](results-modular.json):

| Dimension | Route | Median seconds | Worst seconds | Proof nodes | `.olean` bytes |
| --- | --- | --- | --- | --- | --- |
| 2 | arithmetic | 30.401 | 31.146 | 802 | 84,576 |
| 2 | kernel full | 26.132 | 31.081 | 281 | 65,464 |
| 2 | kernel reduced | 27.864 | 28.706 | 281 | 65,480 |
| 10 | arithmetic | 31.181 | 32.411 | 11,823 | 641,352 |
| 10 | kernel full | 30.788 | 32.721 | 798 | 285,944 |
| 10 | kernel reduced | 33.078 | 34.382 | 798 | 285,960 |
| 20 | arithmetic | 14.885 | 15.947 | 60,873 | 2,732,328 |
| 20 | kernel full | 14.222 | 15.238 | 2,073 | 847,880 |
| 20 | kernel reduced | 13.937 | 14.086 | 2,073 | 847,896 |

Decision: use the strict full kernel checker by default. It has comparable total
time and much smaller proofs: at dimension 20 the arithmetic route allocates about
29 times as many proof expression nodes and produces about 3.2 times the serialized
artifact size. Retain the library-driven arithmetic route for comparison, entry-level
diagnostics, and future scaling investigations. The reduced checker has no consistent
measured timing advantage yet; retain its separate explicit format.

The dimension-20 samples ran later and were substantially faster than dimension 10.
Timing noise and environment state prevent drawing a scaling curve from these small
totals, and phases have not been isolated. The highly structured `I + J` family can
also share repeated proof expressions more than general dense inputs. These results
do not establish Milestone 5's general dense 100×100 target.

## Verification and next work

`lake build`, `lake env lean tests/Triangular.lean`, and
`lake env lean tests/Modular.lean` verify the library and correctness suites. Modular
tests cover both full proof routes, explicit theorem-level replay, empty/singleton
and dense matrices, named/local definitions, reversed goals, composite and large
moduli, negative and large entries, invalid metadata/shape, singular or mismatched
matrices, corrupted witnesses, bad moduli, and tactic backtracking. Reduced tests
separate failed below-diagonal and diagonal conditions from unchecked upper entries.

Next is Milestone 3: the versioned lossless process protocol, Sage producer, and
bounded process bridge feeding the existing checker. Larger random dense matrices,
phase profiling, proof sharing and kernel list traversal remain performance work.
