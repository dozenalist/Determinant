# Determinant certification roadmap

Public API update: the combined integer tactic described below is now named
`det_ne_zero_int`. The new `det_ne_zero` handles concrete integer-entry matrices
over commutative rings of characteristic zero by a checked integer-cast bridge.
See [the characteristic-zero report](benchmarks/CHAR_ZERO.md). Historical milestone
descriptions and archived evidence retain the original tactic names.
The persistent variants are now `det_ne_zero!` and `det_ne_zero_int!`; their
project-local default directory is `det_ne_zero_witnesses`.

## Objective and delivery order

Build Lean tactics that prove the determinant of an integer square matrix is nonzero, with expensive certificate discovery performed by SageMath or another established exact linear algebra library. Lean must verify the mathematical evidence and produce a proof about the matrix in the original goal.

Deliver the project in this order:

1. A tactic for upper triangular matrices with nonzero diagonal entries.
2. A tactic that obtains a prime modulus `p` and a modular inverse `B` from Sage, then verifies the certificate in Lean.
3. The combined tactic `certify_det_ne_zero`, with measured end-to-end runtimes below one minute for representative dense 100 x 100 matrices and benchmarks at larger sizes.
4. After correctness and performance have been demonstrated, a configurable `certify_det_ne_zero!` that stores `A`, `B`, and `p` in a project-local folder and reuses matching certificates without rerunning Sage.

Milestone 1 is implemented by `certify_det_ne_zero_triangular`; see the status below,
the [README](README.md), and the [reproducible benchmark notes](benchmarks/README.md).
Milestone 2 supplies strict offline modular replay and its verified checkers.
Milestone 3 adds Sage certificate production and the bounded Lean process bridge.
Milestone 4 implements the public combined dispatcher. Persistent replay is
implemented in Milestone 6, following the performance gate below.
The strict native WSL benchmark mode now has three complete 100 x 100 runs
below one minute; see [the performance report](benchmarks/DENSE.md) for its input
representation, configuration, reference hardware and remaining scaling limits.

## Starting point and working rules

The project is pinned to Lean `v4.35.0` and Mathlib `v4.35.0`; the manifest currently resolves Mathlib to commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. At the initial roadmap inspection, `Determinant.lean` contained only the module declaration and the `Determinant/` directory was empty. Milestone 1 has since added `Determinant/Basic.lean` and `Determinant/Tactic/Triangular.lean`.

**Default to existing public libraries rather than implementing the underlying mathematics, linear algebra, arithmetic, serialization, hashing, or database machinery again.** Search the pinned dependencies first. Add a small adapter or missing theorem when necessary; write a new algorithm only after identifying a concrete gap or measured bottleneck. Record the alternatives examined and why they were insufficient.

In particular:

- Reuse Mathlib's determinant, triangularity, ring homomorphism, matrix literal, and arithmetic proof infrastructure.
- Use Sage's public matrix construction and inversion APIs over exact finite fields. Let Sage select an appropriate established backend initially.
- Investigate Sage's FLINT, LinBox/FFLAS-FFPACK, and characteristic-two backends when profiling justifies it; do not write Gaussian elimination or finite field inversion in project Python.
- Use Lean's process and JSON facilities and Python's standard JSON, hashing, filesystem, and optional SQLite libraries where applicable.
- Retain the pinned toolchain while establishing a baseline. A dependency upgrade should have its own reason and validation.
- Keep proof production independent of the external producer so another public library can supply the same certificate format later.

## Mathematical design

### Upper triangular matrices

For an upper triangular integer matrix, the determinant equals the product of its diagonal entries. Since the integers have no zero divisors, nonzero diagonal entries imply a nonzero determinant. This takes only the below-diagonal zero conditions and diagonal nonzero conditions; it does not require evaluating the general determinant formula or constructing the possibly enormous diagonal product.

Prefer the existing `Matrix.IsUpperTriangular.det_ne_zero_iff`. Use `Matrix.det_of_isUpperTriangular` and the existing finite-product nonzero results if an adapter needs a more convenient statement. Make the reusable mathematical result general enough for an integral domain when this requires little additional work, while keeping integer matrices the initial tactic interface.

### A modular inverse certificate

Let `A` be the integer matrix and let `Abar` denote its entrywise image in `ZMod p`. Sage supplies `p` and an integer encoding of a square matrix `B`; Lean interprets the entries of `B` modulo `p`.

The baseline verification obligation is `Abar * B = I`. Only this one-sided inverse equation is needed. Lean need not also verify `B * Abar = I`, compute the integer determinant, or evaluate the determinant of `B`.

The proof has two reusable parts:

1. A right inverse over a nontrivial commutative ring implies that `det Abar` is nonzero. Mathlib already provides `Matrix.det_ne_zero_of_right_inverse`.
2. Determinants commute with ring homomorphisms. Thus, if `det A` were zero, its image `det Abar` would be zero, a contradiction. Reuse `RingHom.map_det` or `Int.cast_det`. The reduction map does not have to be injective.

Sage should search over primes so it can use finite field inversion. However, the proof of this particular certificate only needs `p > 1`, which ensures that `ZMod p` is nontrivial; it does not need primality. Design the core theorem with that weaker hypothesis and keep the producer's prime-search policy separate. If an implementation instead uses field-only lemmas, it must prove primality in Lean using existing tools. A producer's assertion that a number is prime is not a proof.

A successful modulus proves nonvanishing over the integers. A failed modulus proves nothing about integer singularity: a nonzero integer determinant can vanish modulo a prime that divides it. A nonsingular integer matrix has only finitely many such bad primes, but a bounded search is still allowed to end without finding a certificate.

### Checking less than a full inverse equation

After the baseline works, investigate this exact deterministic optimization:

- Check that the entries of `Abar * B` below the diagonal are zero.
- Check that its diagonal entries are all one.
- Leave its entries above the diagonal unchecked.

These facts show that the product is upper triangular with determinant one. By determinant multiplicativity, `det Abar` cannot be zero. This works over any nontrivial commutative ring, including `ZMod p` with merely `p > 1`, and connects the triangular work to the modular checker.

There are `n(n + 1)/2` dot products to check instead of `n^2`, so the classical arithmetic work is roughly halved at large `n`; this remains cubic and is not a promised wall-clock speedup. The checker must avoid constructing the unused product entries to realize the benefit. Give this certificate kind its own soundness theorem and format tag. It proves determinant nonvanishing without claiming the full inverse equation.

Merely checking a nonzero diagonal would be insufficient without the below-diagonal conditions. Over composite moduli, even nonzero diagonal entries of a triangular matrix need not have nonzero product; diagonal entries equal to one avoid that issue. Do not substitute random spot checks, a single matrix-vector equation, or a probabilistic Freivalds test for a deterministic Lean proof.

Other certificate formats, such as verified elimination or permutation/triangular decompositions, can be investigated later using public library support. They must justify their extra proof and format complexity with measurements.

## Existing Lean infrastructure to inspect and reuse

The following names and modules were found in the installed pinned Mathlib source. Inspect their full types and imports before implementing adapters; current online documentation can differ from the pinned release.

| Need | Existing starting points |
| --- | --- |
| Triangular determinant and diagonal criterion | `Mathlib.LinearAlgebra.Matrix.Block`: `Matrix.det_of_isUpperTriangular`, `Matrix.IsUpperTriangular.det_ne_zero_iff` |
| One-sided inverse implies nonzero determinant | `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`: `Matrix.det_ne_zero_of_right_inverse` |
| Determinant after reduction | `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`: `RingHom.map_det`, `Int.cast_det`, `Matrix.det_mul` |
| Nontrivial modular ring and cast facts | `Mathlib.Data.ZMod.Basic`: `ZMod.nontrivial`, modular integer cast results |
| Matrix literal parsing | `Mathlib.Tactic.Matrix.Parsing`: `matchMatrixLit?` |
| List representation and its matrix bridge | `Mathlib.Tactic.Matrix.ListMatrix`, `Mathlib.Tactic.Matrix.OfLists`: `ofLists`, `ofLists_mul` |
| Proof-producing dot products and product expansion | `Mathlib.Tactic.Matrix.MulExpand`: `proveDotProduct`, `proveMul` |
| Existing certificate assembly patterns | `Mathlib.Tactic.Echelon.Cert`: `EntryCertifier` usage, `certifyRowsEq`, `certifyProductEq`, triangular certification |
| Arithmetic proof generation | `norm_num`, its modular congruence extensions, and the entry-certifier pattern in `Mathlib.Tactic.Echelon.Rat` |

The matrix helpers already address literal sharing and the cost of kernel traversal. Some list constructors intentionally pad or truncate input; the certificate parser must nevertheless reject wrong dimensions and ragged rows rather than silently treating malformed data as the intended matrix. Some certificate functions are specialized to a particular decomposition, so reuse their lower-level product helpers without forcing inverse certificates into an unrelated format.

Public pinned sources: [triangular results](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/Block.lean), [matrix product proof construction](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Tactic/Matrix/MulExpand.lean), and [existing echelon certification](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Tactic/Echelon/Cert.lean).

## Proof checking and computation policy

Treat Sage, any replacement producer, the lookup script, the digest, and all files as sources of candidate data. They cannot close a goal by reporting success. Every accepted result must follow from proved mathematical lemmas and verified arithmetic about the current goal matrix.

The default target is proof terms checked through Lean's kernel without new certificate-specific axioms or `sorry`. Untrusted native computation may discover entries, witnesses, or intermediate arithmetic results, but the proof must establish their correctness. A proved Boolean checker also needs a checked proof that it accepted the concrete input; its soundness theorem alone is insufficient.

Do not silently implement the default checker with `native_decide` or `decide +native` and describe it as having the same trust requirements. In the pinned Lean generation, native evaluation introduces generated axioms and extends trust to the compilation/runtime path. If an optional native mode is offered, make it explicit, document its trust requirements, and report its benchmarks separately. See the official [native evaluation API](https://lean-lang.org/doc/api/Lean/Meta/Native.html) and [Lean 4.35.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/).

Audit representative final theorem dependencies using Lean's axiom inspection facilities. The strict mode must not introduce native-evaluation axioms, `sorryAx`, or an external-result axiom. Ordinary Mathlib logical dependencies should be documented rather than confused with trusting Sage.

## Milestone 0: establish interfaces and library reuse

1. Confirm the toolchain and dependency pins and read any applicable repository instructions.
2. Inspect the library entry points above and select the smallest import set. Record missing adapters and avoid reproducing existing lemmas.
3. Fix the initial automated input scope to concrete square matrices indexed by `Fin n` with integer entries and a closed, numerically known dimension. Support literals and reducible definitions first; add other finite index types only through a proved reindexing bridge.
4. Decide how supported goal forms are normalized. Initially handle the determinant-nonzero goal directly; add reversed inequalities or harmless notation variants through small normalization steps.
5. Separate mathematical theorems, matrix extraction, certificate checking, process execution, and cache handling. Importing the library must not launch Sage or mutate the cache.
6. Plan a standalone replay interface accepting explicit certificate data. This gives tests, offline use, and future producers the same checker.

Acceptance: a short interface and reuse note identifies the supported inputs, existing helpers, proof policy, and certificate contract before substantial implementation begins.

## Milestone 1: upper triangular tactic

1. Build the small theorem adapter around the existing triangular determinant criterion, if one is needed at all.
2. Implement a dedicated triangular tactic, with a provisional name such as `certify_det_ne_zero_triangular`.
3. First use available triangularity and diagonal-nonzero hypotheses. This permits useful symbolic cases without external computation.
4. For concrete inputs, prove below-diagonal zeros and diagonal nonvanishing with existing arithmetic tools or reusable proof construction. Do not expand the general determinant or multiply all diagonal entries just to prove the product nonzero.
5. Reuse matrix parsing and shared literals. Keep traversal quadratic in the matrix dimension and avoid repeatedly unfolding the whole matrix for each entry.
6. Return clear failures for missing triangularity or a zero diagonal entry. The combined dispatcher may try the modular route after an unsupported triangular attempt.
7. Cover the empty matrix, whose determinant is one, and 1 x 1 matrices explicitly.

Acceptance: correct examples with positive and negative diagonal entries, a 100 x 100 triangular example, hypothesis-driven symbolic examples, and appropriate failures for zero diagonal or nontriangular inputs. No Sage installation is needed for this milestone.

**Status (2026-11-08): complete.** `Determinant/Basic.lean` provides the integral-domain
adapter and a replay theorem; `Determinant/Tactic/Triangular.lean` implements
`certify_det_ne_zero_triangular`. It uses hypotheses first, then Mathlib's literal
parser, shared list representation, arithmetic certifier, and lower triangular
certificate on the transpose. Matrix extraction and certificate construction
traverse quadratically many entries, without expanding the determinant or
constructing the diagonal product. Normalized entries are connected to the
original matrix by checked equality proofs.

`lake build` and `lake env lean tests/Triangular.lean` pass. The suite includes
empty and singleton matrices, signed/large diagonal entries, symbolic matrices
over integral domains, named/local definitions, arithmetic and hypothesis-proved
zeros, reversed inequalities, a generated 100 x 100 literal, and expected failures.
An automated axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`;
all representative proofs pass it. CI runs the suite.

Fresh, strict end-to-end benchmarks at dimensions 10, 50, 100, 128, and 200 all
pass with 20-bit signed nonzero entries. Three-run median/worst timings are
28.109/28.984 seconds at 100, 41.170/58.953 seconds at 128, and
277.496/310.485 seconds at 200. These include startup, imports, elaboration,
kernel checking, and `.olean` writing. The 200 x 200 cost and large artifacts
remain scaling concerns; individual phases have not yet been profiled.
A 100 x 100 case with 256-bit signed entries also passes all three fresh runs,
with median/worst times of 46.508/73.446 seconds. This illustrates why the entry
size and timing variability must accompany performance claims.
See [the benchmark notes](benchmarks/README.md) for hardware, reproducible commands,
and raw measurements. No Sage or native-evaluation mode is used. These triangular measurements do not
establish Milestone 5's general dense-matrix target.

## Milestone 2: modular theorem and verified checker

1. Prove the small reduction lemma lifting nonzero determinant from the modular image to the integer matrix using determinant naturality.
2. Combine it with the existing right-inverse theorem and the checked hypothesis `p > 1`.
3. Establish the link between the goal matrix and its extracted integer table. A proof about a reconstructed matrix must be transported back using definitional equality or a proved equality; runtime evaluation of the table alone is insufficient.
4. Define a validated certificate data representation with an explicit dimension, modulus, kind, and inverse entries. Reject invalid shape or unsupported kind before attempting arithmetic certification.
5. Start with tiny manually supplied certificates. Reuse the list-based product bridge and proof-producing arithmetic rather than simplifying a large function-valued matrix equality indiscriminately.
6. Compare two strict proof routes: library-driven dot-product proofs with certified arithmetic, and a proved executable checker evaluated by kernel-supported computation. Choose based on measured total checking time and proof size.
7. Normalize large signed integer entries modulo `p` once, with a proved connection to the original entries. Keep modular arithmetic exact and reuse cast/congruence results.
8. Make a clean entry point that checks candidate `p` and `B` against the actual current `A` and returns a proof. It must work equally for fresh, cached, or manually supplied data.
9. Add the reduced unit-upper-triangular-product checker only after the full-product baseline is correct. Prove its separate soundness lemma before using it for performance.

Acceptance: valid small certificates close integer determinant goals; altered entries, incorrect moduli, and mismatched matrices fail. A certificate for one matrix cannot accidentally prove a goal about another. No external producer is required to test the checker.

**Status (2026-11-08): complete.** `Determinant/Modular.lean` lifts determinant
nonvanishing through ring homomorphisms and combines it with Mathlib's right-inverse
theorem for `ZMod p` with a checked `1 < p`. It separately proves the reduced
unit-upper-product criterion over nontrivial commutative rings, including composite
moduli.

`Determinant/Certificate.lean` provides versioned raw data, exact dimension/shape
validation, signed residue normalization bridges, full and reduced executable
checkers, and their soundness theorems. `Determinant/Tactic/Modular.lean` exposes
`proveCertificate` against an actual matrix expression and offline
`certify_det_ne_zero_modular` replay. Every normalization has a checked congruence;
the reconstructed integer matrix must be definitionally equal to the current goal.
The reduced format checks only its diagonal and below-diagonal dot products.
No producer, success assertion, native evaluation, or persistent cache is trusted.

Both strict full proof routes were implemented and compared at dimensions 2, 10
and 20, with three fresh elaborations per route and dimension. Kernel evaluation
is the selected default for its comparable total time and smaller proofs.
`certify_det_ne_zero_modular_arithmetic` retains Mathlib's shared product expansion
with `norm_num` remainder proofs; `certify_det_ne_zero_modular_kernel` explicitly
selects the default. At dimension 20 the full kernel route's median/worst times
are 14.222/15.238 seconds, with 2,073 proof nodes and an 847,880-byte artifact;
the arithmetic route takes 14.885/15.947 seconds, with 60,873 nodes and a
2,732,328-byte artifact. The reduced route has no consistent speedup across these
sizes. These structured, small-matrix timings do not establish the dense 100 x 100
target. See [the modular notes](benchmarks/MODULAR.md) and
[raw measurements](benchmarks/results-modular.json) for the exact scope and variability.

`lake build` and both correctness suites pass. Modular tests include both proof
routes, explicit theorem replay, empty/singleton and dense matrices, composite and
large moduli, signed/large entries, named/local definitions, reversed goals, malformed
shapes and formats, altered witnesses, singular/wrong matrices, bad moduli and safe
backtracking. Axiom audits permit only `propext`, `Classical.choice`, and `Quot.sound`,
including the final replay declarations and checker soundness theorems. CI runs both
suites. All tactic implementations now live in `Determinant/Tactic/`; the triangular
tactic shares its extractor with modular replay. The Milestone 3 producer below
uses the same verification path.

## Milestone 3: Sage certificate producer and Lean process bridge

### Sage/Python work

1. Specify a versioned data-only request and response protocol shared with Lean. Send dimensions and row-major signed integer entries, not Lean source or a string to evaluate.
2. Construct the matrix with Sage's exact integer and finite field APIs. Try configurable prime candidates, reduce the input modulo each candidate, and request an inverse through the public matrix API. Avoid redundant determinant/rank computations when the chosen inverse API already reports singularity.
3. On a singular reduction, try another prime within attempt and time limits. Distinguish unsuccessful prime search from a proven singular integer matrix; no finite list of failed primes establishes singularity here.
4. Return canonical residue representatives for `B`, the chosen `p`, dimensions, certificate kind, and useful producer/version metadata. Keep machine-readable output on stdout and diagnostics on stderr.
5. Optionally verify the product in Sage as an early debugging check, while retaining the independent Lean check as the acceptance criterion.
6. Use a small deterministic prime policy for reproducible tests, with configurable alternatives for difficult matrices. Small primes reduce arithmetic costs but can be bad primes; the default must permit retries.
7. Let Sage select a backend first, then benchmark available alternatives. Its documented [modular matrix interface](https://doc.sagemath.org/html/en/reference/matrices/sage/matrix/matrix_modn_dense_double.html) exposes LinBox/FFLAS-FFPACK operations, and its [FLINT modular matrix interface](https://doc.sagemath.org/html/en/reference/matrices/sage/matrix/matrix_modn_dense_flint.html) is another public starting point. Backend availability and thresholds must be checked against the installed Sage release.

### Lean integration work

1. Extract supported concrete entries once, preserving proofs connecting them to `A`, and serialize them using the agreed protocol.
2. Invoke the configured executable and argument list through a process API. Support native executables and a documented Windows/WSL invocation where Sage requires it; avoid assumptions about shell quoting or path translation.
3. Provide startup errors, nonzero exit diagnostics, timeout/cancellation handling, and bounded response sizes. Terminate work that exceeds the request budget.
4. Parse data with existing JSON facilities. Reject truncated output, malformed integers, incompatible protocol versions, wrong dimensions, and invalid modulus bounds.
5. Pass the candidate to the checker from Milestone 2. Process exit status or a producer's success flag never substitutes for verification.
6. Expose the backend through a small producer interface so a library such as FLINT via a maintained binding can replace Sage without modifying the proof layer.

Acceptance: an end-to-end modular tactic proves a dense nonsingular example, skips an intentionally bad first prime, and fails predictably for missing Sage, singular input, malformed output, or exhaustion of the budget.

**Status (2026-11-08): complete.** `scripts/det_certificate.py` implements the
versioned, data-only JSON protocol in [the producer notes](scripts/PROTOCOL.md).
All matrix entries, inverse entries, moduli and primes use lossless decimal
strings. Sage's exact `matrix`, `ZZ`, `GF`, `change_ring`, `inverse`, primality,
and `next_prime` APIs provide the mathematics; no Python elimination algorithm,
rank test or redundant determinant computation was added. Deterministic preferred
primes and successive-prime fallback obey attempt and wall-clock budgets. A
standard-library supervisor bounds imports and individual inversions, and reports
search exhaustion without asserting integer singularity. Version/backend,
attempted primes and elapsed time are included as diagnostic metadata.

`Determinant/Tactic/Bridge.lean` exposes `CertificateProducer`, `processProducer`,
`proveWithProducer`, and the dedicated `certify_det_ne_zero_sage` tactic. It
extracts the goal matrix once, preserves the original expressions for checked
normalization and final goal equality, and uses Milestone 2's strict replay.
Executable/argument arrays, working directory, prime/attempt/time budgets, both
certificate kinds, output limits and optional traces are configurable. Concurrent
bounded readers and an asynchronous writer avoid pipe deadlocks. Cancellation
propagates; timeout/error cleanup terminates native worker trees. The documented
PowerShell adapter handles the pinned Lean/WSL argument incompatibility, paths
with spaces, and explicit Linux paths. WSL worker cleanup is additionally bounded
by the producer's own supervisor deadline.

`lake build`, the triangular/modular regression suites, `tests/Bridge.lean`, and
the real Sage `tests/Sage.lean` pass. Coverage includes dense bad-prime retry,
empty/singleton and signed/large inputs, named/local definitions, reversed goals,
both kinds, singular/wrong matrices, false success flags, malformed/truncated and
incompatible responses, invalid residues/moduli/shapes, missing executable/Sage,
incorrect arguments, bounded stdout/stderr, blocked stdin, timeout, actual Core
cancellation, native worker-tree cleanup, and Windows/WSL paths with spaces.
The standard-Python and real-Sage producer suites pass in their respective
environments. All audited final Lean declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. CI runs the standard-Python and mock-process
checks; real Sage checks have documented separate commands.

Three fresh strict 2 x 2 declarations, including the deliberately bad first prime,
take 17.734, 15.307 and 18.972 seconds (median 17.734; worst 18.972), each producing
a 110,120-byte `.olean`. These include Lake/Lean startup, imports, all producer
work, kernel checking and artifact writing, with built dependencies and running
WSL. Sage 10.10 selects its FLINT modular backend at the successful modulus 3.
See [reproduction and environment notes](scripts/PROTOCOL.md) and
[raw measurements](benchmarks/results-sage-bridge.json). Internal phase profiling
and large-dimension performance remain unmeasured for this path.

Milestone 4 below adds the combined dispatcher. Large dense-matrix performance
and persistent storage are handled separately by Milestones 5 and 6.

## Milestone 4: combine into certify_det_ne_zero

1. Implement the public dispatcher over the shared theorem and checker interfaces.
2. Normalize the target and try the empty/triangular cases first, reusing available hypotheses and concrete entry proofs.
3. When necessary and supported, extract a concrete integer matrix, call the producer, check its certificate, and lift the modular conclusion to the original goal.
4. Keep ordinary `certify_det_ne_zero` free of persistent project-cache writes. It may use temporary files if the process protocol requires them.
5. Expose practical configuration for producer executable/arguments, preferred primes, attempts, deadline, and trace verbosity. Exact syntax can be chosen during implementation.
6. Emit actionable diagnostics that distinguish unsupported input, failed search, external process failure, and rejected mathematical evidence. Symbolic matrices unsupported by the external path should fail clearly.
7. Keep the final proof self-contained in Lean: once a declaration is compiled, importing it must not require the producer or the original temporary files. Re-elaborating its tactic invocation can require certificate discovery again.

Acceptance: one documented tactic selects the triangular or modular route correctly, and both routes produce proofs satisfying the chosen trust policy.

**Status (2026-11-08): complete.** `Determinant/Tactic/Dispatch.lean` exposes
`certify_det_ne_zero` with optional `ProducerConfig` and the interchangeable
`certifyDetNeZero` entry point. It transactionally tries the existing triangular
tactic, preserving hypothesis-driven integral-domain support, empty/singleton
cases and reversed goals, before the shared bounded producer and strict replay.
Interrupts propagate. Unsupported inputs, process/search errors and rejected
evidence retain their distinct diagnostics. Optional dispatch and phase traces
are available; ordinary success is quiet. There are no persistent cache writes.

`tests/Dispatch.lean` checks route selection with a producer that throws if called
on a triangular input; it also covers dense replay, reversed targets, aliases,
local definitions, list matrices, malformed shapes and failed evidence. The real
Sage suite now exercises the combined tactic, including prime retry and both
certificate kinds. All final declarations pass the strict axiom whitelist.
A compiled real-Sage theorem was imported in a fresh Lean process with the
producer deliberately unavailable; it retains only the ordinary Mathlib axioms.
`tests/ImportSage.lean` supplies the standalone import audit. Build and triangular,
modular, dispatcher, bridge and real-Sage regressions pass.

## Milestone 5: verify and achieve the runtime target

This milestone is a gate before persistent caching becomes the principal development focus. A fast Sage inverse alone does not meet the goal; extraction, proof construction, elaboration, and kernel checking can dominate.

1. Establish a reproducible benchmark environment: processor, memory, OS/WSL setup, Lean/Mathlib pins, Sage version/backend, entry bit sizes, and execution method.
2. Test dimensions 10, 50, 100, and at least two larger sizes, such as 128 and 200. Include dense well-conditioned-for-modular-search examples, sparse/triangular examples, large signed entries, and examples requiring a prime retry. Numerical floating-point conditioning is not an acceptance criterion.
3. Generate reproducible nonsingular benchmark matrices using established library operations, and keep singular and corrupted-certificate cases in the correctness suite.
4. Measure extraction/normalization, serialization, producer startup, prime search/inversion, parsing, proof generation, kernel checking, total wall time, peak memory, and proof/artifact size. Report repeated-run median and worst observed times.
5. Run with built dependencies but include producer startup and all per-goal work in the primary uncached timing. Measure the whole fresh proof declaration, not just tactic evaluation. Document exactly how startup and checking are counted.
6. Profile the strict checker early at increasing dimensions. Share row/column literals and arithmetic facts, avoid repeated entry reduction, and respect the difference between fast native array access and the cost of kernel reduction of arrays/lists.
7. Try the unit-upper-triangular-product optimization and existing entry-certifier helpers before developing custom multiplication or packed arithmetic. Use block proofs or specialized small-modulus representations only if profiling identifies a need and their semantic bridges are proved.
8. If strict checking misses the target, retain the failing measurements and investigate better proof construction or a published certificate scheme. Do not claim success by silently changing the trust policy or excluding kernel time.

Acceptance: representative dense 100 x 100 examples complete in less than 60 seconds end to end on documented reference hardware in the advertised mode, with a scaling report for larger sizes. State the tested dimension and entry-size range; this is not a uniform promise for unbounded dimensions, arbitrary integer bit lengths, symbolic definitions, or every bad-prime search. If a larger size also meets the target, record it explicitly.

**Status (2026-11-08): complete for the documented strict native WSL mode.**
The combined tactic's three fresh signed 20-bit dense 100 x 100 declarations take
53.965, 48.003, and 45.426 seconds: median **48.003**, worst **53.965**. Timings
include fresh Lean/import and Sage startup, extraction, serialization, candidate
search, parsing, normalization, all kernel checking, axiom audit and artifact
writing. Built dependencies and input generation are outside the interval.
The mode uses the exact pinned Linux Lean release and Sage natively on WSL's
native filesystem, module-interface imports, a `public noncomputable def` matrix
through lossless JSON `int_matrix%`, and `kind := "unit-upper-product"`.
The reference machine is the documented Intel Core Ultra 7 256V / 16 GB host,
with about 8 GB available to WSL. This is an advertised measured mode, not a
universal guarantee for arbitrary input notation, sizes, bit lengths or search.

Dense dimensions 10 and 50 have three fresh samples (median/worst 3.162/13.455 s
and 6.318/7.390 s). The two 128 x 128 samples take 94.536/95.018 s; one successful
200 x 200 sample takes 384.988 s. Neither larger size meets a minute; no repeated
median is claimed at 200. An additional 100 x 100 bad-prime retry passes in
49.788 s, and a signed 256-bit 100 x 100 example passes in 48.319 s, each measured
once. Triangular inputs take 1.829 s at 50 and 2.782 s at 100 without a producer.
The full inverse checker is also retained and measured (13.007 s at 50).

Profiling justified compact literals, one checked normalization bridge, a shared
proved transpose, natural residue arithmetic using public list operations, and
synchronous checked row lemmas that bound reduction-cache memory. Reflexivity
proofs require kernel reduction of every required condition; compiled preflight
computation only rejects data. No native-evaluation axiom or weakened proof mode
was introduced. All audited proofs retain only `propext`, `Classical.choice`,
and `Quot.sound`. The compiled 100 x 100 theorem imports in a fresh process with
the producer deliberately unavailable. Build, triangular/modular/row/dispatcher,
process and real-Sage suites pass, including the POSIX missing-executable case.

See [DENSE.md](benchmarks/DENSE.md), [raw evidence](benchmarks/evidence/dense/results.json),
and [the detailed handoff](benchmarks/HANDOFF.md) for hardware, exact commands,
phase times, memory, source hashes, proof/artifact sizes, slow/failed baselines,
scaling limits and concrete future optimization instructions. The final 50 x 50
phase table gives median/worst measurements of every measured step. At 200,
row kernel proofs consume 349.167 s versus 1.439 s in producer transport; kernel
arithmetic remains the next scaling bottleneck. The next project milestone is
the persistent tactic in Milestone 6. An optional second 200 x 200 repeat was
stopped to respect the requested work window; it is not counted as a sample.

## Milestone 6: configurable persistent det_ne_zero!

Implement persistence after the combined tactic is correct and the performance evidence above exists. Reuse the same verification path; the exclamation mark introduces certificate storage and reuse, not weaker mathematical checking.

### Storage and lookup contract

Use a configurable directory under the local project root. The implemented default,
requested by the user, is `det_ne_zero_witnesses/` (replacing the earlier proposed
`.determinant-certificates/`). Resolve the project root consistently rather than
using whichever directory launched the editor. Document whether certificates
should be committed or ignored; do not mix user certificates into the dependency
build cache.

Each modular certificate entry must contain the full integer matrix `A`, the modular inverse representative matrix `B`, and `p`, together with dimension, format version, and certificate kind. Include backend/version provenance and optional timing information as metadata. Do not store only a source expression, a matrix name, a digest, or `A mod p` in place of the requested `A`.

Define one canonical encoding of the dimension and full row-major integer matrix. Specify signed decimal normalization, delimiters or length framing, encoding, and format version. Encode arbitrary-precision matrix entries and modulus as decimal strings in JSON, or use another existing lossless format; do not route them through floating-point JSON consumers. Separate the matrix identity format from producer metadata so a Sage version change need not invalidate a still-checkable certificate.

Use a standard cryptographic digest such as SHA-256 of the canonical matrix encoding as the lookup key. A content-addressed path, optionally sharded by digest prefix, is sufficient for the initial lookup table; do not linearly scan every stored matrix. Reuse a public hashing implementation or Python's standard `hashlib`. Hashing still reads the current matrix and is linear in its encoded size.

If a lookup helper is useful, make it a lightweight standard-Python script with no Sage import. For larger collections, SQLite is an optional established index. An index is only an accelerator: the stored certificate and the actual matrix remain authoritative, and a missing index should be recoverable.

### Runtime behavior

1. Apply the cheap empty/triangular route first. A direct triangular proof needs no fabricated `B` or `p`; document that certificate persistence applies when the modular route is used.
2. Extract and canonicalize the current `A`, compute the key, and look for a compatible candidate before starting Sage.
3. On a hit, compare the stored dimension and complete integer matrix with the current canonical table. Treat the digest as a lookup aid, never as a mathematical equality proof.
4. Check the candidate's arithmetic against the actual goal matrix with the shared Lean checker and rebuild the proof. A hit must avoid all Sage startup and inversion, while still doing proof checking.
5. On a miss, call the producer, verify its output, and atomically persist the successful `A`, `B`, and `p` record. Stage it in the same directory and use an existing atomic replacement facility where supported; handle concurrent elaborations without partial entries.
6. Reject corrupted or mismatched entries. Depending on cache policy, either report the problem or recompute; cache-only mode must never launch Sage. Do not silently treat failure as successful verification or delete unrelated entries.
7. Check on every replay. A schema migration, stale producer, or tampered file must not be able to bypass the proof.
8. Provide a way to inspect/export certificates and replay them in a fresh environment with the checker alone. Report cache hit/miss and producer invocation through optional traces without cluttering normal proof output.

### Configuration to provide

| Setting | Required behavior |
| --- | --- |
| Cache directory | Project-local default and an explicit override |
| Policy | Read/write; read-only with fresh computation allowed; cache-only with no external computation; disabled |
| Refresh | Explicit recomputation of an existing candidate, subject to the normal checker |
| Producer | Executable, argument list, backend selection where supported, and environment/path handling |
| Search budget | Preferred primes, maximum attempts, and a total time budget |
| Certificate kind | Full inverse check or a supported proved optimization |
| Proof mode | Strict checking by default; any native mode explicitly distinguished |
| Diagnostics | Quiet default, with lookup, producer, and verification timings available |

Specify precedence among per-invocation settings and project defaults. Keep producer-specific settings out of matrix identity keys unless they change certificate compatibility.

Acceptance: the first modular run creates a complete checked record. A second fresh elaboration of the same goal succeeds with Sage unavailable and shows no producer invocation. Changing one entry of `A` creates a miss; corrupting `B` or `p` fails verification. A growing cache does not cause lookup to scan all entries, and large integer entries survive serialization exactly.

**Status (2026-11-08): complete.** `Determinant/Tactic/Cache.lean` implements
`det_ne_zero!` and `det_ne_zero_int!` around the existing dispatcher and strict
checker. `CacheConfig` extends producer settings with a project-local directory,
read/write, read-only, cache-only and disabled policies, and refresh. The directory
option `determinant.witnessDirectory` supplies project defaults; an explicit
per-invocation directory takes precedence. Root discovery starts at the current
Lean source's nearest Lake project, independently of producer working directory.
The default is `det_ne_zero_witnesses/`; no other witness directories are searched.

`scripts/cache_lookup.py` uses standard Python SHA-256 and an exact filename,
without Sage or a directory scan. Versioned lossless JSON stores full A, B, p,
dimension, kind, and the complete producer response with provenance. Both lookup
and Lean compare full A; every replay proves the certificate against the actual
goal. Successful new proofs are kernel checked before same-directory staging and
atomic replacement. Corruption can trigger a fresh verified attempt, except in
cache-only mode. Triangular proofs keep their fast path and create no record.
Plain JSON inspection and a `--export` command support standalone offline replay.
Selected witness files are intended to be committed unless the user opts to ignore
the folder.

Native Windows `lake build` and the full WSL correctness/Sage regression suite pass.
Cache tests cover fresh-process replay with no producer, directory/policy/refresh
behavior, altered A/B/p, format corruption, failed writes, concurrency, orphan
staging files, paths containing spaces, confinement, and 5000-digit integers.
Importing a compiled cached theorem and replaying an exported `RawCertificate`
also pass with Python and Sage unavailable. Axiom audits retain only the ordinary
Mathlib dependencies `propext`, `Classical.choice`, and `Quot.sound`.

Three fresh strict 100×100 runs per mode have median/worst end-to-end seconds
29.629/29.888 ordinary, 29.058/29.392 on a miss, and 26.103/26.775 on a hit.
Measured cache-only work on a miss totals about 0.92 seconds; total variation is
dominated by kernel checking. One 128×128 run per mode takes 55.978, 57.866, and
55.270 seconds respectively. All hits invoke zero producers. See
[the cache report](benchmarks/CACHE.md) for phase timings, memory, raw logs,
configuration, witness samples, and reproducible commands. Kernel arithmetic
remains the scaling bottleneck; persistence avoids discovery rather than proof
checking.

## Suggested implementation boundaries

The mathematical and tactic modules, Sage producer, process bridge, combined
dispatcher, persistent cache, correctness suites, and benchmark drivers are
implemented. Merge small modules when that improves clarity.

| Proposed area | Responsibility |
| --- | --- |
| `Determinant/Basic.lean` | Small public theorem adapters and shared mathematical interface |
| `Determinant/Tactic/Triangular.lean` | Upper triangular proof automation |
| `Determinant/Modular.lean` | Reduction theorem and soundness of supported certificate kinds |
| `Determinant/Certificate.lean` | Validated data, list bridges, executable checkers and their soundness |
| `Determinant/NatCertificate.lean` | Specialized natural residue checker and proved cast/transpose bridge |
| `Determinant/Tactic/Matrix.lean` | Shared integer matrix extraction |
| `Determinant/Tactic/Literal.lean` | Fast signed integer table quotation through Mathlib's `ofLists` |
| `Determinant/Tactic/Modular.lean` | Candidate replay, normalization and strict proof construction |
| `Determinant/Tactic/Bridge.lean` | Extraction, serialization, producer protocol, and process lifecycle |
| `Determinant/Tactic/Cache.lean` | Canonical matrix identity, lookup, storage, and policies |
| `Determinant/Tactic/Dispatch.lean` | Public uncached dispatcher, triangular-first selection and diagnostics |
| `Determinant/Tactic.lean` | Public tactic imports, including persistent variants |
| `scripts/det_certificate.py` | Thin Sage adapter using public matrix APIs |
| `scripts/cache_lookup.py`, if needed | Lightweight lookup using standard libraries without Sage |
| `tests/` and `benchmarks/` | Correctness fixtures, process/cache integration cases, and repeatable timing |
| `Determinant.lean` and `README.md` | Public imports and user documentation after implementation |

## Validation and handoff requirements

Future agents should complete and document each milestone before moving to the next, with the cache following the uncached performance gate. Leave enough evidence for the next agent to reproduce the result:

- Mathematical coverage: empty and 1 x 1 matrices, upper triangular matrices, negative/large entries, nonsingular dense matrices, duplicate rows, zero rows, and bad-prime retries.
- Certificate rejection: an altered relevant `B` entry, a wrong matrix, wrong dimensions, invalid modulus such as one, malformed/truncated data, and incompatible kind/version. For the optimized checker, test a failed checked condition; some changes may legitimately preserve the weaker certificate.
- Trust coverage: inspect axioms of the final declarations, establish the table-to-goal link, and demonstrate that a producer or cache success flag alone cannot prove anything.
- Process coverage: missing executable, incorrect arguments, timeout, cancellation, stderr diagnostics, and Windows paths containing spaces.
- Cache coverage: hit, miss, fresh elaboration with no Sage, one-entry changes to `A`, incomplete writes, concurrent access, policy behavior, format migration, and lossless integers beyond ordinary machine/JSON floating-point precision.
- Performance coverage: uncached and cached replay separately, strict and optional native modes separately, end-to-end timings and memory, and explicit results at 100 x 100 and larger sizes.
- Reproducibility: build using the existing Lake project, document the Sage environment, and force actual tactic re-elaboration during cache tests. Reusing an up-to-date `.olean` does not test the certificate lookup path.

At each handoff, state what is implemented, which library pieces were reused, which acceptance checks passed, actual measured timings, remaining bottlenecks, and the next concrete milestone. Do not report the complete project as finished until the combined tactic, documented performance target, and persistent replay behavior have all been demonstrated.
