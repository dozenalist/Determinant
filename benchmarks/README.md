# Upper triangular certification

For the persistent `det_ne_zero!` tactic, configuration and measured cache overhead
are documented in [CACHE.md](CACHE.md). The material below records the triangular
baseline.

The initial automatic interface is `A.det ≠ 0` or `0 ≠ A.det` for square integer
matrix literals indexed by a closed `Fin n`, including named/let-bound literals.
The hypothesis path supports arbitrary finite ordered index types and integral
domains. It runs before inspecting the matrix, so symbolic dimensions are allowed.

`Determinant/Basic.lean` contains the public theorem adapter and the explicit replay
interface `det_ne_zero_of_transpose_certificate`. The certificate consists of the
original list of rows, a candidate transpose, a proved equality connecting the
transpose to those rows, and Mathlib's `IsLowerTriangularDiagList` certificate.
No external process or cache participates in this milestone.

Library reuse:

- `Matrix.IsUpperTriangular.det_ne_zero_iff` and its lower triangular counterpart
  supply the determinant argument over integral domains.
- `matchMatrixLit?` parses and validates dimensions once; `ListMatrixLit` and
  `ofLists` share row literals and give the definitional bridge to the goal.
- `certifyLowerTriangularDiagList` checks the transpose. Its row suffix checks,
  together with `ListMatrix.transpose` and `ofLists_transpose`, avoid repeatedly
  evaluating the original matrix at individual indices.
- `EntryCertifier`, `normNumCertifier`, and `mkListCongr` supply arithmetic proofs
  and the bridge when a below-diagonal expression needs normalization to zero.

The existing certifier directly handles the transpose; an additional upper
triangular reflection predicate or a new matrix algorithm was unnecessary.
Per-entry matrix-function simplification would repeatedly unfold nested vector
lookups, so the implementation instead parses once and checks shared row lists.
Parsing, normalization, transposition, and certificate construction traverse at
most quadratically many entries. Kernel conversion and general arithmetic proof
costs depend on representation and entry complexity; this is not a universal
quadratic wall-clock guarantee.

The replay theorem requires mathematical evidence, not a success Boolean.
The final proof's type is checked against the original goal matrix. All arithmetic
and transpose equations are checked by the kernel; no `native_decide`, generated
native-evaluation axioms, `sorry`, or external-result axiom is used.

Run `lake build`, then `lake env lean tests/Triangular.lean`. The suite includes
positive/negative/large diagonal entries, empty and singleton matrices, arithmetic
zeros, named and let-bound definitions, symbolic entries and hypotheses, reversed
goals, and rejection of zero-diagonal, nontriangular, and unsupported goals.
It prints representative theorem axiom dependencies, including the 100×100 proof.

`Run-Triangular.ps1` produces deterministic dense upper triangular literals with
alternating-sign nonzero diagonals. Defaults: dimensions 10, 50, 100, 128, 200;
20-bit nonzero entry magnitudes; three repetitions. Entries below the diagonal
are zero. `-EntryBits 256` exercises large signed integers. Generated sources and
results are kept under the ignored `.lake` directory.

Timing starts immediately before `lake env lean -o ... source.lean` and ends
after the process returns. Thus it includes Lake/Lean startup, imports, literal
elaboration, tactic proof generation, kernel checking, axiom printing, and artifact
writing. Each repetition elaborates source afresh, with dependencies already built.
Matrix source generation and the initial library build are outside the timing.
The script does not measure peak process memory or separate internal phases.

Reference environment (2026-11-08): Intel Core Ultra 7 256V, x86-64 Windows
NT 10.0.26300.0, Lean 4.35.0 release build (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`),
Mathlib 4.35.0 (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`).
Measurements use the ordinary desktop workspace without CPU isolation. Total RAM
and peak process memory were not collected. All audited proofs depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

Three fresh elaborations per case, using the final implementation:

| Dimension | Entry magnitude bits | Median seconds | Worst seconds | `.olean` MiB |
| --- | --- | --- | --- | --- |
| 10 | 20 | 27.452 | 29.630 | 0.35 |
| 50 | 20 | 19.048 | 20.982 | 5.82 |
| 100 | 20 | 28.109 | 28.984 | 20.47 |
| 100 | 256 | 46.508 | 73.446 | 21.05 |
| 128 | 20 | 41.170 | 58.953 | 31.88 |
| 200 | 20 | 277.496 | 310.485 | 73.65 |

The complete samples, source sizes, artifact sizes, and axiom reports are in
[results-triangular-20bit.json](results-triangular-20bit.json) and
[results-triangular-256bit.json](results-triangular-256bit.json). Every run passed.
The 20-bit 100×100 and 128×128 triangular cases completed within one minute in all
three repetitions. The 256-bit 100×100 case exceeded a minute in one repetition.
The 200×200 case is supported but is substantially slower, and
artifact size also grows considerably. Larger-case elaboration and kernel
conversion need profiling before claiming better scaling. Internal phases have
not been timed separately, so these measurements do not isolate a single cause.
These results do not establish the future runtime target for general dense
matrices or the modular checker.

Possible improvements: profile proof construction, elaboration/conversion, and
kernel checking separately; avoid constructing row-congruence proofs when all
normalized zeros are definitionally equal to the originals; investigate further
sharing of certificate terms and literals. Extend extraction to alias chains and
additional concrete matrix representations after measuring their conversion cost.
These are follow-ups, not required for the completed Milestone 1 acceptance cases.
