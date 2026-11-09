# Determinant

A Lean library depending on Mathlib, pinned to Lean and Mathlib `v4.35.0`.

Use `det_ne_zero` for concrete integer-entry matrices over a commutative ring
of characteristic zero (including `ℚ`, `ℝ`, and `ℂ`):

```lean
import Determinant
import Mathlib.Basic.Complex.Basic

example : (!![2, 3; 1, 4] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
  det_ne_zero
```

It proves a structural integer-cast equality, certifies the corresponding integer
matrix with `det_ne_zero_int`, and transports
nonvanishing using the injective integer cast. No `IsDomain R` assumption is needed.
Both tactics accept the same optional `ProducerConfig`; dense examples need Sage
as described below. On integer goals `det_ne_zero` directly calls `det_ne_zero_int`.
Literals, exact square `ofLists` inputs, aliases, local definitions, signed numerals,
and closed arithmetic that `norm_num` recognizes as an integer are supported.
Both orientations of the nonzero goal are accepted. Symbolic entries and fractional
entries that do not normalize to an integer are rejected.
The paired timing comparison is recorded in [benchmarks/CHAR_ZERO.md](../benchmarks/CHAR_ZERO.md).

Use `det_ne_zero!` to save and reuse modular witnesses:

```lean
example : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { directory := "det_ne_zero_witnesses" }

-- Re-elaboration uses the saved witness without starting Sage.
example : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { policy := .cacheOnly }
```

The default folder is `det_ne_zero_witnesses` at the local Lake project root.
`CacheConfig` extends `ProducerConfig`, adding directory, policy, refresh, and
lightweight Python lookup settings. `set_option determinant.witnessDirectory
"proof-data/witnesses"` sets a project default; an explicit `directory` overrides
it. Only that project-local directory is searched. Files use dimension and SHA-256
of the complete canonical integer matrix for direct lookup, and contain full
`A`, `B`, `p`, and producer metadata. Every replay is checked against the actual
goal by Lean. The triangular fast path creates no modular witness.
`det_ne_zero_int!` provides the corresponding integer-only tactic.
See [cache configuration, format, and export](../scripts/CACHE.md) and
[performance measurements](../benchmarks/CACHE.md).

The public `det_ne_zero_int` tactic tries triangular certification, then Sage
discovery and strict modular replay. It does not write a persistent certificate cache.
All tactic implementations live in [`Determinant/Tactic`](../Determinant/Tactic).
Import `Determinant` for the combined tactic, or `Determinant.Tactic.Triangular`,
`Determinant.Tactic.Modular`, or `Determinant.Tactic.Bridge` individually.

```lean
import Determinant

example : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero_int { preferredPrimes := [2, 3, 5], kind := "unit-upper-product" }
```

The optional term has type `Determinant.Tactic.ProducerConfig`. It controls the
executable, separate argument array, working directory, primes, attempt/deadline
budgets, certificate kind, and stream limits. Per-invocation fields override its
defaults. Configuration and Windows/WSL examples are in
[the producer notes](../scripts/PROTOCOL.md). Triangular and hypothesis-driven goals
succeed without launching the configured executable. Unsupported symbolic entries
fail before external discovery.

For large tables, `int_matrix%` quotes signed integer numerals directly into
Mathlib's list representation, avoiding per-entry typeclass elaboration:

```lean
noncomputable def A := int_matrix% [[2, 1], [2, 2]]

example : A.det ≠ 0 := by det_ne_zero_int
```

For generated large tables, the equivalent lossless JSON spelling is
`int_matrix% r#"[["2","1"],["2","2"]]"#`. Entries must be canonical decimal
strings. `noncomputable def` avoids generating native executable code for matrix
data used only in a proof; kernel checking of the data and theorem still occurs.

Ordinary `Mathlib.Tactic.Matrix.ofLists 2 2 [[2, 1], [2, 2]]` is also supported,
including Lean's balanced let bindings in long list notation. The tactic requires exact square
row lengths, follows reducible aliases and local definitions, and checks its proof
against the original matrix. The list constructor's padding/truncation behavior
does not relax the accepted input shape.

Use `certify_det_ne_zero_triangular` for upper triangular matrices:

```lean
import Determinant

example : (!![-2, 17, -31; 0, 5, 9; 0, 0, -7] :
    Matrix (Fin 3) (Fin 3) ℤ).det ≠ 0 := by
  certify_det_ne_zero_triangular
```

The tactic first uses local upper triangularity and diagonal-nonzero hypotheses.
This works for symbolic matrices over any integral domain with a finite ordered
index type. Otherwise it checks square integer matrix literals (`!![...]`) and
definitions that unfold to literals, with a numerically known `Fin n` dimension.
It accepts `A.det ≠ 0` and `0 ≠ A.det`, including empty and singleton matrices.
Entries above the diagonal may be symbolic. Relevant entries can be arithmetic
expressions or have individual equality/nonzero hypotheses. A zero diagonal or
an unproved below-diagonal zero produces an error identifying its coordinates.
Function-defined matrices that do not unfold to literals need the two hypotheses.

```lean
example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (htri : A.IsUpperTriangular) (hdiag : ∀ i, A i i ≠ 0) : A.det ≠ 0 := by
  certify_det_ne_zero_triangular
```

Every result is a kernel-checked proof using Mathlib's triangular determinant
criterion. The tactic neither expands the determinant nor constructs the diagonal
product. It uses no Sage, native evaluation, external certificates, or persistent
cache.

For a general concrete integer matrix, replay an explicit modular certificate:

```lean
example : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular {
    dimension := 2
    modulus := 5
    inverse := [[2, 2], [4, 2]] }
```

The data type is `Determinant.RawCertificate`. Its default `version` is `1` and
default `kind` is `"full-inverse"`. The checker validates metadata, exact square
dimensions and `modulus > 1`, proves congruences for the original signed entries,
and checks that the modular product is the identity. Candidate entries may be
negative or arbitrarily large. It accepts the same concrete literal/definition
and reversed-goal forms as the triangular checker; modular entries must be closed
integer arithmetic. A named `RawCertificate` can be supplied instead of a literal.

`kind := "unit-upper-product"` checks only below-diagonal zeros and diagonal ones
in the product. It has a separate soundness theorem and does not assert a full
inverse equation. Both kinds work with composite moduli. A failed modulus says
nothing about integer singularity.

`certify_det_ne_zero_modular` uses the proved executable checker evaluated by Lean's
kernel. The current checker specializes normalized residues to natural literals,
uses a fused dot product proved equal to the library zip/fold specification,
and shares a proved explicit transpose. A compiled preflight rejects bad data;
the acceptance proof is reflexivity of the concrete Boolean checker. The kernel
must reduce it to `true`. For dimensions above 16 this happens in checked row
lemmas, keeping each reduction cache bounded. The preflight adds no axiom or
trust requirement. `certify_det_ne_zero_modular_kernel`
is an explicit spelling of this route. `certify_det_ne_zero_modular_arithmetic`
retains Mathlib's shared dot-product expansion and proof-producing integer
arithmetic for full inverse certificates. The reduced kind currently uses kernel
evaluation with every spelling. None is a native-evaluation mode. The public
`Determinant.Tactic.proveCertificate` entry point accepts candidate data against
an actual goal matrix, independently of its future producer or storage location.
`checkFull_sound` and `checkUnitUpper_sound` also support theorem-level replay.
`Determinant.checkNat_sound` proves the specialized checker's bridge.

Theorems and data/checker definitions live in `Determinant.Basic`,
`Determinant.Modular`, and `Determinant.Certificate`. Importing these modules or
the tactic modules never launches a process or writes a cache. Persistent replay
is implemented by `det_ne_zero!`; see Milestone 6 in [ROADMAP.md](../ROADMAP.md).

With Sage available to `python3`, discover and strictly check a certificate:

```lean
example : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_sage { preferredPrimes := [2, 3, 5], maxAttempts := 8 }
```

The first prime is intentionally bad; Sage retries at 3. The dedicated tactic
supports executable/argument arrays, working directory, prime/attempt budgets,
timeouts, response limits, and optional diagnostics. All candidates pass through
the existing kernel checker. See [the producer protocol and setup](../scripts/PROTOCOL.md)
for configuration, Windows/WSL instructions, process cleanup semantics, and tests.

Build and run the correctness suite, including a generated 100×100 literal:

```powershell
lake build
lake env lean tests/Triangular.lean
lake env lean tests/Modular.lean
python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean tests/Bridge.lean
lake env lean tests/Dispatch.lean
lake env lean tests/CharZero.lean
lake env lean tests/ModularRows.lean
lake env lean tests/Cache.lean
lake env lean tests/CacheReplay.lean
# In a Python environment with Sage installed:
lake env lean tests/Sage.lean
```

For larger literals, increase `maxRecDepth` as in the tests. The benchmark driver
sets a generous recursion limit and disables the heartbeat limit explicitly:

```powershell
./benchmarks/Run-Triangular.ps1
./benchmarks/Run-Triangular.ps1 -Dimensions 100 -EntryBits 256 -OutputDirectory .lake/triangular-benchmarks-256
```

On Windows systems requiring signed scripts, use a process-local policy for this
repository's driver: `powershell -NoProfile -ExecutionPolicy Bypass -File
benchmarks/Run-Triangular.ps1`.

The driver regenerates source, re-elaborates and kernel-checks each declaration,
writes an `.olean`, and records wall time, artifact size, and axiom dependencies
under `.lake/triangular-benchmarks`. See [the implementation and measurement
notes](../benchmarks/README.md) for the certificate contract and measured results.

The modular comparison driver is `./benchmarks/Run-Modular.ps1`. It compares
strict arithmetic proofs, strict kernel computation, and the reduced checker
on small deterministic dense matrices. See [the modular notes](../benchmarks/MODULAR.md)
for the replay contract, library choices and measurements. These small checker
comparisons do not establish the dense 100×100 runtime target.

The combined tactic's current scaling results, phase timings, memory measurements,
and reproduction commands are in [the dense benchmark report](../benchmarks/DENSE.md).

The measured fast mode uses native Lean and Sage in WSL on its native filesystem,
a `module`, `public noncomputable def` matrix data through the JSON spelling of
`int_matrix%`, and `kind := "unit-upper-product"`. Three signed 20-bit 100×100
declarations with the fused checker took 24.120, 24.348, and 26.143 seconds,
including imports, fresh Sage startup, all kernel checks, and artifact writing.
The fresh baseline median was 36.586 seconds, versus 24.348 seconds after fusion.
See [the measured comparison](../benchmarks/OPTIMIZATION.md) for the 50×50 results,
full-product/retry comparisons, and discarded experiment. This is a measured range
for the documented mode, not a uniform guarantee. Earlier results and future
optimization instructions remain in [the handoff](../benchmarks/HANDOFF.md).
