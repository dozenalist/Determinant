# Determinant

Lean tactics for proving that concrete square matrices have nonzero determinants.
Built on Mathlib, pinned to Lean and Mathlib **v4.35.0**.

| Tactic | Capabilities |
| --- | --- |
| `det_ne_zero_int` | Certifies integer matrices. Tries upper triangularity and nonzero diagonal entries first, then asks SageMath for a modular witness and verifies it in Lean. Also uses triangularity hypotheses for symbolic matrices. |
| `det_ne_zero` | Extends certification to matrices with integer entries over any commutative ring of characteristic zero, including `ℚ`, `ℝ`, and `ℂ`. Proves the integer-cast bridge and transports nonvanishing; no integral-domain assumption is required. |
| `det_ne_zero!` | Adds persistent, project-local modular witnesses to `det_ne_zero`. Reuses a matching witness without starting Sage and checks it again in Lean. Supports read/write, read-only, cache-only, refresh, and disabled policies. |

All results are kernel-checked proofs. Sage supplies candidate data; it is not
trusted to establish the theorem. No `sorry` or native-evaluation axiom is used.

```lean
import Determinant
import Mathlib.Basic.Complex.Basic

-- Triangular matrices need no external tools.
example : (!![-2, 7; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero_int

-- Dense matrices use Sage for modular witness discovery.
example : (!![2, 3; 1, 4] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
  det_ne_zero

-- Save a checked witness in det_ne_zero_witnesses/ (the default directory).
example : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero!

-- Later elaborations can require offline replay; Python is still used for lookup.
example : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { policy := .cacheOnly }
```

Both goal orientations (`A.det ≠ 0` and `0 ≠ A.det`) are supported, as are
matrix literals, exact square `ofLists` tables, reducible definitions, signed
numerals, and closed arithmetic that normalizes to integers. General symbolic
or nonintegral entries need other methods. `det_ne_zero_int!` is the integer-only
cache variant. For large integer tables, use `int_matrix% [[2, 1], [2, 2]]`.

Install the pinned Lean toolchain with [elan](https://github.com/leanprover/elan),
then run `lake update`, `lake exe cache get`, and `lake build`. Dense discovery
needs a `python3` that can import `sage.all`; cache lookup needs standard Python.
The optional `ProducerConfig` / `CacheConfig` controls executables, argument arrays,
prime search, time limits, certificate kind, and witness storage. See the
[setup and Windows/WSL instructions](scripts/PROTOCOL.md) and
[cache configuration](scripts/CACHE.md).

See the [tactic reference and test commands](docs/TACTICS.md),
[benchmark reports](benchmarks/README.md), and [roadmap](ROADMAP.md).
Representative dense 100×100 proofs have measured runtimes below one minute in
the documented [native Linux benchmark configuration](benchmarks/OPTIMIZATION.md).

Licensed under [Apache 2.0](LICENSE).
