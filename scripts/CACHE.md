# Persistent determinant witnesses

`det_ne_zero!` uses the same triangular-first dispatcher, characteristic-zero
bridge, and strict kernel checker as `det_ne_zero`. Its optional term has type
`Determinant.Tactic.CacheConfig`, extending `ProducerConfig` with cache settings:

```lean
import Determinant

example : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { preferredPrimes := [2, 3, 5] }

-- Fresh elaboration of this proof needs Python, but does not need Sage.
example : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { policy := .cacheOnly }
```

`det_ne_zero_int!` is the integer-only spelling. Empty, singleton, triangular,
and hypothesis-driven proofs retain the cheap route and create no modular witness.
Importing the library never invokes the helper, Sage, or filesystem writes.

## Configuration and locality

The default directory is `det_ne_zero_witnesses` in the local Lake project root.
The helper starts at the **current Lean source file**, walks its ancestors to the
nearest `lakefile.toml` or `lakefile.lean`, and uses that project. It does not use
the producer's `workingDirectory`. For input without a source file it starts at
the current directory. `projectRoot := some "/absolute/project"` overrides root
discovery for tooling and unusual layouts.

Only the single configured witness directory is used. No parent, sibling,
dependency, or global witness directories are searched. Absolute overrides must
still be inside the selected project; `..` and symlinks cannot escape it.

```lean
set_option determinant.witnessDirectory "proof-data/det-witnesses"

example : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { directory := "other-witnesses", kind := "unit-upper-product" }
```

An explicit nonempty `directory` overrides `determinant.witnessDirectory`; an
empty string uses that option. Other per-invocation fields override `CacheConfig`
defaults, and a named configuration can be reused with `{ config with ... }`.

| Policy | Read candidates | Compute on miss/invalid candidate | Write checked witness |
| --- | --- | --- | --- |
| `.readWrite` (default) | yes | yes | yes |
| `.readOnly` | yes | yes | no |
| `.cacheOnly` | yes | never | no |
| `.disabled` | no | yes | no |

`refresh := true` bypasses lookup and requests fresh computation; it is incompatible
with `.cacheOnly`. With `.readOnly` it recomputes without writing. `.disabled`
uses exactly the ordinary uncached route. Corrupt/mismatched/old-format candidates
are rejected; read/write and read-only can recompute, while cache-only fails.
Directory/permission/helper configuration errors are reported, rather than hidden.

`lookupExecutable` defaults to `python3`, independently of the Sage producer.
`lookupArguments` defaults to the bundled `scripts/cache_lookup.py`, located via
Lean's source search path, including when this library is a Lake dependency.
Override the complete argument array for other installations. `lookupTimeoutMs`
defaults to 10000. Request/response byte bounds come from the inherited producer
configuration; the helper additionally caps requests at 64 MiB. OS arguments
are passed separately, without shell interpolation. Paths containing spaces work.
On native Windows, install standard Python and set `lookupExecutable` to its
executable path; the Sage producer can independently run through WSL as described
in [PROTOCOL.md](PROTOCOL.md).

## Identity, records, and publication

Identity format `det-ne-zero-matrix-v1` is ASCII (also valid UTF-8):

1. The line `det-ne-zero-matrix-v1` followed by LF.
2. The dimension in canonical unsigned decimal followed by LF.
3. Every full integer entry in row-major order, each followed by LF.

Integer spelling is `0`, positive decimal without leading zeros, or `-` followed
by positive decimal without leading zeros. Thus `-0`, `+1`, and `01` are invalid.
The empty matrix still has both header lines. Python's standard `hashlib.sha256`
hashes these bytes. Filenames are
`matrix-v1-{n}x{n}-{sha256}-{kind}.json`. The bounded filename describes the matrix
by dimension and full-content digest; embedding all entries would exceed common
filename limits for large matrices. Certificate kind is a compatibility tag;
prime preferences, producer versions, ring, source expressions, and names are
not matrix identity. Equivalent integer tables share a key across ambient rings.

Lookup opens exactly that filename: it never lists files, reads unrelated
certificates, or imports Sage. Its cost is linear in the current matrix encoding
and matching record size, independent of the number of cached matrices.
The pinned Lean/Mathlib sources did not supply a public SHA-256 implementation,
so hashing uses standard Python rather than a new project algorithm. Lean's
existing JSON/process bridge and proof checker are reused. SQLite is unnecessary
for a lookup that already opens one exact content-addressed path.

A JSON record has `schema: "det-ne-zero-witness"`, `version: 1`, `matrix` containing
`encoding`, `dimension`, and full row-major `entries`, and `response` containing
the original producer protocol response. That response preserves `certificate`
(`version`, `dimension`, `modulus` = p, `kind`, `inverse` = B) and Sage's backend,
version, and timing metadata. All entries and p are decimal **strings**. The
producer response is stored intact; producer metadata is never proof evidence.

Both the helper and Lean compare the stored full A with the current table.
Lean strictly decodes the certificate and proves its arithmetic against the
actual goal on every replay. A digest match, helper success, or stored success
flag cannot close a goal. On misses the assembled proof is kernel checked before
publication. Invalid mathematical candidates are never published. Cached
mathematical failures roll back tactic state and can trigger one fresh attempt.
The checker introduces no native-evaluation axiom or `sorry`.

Publication uses `tempfile.NamedTemporaryFile` in the same directory, flush/fsync,
and `os.replace`. Unique staging names allow concurrent writers; the last complete
valid record wins. Readers see complete old or new records. Orphan `.staging-*.tmp`
files are ignored and can be removed manually. A failed publication preserves the
old file. Schema changes reject old records; there is no silent migration or
deletion of unrelated files. The filesystem must support atomic replacement.

Witnesses are deliberately **not ignored by default**: commit selected JSON files
to make fresh offline proofs reproducible. Add `/det_ne_zero_witnesses/` to your
project's `.gitignore` if you prefer a disposable local cache.

## Inspection, export, and diagnostics

Records are plain JSON, readable with any text editor or `python3 -m json.tool`.
Copy the selected folder into the same relative location in another project to
use `.cacheOnly`, or export a standalone Lean certificate:

```sh
python3 scripts/cache_lookup.py --export det_ne_zero_witnesses/matrix-v1-...json
```

Paste its `RawCertificate` term after `certify_det_ne_zero_modular` for an integer
goal. This offline interface needs neither helper nor Sage. Export validates data
syntax; Lean remains responsible for mathematical verification.

Enable `trace.Determinant.cache`, `trace.Determinant.producer`, and
`trace.Determinant.timing` for hit/miss/rejection paths, external producer calls,
lookup/store timings, and the extra pre-publication kernel check. Normal proofs
remain quiet. See [the cache benchmark report](../benchmarks/CACHE.md) for fresh
process tests and overhead measurements.
