# Certificate producer protocol, version 1

The producer reads one UTF-8 JSON object from stdin through EOF and writes one
JSON response on stdout. Diagnostics belong on stderr. No Lean source, Python
source, expression evaluation, or producer assertion is part of the protocol.
Importing any library module never starts a producer.

Request example (the determinant is 2, so the first prime is intentionally bad):

```json
{"protocol":"determinant-certificate","version":1,"dimension":2,"entries":["2","1","2","2"],"kind":"full-inverse","preferred_primes":["2","3","5"],"max_attempts":16,"timeout_ms":30000,"verify_product":false}
```

`dimension` is a nonnegative JSON integer; `entries` has exactly its square in
row-major order. Matrix entries are canonical signed decimal **strings**:
`0` or an optional `-` followed by a nonzero decimal digit and more decimal digits.
There is no leading `+`, whitespace, negative zero, leading zero, exponent, or
floating point representation. Moduli and primes use nonnegative decimal strings.
Python's decimal conversion digit limit is disabled to retain arbitrary precision.
Versions, dimensions, attempts, timeouts, and diagnostic timings are JSON integers;
they are parsed exactly by Lean and Python. Timeouts and attempt counts are positive.

The two supported kinds are `full-inverse` and `unit-upper-product`. Sage returns
an actual inverse for either kind; Lean selects the corresponding proved checker.
Preferred candidates must be primes greater than one. After that list, search
continues with successive primes above its maximum (starting at 2 for an empty
list). Each attempted reduction counts against `max_attempts`. Defaults are
`[2,3,5,7]`, 16 attempts, and 30000 ms. No rank or determinant is computed before
`inverse()`. Only its singularity exception causes a retry.

Successful response:

```json
{"protocol":"determinant-certificate","version":1,"status":"ok","certificate":{"version":1,"dimension":2,"modulus":"3","kind":"full-inverse","inverse":[["1","1"],["2","1"]]},"producer":{"name":"SageMath","sage_version":"10.10","backend":"sage.matrix.…","attempted_primes":["2","3"],"elapsed_ms":1000}}
```

The inverse contains exactly `dimension` rows of exactly `dimension` canonical
decimal strings, each between zero and `modulus - 1`. Both protocol and certificate
versions must be 1; dimensions and kind must match the request; the modulus must
exceed one. Metadata records the installed backend and version but is not trusted
or required by the proof layer. Unknown metadata fields can be ignored.

Failure response:

```json
{"protocol":"determinant-certificate","version":1,"status":"error","error":{"code":"search-exhausted","message":"no certificate found within the prime-attempt budget; this does not establish integer singularity"},"attempted_primes":["2"]}
```

Exit statuses: 0 for candidate data, 2 for exhausted search, 3 for timeout, 4 for
invalid request/configuration, 5 for unavailable Sage, 6 for other producer errors.
An argument-parser error can instead use its standard nonzero status and stderr.
Neither status 0 nor `status: ok` establishes a mathematical fact.

## Process and proof boundaries

`ProducerConfig` controls the executable, separate argument array, working
directory, search settings, kind, optional Sage product check, and byte limits.
Defaults bound request and response at 64 MiB each and stderr at 64 KiB. The Python
adapter independently bounds requests at 64 MiB. Output over either limit is a
failure, including excessive diagnostics. Invalid UTF-8, trailing/truncated JSON,
numeric entries instead of strings, unsupported versions, malformed shapes, and
noncanonical residues are rejected. Limits should be raised explicitly if needed.

Lean uses `IO.Process.spawn`, dedicated concurrent pipe tasks, monotonic time,
and `Core.checkInterrupted`. Writing stdin is also asynchronous: a producer that
never consumes input cannot disable the deadline. The cleanup reference has no
stdin handle, so successful writes actually deliver EOF. Timeout, cancellation,
and pipe failures kill the child tree. On POSIX, a fresh session and `/bin/kill
-KILL` cover workers and ignored SIGTERM. On Windows, `taskkill /T /F` terminates
native descendants before Lean's direct-child termination fallback. Termination
utilities have a separate 2000 ms cleanup allowance; reaping is asynchronous.

The Python standard-library supervisor runs Sage in a separate worker using
`subprocess.run(timeout=...)`; it kills and reaps an overdue worker, covering Sage
imports and a single slow inverse as well as the search loop. WSL is a separate
process environment: terminating a Windows launcher need not immediately stop a
Linux descendant. Its supervisor still terminates the Sage worker at the request
deadline. Use a native producer when immediate whole-process-group cancellation
is required. Replacement producers must implement their own descendant cleanup.

`CertificateProducer := Nat → Array Int → CoreM RawCertificate` is the small
replacement-backend interface. `processProducer` implements it; `proveWithProducer`
extracts the actual matrix once and calls `proveCertificateForEntries` with its
original expressions. Normalization congruences and the final definitional equality
connect the candidate to the original goal. Strict kernel computation verifies the
mathematics. The final theorem contains no process/file dependency or new axiom.

The public `det_ne_zero_int` dispatcher tries the hypothesis/triangular route
before this producer. It accepts the same optional `ProducerConfig` as
`certify_det_ne_zero_sage`. Neither tactic writes a persistent cache; use
`det_ne_zero!` for [project-local witness reuse](CACHE.md). Use
`kind := "unit-upper-product"` to check only the diagonal and below it.

Strict replay now uses natural residue literals and an explicitly shared transpose,
with proved bridges in `Determinant/NatCertificate.lean`. Compiled computation is
used only to reject candidates early. Reflexivity of the actual Boolean expression
requires the kernel to reduce the checker to `true`; dimensions above 16 use
checked row lemmas to bound reduction-cache memory. No native-evaluation axiom is
introduced. Normalization and transpose equalities are also checked by conversion.

`trace.Determinant.dispatch` reports route selection; `trace.Determinant.timing`
reports extraction, serialization, transport, parsing, normalization, proof
construction, and goal connection. Transport includes launcher and Sage startup.
Producer metadata additionally records Sage import, matrix construction,
search/inversion, residue encoding, and Linux worker peak RSS in KiB. These are
diagnostics, with no mathematical authority. Benchmark kernel time is collected
with Lean's built-in profiler. Row kernel checking happens inside tactic execution,
so its time is included in both the row phase and the cumulative kernel profile.
The final declaration's kernel check is reported separately. Do not add overlapping
phases together when interpreting the logs.

## Sage API and environment

The adapter uses `matrix(ZZ, n, n, entries)`, `change_ring(GF(p))`, and `inverse()`;
Sage chooses the backend. The public
[LinBox interface](https://doc.sagemath.org/html/en/reference/matrices/sage/matrix/matrix_modn_dense_double.html)
and [FLINT interface](https://doc.sagemath.org/html/en/reference/matrices/sage/matrix/matrix_modn_dense_flint.html)
were examined; neither warrants forcing an implementation before profiling.
No inversion, elimination, prime-search algorithm, serializer, or arithmetic
checker was reimplemented in Python. Prime search and primality testing are Sage's.
The scaling measurements and backend observations are documented in
[the dense benchmark report](../benchmarks/DENSE.md).

Tested environment: native Windows Lean/Mathlib 4.35.0, Windows 11,
WSL 3.0.3, `SageMath-10.10`, Sage 10.10, Python 3.14.10 in WSL, and native
Windows Python 3.11.9 for mock process tests. At the successful modulus 3, Sage
selected `sage.matrix.matrix_modn_dense_flint.Matrix_modn_dense_flint`. In this installation,
`/usr/bin/python3` imports `sage.all`; the old `sage -python` flag is unavailable.
Other installations can configure that legacy launcher if they support it.

Native Sage environment:

```lean
import Determinant
example : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_sage
```

The default command is `python3 scripts/det_certificate.py`. Set `executable`
to the Python interpreter in your Sage environment. Relative arguments resolve
against Lean's current working directory; set `workingDirectory := some "…"`
to the project root when starting Lean elsewhere. No project root is guessed.

Windows/WSL:

```lean
example : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_sage {
    executable := "C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe"
    arguments := #["-NoProfile", "-ExecutionPolicy", "Bypass", "-File",
      "scripts/Invoke-SageWSL.ps1", "-Distribution", "SageMath-10.10",
      "-Python", "/usr/bin/python3", "-Script", "scripts/det_certificate.py"]
    preferredPrimes := [2, 3, 5]
    maxAttempts := 8
    timeoutMs := 30000 }
```

The adapter is necessary because Lean 4.35 quotes every Windows argument, while
this WSL release parses its option prefix directly from the raw command line.
PowerShell invokes WSL's fixed `--distribution`/`--exec` options correctly, forwards
JSON and exit status, and treats the distribution, interpreter, and script as data.
Paths with spaces are supported. Use a Linux path for `-Python` and `-Script`;
Windows paths are not automatically translated by the adapter. The default
relative script path uses WSL's inherited translated working directory.

`set_option trace.Determinant.producer true` shows command arguments, elapsed
producer time, and stderr. Ordinary successful invocations are quiet.

## Reproducible checks

```powershell
lake build
lake env lean tests/Triangular.lean
lake env lean tests/Modular.lean
python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean tests/Bridge.lean
lake env lean tests/Dispatch.lean
lake env lean tests/Sage.lean
```

`Bridge.lean` uses standard Python fixtures; `Sage.lean` needs Sage in that Python
environment. Python's suite explicitly skips its Sage cases when unavailable.
To use a different test interpreter, set `DETERMINANT_TEST_PYTHON`. Its optional
`DETERMINANT_TEST_PREFIX` is a JSON array of arguments preceding the script path.
For the real Sage Lean suite on this Windows environment:

```powershell
$env:DETERMINANT_TEST_PYTHON = 'C:\Windows\System32\WindowsPowerShell\v1.0\powershell.exe'
$env:DETERMINANT_TEST_PREFIX = '["-NoProfile","-ExecutionPolicy","Bypass","-File","scripts/Invoke-SageWSL.ps1","-Distribution","SageMath-10.10","-Python","/usr/bin/python3","-Script"]'
lake env lean tests/Sage.lean
```

For native Windows fixture tests, use an installed native Python executable and
remove `DETERMINANT_TEST_PREFIX`. Use fresh `lake env lean` invocations to force
actual process execution rather than merely importing existing `.olean` files.

All four Lean suites and the build passed. The Python suite passed its eight
applicable methods in Sage (one missing-Sage case skipped) and its five applicable
methods in native Windows Python (four Sage cases skipped). Bridge tests include
actual Core cancellation, a blocked stdin writer, and a worker-start handshake
followed by an assertion that a timed-out native worker cannot write its marker.
All audited final theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Small end-to-end baseline

After configuring the test interpreter above, run:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File benchmarks/Run-SageBridge.ps1
```

The driver re-elaborates `benchmarks/SageBridge.lean` three times with separate
artifacts and stores logs and measurements under `.lake/sage-bridge-benchmarks`.
The source contains one dense 2×2 goal, tries bad prime 2 before successful prime 3,
and audits its final theorem's axioms. There is no certificate cache.

Reference machine: Intel Core Ultra 7 256V, 16 GB visible RAM, x86-64 Windows
NT 10.0.26300.0, with the Lean/Mathlib and Sage environment specified above. WSL
was already running; every invocation starts the launcher, supervisor and Sage
worker afresh. Dependencies were built. Ordinary desktop load was not isolated.
Timing covers the entire `lake env lean -o … benchmarks/SageBridge.lean` process,
including imports, producer startup, retry/inversion, parsing, proof construction,
kernel checking, axiom audit, and artifact writing. Peak memory and internal
phase profiling were not collected.

| Run | Total seconds | Producer trace, seconds | `.olean` bytes |
| --- | ---: | ---: | ---: |
| 1 | 17.734 | 3.791 | 110120 |
| 2 | 15.307 | 2.413 | 110120 |
| 3 | 18.972 | 4.220 | 110120 |

Median total: **17.734 seconds**; worst: **18.972 seconds**. The producer trace
includes launcher/import/transport and search time, not just inversion. The totals
show why producer time alone is insufficient. See
[raw measurements](../benchmarks/results-sage-bridge.json).
This establishes a reproducible bridge baseline only; dense 100×100 and larger
scaling, phase bottlenecks, and the one-minute target belong to Milestone 5.
