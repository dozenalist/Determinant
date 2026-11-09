import Determinant

open Lean Elab Tactic Determinant.Tactic

elab "benchmark_sage" : tactic => do
  let executable := (← IO.getEnv "DETERMINANT_TEST_PYTHON").getD "python3"
  let arguments ← match ← IO.getEnv "DETERMINANT_TEST_PREFIX" with
    | none => pure #["scripts/det_certificate.py"]
    | some value => do
      let argumentPrefix ← IO.ofExcept do
        (← (← Json.parse value).getArr?).mapM Json.getStr?
      pure (argumentPrefix.push "scripts/det_certificate.py")
  certifyWithProducer (processProducer { executable, arguments, preferredPrimes := [2, 3, 5] })

-- One fresh dense goal including an intentionally bad first prime.
set_option trace.Determinant.producer true in
theorem sageBridgeBenchmark : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  benchmark_sage

run_cmd do
  for dependency in ← Lean.collectAxioms ``sageBridgeBenchmark do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "unexpected axiom {dependency}"
