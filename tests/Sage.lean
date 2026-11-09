import Determinant
import Mathlib.Basic.Complex.Basic

open Lean Elab Tactic Determinant.Tactic

namespace SageTests

def sageConfig : IO ProducerConfig := do
  let executable := (← IO.getEnv "DETERMINANT_TEST_PYTHON").getD "python3"
  let argumentPrefix ← match ← IO.getEnv "DETERMINANT_TEST_PREFIX" with
    | none => pure #[]
    | some value => IO.ofExcept do
      (← (← Json.parse value).getArr?).mapM Json.getStr?
  return {
    executable
    arguments := argumentPrefix ++ #["scripts/det_certificate.py"]
    preferredPrimes := [2, 3, 5]
    verifyProduct := true }

elab "sage_certificate" : tactic => do
  let config ← sageConfig
  evalTactic (← `(tactic| det_ne_zero_int {
    executable := $(quote config.executable)
    arguments := $(quote config.arguments)
    preferredPrimes := [2, 3, 5]
    verifyProduct := true }))

-- Exercise the public characteristic-zero syntax with actual Sage discovery.
elab "sage_ring_certificate" : tactic => do
  let config ← sageConfig
  evalTactic (← `(tactic| det_ne_zero {
    executable := $(quote config.executable)
    arguments := $(quote config.arguments)
    preferredPrimes := [2, 3, 5]
    verifyProduct := true }))

theorem complex : (!![2, 3; 1, 4] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
  sage_ring_certificate

theorem charZero {R : Type*} [CommRing R] [CharZero R] :
    (!![2, 3; 1, 4] : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
  sage_ring_certificate

-- Determinant 2: the producer must skip the intentionally bad first prime 2.
set_option trace.Determinant.producer true in
theorem denseRetry : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  sage_certificate

theorem empty : (!![] : Matrix (Fin 0) (Fin 0) ℤ).det ≠ 0 := by sage_certificate
theorem singleton : (!![-3] : Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by sage_certificate
theorem denseThree : (!![2, 1, 1; 1, 2, 1; 1, 1, 2] :
    Matrix (Fin 3) (Fin 3) ℤ).det ≠ 0 := by sage_certificate
theorem signedLarge : (!![-99999999999999999999999999999999999998, 33;
    -4, 100000000000000000000000000000000000002] :
    Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by sage_certificate

theorem reduced : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  run_tac do
    let config ← sageConfig
    detNeZeroInt (processProducer { config with kind := "unit-upper-product" })

-- Both the WSL launcher and the Python supervisor must preserve spaced paths.
theorem spacedPath : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  run_tac do
    let directory : System.FilePath := ".lake/producer with spaces"
    IO.FS.createDirAll directory
    let script := ".lake/producer with spaces/det producer.py"
    IO.FS.writeFile script (← IO.FS.readFile "scripts/det_certificate.py")
    let config ← sageConfig
    let arguments := config.arguments.set! (config.arguments.size - 1) script
    certifyWithProducer (processProducer { config with arguments })

example : True := by
  fail_if_success
    have : (!![1, 2; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by sage_certificate
  fail_if_success
    have : (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by sage_certificate
  trivial

-- No certificate is accepted when the only permitted prime is bad.
example : True := by
  fail_if_success
    have : (!![2, 1; 2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      run_tac do
        let config ← sageConfig
        certifyWithProducer (processProducer { config with maxAttempts := 1 })
  trivial

#print axioms denseRetry
run_cmd do
  for decl in [``denseRetry, ``empty, ``singleton, ``denseThree, ``signedLarge, ``spacedPath,
      ``reduced, ``complex, ``charZero] do
    for dependency in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "unexpected axiom {dependency} in {decl}"

end SageTests
