import Determinant

open Lean Elab Tactic Determinant Determinant.Tactic

namespace BridgeTests

-- Defaults work in CI. Native Windows can point at Python in WSL using these
-- two environment variables; the argument prefix is a JSON array, never shell text.
def fixtureConfig (mode : String) : IO ProducerConfig := do
  let executable := (← IO.getEnv "DETERMINANT_TEST_PYTHON").getD "python3"
  let argumentPrefix ← match ← IO.getEnv "DETERMINANT_TEST_PREFIX" with
    | none => pure #[]
    | some value => IO.ofExcept do
      (← (← Json.parse value).getArr?).mapM Json.getStr?
  return {
    executable
    arguments := argumentPrefix ++ #["tests/fixtures/mock producer.py", "--mode", mode,
      "--literal", "argument with spaces & $()"]
    timeoutMs := 10000 }

elab "mock_certificate " mode:str : tactic => do
  let config ← fixtureConfig mode.getString
  certifyWithProducer (processProducer config)

theorem dense : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  mock_certificate "valid"

theorem reversed : 0 ≠ (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det := by
  mock_certificate "valid"

def named : Matrix (Fin 2) (Fin 2) ℤ := !![2, 3; 1, 2]

theorem namedGoal : named.det ≠ 0 := by mock_certificate "valid"

example : True := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![2, 3; 1, 2]
  have : A.det ≠ 0 := by mock_certificate "valid"
  trivial

example (_x : ℤ) : True := by
  fail_if_success
    have : (!![_x, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      mock_certificate "valid"
  trivial

theorem signedLarge : (!![-99999999999999999999999999999999999998, 3 * 11;
    1 - 5, 100000000000000000000000000000000000002] :
    Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  mock_certificate "valid"

theorem reduced : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  run_tac do
    let config ← fixtureConfig "valid"
    certifyWithProducer (processProducer { config with kind := "unit-upper-product" })

set_option linter.unusedTactic false in
theorem backtracking : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  first | mock_certificate "bad-math" | mock_certificate "valid"

example : True := by
  fail_if_success
    have : (!![2, 4; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      mock_certificate "valid"
  trivial

-- Every failure is observed within the tactic, including a process's false success.
set_option linter.unusedTactic false in
example : True := by
  run_tac do
    for mode in ["bad-math", "wrong-version", "wrong-cert-version", "wrong-dimension",
        "wrong-modulus", "wrong-kind", "ragged", "noncanonical", "numeric-integer",
        "residue-bound", "malformed", "truncated", "invalid-utf8"] do
      evalTactic (← `(tactic| fail_if_success
        have : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
          mock_certificate $(quote mode)))
  trivial

-- Process diagnostics, bounded streams, blocked input, and a literal path with spaces.
run_cmd Lean.Elab.Command.liftCoreM do
  let base ← fixtureConfig "valid"
  let expectFailure := fun config needle => do
    let mut message := ""
    try
      discard <| processProducer config 2 #[2, 3, 1, 2]
    catch error => message := (← error.toMessageData.toString)
    unless (message.splitOn needle).length > 1 do
      throwError "expected '{needle}', got '{message}'"
  expectFailure { base with executable := "determinant-producer-does-not-exist" }
    "could not start"
  expectFailure { base with arguments := base.arguments.push "--unknown-argument" }
    "unrecognized arguments"
  let exiting ← fixtureConfig "exit"
  expectFailure exiting "deliberate producer diagnostic"
  for mode in ["stdout-limit", "stderr-limit"] do
    let config ← fixtureConfig mode
    expectFailure { config with maxResponseBytes := 4096, maxStderrBytes := 4096 }
      "exceeds byte limit"
  let config ← fixtureConfig "wait"
  expectFailure { config with timeoutMs := 200 } "timed out"
  -- A pipe writer must not block cancellation or the deadline.
  let config ← fixtureConfig "no-read"
  let mut rejected := false
  try
    discard <| runProducer { config with timeoutMs := 200 } (String.ofList (List.replicate 1000000 'x'))
  catch error =>
    rejected := ((← error.toMessageData.toString).splitOn "timed out").length > 1
  unless rejected do throwError "blocked stdin did not time out"
  expectFailure { base with timeoutMs := 0 } "must be positive"
  expectFailure { base with maxAttempts := 0 } "must be positive"
  expectFailure { base with maxRequestBytes := 1 } "request exceeds byte limit"
  if (parseProducerResponse 2 "full-inverse" "{\"status\":\"ok\"}").isOk then
    throwError "a success flag without a certificate was accepted"

-- Actual Core cancellation uses the same token supplied by the language server.
run_cmd Lean.Elab.Command.liftCoreM do
  let config ← fixtureConfig "wait"
  let token ← IO.CancelToken.new
  let timer ← IO.asTask (do IO.sleep 200; token.set) .dedicated
  let mut cancelled := false
  let context ← readThe Core.Context
  let state ← getThe Core.State
  let result ← ((runProducer config "{}").run
    { context with cancelTk? := some token } state).toBaseIO
  if let .error error := result then
    cancelled := error.isInterrupt
  discard <| IO.ofExcept timer.get
  unless cancelled do throwError "producer did not propagate cancellation"

-- Killing a supervisor must also stop a native worker before it can write its marker.
run_cmd Lean.Elab.Command.liftCoreM do
  IO.FS.withTempDir fun directory => do
    let marker := directory / "worker survived.txt"
    let base ← fixtureConfig "child-tree"
    let config := { base with
      timeoutMs := 2000
      arguments := base.arguments ++ #["--marker", marker.toString] }
    let mut timedOut := false
    try
      discard <| runProducer config "{}"
    catch error =>
      timedOut := ((← error.toMessageData.toString).splitOn "timed out").length > 1
    unless timedOut do throwError "worker fixture did not time out"
    unless ← (System.FilePath.mk (marker.toString ++ ".started")).pathExists do
      throwError "worker fixture did not start before its deadline"
    IO.sleep 4500
    if ← marker.pathExists then throwError "producer worker survived process-tree cleanup"

-- Serialization and parsing preserve integers well beyond machine/JSON float precision.
run_cmd do
  let huge : Int := -999999999999999999999999999999999999999999999999999999999999999999
  let json := producerRequest 1 #[huge] {}
  let .ok entries := (json.getObjVal? "entries").bind Json.getArr?
    | throwError "missing serialized entries"
  unless entries == #[toJson (toString huge)] do throwError "lossy request serialization"

#print axioms dense
run_cmd do
  for decl in [``dense, ``reversed, ``namedGoal, ``signedLarge, ``reduced, ``backtracking] do
    for dependency in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "unexpected axiom {dependency} in {decl}"

end BridgeTests
