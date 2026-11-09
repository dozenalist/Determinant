module
public import Determinant
meta import Determinant.Tactic.Bridge
meta import Lean.Util.NumObjs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option trace.Determinant.timing true
set_option trace.Determinant.producer true
set_option linter.style.longLine false

open Lean Elab Tactic Determinant.Tactic

run_cmd do
  if let some started ← IO.getEnv "DETERMINANT_BENCHMARK_STARTED_MS" then
    if let some started := started.toNat? then
      Lean.logInfo m!"[Determinant.timing] startup and imports: {(← IO.monoMsNow) - started} ms"

elab "timed_matrix " name:ident " : " type:term " := " value:term : command => do
  let started ← IO.monoMsNow
  Lean.Elab.Command.elabCommand (← `(public noncomputable def $name : $type := $value))
  Lean.logInfo m!"[Determinant.timing] input declaration: {(← IO.monoMsNow) - started} ms"
  IO.eprintln "benchmark input elaborated"
  (← IO.getStderr).flush

elab "benchmark_certify" : tactic => do
  let started ← IO.monoMsNow
  let executable := (← IO.getEnv "DETERMINANT_TEST_PYTHON").getD "python3"
  let argumentPrefix ← match ← IO.getEnv "DETERMINANT_TEST_PREFIX" with
    | none => pure #[]
    | some value => IO.ofExcept do
      (← (← Json.parse value).getArr?).mapM Json.getStr?
  evalTactic (← `(tactic| certify_det_ne_zero {
    executable := $(quote executable)
    arguments := $(quote (argumentPrefix.push "scripts/det_certificate.py"))
    preferredPrimes := [2, 3, 5, 7]
    kind := "unit-upper-product"
    timeoutMs := 30000 }))
  IO.eprintln s!"benchmark tactic returned after {(← IO.monoMsNow) - started} ms"
  (← IO.getStderr).flush

timed_matrix benchmarkMatrix : Matrix (Fin 10) (Fin 10) Int := int_matrix% r#"[["937272","783293","316895","763691","-964838","-644065","-658921","31071","174510","-140800"],["325634","-830586","939506","-974002","-988623","-300585","322475","-962573","-803404","763019"],["-795818","-557364","306702","775180","538215","-490979","367115","-863106","-877737","-928392"],["-968019","667156","444277","429063","919792","508654","696244","874492","855412","-269062"],["-31688","-832336","717414","-35334","528528","-199215","916554","-555419","1002717","-133269"],["-1029084","-407441","-268424","46215","-711681","-1004660","-608447","-391276","887289","-955735"],["527303","473467","648396","236813","-921663","913856","367976","-637465","469853","794049"],["454862","-120853","-228672","-883654","474029","401053","319854","76993","-675805","369200"],["-868402","254119","746321","712801","-16159","-351783","360744","291192","874193","-130564"],["-178231","621008","183053","-610036","-309259","-35618","470786","651941","-1026194","627649"]]"#

set_option profiler true in
set_option profiler.threshold 1 in
public theorem benchmark : benchmarkMatrix.det ≠ 0 := by benchmark_certify

#print axioms benchmark

run_cmd do
  for dependency in ← Lean.collectAxioms ``benchmark do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "unexpected axiom {dependency}"
  let some (.thmInfo info) := (← Lean.getEnv).find? ``benchmark
    | throwError "missing benchmark theorem"
  Lean.logInfo m!"proof nodes: {← Lean.Expr.numObjs info.value}"
  if let some started ← IO.getEnv "DETERMINANT_BENCHMARK_STARTED_MS" then
    if let some started := started.toNat? then
      Lean.logInfo m!"[Determinant.timing] pre-export elapsed: {(← IO.monoMsNow) - started} ms"
