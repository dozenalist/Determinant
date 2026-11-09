import Determinant

open Lean Elab Tactic Determinant.Tactic

namespace CacheTests

def config : CacheConfig := {
  executable := "python3"
  arguments := #["tests/fixtures/mock producer.py", "--marker", ".lake/det-ne-zero-tests/calls"]
  directory := ".lake/det-ne-zero-tests/witnesses" }

run_cmd do
  let directory : System.FilePath := ".lake/det-ne-zero-tests"
  if ← directory.pathExists then IO.FS.removeDirAll directory
  IO.FS.createDirAll directory

set_option trace.Determinant.cache true in
theorem miss : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! config

theorem hit : 0 ≠ (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det := by
  det_ne_zero! { config with policy := .cacheOnly, executable := "must-not-launch" }

-- The same integer table is reused across ambient rings and source expressions.
theorem charZero {R : Type*} [CommRing R] [CharZero R] :
    (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
  det_ne_zero! { config with policy := .readOnly, executable := "must-not-launch" }

theorem arithmeticHit : (!![1 + 1, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero_int! { config with policy := .cacheOnly, executable := "must-not-launch" }

run_cmd do
  unless (← IO.FS.readFile ".lake/det-ne-zero-tests/calls").trimAscii == "producer invoked" do
    throwError "cache hit launched the producer"

theorem changedEntry : (!![7, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! config

theorem reduced : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { config with kind := "unit-upper-product" }

theorem refreshed : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { config with refresh := true }

run_cmd do
  let calls := (← IO.FS.readFile ".lake/det-ne-zero-tests/calls").splitOn "\n"
  unless calls.length == 5 do throwError "refresh did not invoke the producer"

theorem readOnlyMiss : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { config with policy := .readOnly, directory := ".lake/det-ne-zero-tests/read-only" }

theorem disabled : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { config with
    policy := .disabled
    lookupExecutable := "must-not-launch"
    directory := ".lake/det-ne-zero-tests/disabled" }

-- The triangular route never touches the helper, cache, or producer, under any policy.
theorem triangular : (!![-2, 5; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! {
    policy := .cacheOnly
    lookupExecutable := "must-not-launch"
    executable := "must-not-launch"
    directory := ".lake/det-ne-zero-tests/triangular" }

theorem empty : (!![] : Matrix (Fin 0) (Fin 0) ℤ).det ≠ 0 := by
  det_ne_zero! { lookupExecutable := "must-not-launch", executable := "must-not-launch" }

theorem singleton : (!![-3] : Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by
  det_ne_zero!

run_cmd do
  for name in ["read-only", "disabled", "triangular"] do
    if ← (System.FilePath.mk s!".lake/det-ne-zero-tests/{name}").pathExists then
      throwError "unexpected cache write for {name}"

-- The per-invocation directory takes precedence over project defaults.
set_option determinant.witnessDirectory ".lake/det-ne-zero-tests/wrong-default" in
theorem directoryOverride : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { config with policy := .cacheOnly, executable := "must-not-launch" }

set_option determinant.witnessDirectory ".lake/det-ne-zero-tests/witnesses" in
theorem projectDefault : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { policy := .cacheOnly, executable := "must-not-launch" }

theorem spacedDirectory : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { config with directory := ".lake/det-ne-zero-tests/witnesses with spaces" }

theorem spacedDirectoryHit : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! { config with
    directory := ".lake/det-ne-zero-tests/witnesses with spaces"
    policy := .cacheOnly
    executable := "must-not-launch" }

example : True := by
  fail_if_success
    have : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      det_ne_zero! { config with refresh := true, executable := "must-not-launch" }
  fail_if_success
    have : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      det_ne_zero! { config with policy := .cacheOnly, refresh := true }
  fail_if_success
    have : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      det_ne_zero! { config with policy := .cacheOnly, directory := ".lake/det-ne-zero-tests/missing" }
  fail_if_success
    have : (!![2, 4; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      det_ne_zero! config
  trivial

def originalWitness : IO System.FilePath := do
  for entry in ← (System.FilePath.mk config.directory).readDir do
    let data ← IO.ofExcept (Json.parse (← IO.FS.readFile entry.path))
    let matrix ← IO.ofExcept (data.getObjVal? "matrix")
    if (matrix.getObjVal? "entries").toOption ==
        some (toJson (["2", "3", "1", "2"] : List String)) then
      let response ← IO.ofExcept (data.getObjVal? "response")
      let cert ← IO.ofExcept (response.getObjVal? "certificate")
      if (cert.getObjVal? "kind").toOption == some (toJson "full-inverse") then return entry.path
  throw (IO.userError "missing witness")

-- Corrupt mathematical evidence must fail even when metadata and full A still match.
run_cmd do
  let path ← originalWitness
  let contents ← IO.FS.readFile path
  let corrupt := contents.replace "\"inverse\":[[\"2\",\"2\"]" "\"inverse\":[[\"3\",\"2\"]"
  unless corrupt != contents do throwError "test did not corrupt B"
  IO.FS.writeFile path corrupt

example : True := by
  fail_if_success
    have : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      det_ne_zero! { config with policy := .cacheOnly, executable := "must-not-launch" }
  trivial

set_option trace.Determinant.cache true in
theorem repaired : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! config

run_cmd do
  let path ← originalWitness
  let contents ← IO.FS.readFile path
  IO.FS.writeFile path (contents.replace "\"modulus\":\"5\"" "\"modulus\":\"7\"")

example : True := by
  fail_if_success
    have : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      det_ne_zero! { config with policy := .cacheOnly, executable := "must-not-launch" }
  trivial

run_cmd do
  let path ← originalWitness
  let contents ← IO.FS.readFile path
  IO.FS.writeFile path (contents.replace "\"modulus\":\"7\"" "\"modulus\":\"5\"")
  unless (← (System.FilePath.mk config.directory).readDir).size == 3 do
    throwError "a rejected mathematical certificate was published"

theorem signedLarge : (!![-99999999999999999999999999999999999998, 33;
    -4, 100000000000000000000000000000000000002] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  det_ne_zero! config

run_cmd do
  for decl in [``miss, ``hit, ``charZero, ``arithmeticHit, ``changedEntry, ``reduced,
      ``refreshed, ``readOnlyMiss, ``disabled, ``triangular, ``empty, ``singleton,
      ``directoryOverride, ``projectDefault, ``spacedDirectory, ``spacedDirectoryHit,
      ``repaired, ``signedLarge] do
    for dependency in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "unexpected axiom {dependency} in {decl}"

end CacheTests
