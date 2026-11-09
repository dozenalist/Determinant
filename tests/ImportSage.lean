-- Compile tests/Sage.lean as module Sage and put its artifact directory on LEAN_PATH.
-- This file needs the compiled theorem, but does not elaborate its producer invocation.
import Sage

#check SageTests.denseRetry
#print axioms SageTests.denseRetry

run_cmd do
  for dependency in ← Lean.collectAxioms ``SageTests.denseRetry do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "unexpected axiom {dependency}"
