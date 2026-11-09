import Determinant

open Matrix Determinant

namespace ModularTests

def inverseFive : RawCertificate := {
  dimension := 2, modulus := 5, inverse := [[2, 2], [4, 2]] }

theorem dense : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular inverseFive

theorem denseKernel : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular_kernel inverseFive

theorem denseArithmetic : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular_arithmetic inverseFive

-- Standalone replay without invoking either tactic or any candidate evaluator.
theorem explicitReplay : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 :=
  checkFull_sound (n := 2) (p := 5) (original := [[2, 3], [1, 2]])
    (a := [[2, 3], [1, 2]]) (b := [[2, 2], [4, 2]])
    (by decide) (by decide) (by decide)

theorem composite : (!![2, 3; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular {
    dimension := 2, modulus := 6, inverse := [[2, 3], [5, 2]] }

theorem singleton : (!![-3] : Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular { dimension := 1, modulus := 8, inverse := [[5]] }

theorem empty : (!![] : Matrix (Fin 0) (Fin 0) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular { dimension := 0, modulus := 4, inverse := [] }

theorem emptyKernel : (!![] : Matrix (Fin 0) (Fin 0) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular_kernel { dimension := 0, modulus := 4, inverse := [] }

def named : Matrix (Fin 2) (Fin 2) ℤ := !![2, 3; 1, 2]

theorem reversed : 0 ≠ named.det := by
  certify_det_ne_zero_modular inverseFive

theorem signedLarge : (!![-99999999999999999999999999999999999998, 3 * 11;
    1 - 5, 100000000000000000000000000000000000002] :
    Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular inverseFive

theorem negativeWitness : named.det ≠ 0 := by
  certify_det_ne_zero_modular {
    dimension := 2, modulus := 5, inverse := [[2, -3], [-1, 2]] }

theorem denseThree : (!![2, 1, 1; 1, 2, 1; 1, 1, 2] : Matrix (Fin 3) (Fin 3) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular_arithmetic {
    dimension := 3, modulus := 5, inverse := [[2, 1, 1], [1, 2, 1], [1, 1, 2]] }

theorem largeModulus : (!![-1] : Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular_arithmetic {
    dimension := 1, modulus := 18446744073709551617, inverse := [[-1]] }

-- The intentionally failing first branch is the behavior under test.
set_option linter.unusedTactic false in
theorem backtracking : named.det ≠ 0 := by
  first
  | certify_det_ne_zero_modular_kernel {
      dimension := 2, modulus := 5, inverse := [[3, 2], [4, 2]] }
  | certify_det_ne_zero_modular inverseFive

example : True := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![2, 3; 1, 2]
  have : A.det ≠ 0 := by certify_det_ne_zero_modular inverseFive
  trivial

example : (let A : Matrix (Fin 2) (Fin 2) ℤ := !![2, 3; 1, 2]; A.det ≠ 0) := by
  dsimp only
  certify_det_ne_zero_modular_kernel inverseFive

-- Mathematical rejection, including a certificate valid for a different current matrix.
example : True := by
  fail_if_success
    have : named.det ≠ 0 := by
      certify_det_ne_zero_modular_arithmetic {
        dimension := 2, modulus := 5, inverse := [[3, 2], [4, 2]] }
  fail_if_success
    have : named.det ≠ 0 := by
      certify_det_ne_zero_modular_kernel {
        dimension := 2, modulus := 5, inverse := [[3, 2], [4, 2]] }
  fail_if_success
    have : (!![2, 4; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular_arithmetic inverseFive
  fail_if_success
    have : (!![2, 3; 2, 3] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular_kernel inverseFive
  fail_if_success
    have : (!![2, 3; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular inverseFive
  fail_if_success
    have : named.det ≠ 0 := by
      certify_det_ne_zero_modular_arithmetic { inverseFive with modulus := 7 }
  -- An unsuccessful modulus proves nothing about the nonsingular integer matrix.
  fail_if_success
    have : (!![2] : Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular { dimension := 1, modulus := 2, inverse := [[1]] }
  fail_if_success
    have : (!![0] : Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular { dimension := 1, modulus := 5, inverse := [[0]] }
  trivial

-- Invalid metadata/shape must be rejected even for the empty matrix or padded identities.
example : True := by
  fail_if_success
    have : named.det ≠ 0 := by
      certify_det_ne_zero_modular { inverseFive with version := 2 }
  fail_if_success
    have : named.det ≠ 0 := by
      certify_det_ne_zero_modular { inverseFive with kind := "producer-says-success" }
  fail_if_success
    have : named.det ≠ 0 := by
      certify_det_ne_zero_modular { inverseFive with dimension := 3 }
  fail_if_success
    have : named.det ≠ 0 := by
      certify_det_ne_zero_modular { inverseFive with inverse := [[2, 2], [4]] }
  fail_if_success
    have : named.det ≠ 0 := by
      certify_det_ne_zero_modular { inverseFive with inverse := [[2, 2], [4, 2, 0]] }
  fail_if_success
    have : named.det ≠ 0 := by
      certify_det_ne_zero_modular { inverseFive with inverse := [[2, 2]] }
  fail_if_success
    have : named.det ≠ 0 := by
      certify_det_ne_zero_modular { inverseFive with inverse := [[2, 2], [4, 2], [0, 0]] }
  -- Padding this table would give a valid inverse: shape rejection is mandatory.
  fail_if_success
    have : (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular {
        dimension := 2, modulus := 5, inverse := [[1], [0, 1]] }
  fail_if_success
    have : (!![] : Matrix (Fin 0) (Fin 0) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular { dimension := 0, modulus := 5, inverse := [[]] }
  fail_if_success
    have : (!![] : Matrix (Fin 0) (Fin 0) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular { dimension := 0, modulus := 1, inverse := [] }
  fail_if_success
    have : named.det ≠ 0 := by
      certify_det_ne_zero_modular { inverseFive with modulus := 0 }
  fail_if_success
    have : (1 : ℤ) ≠ 0 := by
      certify_det_ne_zero_modular inverseFive
  fail_if_success
    have : named.det ≠ 1 := by
      certify_det_ne_zero_modular inverseFive
  trivial

example (_A : Matrix (Fin 2) (Fin 2) ℤ) : True := by
  fail_if_success
    have : _A.det ≠ 0 := by certify_det_ne_zero_modular inverseFive
  trivial

-- Validator results are inspectable without executing a tactic or external producer.
example : (inverseFive.validate 2).isOk = true := by decide
example : ({ inverseFive with modulus := 1 }.validate 2).isOk = false := by decide
example : ({ inverseFive with kind := "future-format" }.validate 2).isOk = false := by decide

-- The specialized natural checker preserves full versus reduced obligations.
example : natDot 3 [2, 4, 7] [3, 5, 8] = 82 := by decide
example : natDot 3 [2] [3, 5, 8] = 6 := by decide
example : checkNat false 5 [[2, 3], [1, 2]] [[2, 4], [2, 2]] = true := by decide
example : checkNat false 6 [[1, 1], [1, 2]] [[2, 5], [1, 0]] = false := by decide
example : checkNat true 6 [[1, 1], [1, 2]] [[2, 5], [1, 0]] = true := by decide
example : checkNat true 6 [[1, 1], [1, 2]] [[1, 0], [1, 0]] = false := by decide

-- Literal recognition is untrusted data extraction, including custom instances.
-- The normalization equality must still be proved for the original expression.
set_option linter.style.haveILetI false in
example : True := by
  letI : OfNat ℤ 2 := ⟨0⟩
  fail_if_success
    have : (!![2] : Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular { dimension := 1, modulus := 5, inverse := [[3]] }
  trivial

-- This product is [[1, 1], [0, 1]] modulo 6, so it is deliberately not a full inverse.
def reduced : RawCertificate := {
  dimension := 2, modulus := 6, kind := "unit-upper-product", inverse := [[2, 1], [5, 0]] }

theorem reducedComposite : (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular reduced

theorem reducedEmpty : (!![] : Matrix (Fin 0) (Fin 0) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular {
    dimension := 0, modulus := 5, kind := "unit-upper-product", inverse := [] }

theorem reducedSingleton : (!![-3] : Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by
  certify_det_ne_zero_modular {
    dimension := 1, modulus := 8, kind := "unit-upper-product", inverse := [[5]] }

example : True := by
  fail_if_success
    have : (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular { reduced with kind := "full-inverse" }
  -- Preserve the diagonal ones but change the checked below-diagonal entry to one.
  fail_if_success
    have : (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular { reduced with inverse := [[1, 1], [0, 0]] }
  -- Preserve the below-diagonal zero but change a diagonal entry.
  fail_if_success
    have : (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular { reduced with inverse := [[2, 2], [5, 0]] }
  -- A nonzero diagonal over a composite ring is insufficient: [2] mod 4 is not a unit.
  fail_if_success
    have : (!![2] : Matrix (Fin 1) (Fin 1) ℤ).det ≠ 0 := by
      certify_det_ne_zero_modular {
        dimension := 1, modulus := 4, kind := "unit-upper-product", inverse := [[1]] }
  trivial

#print axioms dense
#print axioms denseKernel
#print axioms denseArithmetic
#print axioms composite
#print axioms signedLarge
#print axioms reducedComposite

run_cmd do
  for decl in [``dense, ``denseKernel, ``denseArithmetic, ``explicitReplay, ``composite,
      ``singleton, ``empty,
      ``emptyKernel, ``reversed, ``signedLarge, ``negativeWitness, ``denseThree, ``largeModulus,
      ``backtracking,
      ``reducedComposite, ``reducedEmpty,
      ``reducedSingleton, ``det_ne_zero_of_modular_right_inverse, ``checkFull_sound,
      ``det_ne_zero_of_modular_unit_upper_product, ``checkUnitUpper_sound,
      ``natDot_cast, ``natDotZip_eq, ``natDotFused_eq, ``checkNat_sound] do
    for dependency in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "unexpected axiom {dependency} in {decl}"

end ModularTests
