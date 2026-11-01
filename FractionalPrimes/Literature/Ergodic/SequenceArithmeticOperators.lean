module

public import FractionalPrimes.Literature.Harmonic.MSZSquareFunctionBridge
public import FractionalPrimes.Literature.Ergodic.ArithmeticSystemOperatorDecay
public import FractionalPrimes.Literature.Ergodic.ArithmeticAverageIncrements
public import FractionalPrimes.Literature.Ergodic.LogarithmicPerturbationLinear
public import FractionalPrimes.Literature.Harmonic.UnweightedVariation

/-! Norm and difference identities for applying the checked perturbation theorem. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
open Literature.Harmonic
noncomputable section

theorem integerKernelConvolutionRealExponentCLM_norm_le
    (p : ℝ) (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] (K : IntegerL1Kernel) :
    ‖integerKernelConvolutionRealExponentCLM p hp K‖ ≤
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) K‖ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  apply (integerKernelConvolutionRealExponentCLM p hp K).opNorm_le_bound (norm_nonneg _)
  intro f
  change ‖countLpToGeneralLp hp0 ENNReal.ofReal_ne_top
    (integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) K
      (generalLpToCountLp hp0 ENNReal.ofReal_ne_top f))‖ ≤ _
  rw [countLpToGeneralLp_norm]
  have h := (integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) K).le_opNorm
    (generalLpToCountLp hp0 ENNReal.ofReal_ne_top f)
  simpa only [generalLpToCountLp_norm] using h

theorem primeComparisonSequenceOperator_eq_sub
    (p : ℝ) (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] (c : ℝ) (N : Scale) :
    integerKernelConvolutionRealExponentCLM p hp (primeComparisonIntegerKernel c N) =
      integerKernelConvolutionRealExponentCLM p hp (vonMangoldtIntegerKernel c N) -
        integerKernelConvolutionRealExponentCLM p hp (floorPowerKernel c N) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  change integerKernelConvolutionRealExponentCLM p hp (primeComparisonIntegerKernel c N) f x =
    integerKernelConvolutionRealExponentCLM p hp (vonMangoldtIntegerKernel c N) f x -
      integerKernelConvolutionRealExponentCLM p hp (floorPowerKernel c N) f x
  rw [integerKernelConvolutionRealExponentCLM_apply,
    integerKernelConvolutionRealExponentCLM_apply,
    integerKernelConvolutionRealExponentCLM_apply,
    primeComparisonIntegerKernel_convolution,
    ← vonMangoldtAverage_integerShift_eq_integerKernelConvolution,
    ← unweightedAverage_integerShift_eq_integerKernelConvolution]

#print axioms primeComparisonSequenceOperator_eq_sub

theorem vonMangoldtSequenceOperator_apply
    (p : ℝ) (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (c : ℝ) (N : Scale) (f : IntegerSequenceLp p) (x : ℤ) :
    integerKernelConvolutionRealExponentCLM p hp (vonMangoldtIntegerKernel c N) f x =
      vonMangoldtAverage integerShiftSystem c (f : ℤ → ℂ) N x := by
  rw [integerKernelConvolutionRealExponentCLM_apply,
    ← vonMangoldtAverage_integerShift_eq_integerKernelConvolution]

theorem unweightedSequenceOperator_apply
    (p : ℝ) (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (c : ℝ) (N : Scale) (f : IntegerSequenceLp p) (x : ℤ) :
    integerKernelConvolutionRealExponentCLM p hp (floorPowerKernel c N) f x =
      unweightedAverage integerShiftSystem c (f : ℤ → ℂ) N x := by
  rw [integerKernelConvolutionRealExponentCLM_apply,
    ← unweightedAverage_integerShift_eq_integerKernelConvolution]

theorem vonMangoldtSequenceOperator_increment_norm
    (p : ℝ) (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (c : FractionalExponent) (N : Scale) :
    ‖integerKernelConvolutionRealExponentCLM p hp
        (vonMangoldtIntegerKernel c.value (perturbationSuccessorScale N)) -
      integerKernelConvolutionRealExponentCLM p hp (vonMangoldtIntegerKernel c.value N)‖ ≤
      2 * (Real.log (2 * (N.val : ℝ)) / ((N.val : ℝ) + 1)) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  let T := integerKernelConvolutionRealExponentCLM p hp
      (vonMangoldtIntegerKernel c.value (perturbationSuccessorScale N)) -
    integerKernelConvolutionRealExponentCLM p hp (vonMangoldtIntegerKernel c.value N)
  have hlog : 0 ≤ Real.log (2 * (N.val : ℝ)) := by
    apply Real.log_nonneg
    have h : (1 : ℝ) ≤ N.val := by exact_mod_cast N.property
    linarith
  have hcoef : 0 ≤ 2 * (Real.log (2 * (N.val : ℝ)) / ((N.val : ℝ) + 1)) := by positivity
  apply T.opNorm_le_bound hcoef
  intro f
  have hf := memLp_count_of_memlp_seq_finite hp0 ENNReal.ofReal_ne_top f
  have hmeasure := integerShiftSystem_measure
  have hfS : MemLp (f : ℤ → ℂ) (ENNReal.ofReal p) integerShiftSystem.μ := by
    rw [hmeasure]
    exact hf
  have hraw := (weightedAverageIncrementBounds integerShiftSystem c N.val N.property
    (p := ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr hp.le) (f : ℤ → ℂ) hfS).1
  rw [hmeasure] at hraw
  have hout : (T f : ℤ → ℂ) =
      vonMangoldtAverage integerShiftSystem c.value (f : ℤ → ℂ) (perturbationSuccessorScale N) -
        vonMangoldtAverage integerShiftSystem c.value (f : ℤ → ℂ) N := by
    funext x
    change integerKernelConvolutionRealExponentCLM p hp
        (vonMangoldtIntegerKernel c.value (perturbationSuccessorScale N)) f x -
      integerKernelConvolutionRealExponentCLM p hp (vonMangoldtIntegerKernel c.value N) f x = _
    rw [vonMangoldtSequenceOperator_apply, vonMangoldtSequenceOperator_apply]
    rfl
  have hraw' : eLpNorm
      (vonMangoldtAverage integerShiftSystem c.value (f : ℤ → ℂ) (perturbationSuccessorScale N) -
        vonMangoldtAverage integerShiftSystem c.value (f : ℤ → ℂ) N)
      (ENNReal.ofReal p) Measure.count ≤
    ENNReal.ofReal (2 * Real.log (2 * (N.val : ℝ)) / ((N.val : ℝ) + 1)) *
      eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
    simpa only [perturbationSuccessorScale, Nat.cast_add, Nat.cast_one] using hraw
  rw [← hout, eLpNorm_integerSequenceLp_eq hp0 ENNReal.ofReal_ne_top,
    eLpNorm_integerSequenceLp_eq hp0 ENNReal.ofReal_ne_top] at hraw'
  have hcoefeq : 2 * Real.log (2 * (N.val : ℝ)) / ((N.val : ℝ) + 1) =
      2 * (Real.log (2 * (N.val : ℝ)) / ((N.val : ℝ) + 1)) := by ring
  rw [hcoefeq, ← ENNReal.ofReal_mul hcoef] at hraw'
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hcoef (norm_nonneg f))).mp hraw'

#print axioms vonMangoldtSequenceOperator_increment_norm
end
end FractionalPrimes
