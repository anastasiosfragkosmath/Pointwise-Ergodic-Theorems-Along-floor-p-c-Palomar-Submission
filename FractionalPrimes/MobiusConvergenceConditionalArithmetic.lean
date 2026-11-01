module
public import FractionalPrimes.Literature.Ergodic.MobiusDenseExtension
public import FractionalPrimes.ArithmeticCorrelationOperatorDecay
@[expose] public section

/-!
# Conditional arithmetic Möbius convergence

The checked Fourier/operator adapter turns the source DP and restricted PTW
tasks into the D=4 discrete operator-decay premise used by the Möbius dense
extension.  This file performs only that final composition.
-/

namespace FractionalPrimes

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Möbius averages converge almost everywhere and in Lp for every Lp input,
conditional on the exact source short-interval Dirichlet and restricted PTW
tasks. The only arithmetic input to the dense extension is the checked D=4
decay of the actual prime-comparison and Möbius convolution operators. -/
theorem mobiusAverageTendsToZero_of_OAISource_DP_PTW
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : FractionalExponent) {p : ℝ} (hp : 1 < p)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    (∀ᵐ x ∂S.μ, Tendsto
      (fun N : Scale => mobiusAverage S c.value f N x) atTop (𝓝 0)) ∧
    Tendsto (fun N : Scale =>
      eLpNorm (mobiusAverage S c.value f N) (ENNReal.ofReal p) S.μ)
      atTop (𝓝 0) := by
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨B, hB, hdecay⟩ :=
    arithmeticComparisonDiscreteOperatorDecayOf_OAISource_DP_PTW
      (p := 2) (c := c.value) (by norm_num) c.one_lt c.nonIntegral hDP hPTW
      (4 : ℝ) (by norm_num)
  have hoperatorD4 :
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ N : Scale, 3 ≤ N.1 →
          ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ))
              (primeComparisonIntegerKernel c.value N)‖ +
            ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal (2 : ℝ))
              (mobiusIntegerKernel c.value N)‖ ≤
                B * (Real.log (N.1 : ℝ)) ^ (-4 : ℝ) := by
    exact ⟨B, hB, fun N hN => hdecay N hN⟩
  exact mobiusAverage_tendsto_zero_of_discreteOperatorDecay
    S c hp f hf hoperatorD4

#print axioms mobiusAverageTendsToZero_of_OAISource_DP_PTW

end
end FractionalPrimes
