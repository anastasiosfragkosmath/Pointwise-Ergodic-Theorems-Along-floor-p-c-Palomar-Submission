module
public import FractionalPrimes.ArithmeticCorrelationOperatorDecay
public import FractionalPrimes.Literature.Ergodic.PrimeConvergenceWithEnumeration
@[expose] public section

/-!
# Conditional prime convergence from the arithmetic DP/PTW inputs

The whole-prefix Fourier estimate gives a sum of the prime and Möbius
operator norms.  The prime convergence API requires only the prime summand,
which follows by nonnegativity of the other norm.  The analytic Dirichlet and
restricted PTW task premises remain explicit throughout.
-/

namespace FractionalPrimes

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Conditional common-limit convergence of the von Mangoldt, ordinary prime,
and enumerated-prime averages from the exact source DP and restricted PTW
tasks.  No unconditional arithmetic input is asserted here. -/
theorem primeConvergenceWithEnumerationOf_OAISource_DP_PTW
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask)
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun N : Scale =>
        vonMangoldtAverage S c.value f N x) atTop (𝓝 (g x))) ∧
      Tendsto (fun N : Scale =>
        eLpNorm (vonMangoldtAverage S c.value f N - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun n : ℕ =>
        primeAverage S c.value f (n + 2) (by omega) x) atTop (𝓝 (g x))) ∧
      Tendsto (fun n : ℕ =>
        eLpNorm (primeAverage S c.value f (n + 2) (by omega) - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun J : Scale =>
        enumeratedPrimeAverage S c.value f J x) atTop (𝓝 (g x))) ∧
      Tendsto (fun J : Scale =>
        eLpNorm (enumeratedPrimeAverage S c.value f J - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
  have hprimeDecay :
      letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ∀ D : ℝ, 0 < D → ∃ C : ℝ, ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
          (primeComparisonIntegerKernel c.value N)‖ ≤
            C * (Real.log (N.val : ℝ)) ^ (-D) := by
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    intro D hD
    obtain ⟨C, hC, hbound⟩ :=
      arithmeticComparisonDiscreteOperatorDecayOf_OAISource_DP_PTW
        (p := p) (c := c.value) hp c.one_lt c.nonIntegral hDP hPTW D hD
    refine ⟨C, ?_⟩
    intro N hN
    have hsum := hbound N hN
    exact le_trans (le_add_of_nonneg_right (norm_nonneg _)) hsum
  exact primeConvergenceWithEnumeration_of_operatorDecay hp c hprimeDecay S f hf

#print axioms primeConvergenceWithEnumerationOf_OAISource_DP_PTW

end
end FractionalPrimes
