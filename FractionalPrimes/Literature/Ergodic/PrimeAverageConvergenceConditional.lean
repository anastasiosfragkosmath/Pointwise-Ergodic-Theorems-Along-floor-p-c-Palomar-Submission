module

public import FractionalPrimes.Literature.Ergodic.PrimeOnlyConvergence
public import FractionalPrimes.Literature.Ergodic.WeightedPrimeCommonLimit
public import FractionalPrimes.Literature.Ergodic.PrimePointwiseNormalization
public import FractionalPrimes.Literature.Ergodic.PrimeLpNormalization
public import FractionalPrimes.Literature.Ergodic.PrimePsiFromOperatorDecay

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FractionalPrimes
noncomputable section

/-- The actual prime and von Mangoldt averages converge in both modes to
one common limit, with the remaining arithmetic inputs explicitly retained. -/
theorem primeAverageConvergence_of_operatorDecay_and_psi
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
    (hdecay : letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ∀ D : ℝ, 0 < D → ∃ C : ℝ, ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
          (primeComparisonIntegerKernel c.value N)‖ ≤
            C * (Real.log (N.val : ℝ)) ^ (-D))
    (hpsi : Tendsto (fun N : ℕ => paperPsi N / (N : ℝ)) atTop (𝓝 1))
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun N : Scale => vonMangoldtAverage S c.value f N x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun N : Scale => eLpNorm (vonMangoldtAverage S c.value f N - g)
        (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun n : ℕ => primeAverage S c.value f (n + 2) (by omega) x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun n : ℕ => eLpNorm (primeAverage S c.value f (n + 2) (by omega) - g)
        (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨g, hg, hLAE, hLLp⟩ := primeOnlyAverageConvergence_of_operatorDecay hp c hdecay S f hf
  have hpi : Tendsto (fun N : ℕ =>
      (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    have h := (primeCountingNormalization_of_paperPsi_div_tendsto_one hpsi).2.2.1
    simpa only [paperPi, Nat.floor_natCast] using h
  have hA := vonMangoldt_tendsto_of_primeOnly_tendsto S c.value hp f g hf hLAE hLLp
  exact ⟨g, hg, hA.1, hA.2,
    primeAverage_ae_tendsto_of_logWeighted S c.value f g hLAE hpi,
    primeAverage_eLpNorm_tendsto_of_logWeighted S c.value f g hf hg hLLp hpi⟩

#print axioms primeAverageConvergence_of_operatorDecay_and_psi

/-- Comparison decay alone supplies the numerical normalization and the
common a.e. and Lp limit for the actual weighted and usual prime averages. -/
theorem primeAverageConvergence_of_operatorDecay
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
    (hdecay : letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ∀ D : ℝ, 0 < D → ∃ C : ℝ, ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
          (primeComparisonIntegerKernel c.value N)‖ ≤
            C * (Real.log (N.val : ℝ)) ^ (-D))
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun N : Scale => vonMangoldtAverage S c.value f N x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun N : Scale => eLpNorm (vonMangoldtAverage S c.value f N - g)
        (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun n : ℕ => primeAverage S c.value f (n + 2) (by omega) x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun n : ℕ => eLpNorm (primeAverage S c.value f (n + 2) (by omega) - g)
        (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
  exact primeAverageConvergence_of_operatorDecay_and_psi hp c hdecay
    (paperPsi_div_tendsto_one_of_operatorDecay hp c.value hdecay) S f hf

#print axioms primeAverageConvergence_of_operatorDecay
end
end FractionalPrimes
