module

public import FractionalPrimes.Literature.Ergodic.PrimeAverageConvergenceConditional
public import FractionalPrimes.Literature.Ergodic.PrimeAverageEnumeration

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FractionalPrimes
noncomputable section

/-- All three paper formulations have one common limit once actual arithmetic
comparison decay is supplied. This retained input is not a claim that the
unconditional arithmetic theorem has been completed. -/
theorem primeConvergenceWithEnumeration_of_operatorDecay
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
        (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun J : Scale => enumeratedPrimeAverage S c.value f J x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun J : Scale => eLpNorm (enumeratedPrimeAverage S c.value f J - g)
        (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
  obtain ⟨g, hg, hAE, hLp, hPAE, hPLp⟩ :=
    primeAverageConvergence_of_operatorDecay hp c hdecay S f hf
  exact ⟨g, hg, hAE, hLp, hPAE, hPLp,
    (primeAverage_ae_tendsto_iff_enumerated S c.value f g).mp hPAE,
    (primeAverage_eLpNorm_tendsto_iff_enumerated S c.value f g
      (ENNReal.ofReal p)).mp hPLp⟩

#print axioms primeConvergenceWithEnumeration_of_operatorDecay
end
end FractionalPrimes
