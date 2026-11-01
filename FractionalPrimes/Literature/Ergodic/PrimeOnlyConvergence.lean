module

public import FractionalPrimes.Literature.Ergodic.VonMangoldtConvergence
public import FractionalPrimes.Literature.Ergodic.ScaleConvergenceBridge
public import FractionalPrimes.Literature.Ergodic.HigherPrimePowersVanish

@[expose] public section
open MeasureTheory
open scoped ENNReal Topology
namespace FractionalPrimes
noncomputable section

/-- Removing higher prime powers preserves both modes and the common limit.
This retains exactly the remaining arithmetic comparison-decay premise. -/
theorem primeOnlyAverageConvergence_of_operatorDecay
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
    (hdecay : letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ∀ D : ℝ, 0 < D → ∃ C : ℝ, ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
          (primeComparisonIntegerKernel c.value N)‖ ≤
            C * (Real.log (N.val : ℝ)) ^ (-D))
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Filter.Tendsto
        (fun N : Scale => paperPrimeOnlyPart S c.value f N x)
        Filter.atTop (𝓝 (g x))) ∧
      Filter.Tendsto (fun N : Scale => eLpNorm
        (paperPrimeOnlyPart S c.value f N - g)
          (ENNReal.ofReal p) S.μ) Filter.atTop (𝓝 0) := by
  obtain ⟨g, _hgStrong, hgMem, hAE, hLp⟩ :=
    vonMangoldtAverageConvergence_of_operatorDecay hp c hdecay S f hf
  apply paperPrimeOnlyPart_converges_of_vonMangoldtAverage_converges S c p hp f hf
  refine ⟨g, hgMem, ?_, ?_⟩
  · filter_upwards [hAE] with x hx
    exact tendsto_scale_of_natSucc _ hx
  · apply tendsto_scale_of_natSucc
    simpa only [Pi.sub_def] using hLp

#print axioms primeOnlyAverageConvergence_of_operatorDecay
end
end FractionalPrimes
