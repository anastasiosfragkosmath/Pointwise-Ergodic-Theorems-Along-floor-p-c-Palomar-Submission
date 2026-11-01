module

public import FractionalPrimes.Literature.Ergodic.PrimeVariationSystem
public import FractionalPrimes.VariationConvergence

@[expose] public section
open MeasureTheory
open scoped ENNReal Topology
namespace FractionalPrimes
open Literature.Ergodic
noncomputable section

/-- Both convergence modes of the actual von Mangoldt averages, with the
remaining arithmetic comparison input explicit. -/
theorem vonMangoldtAverageConvergence_of_operatorDecay
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
    (hdecay : letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ∀ D : ℝ, 0 < D → ∃ C : ℝ, ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
          (primeComparisonIntegerKernel c.value N)‖ ≤
            C * (Real.log (N.val : ℝ)) ^ (-D))
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∃ g : X → ℂ, StronglyMeasurable g ∧ MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Filter.Tendsto
        (fun n : ℕ => vonMangoldtAverage S c.value f ⟨n + 1, by omega⟩ x)
        Filter.atTop (𝓝 (g x))) ∧
      Filter.Tendsto (fun n : ℕ => eLpNorm
        (fun x => vonMangoldtAverage S c.value f ⟨n + 1, by omega⟩ x - g x)
          (ENNReal.ofReal p) S.μ) Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := primePowerVariation_of_operatorDecay hp (by norm_num : (2 : ℝ) < 3)
    c hdecay
  have hV : MemLp (rVariationFun 3 (fun N => vonMangoldtAverage S c.value f N))
      (ENNReal.ofReal p) S.μ :=
    memLp_iff.mpr ((hbound S f hf).trans_lt (ENNReal.mul_lt_top hC.lt_top hf.eLpNorm_lt_top))
  have hFmeas (N : Scale) : AEStronglyMeasurable (vonMangoldtAverage S c.value f N) S.μ := by
    have h := aemeasurable_finiteKernelSystemOperator S
      (weightedFloorKernelFinsupp c.value N (fun n => (vonMangoldtWeight n : ℂ))) f
      hf.aestronglyMeasurable
    rw [weightedFloorKernelFinsupp_systemOperator] at h
    exact h.aestronglyMeasurable
  have hFone : MemLp (vonMangoldtAverage S c.value f ⟨1, by omega⟩)
      (ENNReal.ofReal p) S.μ := by
    rw [vonMangoldtAverage_one]
    exact MemLp.zero
  exact exists_limit_and_tendsto_eLpNorm_of_rVariationFun_memLp hp.le
    (by norm_num : (0 : ℝ) < 3) (fun N => vonMangoldtAverage S c.value f N) hFmeas hV hFone

#print axioms vonMangoldtAverageConvergence_of_operatorDecay
end
end FractionalPrimes
