module

public import FractionalPrimes.Literature.Ergodic.PrimeVariationPerturbation
public import FractionalPrimes.Literature.Ergodic.WeightedVariationTransference

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
open Literature.Ergodic
noncomputable section
universe u

/-- The source system variation conclusion, with the remaining arithmetic
comparison input explicitly retained. The constant is chosen before the system. -/
theorem primePowerVariation_of_operatorDecay
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r) (c : FractionalExponent)
    (hdecay : letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ∀ D : ℝ, 0 < D → ∃ C : ℝ, ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
          (primeComparisonIntegerKernel c.value N)‖ ≤
            C * (Real.log (N.val : ℝ)) ^ (-D)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ {X : Type u} [MeasurableSpace X] (S : InvertibleSystem X)
        (f : X → ℂ), MemLp f (ENNReal.ofReal p) S.μ →
        eLpNorm (rVariationFun r (fun N => vonMangoldtAverage S c.value f N))
            (ENNReal.ofReal p) S.μ ≤
          C * eLpNorm f (ENNReal.ofReal p) S.μ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨C, hC, hdisc⟩ := vonMangoldtDiscreteVariation_of_operatorDecay hp hr c hdecay
  have hCcoe : ENNReal.ofNNReal C.toNNReal = C := ENNReal.coe_toNNReal hC
  have hdisc' : ∀ g : IntegerSequenceLp p,
      eLpNorm (rVariationFun r (fun N =>
          weightedAverage integerShiftSystem c.value
            (fun n => (vonMangoldtWeight n : ℂ)) (g : ℤ → ℂ) N))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofNNReal C.toNNReal * eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
    intro g
    rw [hCcoe]
    exact hdisc g
  refine ⟨C, hC, fun {X} _ S f hf => ?_⟩
  have h := transferWeightedFloorVariation hp (by linarith : 1 ≤ r) c.value
    (fun _ n => (vonMangoldtWeight n : ℂ)) C.toNNReal hdisc' S f hf
  rw [hCcoe] at h
  exact h

#print axioms primePowerVariation_of_operatorDecay
end
end FractionalPrimes
