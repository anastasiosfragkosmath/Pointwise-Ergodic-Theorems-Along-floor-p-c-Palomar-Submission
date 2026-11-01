module

public import FractionalPrimes.Literature.Harmonic.UnweightedVariation
public import FractionalPrimes.Literature.Ergodic.WeightedVariationTransference

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
open Literature.Ergodic
noncomputable section
universe u

/-- Unconditional transfer of the completed ordinary-average variation bound. -/
theorem unweightedErgodicVariation
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r) (c : FractionalExponent) :
    ∃ C : NNReal, ∀ {X : Type u} [MeasurableSpace X] (S : InvertibleSystem X)
      (f : X → ℂ), MemLp f (ENNReal.ofReal p) S.μ →
      eLpNorm (rVariationFun r (fun N => unweightedAverage S c.value f N))
          (ENNReal.ofReal p) S.μ ≤
        ENNReal.ofNNReal C * eLpNorm f (ENNReal.ofReal p) S.μ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  obtain ⟨C, _hC, hbound⟩ := unweightedVariation hp hr c.value c.one_lt c.nonIntegral
  have hdisc (g : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) :
      eLpNorm (rVariationFun r (fun N =>
          weightedAverage integerShiftSystem c.value (fun _ => 1) (g : ℤ → ℂ) N))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofNNReal (Real.toNNReal C) * eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
    let G := generalLpToCountLp hp0 ENNReal.ofReal_ne_top g
    have hG : (G : ℤ → ℂ) = (g : ℤ → ℂ) :=
      funext (generalLpToCountLp_apply hp0 ENNReal.ofReal_ne_top g)
    have h := hbound G
    rw [hG] at h
    exact h
  refine ⟨Real.toNNReal C, fun {X} _ S f hf => ?_⟩
  exact transferWeightedFloorVariation hp (by linarith : 1 ≤ r) c.value
    (fun _ _ => 1) (Real.toNNReal C) hdisc S f hf

#print axioms unweightedErgodicVariation
end
end FractionalPrimes
