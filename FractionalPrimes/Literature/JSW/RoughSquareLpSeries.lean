module

public import FractionalPrimes.Literature.JSW.RoughSquareConvolutionResolution

/-! The Banach-valued series and exact norm bound obtained from localized
decay in the approved rough-square reconstruction. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def roughSquareSourceRawLpVector
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hp : 1 < p)
    (j : ℤ) (F : Finset ℤ) (f : Variation.LayerCakeInput (volume : Measure ℝ)) :
    Lp (EuclideanSpace ℂ {k : ℤ // k ∈ F}) (ENNReal.ofReal p) (volume : Measure ℝ) :=
  (roughSquareSourceRawVector_memLp hSupp hσ hb hp j F f).toLp
    (roughSquareSourceRawVector (σ := σ) hb j F f.1)

theorem roughSquareSourceRawLpVector_series_of_decay
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p δ C : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hp : 1 < p)
    (hδ : 0 < δ) (hC : 0 ≤ C)
    (F : Finset ℤ) (f : Variation.LayerCakeInput (volume : Measure ℝ))
    (hbound : ∀ j : ℤ,
      eLpNorm (roughSquareSourceRawVector (σ := σ) hb j F f.1) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * b ^ (-(δ * |(j : ℝ)|))) *
          eLpNorm f.1 (ENNReal.ofReal p) volume) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    Summable (fun j : ℤ => roughSquareSourceRawLpVector hSupp hσ hb hp j F f) ∧
      ‖∑' j : ℤ, roughSquareSourceRawLpVector hSupp hσ hb hp j F f‖ ≤
        C * ((1+b^(-δ))/(1-b^(-δ))) * lpNorm f.1 (ENNReal.ofReal p) volume := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hf := roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p)
  have hn (j : ℤ) : ‖roughSquareSourceRawLpVector hSupp hσ hb hp j F f‖ ≤
      (C * lpNorm f.1 (ENNReal.ofReal p) volume) * b ^ (-(δ * |(j : ℝ)|)) := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top) (hbound j)
    have hc : 0 ≤ C * b ^ (-(δ * |(j : ℝ)|)) :=
      mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h
    change lpNorm _ _ _ ≤ _ at h
    simpa only [roughSquareSourceRawLpVector, Lp.norm_toLp, toReal_eLpNorm,
      mul_assoc, mul_left_comm, mul_comm] using h
  have hsum := (roughSquareGeometric_decay_hasSum hb hδ).mul_left
    (C * lpNorm f.1 (ENNReal.ofReal p) volume)
  refine ⟨hsum.summable.of_norm_bounded hn, ?_⟩
  have h := tsum_of_norm_bounded hsum hn
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

#print axioms roughSquareSourceRawLpVector_series_of_decay
end
end FractionalPrimes.Literature.JSW
end
