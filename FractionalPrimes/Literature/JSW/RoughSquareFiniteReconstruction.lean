module

public import FractionalPrimes.Literature.JSW.RoughSquareLpCoordinates

/-! The exact geometric sum bound transferred to the finite cancellation
square vector by the checked reconstruction identity. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem roughSquareFinite_bound_of_decay
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p δ C : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hp : 1 < p)
    (hδ : 0 < δ) (hC : 0 ≤ C)
    (F : Finset ℤ) (f : Variation.LayerCakeInput (volume : Measure ℝ))
    (hbound : ∀ j : ℤ,
      eLpNorm (roughSquareSourceRawVector (σ := σ) hb j F f.1) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * b ^ (-(δ * |(j : ℝ)|))) *
          eLpNorm f.1 (ENNReal.ofReal p) volume) :
    lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
      (localizedSquareNuLpConvolution hSupp p b hp k.1
        ((roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p)).toLp f.1) : ℝ → ℂ) x))
      (ENNReal.ofReal p) volume ≤
        C * ((1+b^(-δ))/(1-b^(-δ))) * lpNorm f.1 (ENNReal.ofReal p) volume := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨hsum, hnorm⟩ := roughSquareSourceRawLpVector_series_of_decay
    hSupp hσ hb hp hδ hC F f hbound
  have hAE := roughSquareSourceRawLpVector_tsum_ae_eq hSupp hσ hb hp F f hsum
  have hn := congrArg ENNReal.toReal (eLpNorm_congr_ae hAE (p := ENNReal.ofReal p))
  rw [← Lp.norm_def] at hn
  change _ = lpNorm _ _ _ at hn
  rw [← hn]
  exact hnorm

theorem roughSquareFinite_bound_above_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q₀ p u : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hp : 2 < p) (hpu : p < u)
    (hregion : |u⁻¹ - (2 : ℝ)⁻¹| < (2*q₀)⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Finset ℤ)
      (f : Variation.LayerCakeInput (volume : Measure ℝ)),
      lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp p b (by linarith : 1 < p) k.1
          ((roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p)).toLp f.1) : ℝ → ℂ) x))
        (ENNReal.ofReal p) volume ≤ K * lpNorm f.1 (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hdecay⟩ := roughSquareNormalizedDecay_above_two
    hSupp hσ hb hβ hq₀ hMax hp hpu hregion
  let δ := min 1 β * weakTypeInterpolationTheta0 2 p u
  let A := weakTypeInterpolationConstant 2 p u *
    (roughSquareLocalizedAmplitude b β D) ^ weakTypeInterpolationTheta0 2 p u *
    (C * littlewoodPaleyUpperConstant u b (ne_of_gt (by linarith : 0 < b))) ^
      weakTypeInterpolationTheta1 2 p u
  have hδ : 0 < δ := mul_pos (lt_min (by norm_num) hβ)
    (roughSquareInterpolationWeights_pos (by norm_num : (1 : ℝ) ≤ 2) hp hpu).1
  have hI : 0 ≤ weakTypeInterpolationConstant 2 p u := by
    have hp0 : 0 < p := by linarith
    have hd0 : 0 < p - 2 := by linarith
    have hd1 : 0 < u - p := by linarith
    unfold weakTypeInterpolationConstant
    positivity
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hI
    (Real.rpow_nonneg (roughSquareLocalizedAmplitude_nonneg b β D) _))
    (Real.rpow_nonneg (mul_nonneg hC.le
      (roughSquareLittlewoodPaleyUpperConstant_nonneg (by linarith) hb)) _)
  have hq : b^(-δ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  refine ⟨A * ((1+b^(-δ))/(1-b^(-δ))), mul_nonneg hA
    (div_nonneg (by positivity) (by linarith)), ?_⟩
  intro F f
  exact roughSquareFinite_bound_of_decay hSupp hσ hb (by linarith : 1 < p)
    hδ hA F f (fun j => hdecay j F f)

theorem roughSquareFinite_bound_below_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q₀ p u : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hu : 1 < u) (hup : u < p) (hp : p < 2)
    (hregion : |u⁻¹ - (2 : ℝ)⁻¹| < (2*q₀)⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Finset ℤ)
      (f : Variation.LayerCakeInput (volume : Measure ℝ)),
      lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp p b (by linarith : 1 < p) k.1
          ((roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p)).toLp f.1) : ℝ → ℂ) x))
        (ENNReal.ofReal p) volume ≤ K * lpNorm f.1 (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hdecay⟩ := roughSquareNormalizedDecay_below_two
    hSupp hσ hb hβ hq₀ hMax hu hup hp hregion
  let δ := min 1 β * weakTypeInterpolationTheta1 u p 2
  let A := weakTypeInterpolationConstant u p 2 *
    (roughSquareLocalizedAmplitude b β D) ^ weakTypeInterpolationTheta1 u p 2 *
    (C * littlewoodPaleyUpperConstant u b (ne_of_gt (by linarith : 0 < b))) ^
      weakTypeInterpolationTheta0 u p 2
  have hδ : 0 < δ := mul_pos (lt_min (by norm_num) hβ)
    (roughSquareInterpolationWeights_pos hu.le hup hp).2
  have hI : 0 ≤ weakTypeInterpolationConstant u p 2 := by
    have hp0 : 0 < p := by linarith
    have hu0 : 0 < u := by linarith
    have hd0 : 0 < p - u := by linarith
    have hd1 : 0 < 2 - p := by linarith
    unfold weakTypeInterpolationConstant
    positivity
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hI
    (Real.rpow_nonneg (roughSquareLocalizedAmplitude_nonneg b β D) _))
    (Real.rpow_nonneg (mul_nonneg hC.le
      (roughSquareLittlewoodPaleyUpperConstant_nonneg_below hu (by linarith) hb)) _)
  have hq : b^(-δ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  refine ⟨A * ((1+b^(-δ))/(1-b^(-δ))), mul_nonneg hA
    (div_nonneg (by positivity) (by linarith)), ?_⟩
  intro F f
  exact roughSquareFinite_bound_of_decay hSupp hσ hb (by linarith : 1 < p)
    hδ hA F f (fun j => hdecay j F f)

#print axioms roughSquareFinite_bound_below_two
#print axioms roughSquareFinite_bound_of_decay
#print axioms roughSquareFinite_bound_above_two
end
end FractionalPrimes.Literature.JSW
end
