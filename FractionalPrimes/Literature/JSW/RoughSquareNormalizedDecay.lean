module

public import FractionalPrimes.Literature.JSW.RoughSquareLpSeries

/-! The shift-independent source interpolation coefficient and its
geometric factor, in the exact form used by the Lp series theorem. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def roughSquareLocalizedAmplitude (b β D : ℝ) : ℝ :=
  (2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
    Real.sqrt (littlewoodPaleyNb b)

theorem roughSquareLocalizedAmplitude_nonneg (b β D : ℝ) :
    0 ≤ roughSquareLocalizedAmplitude b β D :=
  mul_nonneg (mul_nonneg (by nlinarith [Real.pi_pos, abs_nonneg D])
    (le_trans (by norm_num) (le_max_left 2 _))) (Real.sqrt_nonneg _)

theorem roughSquareNormalizedDecay_above_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q₀ p u : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hp : 2 < p) (hpu : p < u)
    (hregion : |u⁻¹ - (2 : ℝ)⁻¹| < (2*q₀)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (F : Finset ℤ)
      (f : Variation.LayerCakeInput (volume : Measure ℝ)),
      eLpNorm (roughSquareSourceRawVector (σ := σ) hb j F f.1)
        (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((weakTypeInterpolationConstant 2 p u *
        (roughSquareLocalizedAmplitude b β D) ^ weakTypeInterpolationTheta0 2 p u *
        (C * littlewoodPaleyUpperConstant u b (ne_of_gt (by linarith : 0 < b))) ^
          weakTypeInterpolationTheta1 2 p u) *
        b ^ (-(min 1 β * weakTypeInterpolationTheta0 2 p u * |(j : ℝ)|))) *
          eLpNorm f.1 (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hbound⟩ := roughSquareSourceRawVector_interpolation_above_two
    hSupp hσ hb hβ hq₀ hMax hp hpu hregion
  refine ⟨C, hC, ?_⟩
  intro j F f
  have h := hbound j F f
  rw [eLpNorm_norm _ (roughSquareSourceRawVector_memLp hSupp hσ hb
    (by linarith : 1 < p) j F f).aestronglyMeasurable] at h
  let A := roughSquareLocalizedAmplitude b β D
  let B := C * littlewoodPaleyUpperConstant u b (ne_of_gt (by linarith : 0 < b))
  let I := weakTypeInterpolationConstant 2 p u
  let θ₀ := weakTypeInterpolationTheta0 2 p u
  let θ₁ := weakTypeInterpolationTheta1 2 p u
  change eLpNorm _ _ _ ≤ ENNReal.ofReal
    (I * (A * b ^ (-(min 1 β * |(j : ℝ)|))) ^ θ₀ * B ^ θ₁) *
      eLpNorm f.1 (ENNReal.ofReal p) volume at h
  have heq : I * (A * b ^ (-(min 1 β * |(j : ℝ)|))) ^ θ₀ * B ^ θ₁ =
      (I * A ^ θ₀ * B ^ θ₁) * b ^ (-(min 1 β * θ₀ * |(j : ℝ)|)) := by
    rw [roughSquareLocalizedDecay_rpow (roughSquareLocalizedAmplitude_nonneg b β D)
      (by linarith : 0 < b)]
    ring
  rw [heq] at h
  exact h

theorem roughSquareSourceRawLpVector_summable_above_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q₀ p u : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hp : 2 < p) (hpu : p < u)
    (hregion : |u⁻¹ - (2 : ℝ)⁻¹| < (2*q₀)⁻¹)
    (F : Finset ℤ) (f : Variation.LayerCakeInput (volume : Measure ℝ)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ p)⟩
    Summable (fun j : ℤ => roughSquareSourceRawLpVector hSupp hσ hb
      (by linarith : 1 < p) j F f) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ p)⟩
  obtain ⟨C, hC, hdecay⟩ := roughSquareNormalizedDecay_above_two
    hSupp hσ hb hβ hq₀ hMax hp hpu hregion
  have hθ := (roughSquareInterpolationWeights_pos (by norm_num : (1 : ℝ) ≤ 2) hp hpu).1
  have hδ : 0 < min 1 β * weakTypeInterpolationTheta0 2 p u :=
    mul_pos (lt_min (by norm_num) hβ) hθ
  have hI : 0 ≤ weakTypeInterpolationConstant 2 p u := by
    have h0 : 0 < p := by linarith
    have hd0 : 0 < p - 2 := by linarith
    have hd1 : 0 < u - p := by linarith
    unfold weakTypeInterpolationConstant
    positivity
  exact (roughSquareSourceRawLpVector_series_of_decay hSupp hσ hb
    (by linarith : 1 < p) hδ
    (mul_nonneg (mul_nonneg hI (Real.rpow_nonneg
      (roughSquareLocalizedAmplitude_nonneg b β D) _))
      (Real.rpow_nonneg (mul_nonneg hC.le
        (roughSquareLittlewoodPaleyUpperConstant_nonneg (by linarith) hb)) _))
    F f (fun j => hdecay j F f)).1

theorem roughSquareNormalizedDecay_below_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q₀ p u : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hu : 1 < u) (hup : u < p) (hp : p < 2)
    (hregion : |u⁻¹ - (2 : ℝ)⁻¹| < (2*q₀)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (F : Finset ℤ)
      (f : Variation.LayerCakeInput (volume : Measure ℝ)),
      eLpNorm (roughSquareSourceRawVector (σ := σ) hb j F f.1)
        (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((weakTypeInterpolationConstant u p 2 *
        (roughSquareLocalizedAmplitude b β D) ^ weakTypeInterpolationTheta1 u p 2 *
        (C * littlewoodPaleyUpperConstant u b (ne_of_gt (by linarith : 0 < b))) ^
          weakTypeInterpolationTheta0 u p 2) *
        b ^ (-(min 1 β * weakTypeInterpolationTheta1 u p 2 * |(j : ℝ)|))) *
          eLpNorm f.1 (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hbound⟩ := roughSquareSourceRawVector_interpolation_below_two
    hSupp hσ hb hβ hq₀ hMax hu hup hp hregion
  refine ⟨C, hC, ?_⟩
  intro j F f
  have h := hbound j F f
  rw [eLpNorm_norm _ (roughSquareSourceRawVector_memLp hSupp hσ hb
    (by linarith : 1 < p) j F f).aestronglyMeasurable] at h
  let A := roughSquareLocalizedAmplitude b β D
  let B := C * littlewoodPaleyUpperConstant u b (ne_of_gt (by linarith : 0 < b))
  let I := weakTypeInterpolationConstant u p 2
  let θ₀ := weakTypeInterpolationTheta0 u p 2
  let θ₁ := weakTypeInterpolationTheta1 u p 2
  change eLpNorm _ _ _ ≤ ENNReal.ofReal
    (I * B ^ θ₀ * (A * b ^ (-(min 1 β * |(j : ℝ)|))) ^ θ₁) *
      eLpNorm f.1 (ENNReal.ofReal p) volume at h
  have heq : I * B ^ θ₀ * (A * b ^ (-(min 1 β * |(j : ℝ)|))) ^ θ₁ =
      (I * A ^ θ₁ * B ^ θ₀) * b ^ (-(min 1 β * θ₁ * |(j : ℝ)|)) := by
    rw [roughSquareLocalizedDecay_rpow (roughSquareLocalizedAmplitude_nonneg b β D)
      (by linarith : 0 < b)]
    ring
  rw [heq] at h
  exact h

theorem roughSquareSourceRawLpVector_summable_below_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q₀ p u : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hu : 1 < u) (hup : u < p) (hp : p < 2)
    (hregion : |u⁻¹ - (2 : ℝ)⁻¹| < (2*q₀)⁻¹)
    (F : Finset ℤ) (f : Variation.LayerCakeInput (volume : Measure ℝ)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ p)⟩
    Summable (fun j : ℤ => roughSquareSourceRawLpVector hSupp hσ hb
      (by linarith : 1 < p) j F f) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ p)⟩
  obtain ⟨C, hC, hdecay⟩ := roughSquareNormalizedDecay_below_two
    hSupp hσ hb hβ hq₀ hMax hu hup hp hregion
  have hθ := (roughSquareInterpolationWeights_pos hu.le hup hp).2
  have hδ : 0 < min 1 β * weakTypeInterpolationTheta1 u p 2 :=
    mul_pos (lt_min (by norm_num) hβ) hθ
  have hI : 0 ≤ weakTypeInterpolationConstant u p 2 := by
    have h0 : 0 < p := by linarith
    have hu0 : 0 < u := by linarith
    have hd0 : 0 < p - u := by linarith
    have hd1 : 0 < 2 - p := by linarith
    unfold weakTypeInterpolationConstant
    positivity
  exact (roughSquareSourceRawLpVector_series_of_decay hSupp hσ hb
    (by linarith : 1 < p) hδ
    (mul_nonneg (mul_nonneg hI (Real.rpow_nonneg
      (roughSquareLocalizedAmplitude_nonneg b β D) _))
      (Real.rpow_nonneg (mul_nonneg hC.le
        (roughSquareLittlewoodPaleyUpperConstant_nonneg_below hu (by linarith) hb)) _))
    F f (fun j => hdecay j F f)).1

#print axioms roughSquareSourceRawLpVector_summable_below_two
#print axioms roughSquareNormalizedDecay_below_two
#print axioms roughSquareSourceRawLpVector_summable_above_two
#print axioms roughSquareNormalizedDecay_above_two

end
end FractionalPrimes.Literature.JSW
end
