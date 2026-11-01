module

public import FractionalPrimes.Literature.JSW.SmoothPsiAtomL1
public import FractionalPrimes.Literature.JSW.PredictableTransformBound

/-! Exact small-scale and dyadic-average support facts for smooth atom errors. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem smoothPsiDilatedDensity_eq_zero_of_far
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ z : ℝ} (hτ : 0 < τ) (hfar : 2*τ < |z|) :
    smoothPsiDilatedDensity σ τ z = 0 := by
  have hout : z/τ ∉ Set.Icc (-(2 : ℝ)) 2 := by
    intro hi
    have h := abs_le.mpr hi
    rw [abs_div, abs_of_pos hτ] at h
    have := (div_le_iff₀ hτ).1 h
    linarith
  simp [smoothPsiDilatedDensity, measureSplittingPsi_eq_zero_of_not_mem_Icc σ hSupp hout]

theorem smoothPsi_atom_smallScale_separation
    {τ : ℝ} (hτ : 0 < τ) (m j : ℤ) (hscale : τ ≤ (2 : ℝ)^m)
    {x y : ℝ} (hx : x ∉ dyadicNinefoldInterval m j) (hy : y ∈ dyadicInterval m j) :
    2*τ < |x-y| := by
  have hℓ : 0 < (2 : ℝ)^m := zpow_pos (by norm_num) _
  have hy' : (j : ℝ)*(2 : ℝ)^m ≤ y ∧ y < ((j : ℝ)+1)*(2 : ℝ)^m := by
    simpa only [dyadicInterval, Set.mem_Ico, Int.cast_add, Int.cast_one] using hy
  have hx' : ¬ (((j : ℝ)-4)*(2 : ℝ)^m ≤ x ∧ x < ((j : ℝ)+5)*(2 : ℝ)^m) := by
    simpa only [dyadicNinefoldInterval, Set.mem_Ico, Int.cast_sub, Int.cast_add,
      Int.cast_ofNat] using hx
  rcases not_and_or.mp hx' with hleft | hright
  · have hlt : x < ((j : ℝ)-4)*(2 : ℝ)^m := lt_of_not_ge hleft
    have hxy : x-y < 0 := by nlinarith [hy'.1]
    rw [abs_of_neg hxy]
    nlinarith [hy'.1]
  · have hle : ((j : ℝ)+5)*(2 : ℝ)^m ≤ x := le_of_not_gt hright
    have hyx : 0 < x-y := by nlinarith [hy'.2]
    rw [abs_of_pos hyx]
    nlinarith [hy'.2]

theorem smoothPsiDensityConvolution_atom_smallScale_zero
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (m j : ℤ) (hscale : τ ≤ (2 : ℝ)^m)
    {u : ℝ → ℂ} (hsupp : ∀ y, y ∉ dyadicInterval m j → u y = 0)
    {x : ℝ} (hx : x ∉ dyadicNinefoldInterval m j) :
    smoothPsiDensityConvolution σ τ u x = 0 := by
  change (∫ y, Complex.ofReal (smoothPsiDilatedDensity σ τ (x-y))*u y ∂volume) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : y ∈ dyadicInterval m j
  · have hz := smoothPsiDilatedDensity_eq_zero_of_far hSupp hτ
      (smoothPsi_atom_smallScale_separation hτ m j hscale hx hy)
    simp [hz]
  · simp [hsupp y hy]

theorem dyadicAverage_meanZeroAtom_zero_off_ninefold
    {u : ℝ → ℂ} (hmean : ∫ x, u x ∂volume = 0)
    (m j : ℤ) (hsupp : ∀ y, y ∉ dyadicInterval m j → u y = 0)
    (n : ℤ) {x : ℝ} (hx : x ∉ dyadicNinefoldInterval m j) :
    dyadicAverage n u x = 0 :=
  dyadicAverage_meanZeroAtom_zero_off hmean m j hsupp n
    (fun hQ => hx (dyadicInterval_subset_ninefold m j hQ))

#print axioms smoothPsiDensityConvolution_atom_smallScale_zero
#print axioms dyadicAverage_meanZeroAtom_zero_off_ninefold
end
end FractionalPrimes.Literature.JSW
end
