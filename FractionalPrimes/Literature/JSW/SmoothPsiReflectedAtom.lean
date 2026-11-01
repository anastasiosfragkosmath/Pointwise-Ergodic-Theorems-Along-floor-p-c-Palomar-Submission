module

public import FractionalPrimes.Literature.JSW.SmoothPsiReflectedTranslation

/-! Reflected smooth kernels satisfy the source atom cancellation bound. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothPsiReflectedConvolution
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (τ : ℝ) (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, Complex.ofReal (smoothPsiReflectedDensity σ τ (x-y))*u y ∂volume

theorem smoothPsiReflectedConvolution_atom_L1_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (m j : ℤ) {u : ℝ → ℂ}
    (hu : Integrable u volume) (hmean : ∫ y, u y ∂volume = 0)
    (hsupp : ∀ y, y ∉ dyadicInterval m j → u y = 0) :
    Integrable (smoothPsiReflectedConvolution σ τ u) volume ∧
    lpNorm (smoothPsiReflectedConvolution σ τ u) 1 volume ≤
      ((2 : ℝ)^m/(2*τ))*lpNorm (deriv φ) 1 volume*lpNorm u 1 volume := by
  let K : ℝ → ℂ := fun x => Complex.ofReal (smoothPsiReflectedDensity σ τ x)
  let c : ℝ := ((j : ℝ)+1/2)*(2 : ℝ)^m
  have hK : Integrable K volume :=
    Complex.ofRealCLM.integrable_comp (smoothPsiReflectedDensity_integrable hSupp hτ)
  have hshift (y : ℝ) (hy : y ∈ dyadicInterval m j) :
      (∫ x : ℝ, ‖K (x-y)-K (x-c)‖ ∂volume) ≤
        ((2 : ℝ)^m/(2*τ))*lpNorm (deriv φ) 1 volume := by
    have hmod := smoothPsiReflectedDensity_L1_translation hSupp hτ y c
    have hd : |y-c| ≤ (2 : ℝ)^m/2 := by
      have h := smoothDyadicCellCenter_distance m y
      simpa only [smoothDyadicCellCenter, dyadicIntervalIndex_eq_of_mem hy] using h
    have heq (x : ℝ) : ‖K (x-y)-K (x-c)‖ =
        ‖smoothPsiReflectedDensity σ τ (x-y)-smoothPsiReflectedDensity σ τ (x-c)‖ := by
      dsimp [K]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simp_rw [heq]
    rw [← lpNorm_one_eq_integral_norm hmod.1.aestronglyMeasurable]
    calc
      _ ≤ (|y-c|/τ)*lpNorm (deriv φ) 1 volume := hmod.2
      _ ≤ (((2 : ℝ)^m/2)/τ)*lpNorm (deriv φ) 1 volume :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hd hτ.le) lpNorm_nonneg
      _ = _ := by ring
  obtain ⟨hout,hbound⟩ := convolution_meanZero_integral_norm_le hK hu hmean hsupp hshift
  refine ⟨hout, ?_⟩
  change lpNorm (fun x : ℝ => ∫ y, K (x-y)*u y ∂volume) 1 volume ≤ _
  rw [lpNorm_one_eq_integral_norm hout.aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hu.aestronglyMeasurable]
  exact hbound


theorem smoothPsiReflectedConvolution_atom_smallScale_zero
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (m j : ℤ) (hscale : τ ≤ (2 : ℝ)^m)
    {u : ℝ → ℂ} (hsupp : ∀ y, y ∉ dyadicInterval m j → u y = 0)
    {x : ℝ} (hx : x ∉ dyadicNinefoldInterval m j) :
    smoothPsiReflectedConvolution σ τ u x = 0 := by
  change (∫ y, Complex.ofReal (smoothPsiReflectedDensity σ τ (x-y))*u y ∂volume) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  change Complex.ofReal (smoothPsiReflectedDensity σ τ (x-y))*u y = (0 : ℂ)
  by_cases hy : y ∈ dyadicInterval m j
  · have hz := smoothPsiDilatedDensity_eq_zero_of_far hSupp hτ
      (z := -(x-y)) (by simpa only [abs_neg] using
        smoothPsi_atom_smallScale_separation hτ m j hscale hx hy)
    simp only [smoothPsiReflectedDensity, hz, Complex.ofReal_zero, zero_mul]
  · simp [hsupp y hy]

#print axioms smoothPsiReflectedConvolution_atom_L1_bound
#print axioms smoothPsiReflectedConvolution_atom_smallScale_zero
end
end FractionalPrimes.Literature.JSW
end
