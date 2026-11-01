module

public import FractionalPrimes.Literature.JSW.SmoothPsiScaledL1Translation
public import FractionalPrimes.Literature.JSW.SmoothConvolutionCancellation
public import FractionalPrimes.Literature.JSW.SmoothDyadicLowKernelIdentity

/-! Exact actual smooth convolution bounds for mean-zero dyadic atoms. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem smoothPsiDilatedDensity_integrable
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) : Integrable (smoothPsiDilatedDensity σ τ) volume := by
  have h := ((measureSplittingPsi_integrable σ hSupp).comp_mul_left'
    (inv_ne_zero hτ.ne')).const_mul τ⁻¹
  change Integrable (fun x : ℝ => τ⁻¹*measureSplittingPsi σ (x/τ)) volume
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem smoothPsiDensityConvolution_atom_L1_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (m j : ℤ) {u : ℝ → ℂ}
    (hu : Integrable u volume) (hmean : ∫ y, u y ∂volume = 0)
    (hsupp : ∀ y, y ∉ dyadicInterval m j → u y = 0) :
    Integrable (smoothPsiDensityConvolution σ τ u) volume ∧
    lpNorm (smoothPsiDensityConvolution σ τ u) 1 volume ≤
      ((2 : ℝ)^m/(2*τ))*lpNorm (deriv φ) 1 volume*lpNorm u 1 volume := by
  let K : ℝ → ℂ := fun x => Complex.ofReal (smoothPsiDilatedDensity σ τ x)
  let c : ℝ := ((j : ℝ)+1/2)*(2 : ℝ)^m
  have hK : Integrable K volume :=
    Complex.ofRealCLM.integrable_comp (smoothPsiDilatedDensity_integrable hSupp hτ)
  have hshift (y : ℝ) (hy : y ∈ dyadicInterval m j) :
      (∫ x : ℝ, ‖K (x-y)-K (x-c)‖ ∂volume) ≤
        ((2 : ℝ)^m/(2*τ))*lpNorm (deriv φ) 1 volume := by
    have hmod := smoothPsiDilatedDensity_L1_translation hSupp hτ y c
    have hd : |y-c| ≤ (2 : ℝ)^m/2 := by
      have h := smoothDyadicCellCenter_distance m y
      simpa only [smoothDyadicCellCenter, dyadicIntervalIndex_eq_of_mem hy] using h
    have heq (x : ℝ) : ‖K (x-y)-K (x-c)‖ =
        ‖smoothPsiDilatedDensity σ τ (x-y)-smoothPsiDilatedDensity σ τ (x-c)‖ := by
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

#print axioms smoothPsiDensityConvolution_atom_L1_bound
#print axioms smoothPsiDilatedDensity_integrable
end
end FractionalPrimes.Literature.JSW
end
