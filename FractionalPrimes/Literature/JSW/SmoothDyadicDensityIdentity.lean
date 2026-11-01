module

public import FractionalPrimes.Literature.JSW.SmoothDyadicLowKernelIdentity
public import FractionalPrimes.Literature.JSW.PositiveMaximalPsiAdapters
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The literal density/probability convolution identity at every positive scale. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem smoothPsiDensityConvolution_eq_probability_all
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {τ : ℝ} (hτ : 0 < τ) (g : ℝ → ℂ) (x : ℝ) :
    smoothPsiDensityConvolution σ τ g x =
      jswConvolution (Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)) g x := by
  let F : ℝ → ℂ := fun y => Complex.ofReal (τ⁻¹*measureSplittingPsi σ ((x-y)/τ))*g y
  have hchange : (∫ z : ℝ, F (x-τ*z) ∂volume) = τ⁻¹ • (∫ y, F y ∂volume) := by
    have hmul := Measure.integral_comp_mul_left (fun w : ℝ => F (x-w)) τ
    rw [integral_sub_left_eq_self F volume x] at hmul
    simpa only [abs_of_pos (inv_pos.mpr hτ)] using hmul
  have hlhs : (∫ z : ℝ, F (x-τ*z) ∂volume) =
      τ⁻¹ • (∫ z : ℝ, (measureSplittingPsi σ z : ℂ)*g (x-τ*z) ∂volume) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with z
    have harg : (x-(x-τ*z))/τ = z := by field_simp; ring
    dsimp only [F]
    rw [harg, Complex.ofReal_mul, Complex.real_smul]
    ring
  have hdensity : smoothPsiDensityConvolution σ τ g x =
      ∫ z : ℝ, (measureSplittingPsi σ z : ℂ)*g (x-τ*z) ∂volume := by
    have heq := congrArg (fun w : ℂ => τ • w) (hchange.symm.trans hlhs)
    change (∫ y, F y ∂volume) = _
    simpa only [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul] using heq
  rw [hdensity, jswConvolution, (measurableEmbedding_mulLeft₀ hτ.ne').integral_map]
  rw [initialSquarePsiProbabilityMeasure]
  have hψmeas : Measurable (fun z => ENNReal.ofReal (measureSplittingPsi σ z)) :=
    ENNReal.measurable_ofReal.comp (measureSplittingPsi_contDiff σ).continuous.measurable
  rw [integral_withDensity_eq_integral_toReal_smul hψmeas
    (ae_of_all volume fun z => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (measureSplittingPsi_nonneg σ z), Complex.real_smul]

/-- Compatibility wrapper for the existing measurable-input API. -/
theorem smoothPsiDensityConvolution_eq_probability
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {τ : ℝ} (hτ : 0 < τ) {g : ℝ → ℂ} (_hg : Measurable g) (x : ℝ) :
    smoothPsiDensityConvolution σ τ g x =
      jswConvolution (Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)) g x :=
  smoothPsiDensityConvolution_eq_probability_all hτ g x

#print axioms smoothPsiDensityConvolution_eq_probability_all
#print axioms smoothPsiDensityConvolution_eq_probability
end
end FractionalPrimes.Literature.JSW
end
