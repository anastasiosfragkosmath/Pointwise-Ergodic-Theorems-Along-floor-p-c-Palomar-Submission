module

public import FractionalPrimes.Literature.JSW.SmoothDyadicKernelIntegrability

/-! Exact cancellation-kernel reconstruction of the actual smooth density convolution. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothPsiDensityConvolution
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (τ : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, Complex.ofReal (τ⁻¹*measureSplittingPsi σ ((x-y)/τ))*g y ∂volume

theorem smoothDyadicCancellationKernel_row_memLp_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (j : ℤ) (x : ℝ) :
    MemLp (smoothDyadicCancellationKernel σ τ j x) 2 volume := by
  apply memLp_two_of_band_bound (R := 2*τ+(2 : ℝ)^j) (c := x)
    (M := ((2 : ℝ)^j/τ^2)*lpNorm (deriv φ) ∞ volume)
    (mul_nonneg (div_nonneg (le_of_lt (zpow_pos (by norm_num) _)) (sq_nonneg _)) lpNorm_nonneg)
    ((smoothDyadicCancellationKernel_measurable σ τ j).comp measurable_prodMk_left)
    (smoothDyadicCancellationKernel_bound σ hτ j x)
  intro y hy
  exact smoothDyadicCancellationKernel_eq_zero hSupp hτ j x y
    (by simpa only [abs_sub_comm y x] using hy)

theorem smoothPsiDensityConvolution_dyadicDifference_eq_kernel
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (j : ℤ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (x : ℝ) :
    smoothPsiDensityConvolution σ τ (dyadicDifference j f) x =
      Schur.kernelApply volume (smoothDyadicCancellationKernel σ τ j) (dyadicDifference j f) x := by
  let g := dyadicDifference j f
  let a : ℝ → ℂ := fun y => Complex.ofReal
    (τ⁻¹*measureSplittingPsi σ ((x-smoothDyadicCellCenter j y)/τ))
  have hg := memLp_dyadicDifference_two_of_memLp hf j
  have hcent : Integrable (fun y => a y*g y) volume :=
    centeredPsiTest_mul_dyadicDifference_integrable hSupp hτ j x hf
  have hker : Integrable (fun y => smoothDyadicCancellationKernel σ τ j x y*g y) volume :=
    (smoothDyadicCancellationKernel_row_memLp_two hSupp hτ j x).integrable_mul hg
  have hzero : (∫ y, a y*g y ∂volume) = 0 :=
    integral_centeredPsi_mul_dyadicDifference_eq_zero τ j x
      (hf.locallyIntegrable (by norm_num)) hcent
  calc
    _ = ∫ y, (smoothDyadicCancellationKernel σ τ j x y*g y + a y*g y) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp [smoothDyadicCancellationKernel, a]
      push_cast
      ring
    _ = (∫ y, smoothDyadicCancellationKernel σ τ j x y*g y ∂volume) +
        ∫ y, a y*g y ∂volume := integral_add hker hcent
    _ = _ := by rw [hzero, add_zero]; rfl

theorem smoothDyadic_lowFrequency_density_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (j : ℤ) (hscale : (2 : ℝ)^j ≤ τ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (smoothPsiDensityConvolution σ τ (dyadicDifference j f)) 2 volume ∧
    lpNorm (smoothPsiDensityConvolution σ τ (dyadicDifference j f)) 2 volume ≤
      (8*((2 : ℝ)^j/τ)*lpNorm (deriv φ) ∞ volume) * lpNorm (dyadicDifference j f) 2 volume := by
  have hid : smoothPsiDensityConvolution σ τ (dyadicDifference j f) =
      Schur.kernelApply volume (smoothDyadicCancellationKernel σ τ j) (dyadicDifference j f) :=
    funext (smoothPsiDensityConvolution_dyadicDifference_eq_kernel hSupp hτ j hf)
  rw [hid]
  exact smoothDyadicCancellationKernel_lp_bound hSupp hτ j hscale
    (memLp_dyadicDifference_two_of_memLp hf j)

#print axioms smoothPsiDensityConvolution_dyadicDifference_eq_kernel
#print axioms smoothDyadic_lowFrequency_density_bound
end
end FractionalPrimes.Literature.JSW
end
