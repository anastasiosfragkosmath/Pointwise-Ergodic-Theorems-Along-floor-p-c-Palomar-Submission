module

public import FractionalPrimes.Literature.JSW.SmoothDyadicKernelSupport
public import FractionalPrimes.Literature.JSW.SchurKernel

/-! Exact finite-band mass estimates for the source low-frequency kernel. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem lintegral_enorm_le_of_band_bound
    {F : ℝ → ℂ} {R M c : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hbound : ∀ x, ‖F x‖ ≤ M) (hzero : ∀ x, R < |x-c| → F x = 0) :
    (∫⁻ x, ‖F x‖ₑ ∂volume) ≤ ENNReal.ofReal (2*R*M) := by
  classical
  have hpoint (x : ℝ) : ‖F x‖ₑ ≤
      Set.indicator (Set.Icc (c-R) (c+R)) (fun _ => ENNReal.ofReal M) x := by
    by_cases hx : x ∈ Set.Icc (c-R) (c+R)
    · rw [Set.indicator_of_mem hx, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hbound x)
    · have hfar : R < |x-c| := by
        apply lt_of_not_ge
        intro habs
        apply hx
        rcases abs_le.mp habs with ⟨ha,hb⟩
        constructor <;> linarith
      simp [Set.indicator_of_notMem hx, hzero x hfar]
  calc
    _ ≤ ∫⁻ x, Set.indicator (Set.Icc (c-R) (c+R))
        (fun _ => ENNReal.ofReal M) x ∂volume := lintegral_mono hpoint
    _ = ENNReal.ofReal M * volume (Set.Icc (c-R) (c+R)) :=
      by rw [lintegral_indicator_const measurableSet_Icc]
    _ = _ := by
      rw [Real.volume_Icc, ← ENNReal.ofReal_mul hM]
      congr 1
      ring

theorem smoothDyadicCancellationKernel_masses
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (j : ℤ) (hscale : (2 : ℝ)^j ≤ τ) :
    let C := ENNReal.ofReal (8*((2 : ℝ)^j/τ)*lpNorm (deriv φ) ∞ volume)
    (∀ x, (∫⁻ y, ‖smoothDyadicCancellationKernel σ τ j x y‖ₑ ∂volume) ≤ C) ∧
    (∀ y, (∫⁻ x, ‖smoothDyadicCancellationKernel σ τ j x y‖ₑ ∂volume) ≤ C) := by
  let M := ((2 : ℝ)^j/τ^2)*lpNorm (deriv φ) ∞ volume
  let R := 2*τ+(2 : ℝ)^j
  have hp : 0 < (2 : ℝ)^j := zpow_pos (by norm_num) _
  have hM : 0 ≤ M := mul_nonneg (div_nonneg hp.le (sq_nonneg _)) lpNorm_nonneg
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hconst : 2*R*M ≤ 8*((2 : ℝ)^j/τ)*lpNorm (deriv φ) ∞ volume := by
    have hRle : 2*R ≤ 6*τ := by dsimp [R]; linarith
    calc
      _ ≤ (6*τ)*M := mul_le_mul_of_nonneg_right hRle hM
      _ = 6*((2 : ℝ)^j/τ)*lpNorm (deriv φ) ∞ volume := by
        dsimp [M]
        field_simp
      _ ≤ _ := by
        have hnonneg := mul_nonneg (div_nonneg hp.le hτ.le)
          (lpNorm_nonneg (f := deriv φ) (p := ∞) (μ := volume))
        nlinarith
  constructor
  · intro x
    apply le_trans (lintegral_enorm_le_of_band_bound (c := x) hR hM
      (fun y => smoothDyadicCancellationKernel_bound σ hτ j x y) ?_)
      (ENNReal.ofReal_le_ofReal hconst)
    intro y hy
    exact smoothDyadicCancellationKernel_eq_zero hSupp hτ j x y (by simpa [R, abs_sub_comm] using hy)
  · intro y
    apply le_trans (lintegral_enorm_le_of_band_bound (c := y) hR hM
      (fun x => smoothDyadicCancellationKernel_bound σ hτ j x y) ?_)
      (ENNReal.ofReal_le_ofReal hconst)
    intro x hx
    exact smoothDyadicCancellationKernel_eq_zero hSupp hτ j x y hx

theorem smoothDyadicCancellationKernel_lp_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (j : ℤ) (hscale : (2 : ℝ)^j ≤ τ)
    {g : ℝ → ℂ} (hg : MemLp g 2 volume) :
    MemLp (Schur.kernelApply volume (smoothDyadicCancellationKernel σ τ j) g) 2 volume ∧
    lpNorm (Schur.kernelApply volume (smoothDyadicCancellationKernel σ τ j) g) 2 volume ≤
      (8*((2 : ℝ)^j/τ)*lpNorm (deriv φ) ∞ volume) * lpNorm g 2 volume := by
  let C := 8*((2 : ℝ)^j/τ)*lpNorm (deriv φ) ∞ volume
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num)
    (div_nonneg (le_of_lt (zpow_pos (by norm_num) _)) hτ.le)) lpNorm_nonneg
  obtain ⟨hrow,hcol⟩ := smoothDyadicCancellationKernel_masses hSupp hτ j hscale
  have hbound := Schur.eLpNorm_kernelApply_le
    (smoothDyadicCancellationKernel_measurable σ τ j) hrow hcol
    hg.aestronglyMeasurable.aemeasurable
  change eLpNorm (Schur.kernelApply volume (smoothDyadicCancellationKernel σ τ j) g) 2 volume ≤
    ENNReal.ofReal C * eLpNorm g 2 volume at hbound
  have hfinite := ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := C)) hg.eLpNorm_lt_top
  refine ⟨lt_of_le_of_lt hbound hfinite, ?_⟩
  have ht := ENNReal.toReal_mono hfinite.ne hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at ht
  exact ht

#print axioms smoothDyadicCancellationKernel_lp_bound
#print axioms smoothDyadicCancellationKernel_masses
end
end FractionalPrimes.Literature.JSW
end
