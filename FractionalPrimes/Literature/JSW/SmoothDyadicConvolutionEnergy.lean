module

public import FractionalPrimes.Literature.JSW.SmoothDyadicTranslationEnergy

/-! Probability smoothing of step functions: the exact integrated energy argument. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem dyadicStepProbabilitySmoothing_energy_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun t : ℝ => |t|) μ)
    {h : ℝ} (hh : 0 < h) {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (hgmeas : Measurable g)
    (hstep : ∀ j : ℤ, ∃ c : ℂ, ∀ x,
      x ∈ Set.Ico ((j : ℝ)*h) (((j+1 : ℤ) : ℝ)*h) → g x = c) :
    MemLp (fun x : ℝ => jswConvolution μ g x-g x) 2 volume ∧
    lpNorm (fun x : ℝ => jswConvolution μ g x-g x) 2 volume ^ 2 ≤
      (4/h * lpNorm g 2 volume ^ 2) * (∫ t : ℝ, |t| ∂μ) := by
  have hprod := integrable_translationDifference_energy μ hg
  have hmeas : StronglyMeasurable (fun x : ℝ => jswConvolution μ g x-g x) := by
    have hjoint : StronglyMeasurable (fun z : ℝ × ℝ => g (z.1-z.2)) :=
      (hgmeas.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
    exact hjoint.integral_prod_right'.sub hgmeas.stronglyMeasurable
  have hJensen : ∀ᵐ x ∂volume,
      ‖jswConvolution μ g x-g x‖^2 ≤ ∫ t, ‖g (x-t)-g x‖^2 ∂μ := by
    filter_upwards [hprod.prod_right_ae] with x hx
    have hdm : AEStronglyMeasurable (fun t : ℝ => g (x-t)-g x) μ := by
      exact ((hgmeas.comp (measurable_const.sub measurable_id)).sub measurable_const).stronglyMeasurable.aestronglyMeasurable
    have hdmem : MemLp (fun t : ℝ => g (x-t)-g x) 2 μ :=
      (memLp_two_iff_integrable_sq_norm hdm).2 hx
    have hdint : Integrable (fun t : ℝ => g (x-t)-g x) μ :=
      memLp_one_iff_integrable.mp (hdmem.mono_exponent (by norm_num))
    have hgint : Integrable (fun t : ℝ => g (x-t)) μ := by
      convert hdint.add (integrable_const (g x)) using 1
      ext t
      simp
    have hid : (∫ t, g (x-t)-g x ∂μ) = jswConvolution μ g x-g x := by
      rw [integral_sub hgint (integrable_const (g x))]
      simp [jswConvolution]
    rw [← hid]
    exact norm_integral_sq_le_integral_norm_sq_probability hdint hx
  have houtInt : Integrable (fun x : ℝ => ‖jswConvolution μ g x-g x‖^2) volume := by
    apply hprod.integral_prod_left.mono' (hmeas.norm.pow 2).aestronglyMeasurable
    filter_upwards [hJensen] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  have houtMem : MemLp (fun x : ℝ => jswConvolution μ g x-g x) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2 houtInt
  refine ⟨houtMem, ?_⟩
  rw [lpNorm_two_sq_eq_integral_norm_sq _ houtMem]
  calc
    _ ≤ ∫ x, ∫ t, ‖g (x-t)-g x‖^2 ∂μ ∂volume :=
      integral_mono_ae houtInt hprod.integral_prod_left hJensen
    _ = ∫ t, ∫ x, ‖g (x-t)-g x‖^2 ∂volume ∂μ := integral_integral_swap hprod
    _ ≤ _ := dyadicStepTranslation_integrated_energy_le μ hmoment hh hg hstep

#print axioms dyadicStepProbabilitySmoothing_energy_le
end
end FractionalPrimes.Literature.JSW
end
