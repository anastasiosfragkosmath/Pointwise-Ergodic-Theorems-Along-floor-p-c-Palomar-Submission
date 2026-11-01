module

public import FractionalPrimes.Literature.JSW.DyadicStepTranslation
public import FractionalPrimes.Literature.JSW.PositiveVectorL2

/-! Integrated translation energies for the smooth/dyadic high-frequency branch. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem integrable_translationDifference_energy
    (μ : Measure ℝ) [IsFiniteMeasure μ] {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) :
    Integrable (fun z : ℝ × ℝ => ‖g (z.1-z.2)-g z.1‖^2) (volume.prod μ) := by
  have hfst : MemLp (fun z : ℝ × ℝ => g z.1) 2 (volume.prod μ) := hg.comp_fst μ
  have hshift : MemLp (fun z : ℝ × ℝ => g (z.1-z.2)) 2 (volume.prod μ) :=
    hfst.comp_measurePreserving (measurePreserving_sub_prod volume μ)
  exact (hshift.sub hfst).integrable_norm_pow (by norm_num)

theorem dyadicStepTranslation_energy_le
    {h : ℝ} (hh : 0 < h) {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (hstep : ∀ j : ℤ, ∃ c : ℂ, ∀ x,
      x ∈ Set.Ico ((j : ℝ)*h) (((j+1 : ℤ) : ℝ)*h) → g x = c)
    (t : ℝ) :
    (∫ x : ℝ, ‖g (x-t)-g x‖^2 ∂volume) ≤
      4 * (|t|/h) * lpNorm g 2 volume ^ 2 := by
  have hshift := hg.comp_measurePreserving (measurePreserving_sub_right volume t)
  have hid := lpNorm_two_sq_eq_integral_norm_sq (fun x : ℝ => g (x-t)-g x) (hshift.sub hg)
  rw [← hid]
  have hbound := dyadicStepTranslation hh hg hstep t
  have hs := pow_le_pow_left₀ lpNorm_nonneg hbound 2
  have hmin : 0 ≤ min 1 (|t|/h) := le_min (by norm_num) (div_nonneg (abs_nonneg _) hh.le)
  rw [mul_pow, mul_pow, Real.sq_sqrt hmin] at hs
  calc
    _ ≤ 4 * min 1 (|t|/h) * lpNorm g 2 volume ^ 2 := by nlinarith [hs]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)) (sq_nonneg _)

theorem dyadicStepTranslation_integrated_energy_le
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hmoment : Integrable (fun t : ℝ => |t|) μ)
    {h : ℝ} (hh : 0 < h) {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (hstep : ∀ j : ℤ, ∃ c : ℂ, ∀ x,
      x ∈ Set.Ico ((j : ℝ)*h) (((j+1 : ℤ) : ℝ)*h) → g x = c) :
    (∫ t : ℝ, ∫ x : ℝ, ‖g (x-t)-g x‖^2 ∂volume ∂μ) ≤
      (4/h * lpNorm g 2 volume ^ 2) * (∫ t : ℝ, |t| ∂μ) := by
  have henergy := integrable_translationDifference_energy μ hg
  have hinner : Integrable (fun t : ℝ => ∫ x : ℝ, ‖g (x-t)-g x‖^2 ∂volume) μ :=
    henergy.integral_prod_right
  have hdom := hmoment.const_mul (4/h * lpNorm g 2 volume ^ 2)
  calc
    _ ≤ ∫ t : ℝ, (4/h * lpNorm g 2 volume ^ 2) * |t| ∂μ := by
      apply integral_mono_ae hinner hdom
      filter_upwards [] with t
      convert dyadicStepTranslation_energy_le hh hg hstep t using 1 <;> ring
    _ = _ := integral_const_mul _ _

#print axioms dyadicStepTranslation_integrated_energy_le
#print axioms integrable_translationDifference_energy
#print axioms dyadicStepTranslation_energy_le
end
end FractionalPrimes.Literature.JSW
end
