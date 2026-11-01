module

public import FractionalPrimes.Literature.JSW.FiniteJumpLpAssembly
public import FractionalPrimes.Literature.Variation.WeakVariationOfJump

/-! Exact equivalence of the real finite jump control and the source ENNReal jump moments. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
open FractionalPrimes.Literature.Variation
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem jumpAmplitude_eq_ofReal_finiteJumpControl
    {I : Type*} [LinearOrder I] [Fintype I]
    (F : I → ℝ → ℂ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    jumpAmplitude F t x = ENNReal.ofReal (finiteJumpControl F t x) := by
  unfold jumpAmplitude finiteJumpControl
  rw [separatedJumpCount_eq_finiteSeparatedJumpCount, ENNReal.ofReal_mul ht,
    Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.ofReal_natCast]
  rfl

theorem finiteJumpControl_moment_eq_eLpNorm_rpow
    {I : Type*} [LinearOrder I] [Fintype I]
    (F : I → ℝ → ℂ) (hF : ∀ i, Measurable (F i))
    {t p : ℝ} (ht : 0 ≤ t) (hp : 0 < p) :
    (∫⁻ x, (jumpAmplitude F t x).rpow p ∂volume) =
      eLpNorm (finiteJumpControl F t) (ENNReal.ofReal p) volume ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  calc
    _ = ∫⁻ x, ‖finiteJumpControl F t x‖ₑ ^ p ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [] with x
      rw [jumpAmplitude_eq_ofReal_finiteJumpControl F ht]
      have hnorm : ENNReal.ofReal (finiteJumpControl F t x) = ‖finiteJumpControl F t x‖ₑ := by
        rw [← ofReal_norm, Real.norm_of_nonneg (finiteJumpControl_nonneg F ht x)]
      rw [hnorm]
      rfl
    _ = _ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top
        (finiteJumpControl_measurable F t hF).aestronglyMeasurable, htoReal]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

#print axioms finiteJumpControl_moment_eq_eLpNorm_rpow
end
end FractionalPrimes.Literature.JSW
end
