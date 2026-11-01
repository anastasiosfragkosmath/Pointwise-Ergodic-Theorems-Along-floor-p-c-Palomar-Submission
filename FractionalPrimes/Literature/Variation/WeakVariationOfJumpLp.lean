module

public import FractionalPrimes.Literature.Variation.WeakVariationOfJump
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-!
# The weak variation estimate in `eLpNorm` form

The preceding proof is carried out with pth moments.  This module converts
the finite-exponent `eLpNorm` endpoint assumptions in `lv:weak-variation`
to those moments and records the conclusion with the source's pth power of
the input norm.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory
open scoped ENNReal

theorem complexLpMoment_eq_eLpNorm_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ}
    (hp : 0 < p) (f : X → ℂ) (hf : Measurable f) :
    complexLpMoment p μ f = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  calc
    complexLpMoment p μ f = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      unfold complexLpMoment
      apply lintegral_congr_ae
      filter_upwards with x
      simp [ENNReal.rpow_eq_pow]
    _ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hf.aestronglyMeasurable,
        htoReal]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

private theorem jumpAmplitudeLpMoment_eq_eLpNorm_rpow
    {I X : Type*} [LinearOrder I] [Fintype I] [MeasurableSpace X]
    (μ : Measure X) {p : ℝ} (hp : 0 < p) (F : I → X → ℂ)
    (threshold : ℝ) (hF : ∀ i, Measurable (F i)) :
    (∫⁻ x, (jumpAmplitude F threshold x).rpow p ∂μ) =
      eLpNorm (jumpAmplitude F threshold) (ENNReal.ofReal p) μ ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hmeas : Measurable (jumpAmplitude F threshold) :=
    measurable_jumpAmplitude F threshold hF
  calc
    (∫⁻ x, (jumpAmplitude F threshold x).rpow p ∂μ) =
        ∫⁻ x, ‖jumpAmplitude F threshold x‖ₑ ^ p ∂μ := by
          apply lintegral_congr_ae
          filter_upwards with x
          simp [ENNReal.rpow_eq_pow]
    _ = eLpNorm (jumpAmplitude F threshold) (ENNReal.ofReal p) μ ^ p := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop
        hmeas.aestronglyMeasurable, htoReal]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- Blueprint `lv:weak-variation` with its endpoint assumptions written as
actual finite-exponent `eLpNorm` bounds.  The conclusion is the pth-moment
level-set estimate with the input factor written as
`eLpNorm f (ENNReal.ofReal p) μ ^ p`. -/
theorem weakVariationOfJump_eLpNorm
    {I X : Type*} [LinearOrder I] [Fintype I] [MeasurableSpace X]
    (μ : Measure X) (p r A B : ℝ) (F : I → X → ℂ) (f : X → ℂ)
    (hp : 0 < p) (hr : 2 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∀ i, Measurable (F i)) (hf : Measurable f)
    (hfixed : ∀ i,
      eLpNorm (F i) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal B * eLpNorm f (ENNReal.ofReal p) μ)
    (hjump : ∀ threshold : ℝ, 0 < threshold →
      eLpNorm (jumpAmplitude F threshold) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) μ) :
    ∀ t : ℝ, 0 < t →
      μ {x | ENNReal.ofReal t < orderedRVariationFun r F x} ≤
        ENNReal.ofReal (weakVariationConstantPow p r A B) *
          (ENNReal.ofReal t).rpow (-p) *
            eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  have hfixedMoment : ∀ i, complexLpMoment p μ (F i) ≤
      (ENNReal.ofReal B).rpow p * complexLpMoment p μ f := by
    intro i
    have hFi := complexLpMoment_eq_eLpNorm_rpow μ hp (F i) (hF i)
    have hf' := complexLpMoment_eq_eLpNorm_rpow μ hp f hf
    have hbound := ENNReal.rpow_le_rpow (hfixed i) hp.le
    rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal B)
      (eLpNorm f (ENNReal.ofReal p) μ) hp.le] at hbound
    rw [hFi, hf']
    simpa only [ENNReal.rpow_eq_pow] using hbound
  have hjumpMoment : ∀ threshold : ℝ, 0 < threshold →
      (∫⁻ x, (jumpAmplitude F threshold x).rpow p ∂μ) ≤
        (ENNReal.ofReal A).rpow p * complexLpMoment p μ f := by
    intro threshold hthreshold
    have hAmp := jumpAmplitudeLpMoment_eq_eLpNorm_rpow μ hp F threshold hF
    have hf' := complexLpMoment_eq_eLpNorm_rpow μ hp f hf
    have hbound := ENNReal.rpow_le_rpow (hjump threshold hthreshold) hp.le
    rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal A)
      (eLpNorm f (ENNReal.ofReal p) μ) hp.le] at hbound
    rw [hAmp, hf']
    simpa only [ENNReal.rpow_eq_pow] using hbound
  have hweak := weakVariationOfJump μ p r A B F f hp hr hA hB hF hf
    hfixedMoment hjumpMoment
  have hinput := complexLpMoment_eq_eLpNorm_rpow μ hp f hf
  change ∀ t : ℝ, 0 < t →
    μ {x | ENNReal.ofReal t < orderedRVariationFun r F x} ≤
      ENNReal.ofReal (weakVariationConstantPow p r A B) *
        (ENNReal.ofReal t).rpow (-p) * complexLpMoment p μ f at hweak
  intro t ht
  have hlevel := hweak t ht
  rw [hinput] at hlevel
  exact hlevel

end FractionalPrimes.Literature.Variation
