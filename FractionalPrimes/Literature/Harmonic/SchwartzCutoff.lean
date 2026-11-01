module

public import FractionalPrimes.Literature.Harmonic.ContinuousModel
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Inverse Fourier transforms of smooth cutoffs

This module proves the exact weighted derivative estimate for the inverse Fourier
transform of a compactly supported smooth function in the normalization used in
the harmonic-analysis blueprint.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace FractionalPrimes.Literature.Harmonic

noncomputable section

/-- The inverse Fourier transform of a smooth compactly supported cutoff,
viewed as a Schwartz map. -/
def inverseFourierCutoffSchwartz (cutoff : ℝ → ℂ)
    (hcutoffSmooth : ContDiff ℝ (∞ : ℕ∞ω) cutoff)
    (hcutoffCompact : HasCompactSupport cutoff) :
    SchwartzMap ℝ ℂ := 𝓕⁻ (hcutoffCompact.toSchwartzMap hcutoffSmooth)

/-- The pointwise integral formula for the inverse Fourier transform, in the
`e(t) = exp(2πit)` convention of the paper. -/
theorem inverseFourierCutoffSchwartz_apply (cutoff : ℝ → ℂ)
    (hcutoffSmooth : ContDiff ℝ (∞ : ℕ∞ω) cutoff)
    (hcutoffCompact : HasCompactSupport cutoff) (x : ℝ) :
    inverseFourierCutoffSchwartz cutoff hcutoffSmooth hcutoffCompact x =
      ∫ ξ : ℝ, cutoff ξ * unitFrequencyPhase (x * ξ) := by
  change (𝓕⁻ (hcutoffCompact.toSchwartzMap hcutoffSmooth) : SchwartzMap ℝ ℂ) x = _
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp [unitFrequencyPhase, smul_eq_mul, inner, mul_comm, mul_left_comm, mul_assoc]

/-- Each frequency moment of a Schwartz function remains Schwartz. -/
private def cutoffFrequencyMoment (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => (ξ : ℂ) ^ n) f

private theorem cutoffFrequencyMoment_apply (n : ℕ) (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    cutoffFrequencyMoment n f ξ = (ξ : ℂ) ^ n * f ξ := by
  rw [cutoffFrequencyMoment, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  exact smul_eq_mul _ _

private theorem cutoffFrequencyMoment_succ (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    cutoffFrequencyMoment (n + 1) f =
      SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => (ξ : ℂ))
        (cutoffFrequencyMoment n f) := by
  ext ξ
  rw [cutoffFrequencyMoment_apply, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop),
    cutoffFrequencyMoment_apply]
  ring

private theorem cutoffFrequencyMoment_zero (f : SchwartzMap ℝ ℂ) :
    cutoffFrequencyMoment 0 f = f := by
  ext ξ
  rw [cutoffFrequencyMoment_apply]
  simp

private theorem cutoffFrequencyMoment_one_comp (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    cutoffFrequencyMoment 1 (cutoffFrequencyMoment n f) =
      cutoffFrequencyMoment (n + 1) f := by
  ext ξ
  rw [cutoffFrequencyMoment_apply, cutoffFrequencyMoment_apply,
    cutoffFrequencyMoment_apply]
  ring

/-- Iterated derivatives formed inside Schwartz space. -/
private def cutoffSchwartzDerivative : ℕ → SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ
  | 0, f => f
  | n + 1, f => SchwartzMap.derivCLM ℝ ℂ (cutoffSchwartzDerivative n f)

private theorem cutoffSchwartzDerivative_apply (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (x : ℝ) :
    cutoffSchwartzDerivative n f x = iteratedDeriv n (fun y : ℝ => f y) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [cutoffSchwartzDerivative, SchwartzMap.derivCLM_apply, iteratedDeriv_succ]
      have hfun : (cutoffSchwartzDerivative n f : ℝ → ℂ) =
          iteratedDeriv n (fun y : ℝ => f y) := funext ih
      rw [hfun]

private def cutoffFourierConstant : ℂ := (2 * Real.pi : ℝ) * Complex.I

private theorem deriv_inverseFourierCutoffSchwartz (f : SchwartzMap ℝ ℂ) :
    deriv (fun x : ℝ => (𝓕⁻ f) x) =
      fun x => cutoffFourierConstant * (𝓕⁻ (cutoffFrequencyMoment 1 f)) x := by
  funext x
  have h := congrArg (fun g : SchwartzMap ℝ ℂ => g x)
    (SchwartzMap.lineDerivOp_fourierInv_eq f (1 : ℝ))
  have hfun : cutoffFrequencyMoment 1 f =
      SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => inner ℝ ξ (1 : ℝ)) f := by
    ext ξ
    rw [cutoffFrequencyMoment_apply,
      SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp [inner]
  simpa [cutoffFourierConstant, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv, hfun] using h

private theorem iteratedDeriv_inverseFourierCutoffSchwartz (n : ℕ)
    (f : SchwartzMap ℝ ℂ) :
    iteratedDeriv n (fun x : ℝ => (𝓕⁻ f) x) =
      fun x => cutoffFourierConstant ^ n *
        (𝓕⁻ (cutoffFrequencyMoment n f)) x := by
  induction n with
  | zero =>
      funext x
      rw [iteratedDeriv_zero, cutoffFrequencyMoment_zero]
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      rw [deriv_const_mul_field', deriv_inverseFourierCutoffSchwartz]
      rw [cutoffFrequencyMoment_one_comp]
      simp only [cutoffFourierConstant]
      ring

private theorem inverseFourierCutoffSchwartz_norm_le_integral (f : SchwartzMap ℝ ℂ)
    (x : ℝ) : ‖(𝓕⁻ f) x‖ ≤ ∫ ξ : ℝ, ‖f ξ‖ := by
  have hcoe : (𝓕⁻ f : SchwartzMap ℝ ℂ) = 𝓕⁻ (f : ℝ → ℂ) :=
    SchwartzMap.fourierInv_coe f
  calc
    ‖(𝓕⁻ f) x‖ =
        ‖∫ ξ : ℝ, Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) • f ξ‖ := by
          rw [hcoe, Real.fourierInv_eq']
    _ ≤ ∫ ξ : ℝ,
          ‖Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) • f ξ‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, ‖f ξ‖ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp [Complex.norm_exp, inner, mul_comm, mul_left_comm, mul_assoc]

private theorem cutoffFourierConstant_ne_zero : cutoffFourierConstant ≠ 0 := by
  unfold cutoffFourierConstant
  apply mul_ne_zero
  · exact_mod_cast (ne_of_gt (show 0 < 2 * Real.pi by positivity))
  · exact Complex.I_ne_zero

private theorem x_mul_inverseFourierCutoffSchwartz (f : SchwartzMap ℝ ℂ) :
    (fun x : ℝ => (x : ℂ) * (𝓕⁻ f) x) =
      fun x => (-cutoffFourierConstant⁻¹) *
        (𝓕⁻ (cutoffSchwartzDerivative 1 f)) x := by
  funext x
  have hD : LineDeriv.lineDerivOp (1 : ℝ) f = cutoffSchwartzDerivative 1 f := by
    ext y
    simp [cutoffSchwartzDerivative, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have h := congrArg (fun g : SchwartzMap ℝ ℂ => g x)
    (SchwartzMap.fourierInv_lineDerivOp_eq f (1 : ℝ))
  rw [hD] at h
  have hpoint : (𝓕⁻ (cutoffSchwartzDerivative 1 f)) x =
      -cutoffFourierConstant * ((x : ℂ) * (𝓕⁻ f) x) := by
    have hg : (fun y : ℝ => inner ℝ y (1 : ℝ)).HasTemperateGrowth :=
      ((innerSL ℝ).flip (1 : ℝ)).hasTemperateGrowth
    change (𝓕⁻ (cutoffSchwartzDerivative 1 f)) x =
      -(2 * (Real.pi : ℂ) * Complex.I) *
        ((SchwartzMap.smulLeftCLM ℂ
          (fun y : ℝ => inner ℝ y (1 : ℝ)) (𝓕⁻ f)) x) at h
    rw [SchwartzMap.smulLeftCLM_apply_apply hg] at h
    simpa [cutoffFourierConstant, smul_eq_mul, inner, mul_assoc] using h
  calc
    (x : ℂ) * (𝓕⁻ f) x =
        (-cutoffFourierConstant⁻¹) *
          (-cutoffFourierConstant * ((x : ℂ) * (𝓕⁻ f) x)) := by
            field_simp [cutoffFourierConstant_ne_zero]
    _ = (-cutoffFourierConstant⁻¹) *
          (𝓕⁻ (cutoffSchwartzDerivative 1 f)) x := by rw [← hpoint]

private theorem cutoffWeightedInverseFourier (b : ℕ) (f : SchwartzMap ℝ ℂ) :
    (fun x : ℝ => (x : ℂ) ^ b * (𝓕⁻ f) x) =
      fun x => (-cutoffFourierConstant⁻¹) ^ b *
        (𝓕⁻ (cutoffSchwartzDerivative b f)) x := by
  induction b with
  | zero =>
      funext x
      simp [cutoffSchwartzDerivative]
  | succ b ih =>
      funext x
      calc
        (x : ℂ) ^ (b + 1) * (𝓕⁻ f) x =
            (x : ℂ) * ((x : ℂ) ^ b * (𝓕⁻ f) x) := by rw [pow_succ]; ring
        _ = (x : ℂ) *
            ((-cutoffFourierConstant⁻¹) ^ b *
              (𝓕⁻ (cutoffSchwartzDerivative b f)) x) := by
                rw [congrFun ih x]
        _ = (-cutoffFourierConstant⁻¹) ^ b *
            ((x : ℂ) * (𝓕⁻ (cutoffSchwartzDerivative b f)) x) := by ring
        _ = (-cutoffFourierConstant⁻¹) ^ b *
            ((-cutoffFourierConstant⁻¹) *
              (𝓕⁻ (cutoffSchwartzDerivative (b + 1) f)) x) := by
                rw [congrFun
                  (x_mul_inverseFourierCutoffSchwartz (cutoffSchwartzDerivative b f)) x]
                rw [show cutoffSchwartzDerivative 1 (cutoffSchwartzDerivative b f) =
                  cutoffSchwartzDerivative (b + 1) f by
                    simp [cutoffSchwartzDerivative]]
        _ = (-cutoffFourierConstant⁻¹) ^ (b + 1) *
            (𝓕⁻ (cutoffSchwartzDerivative (b + 1) f)) x := by
              rw [pow_succ]
              ring

private theorem cutoffFourierConstant_norm :
    ‖cutoffFourierConstant‖ = 2 * Real.pi := by
  simp [cutoffFourierConstant]

private theorem cutoffFourierCoefficient_norm (a b : ℕ) :
    ‖cutoffFourierConstant ^ a * (-cutoffFourierConstant⁻¹) ^ b‖ =
      (2 * Real.pi : ℝ) ^ ((a : ℤ) - (b : ℤ)) := by
  have hr : 0 < (2 * Real.pi : ℝ) := by positivity
  rw [norm_mul, norm_pow, norm_pow, cutoffFourierConstant_norm,
    norm_neg, norm_inv, cutoffFourierConstant_norm]
  rw [zpow_sub₀ (ne_of_gt hr), zpow_natCast, zpow_natCast,
    div_eq_mul_inv, inv_pow]

/-- The pointwise exact weighted derivative bound from `ha:schwartz-cutoff`. -/
theorem inverseFourierCutoffSchwartz_pointwise_bound (cutoff : SchwartzMap ℝ ℂ)
    (a b : ℕ) (x : ℝ) :
    ‖(x : ℂ) ^ b * iteratedDeriv a (fun y : ℝ => (𝓕⁻ cutoff) y) x‖ ≤
      ((2 * Real.pi : ℝ) ^ ((a : ℤ) - (b : ℤ))) *
        ∫ ξ : ℝ, ‖iteratedDeriv b (fun y : ℝ => (y : ℂ) ^ a * cutoff y) ξ‖ := by
  let frequencyMoment := cutoffFrequencyMoment a cutoff
  have hfrequency : (fun y : ℝ => frequencyMoment y) =
      (fun y : ℝ => (y : ℂ) ^ a * cutoff y) := by
    funext y
    exact cutoffFrequencyMoment_apply a cutoff y
  have hderivative := congrFun (iteratedDeriv_inverseFourierCutoffSchwartz a cutoff) x
  have hweight := congrFun (cutoffWeightedInverseFourier b frequencyMoment) x
  have hderivativeTarget : cutoffSchwartzDerivative b frequencyMoment x =
      iteratedDeriv b (fun y : ℝ => (y : ℂ) ^ a * cutoff y) x := by
    rw [cutoffSchwartzDerivative_apply, hfrequency]
  have hformula : (x : ℂ) ^ b *
      iteratedDeriv a (fun y : ℝ => (𝓕⁻ cutoff) y) x =
        (cutoffFourierConstant ^ a * (-cutoffFourierConstant⁻¹) ^ b) *
          (𝓕⁻ (cutoffSchwartzDerivative b frequencyMoment)) x := by
    calc
      (x : ℂ) ^ b *
          iteratedDeriv a (fun y : ℝ => (𝓕⁻ cutoff) y) x =
          (x : ℂ) ^ b * (cutoffFourierConstant ^ a *
            (𝓕⁻ frequencyMoment) x) := by rw [hderivative]
      _ = cutoffFourierConstant ^ a *
          ((x : ℂ) ^ b * (𝓕⁻ frequencyMoment) x) := by ring
      _ = cutoffFourierConstant ^ a *
          ((-cutoffFourierConstant⁻¹) ^ b *
            (𝓕⁻ (cutoffSchwartzDerivative b frequencyMoment)) x) := by rw [hweight]
      _ = (cutoffFourierConstant ^ a * (-cutoffFourierConstant⁻¹) ^ b) *
          (𝓕⁻ (cutoffSchwartzDerivative b frequencyMoment)) x := by ring
  calc
    _ = ‖(cutoffFourierConstant ^ a * (-cutoffFourierConstant⁻¹) ^ b) *
          (𝓕⁻ (cutoffSchwartzDerivative b frequencyMoment)) x‖ := by rw [hformula]
    _ = ‖cutoffFourierConstant ^ a * (-cutoffFourierConstant⁻¹) ^ b‖ *
          ‖(𝓕⁻ (cutoffSchwartzDerivative b frequencyMoment)) x‖ := norm_mul _ _
    _ ≤ ‖cutoffFourierConstant ^ a * (-cutoffFourierConstant⁻¹) ^ b‖ *
          ∫ ξ : ℝ, ‖cutoffSchwartzDerivative b frequencyMoment ξ‖ :=
            mul_le_mul_of_nonneg_left
              (inverseFourierCutoffSchwartz_norm_le_integral
                (cutoffSchwartzDerivative b frequencyMoment) x) (norm_nonneg _)
    _ = ((2 * Real.pi : ℝ) ^ ((a : ℤ) - (b : ℤ))) *
          ∫ ξ : ℝ, ‖iteratedDeriv b (fun y : ℝ => (y : ℂ) ^ a * cutoff y) ξ‖ := by
            rw [cutoffFourierCoefficient_norm]
            congr 1
            apply integral_congr_ae
            filter_upwards [] with ξ
            rw [cutoffSchwartzDerivative_apply, hfrequency]

/-- The supremum seminorm occurring in the inverse-cutoff estimate. -/
def inverseFourierCutoffWeightedSup (cutoff : SchwartzMap ℝ ℂ) (a b : ℕ) : ℝ :=
  sSup (Set.range fun x : ℝ =>
    ‖(x : ℂ) ^ b * iteratedDeriv a (fun y : ℝ => (𝓕⁻ cutoff) y) x‖)

/-- The exact supremum estimate for an arbitrary Schwartz frequency cutoff. -/
theorem inverseFourierCutoffWeightedSup_bound (cutoff : SchwartzMap ℝ ℂ)
    (a b : ℕ) :
    inverseFourierCutoffWeightedSup cutoff a b ≤
      ((2 * Real.pi : ℝ) ^ ((a : ℤ) - (b : ℤ))) *
        ∫ ξ : ℝ, ‖iteratedDeriv b (fun y : ℝ => (y : ℂ) ^ a * cutoff y) ξ‖ := by
  apply csSup_le
  · exact ⟨_, ⟨0, rfl⟩⟩
  · rintro z ⟨x, rfl⟩
    exact inverseFourierCutoffSchwartz_pointwise_bound cutoff a b x

/-- The blueprint's `ha:schwartz-cutoff` estimate for every compactly
supported smooth complex cutoff. -/
theorem inverseFourierCutoffSchwartz_bound (cutoff : ℝ → ℂ)
    (hcutoffSmooth : ContDiff ℝ (∞ : ℕ∞ω) cutoff)
    (hcutoffCompact : HasCompactSupport cutoff) (a b : ℕ) :
    inverseFourierCutoffWeightedSup (hcutoffCompact.toSchwartzMap hcutoffSmooth) a b ≤
      ((2 * Real.pi : ℝ) ^ ((a : ℤ) - (b : ℤ))) *
        ∫ ξ : ℝ, ‖iteratedDeriv b (fun y : ℝ => (y : ℂ) ^ a * cutoff y) ξ‖ := by
  simpa [inverseFourierCutoffWeightedSup] using
    inverseFourierCutoffWeightedSup_bound
      (hcutoffCompact.toSchwartzMap hcutoffSmooth) a b

/-- The cutoff fixed in `ha:model` has a Schwartz inverse transform. -/
theorem continuousModelPsiSchwartz_isSchwartz :
    ∃ f : SchwartzMap ℝ ℂ, (f : ℝ → ℂ) = continuousModelPsi := by
  exact ⟨continuousModelPsiSchwartz, rfl⟩

end

end FractionalPrimes.Literature.Harmonic
