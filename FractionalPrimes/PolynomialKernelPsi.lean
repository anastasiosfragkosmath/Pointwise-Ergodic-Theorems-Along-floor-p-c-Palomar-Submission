module

public import FractionalPrimes.PolynomialKernelCutoff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

@[expose] public section

open MeasureTheory
open scoped FourierTransform

namespace FractionalPrimes

/-- The rescaling `t ↦ 2πt` needed to convert Mathlib's `e(-2πitu)`
Fourier convention to the blueprint's angular convention. -/
noncomputable def polynomialKernelScaleEquiv : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 (2 * Real.pi) (mul_ne_zero (by norm_num) Real.pi_ne_zero))

theorem polynomialKernelScaleEquiv_apply (u : ℝ) :
    polynomialKernelScaleEquiv u = (2 * Real.pi) * u := by
  simp [polynomialKernelScaleEquiv, ContinuousLinearEquiv.smulLeft,
    DistribMulAction.toModuleAut, Units.smul_def]

/-- The cutoff in the rescaled Mathlib frequency variable, embedded in
complex-valued Schwartz space without changing its real values. -/
noncomputable def polynomialKernelFrequencyCutoff : SchwartzMap ℝ ℂ :=
  (polynomialKernelCutoffSchwartz.compCLMOfContinuousLinearEquiv ℝ
      polynomialKernelScaleEquiv).postcompCLM Complex.ofRealCLM

@[simp]
theorem polynomialKernelFrequencyCutoff_apply (t : ℝ) :
    polynomialKernelFrequencyCutoff t =
      (polynomialKernelCutoff ((2 * Real.pi) * t) : ℂ) := by
  change Complex.ofReal (polynomialKernelCutoff (polynomialKernelScaleEquiv t)) = _
  rw [polynomialKernelScaleEquiv_apply]

@[simp]
theorem polynomialKernelCutoff_neg (t : ℝ) :
    polynomialKernelCutoff (-t) = polynomialKernelCutoff t := by
  simp [polynomialKernelCutoff]

@[simp]
theorem polynomialKernelFrequencyCutoff_neg (t : ℝ) :
    polynomialKernelFrequencyCutoff (-t) = polynomialKernelFrequencyCutoff t := by
  simp [polynomialKernelFrequencyCutoff_apply]

/-- The blueprint angular inverse transform, represented as a Schwartz map
by Mathlib's inverse Fourier transform after the explicit `2π` rescaling. -/
noncomputable def polynomialKernelPsiSchwartz : SchwartzMap ℝ ℂ :=
  𝓕⁻ polynomialKernelFrequencyCutoff

/-- The exact angular inverse-transform formula for the Schwartz map. The
real scalar action is the complex coefficient `1/(2π)` from the blueprint. -/
theorem polynomialKernelPsiSchwartz_apply_eq_angular (u : ℝ) :
    polynomialKernelPsiSchwartz u =
      ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ t : ℝ, (polynomialKernelCutoff t : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) := by
  let g : ℝ → ℂ := fun t => (polynomialKernelCutoff t : ℂ) *
    Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))
  have hscale : (∫ t : ℝ, g ((2 * Real.pi) * t)) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, g t := by
    rw [Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
  rw [polynomialKernelPsiSchwartz, SchwartzMap.fourierInv_coe,
    Real.fourierInv_eq']
  calc
    _ = ∫ t : ℝ, g ((2 * Real.pi) * t) := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp [g]
      rw [polynomialKernelFrequencyCutoff_apply]
      have hexp :
          Complex.exp (↑(2 * Real.pi * (u * (starRingEnd ℝ) t)) * Complex.I) =
            Complex.exp (Complex.I * ↑(2 * Real.pi * t) * ↑u) := by
        congr 1
        simp
        ring
      rw [hexp, mul_comm]
    _ = ((2 * Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, g t := hscale
    _ = _ := rfl

/-- The inverse angular transform of the even cutoff is even. -/
theorem polynomialKernelPsiSchwartz_even (u : ℝ) :
    polynomialKernelPsiSchwartz (-u) = polynomialKernelPsiSchwartz u := by
  have hcomp :
      (polynomialKernelFrequencyCutoff : ℝ → ℂ) ∘
          (LinearIsometryEquiv.neg ℝ (E := ℝ) : ℝ ≃ₗᵢ[ℝ] ℝ) =
        polynomialKernelFrequencyCutoff := by
    funext t
    simp
  simp only [polynomialKernelPsiSchwartz, SchwartzMap.fourierInv_coe,
    Real.fourierInv_eq_fourier_neg, neg_neg]
  have hfourier :=
    Real.fourier_comp_linearIsometry
      (LinearIsometryEquiv.neg ℝ (E := ℝ))
      (polynomialKernelFrequencyCutoff : ℝ → ℂ) u
  rw [hcomp] at hfourier
  exact hfourier

/-- Conjugation of the angular inverse transform corresponds to reflection
of its real-valued frequency cutoff. -/
theorem polynomialKernelPsiSchwartz_conj (u : ℝ) :
    star (polynomialKernelPsiSchwartz u) = polynomialKernelPsiSchwartz (-u) := by
  rw [polynomialKernelPsiSchwartz_apply_eq_angular,
    polynomialKernelPsiSchwartz_apply_eq_angular]
  simp
  rw [← integral_conj]
  congr 1
  funext t
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_conj]
  ring_nf

/-- The blueprint angular inverse transform is real-valued. -/
theorem polynomialKernelPsiSchwartz_im (u : ℝ) :
    (polynomialKernelPsiSchwartz u).im = 0 := by
  have h := polynomialKernelPsiSchwartz_conj u
  rw [polynomialKernelPsiSchwartz_even] at h
  exact Complex.conj_eq_iff_im.1 h

end FractionalPrimes
