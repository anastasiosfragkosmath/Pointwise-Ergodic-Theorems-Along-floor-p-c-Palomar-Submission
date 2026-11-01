module

public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section

open MeasureTheory
open scoped FourierTransform

namespace FractionalPrimes.Literature.LongArithmetic

/-- The angular-frequency Fourier transform used in the long-arithmetic
Perron argument. -/
noncomputable def angularFourierTransform (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ u : ℝ, f u * Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ))

/-- Fourier inversion in angular-frequency normalization, obtained from
Mathlib's `2π`-normalized Fourier inversion theorem. -/
theorem integrableFourierInversion
    {f : ℝ → ℂ} (hf : Integrable f)
    (hF : Integrable (angularFourierTransform f))
    {v : ℝ} (hv : ContinuousAt f v) :
    f v = (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
      ∫ t : ℝ, angularFourierTransform f t *
        Complex.exp (Complex.I * (t : ℂ) * (v : ℂ)) := by
  let h₂π : ℝ := 2 * Real.pi
  have h₂π_ne : h₂π ≠ 0 := by
    dsimp [h₂π]
    positivity
  have h₂π_pos : 0 < h₂π := by
    dsimp [h₂π]
    positivity
  have htransform (t : ℝ) :
      angularFourierTransform f t = 𝓕 f (t / h₂π) := by
    unfold angularFourierTransform
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with u
    rw [Real.inner_apply]
    simp only [smul_eq_mul]
    have hexp :
        (↑(-2 * Real.pi * (u * (t / h₂π)) : ℝ) : ℂ) * Complex.I =
          -Complex.I * (t : ℂ) * (u : ℂ) := by
      have hreal : -2 * Real.pi * (u * (t / h₂π)) = -t * u := by
        dsimp [h₂π]
        field_simp [Real.pi_ne_zero]
      rw [hreal]
      push_cast
      ring
    rw [hexp]
    ring
  have hfourier : Integrable (𝓕 f) := by
    have h := hF.comp_mul_right' h₂π_ne
    simpa only [Function.comp_apply, htransform, mul_div_cancel_right₀ _ h₂π_ne] using h
  have hinv : 𝓕⁻ (𝓕 f) v = f v := hf.fourierInv_fourier_eq hfourier hv
  let g : ℝ → ℂ := fun t =>
    Complex.exp (Complex.I * (t : ℂ) * (v : ℂ)) * angularFourierTransform f t
  have hinv_scaled : (∫ y : ℝ, g (h₂π * y)) = f v := by
    simpa [g, htransform, Real.fourierInv_eq', h₂π, mul_assoc, mul_left_comm,
      mul_comm] using hinv
  have hscale := Measure.integral_comp_mul_left g h₂π
  rw [abs_of_pos (inv_pos.mpr h₂π_pos)] at hscale
  rw [hinv_scaled] at hscale
  have hscale' :
      f v = (↑(h₂π⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, g t := by
    simpa [smul_eq_mul, mul_comm] using hscale
  simpa [g, h₂π, angularFourierTransform, mul_comm] using hscale'

#print axioms integrableFourierInversion

end FractionalPrimes.Literature.LongArithmetic

end
