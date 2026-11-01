module

public import FractionalPrimes.Literature.DirichletAdapter.ResiduePeriodization
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! The Fourier integration-by-parts input for residue quadrature. -/

@[expose] public section

open MeasureTheory Real Complex
open scoped FourierTransform
open scoped ContDiff

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The Fourier transform is bounded pointwise by the `L¹` norm. -/
theorem norm_realFourier_le_integral_norm
    (f : ℝ → ℂ) (ξ : ℝ) :
    ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ ∂volume := by
  rw [Real.fourier_real_eq]
  calc
    ‖∫ x : ℝ, (𝐞 (-(x * ξ))) • f x ∂volume‖ ≤
      ∫ x : ℝ, ‖(𝐞 (-(x * ξ))) • f x‖ ∂volume :=
        norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖f x‖ ∂volume := by
      congr 1
      funext x
      simp

#print axioms norm_realFourier_le_integral_norm

/-- The exact integration-by-parts Fourier inequality before dividing by
the nonzero frequency factor. -/
theorem fourier_iteratedDeriv_norm_bound
    (f : ℝ → ℂ) (j : ℕ)
    (hf : ContDiff ℝ ∞ f)
    (hInt : ∀ n : ℕ, Integrable (iteratedDeriv n f) volume)
    (ξ : ℝ) :
    ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) ^ j‖ * ‖𝓕 f ξ‖ ≤
      ∫ x : ℝ, ‖iteratedDeriv j f x‖ ∂volume := by
  have hFourier := congrFun
    (Real.fourier_iteratedDeriv hf (fun n _ => hInt n) (le_top : (j : ℕ∞) ≤ ⊤)) ξ
  have hUpper := norm_realFourier_le_integral_norm (iteratedDeriv j f) ξ
  rw [hFourier] at hUpper
  simpa only [norm_smul, norm_pow] using hUpper

#print axioms fourier_iteratedDeriv_norm_bound

/-- The same bound with the Fourier frequency factor written as a
nonnegative real power, ready for the `j≥2` integer-frequency sum. -/
theorem fourier_iteratedDeriv_real_bound
    (f : ℝ → ℂ) (j : ℕ)
    (hf : ContDiff ℝ ∞ f)
    (hInt : ∀ n : ℕ, Integrable (iteratedDeriv n f) volume)
    (ξ : ℝ) :
    (2 * Real.pi * |ξ|) ^ j * ‖𝓕 f ξ‖ ≤
      ∫ x : ℝ, ‖iteratedDeriv j f x‖ ∂volume := by
  have hnorm :
      ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) ^ j‖ =
        (2 * Real.pi * |ξ|) ^ j := by
    rw [norm_pow]
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [← hnorm]
  exact fourier_iteratedDeriv_norm_bound f j hf hInt ξ

#print axioms fourier_iteratedDeriv_real_bound

/-- Explicit nonzero-frequency decay after `j` integrations by parts. -/
theorem fourier_iteratedDeriv_div_bound
    (f : ℝ → ℂ) (j : ℕ)
    (hf : ContDiff ℝ ∞ f)
    (hInt : ∀ n : ℕ, Integrable (iteratedDeriv n f) volume)
    (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖𝓕 f ξ‖ ≤
      (∫ x : ℝ, ‖iteratedDeriv j f x‖ ∂volume) /
        (2 * Real.pi * |ξ|) ^ j := by
  have hfreq : 0 < 2 * Real.pi * |ξ| := by
    have habs : 0 < |ξ| := abs_pos.mpr hξ
    positivity
  apply (le_div_iff₀ (pow_pos hfreq j)).2
  simpa [mul_comm] using fourier_iteratedDeriv_real_bound f j hf hInt ξ

#print axioms fourier_iteratedDeriv_div_bound

end FractionalPrimes.Literature.DirichletAdapter

end
