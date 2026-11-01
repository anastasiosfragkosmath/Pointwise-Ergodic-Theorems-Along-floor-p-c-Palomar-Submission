module

public import FractionalPrimes.Literature.DirichletAdapter.FourierModeRemoval

/-! One nonzero Fourier mode of the residue-affine periodization. -/

@[expose] public section

open MeasureTheory Real
open scoped FourierTransform ContDiff

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The exact one-frequency bound before its elementary `q`-power simplification. -/
theorem affine_fourier_mode_bound
    (F : ℝ → ℂ) (j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hInt : ∀ n : ℕ, Integrable (iteratedDeriv n F) volume)
    (q b : ℝ) (hq : 0 < q) (k : ℤ) (hk : k ≠ 0) :
    ‖𝓕 (fun x : ℝ => F (b + q * x)) (k : ℝ)‖ ≤
      q⁻¹ *
        ((∫ x : ℝ, ‖iteratedDeriv j F x‖ ∂volume) /
          (2 * Real.pi * |((k : ℝ) / q)|) ^ j) := by
  rw [fourier_comp_residue_affine F q b (k : ℝ) hq]
  have hkreal : (k : ℝ) / q ≠ 0 := by
    exact div_ne_zero (by exact_mod_cast hk) hq.ne'
  have hdecay := fourier_iteratedDeriv_div_bound F j hF hInt
    ((k : ℝ) / q) hkreal
  simpa only [norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hq, Circle.norm_smul] using
      (mul_le_mul_of_nonneg_left hdecay (inv_nonneg.mpr hq.le))

#print axioms affine_fourier_mode_bound

end FractionalPrimes.Literature.DirichletAdapter

end
