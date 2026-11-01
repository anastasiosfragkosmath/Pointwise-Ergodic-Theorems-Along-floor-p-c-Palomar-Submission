module

public import FractionalPrimes.Literature.DirichletAdapter.AffineFourierModeBound
public import Mathlib.Tactic
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Positive-factor algebra for the quadrature Fourier modes. -/

@[expose] public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace FractionalPrimes.Literature.DirichletAdapter

theorem quadrature_mode_factor_le
    (q ξ A : ℝ) (j : ℕ) (hq : 0 < q) (hξ : ξ ≠ 0)
    (hA : 0 ≤ A) (hj : 1 ≤ j) :
    q⁻¹ * (A / (2 * Real.pi * |ξ / q|) ^ j) ≤
      q ^ (j - 1) * (A / |ξ| ^ j) := by
  have habs : 0 < |ξ / q| := abs_pos.mpr (div_ne_zero hξ hq.ne')
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hbase : |ξ / q| ≤ 2 * Real.pi * |ξ / q| := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) habs.le]
  have hdiv :
      A / (2 * Real.pi * |ξ / q|) ^ j ≤ A / |ξ / q| ^ j := by
    gcongr
  calc
    q⁻¹ * (A / (2 * Real.pi * |ξ / q|) ^ j) ≤
      q⁻¹ * (A / |ξ / q| ^ j) :=
        mul_le_mul_of_nonneg_left hdiv (inv_nonneg.mpr hq.le)
    _ = q ^ (j - 1) * (A / |ξ| ^ j) := by
      rw [abs_div, abs_of_pos hq, div_pow]
      have hpow : q ^ j = q ^ (j - 1) * q := by
        conv_lhs => rw [← Nat.sub_add_cancel hj]
        rw [pow_add, pow_one]
      rw [hpow]
      field_simp

#print axioms quadrature_mode_factor_le

/-- Each nonzero affine Fourier coefficient is dominated by the blueprint
`q^(j-1)` scale times the reciprocal integer mode. -/
theorem affine_fourier_mode_le_reciprocal
    (F : ℝ → ℂ) (j : ℕ) (hj : 1 ≤ j)
    (hF : ContDiff ℝ ∞ F)
    (hInt : ∀ n : ℕ, Integrable (iteratedDeriv n F) volume)
    (q b : ℝ) (hq : 0 < q) (k : ℤ) (hk : k ≠ 0) :
    ‖𝓕 (fun x : ℝ => F (b + q * x)) (k : ℝ)‖ ≤
      q ^ (j - 1) *
        ((∫ x : ℝ, ‖iteratedDeriv j F x‖ ∂volume) * reciprocalMode j k) := by
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hA : 0 ≤ ∫ x : ℝ, ‖iteratedDeriv j F x‖ ∂volume :=
    integral_nonneg fun x => norm_nonneg _
  have h1 := affine_fourier_mode_bound F j hF hInt q b hq k hk
  have h2 := quadrature_mode_factor_le q (k : ℝ)
    (∫ x : ℝ, ‖iteratedDeriv j F x‖ ∂volume) j hq hkreal hA hj
  rw [reciprocalMode, if_neg hk]
  calc
    ‖𝓕 (fun x : ℝ => F (b + q * x)) (k : ℝ)‖ ≤
        q⁻¹ * ((∫ x : ℝ, ‖iteratedDeriv j F x‖ ∂volume) /
          (2 * Real.pi * |(k : ℝ) / q|) ^ j) := h1
    _ ≤ q ^ (j - 1) *
        ((∫ x : ℝ, ‖iteratedDeriv j F x‖ ∂volume) / |(k : ℝ)| ^ j) := h2
    _ = q ^ (j - 1) *
        ((∫ x : ℝ, ‖iteratedDeriv j F x‖ ∂volume) *
          (1 / |(k : ℝ)| ^ j)) := by ring

#print axioms affine_fourier_mode_le_reciprocal

end FractionalPrimes.Literature.DirichletAdapter

end
