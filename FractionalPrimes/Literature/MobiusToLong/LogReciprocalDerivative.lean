module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace FractionalPrimes.Literature.MobiusToLong

/-- The derivative of the logarithmically weighted reciprocal kernel. -/
theorem log_reciprocal_weight_deriv {t : ℝ} (ht : t ≠ 0) :
    deriv (fun x : ℝ => Real.log x * x⁻¹) t = (1 - Real.log t) / t ^ 2 := by
  change deriv (Real.log * fun y : ℝ => y⁻¹) t = _
  rw [deriv_mul (Real.differentiableAt_log ht)
      (hasDerivAt_inv ht).differentiableAt,
    Real.deriv_log, deriv_inv']
  field_simp [ht]
  <;> ring

/-- Multiplying a real power by its positive base increases the exponent by
one. This form avoids a syntactic `rpow`/power rewrite in endpoint estimates. -/
theorem realRpow_neg_mul_base_eq_one_sub {a r : ℝ} (ha : 0 < a) :
    Real.rpow a (-r) * a = Real.rpow a (1 - r) := by
  change a ^ (-r) * a = a ^ (1 - r)
  calc
    _ = a ^ (-r + 1) := by
      rw [← Real.rpow_add_one (ne_of_gt ha) (-r)]
    _ = a ^ (1 - r) := by
      rw [show -r + 1 = 1 - r by ring]

/-- When `log t ≥ 1`, the logarithmic kernel has nonnegative real
coefficient, so its absolute value can be moved entirely to the weight. -/
theorem abs_mul_log_kernel_eq {m t : ℝ} (ht : 0 < t)
    (hlog : 1 ≤ Real.log t) :
    |m * ((Real.log t - 1) / t ^ 2)| =
      |m| * ((Real.log t - 1) / t ^ 2) := by
  rw [abs_mul, abs_div]
  rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
  rw [abs_of_pos (sq_pos_of_pos ht)]

end FractionalPrimes.Literature.MobiusToLong

end
