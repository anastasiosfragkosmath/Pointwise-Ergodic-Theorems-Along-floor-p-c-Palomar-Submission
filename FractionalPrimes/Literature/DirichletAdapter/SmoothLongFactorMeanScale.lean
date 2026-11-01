module

public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownRetention
public import Mathlib.Tactic

/-! The source scale-product bound in the final Type-I mean estimate. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Uniformity

/-- The blueprint's `√P ≤ 2^11 √X`, preserving its exact scale loss. -/
theorem smoothHeathBrownSupportRetained_sqrt_scaleProduct_le
    {X z : ℝ} {fs : List (SmoothHeathBrownFactor X)}
    (hlen : fs.length ≤ 20) (hfsne : fs ≠ []) (hX : 0 ≤ X)
    (hfs : smoothHeathBrownSupportRetained (X := X) (z := z) fs) :
    Real.sqrt (smoothHeathBrownScaleProduct fs) ≤
      (2 : ℝ) ^ 11 * Real.sqrt X := by
  have hP := (smoothHeathBrownSupportRetained_scale_bounds
    hlen hfsne hX hfs).2
  have hsqrt := Real.sqrt_le_sqrt hP
  have hpow : Real.sqrt ((2 : ℝ) ^ 22 * X) =
      (2 : ℝ) ^ 11 * Real.sqrt X := by
    rw [show (2 : ℝ) ^ 22 = ((2 : ℝ) ^ 11) ^ 2 by ring,
      Real.sqrt_mul (by positivity : 0 ≤ ((2 : ℝ) ^ 11) ^ 2),
      Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 11)]
  simpa only [hpow] using hsqrt

/-- Cancellation of the selected scale after multiplying the outer and
inner square-root factors. -/
theorem smoothLongFactor_sqrt_ratio_mul_sqrt
    (P N : ℝ) (hP : 0 ≤ P) (hN : 0 < N) :
    Real.sqrt (P / N) * Real.sqrt N = Real.sqrt P := by
  rw [← Real.sqrt_mul (div_nonneg hP hN.le)]
  rw [div_mul_cancel₀ P hN.ne']

/-- A selected factor at least `P^(3/8)` in a retained component has
the blueprint's explicit long-scale lower bound. -/
theorem smoothLongFactor_selectedScale_lower
    (X P N : ℝ) (hX : 0 ≤ X) (hP : 0 ≤ P)
    (hXP : X / (2 : ℝ) ^ 22 ≤ P)
    (hNP : P ^ (3 / 8 : ℝ) ≤ N) :
    (2 : ℝ) ^ (-(22 : ℝ)) * X ^ (3 / 8 : ℝ) ≤ N := by
  have hXPpow : (X / (2 : ℝ) ^ 22) ^ (3 / 8 : ℝ) ≤
      P ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow (div_nonneg hX (by positivity)) hXP (by norm_num)
  have hconst : (2 : ℝ) ^ (-(22 : ℝ)) ≤
      ((2 : ℝ) ^ 22) ^ (-(3 / 8 : ℝ)) := by
    have hnat : (2 : ℝ) ^ (22 : ℕ) = (2 : ℝ) ^ (22 : ℝ) := by norm_cast
    rw [hnat, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hXpow : 0 ≤ X ^ (3 / 8 : ℝ) := by positivity
  calc
    (2 : ℝ) ^ (-(22 : ℝ)) * X ^ (3 / 8 : ℝ) ≤
        ((2 : ℝ) ^ 22) ^ (-(3 / 8 : ℝ)) * X ^ (3 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_right hconst hXpow
    _ = (X / (2 : ℝ) ^ 22) ^ (3 / 8 : ℝ) := by
      rw [Real.div_rpow hX (by positivity : 0 ≤ (2 : ℝ) ^ 22),
        div_eq_mul_inv, Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ) ^ 22)]
      ring
    _ ≤ P ^ (3 / 8 : ℝ) := hXPpow
    _ ≤ N := hNP

#print axioms smoothHeathBrownSupportRetained_sqrt_scaleProduct_le
#print axioms smoothLongFactor_sqrt_ratio_mul_sqrt
#print axioms smoothLongFactor_selectedScale_lower

end FractionalPrimes.Literature.DirichletAdapter

end
