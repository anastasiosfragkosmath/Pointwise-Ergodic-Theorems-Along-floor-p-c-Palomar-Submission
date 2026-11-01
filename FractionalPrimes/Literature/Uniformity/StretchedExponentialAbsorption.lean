module

public import FractionalPrimes.Literature.Uniformity.LogAbsorption

/-!
# Exact stretched-exponential absorption

Blueprint `lucr:absorption`. The elementary maximization is proved from
Mathlib's `log z ≤ z-1`; the constant is the literal approved constant.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

noncomputable section

/-- The exact maximum of `u^a exp(-delta*u)` on the positive half-line. -/
theorem rpow_mul_exp_neg_le_exact_max
    (a δ u : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hu : 0 < u) :
    Real.rpow u a * Real.exp (-(δ * u)) ≤
      Real.rpow (a / (Real.exp 1 * δ)) a := by
  let z : ℝ := δ * u / a
  have hz : 0 < z := by dsimp [z]; positivity
  have huEq : u = (a / δ) * z := by dsimp [z]; field_simp
  have hlogu : Real.log u = Real.log a - Real.log δ + Real.log z := by
    rw [huEq, Real.log_mul (by positivity : a / δ ≠ 0) hz.ne',
      Real.log_div ha.ne' hδ.ne']
  have hlogbase : Real.log (a / (Real.exp 1 * δ)) =
      Real.log a - 1 - Real.log δ := by
    rw [Real.log_div ha.ne' (by positivity),
      Real.log_mul (Real.exp_ne_zero 1) hδ.ne', Real.log_exp]
    ring
  have hscale : a * z = δ * u := by dsimp [z]; field_simp
  have hlogz := Real.log_le_sub_one_of_pos hz
  change u ^ a * Real.exp (-(δ * u)) ≤ (a / (Real.exp 1 * δ)) ^ a
  rw [Real.rpow_def_of_pos hu a,
    Real.rpow_def_of_pos (by positivity : 0 < a / (Real.exp 1 * δ)) a,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hlogu, hlogbase]
  nlinarith [mul_le_mul_of_nonneg_left hlogz ha.le]

/-- Blueprint `lucr:absorption`, with no enlarged or implicit constant. -/
theorem stretchedExponentialAbsorption
    (A δ t : ℝ) (hA : 0 < A) (hδ : 0 < δ) (ht : 0 < t) :
    Real.exp (-(δ * Real.rpow t (9 / 10 : ℝ))) ≤
      Real.rpow (10 * A / (9 * Real.exp 1 * δ)) (10 * A / 9) *
        Real.rpow t (-A) := by
  let a : ℝ := 10 * A / 9
  let u : ℝ := Real.rpow t (9 / 10 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hpower : Real.rpow u a = Real.rpow t A := by
    dsimp [u, a]
    rw [← Real.rpow_mul ht.le]
    congr 1
    ring
  have hbase : a / (Real.exp 1 * δ) = 10 * A / (9 * Real.exp 1 * δ) := by
    dsimp [a]
    field_simp
  have hbound : Real.rpow t A * Real.exp (-(δ * u)) ≤
      Real.rpow (10 * A / (9 * Real.exp 1 * δ)) a := by
    simpa only [hpower, hbase] using rpow_mul_exp_neg_le_exact_max a δ u ha hδ hu
  have htp : 0 < Real.rpow t A := Real.rpow_pos_of_pos ht A
  calc
    Real.exp (-(δ * Real.rpow t (9 / 10 : ℝ))) =
        (Real.rpow t A * Real.exp (-(δ * u))) * (Real.rpow t A)⁻¹ := by
      dsimp [u]
      field_simp [htp.ne']
    _ ≤ Real.rpow (10 * A / (9 * Real.exp 1 * δ)) a * (Real.rpow t A)⁻¹ :=
      mul_le_mul_of_nonneg_right hbound (inv_nonneg.mpr htp.le)
    _ = _ := by
      change (10 * A / (9 * Real.exp 1 * δ)) ^ a * (t ^ A)⁻¹ =
        (10 * A / (9 * Real.exp 1 * δ)) ^ (10 * A / 9) * t ^ (-A)
      rw [Real.rpow_neg ht.le]

end

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.stretchedExponentialAbsorption
