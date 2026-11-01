module

public import FractionalPrimes.CramerDensityExact

@[expose] public section

namespace FractionalPrimes

/-- Specialize the exact exponent-four density bound to the approved cutoff
scale `Q(X) = exp ((log X)^(1/10))`. -/
theorem paperCramerDensity_at_cutoff_scale {X : ℝ} (hX : 3 ≤ X) :
    paperCramerDensity (Real.exp ((Real.log X) ^ (1 / 10 : ℝ))) ≤
      Real.exp 13 * (Real.log X) ^ (2 / 5 : ℝ) := by
  have hXpos : 0 < X := by linarith
  have hlogX : 1 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact (Real.exp_one_lt_three.le).trans hX
  have hlogXpos : 0 < Real.log X := by linarith
  have hlogXnonneg : 0 ≤ Real.log X := le_trans (by norm_num) hlogX
  have hscale : 1 ≤ (Real.log X) ^ (1 / 10 : ℝ) :=
    Real.one_le_rpow hlogX (by norm_num)
  have htwo_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    norm_num at h
    exact h
  have hcutoff :
      2 ≤ Real.exp ((Real.log X) ^ (1 / 10 : ℝ)) := by
    exact htwo_le_exp_one.trans (Real.exp_le_exp.mpr hscale)
  have hproduct :=
    (paperCramerDensity_lc_product
      (w := Real.exp ((Real.log X) ^ (1 / 10 : ℝ))) hcutoff).2
  have hpower :
      ((Real.log X) ^ (1 / 10 : ℝ)) ^ (4 : ℕ) =
        (Real.log X) ^ (2 / 5 : ℝ) := by
    calc
      ((Real.log X) ^ (1 / 10 : ℝ)) ^ (4 : ℕ) =
          ((Real.log X) ^ (1 / 10 : ℝ)) ^ (4 : ℝ) :=
        (Real.rpow_natCast _ 4).symm
      _ = (Real.log X) ^ ((1 / 10 : ℝ) * (4 : ℝ)) :=
        (Real.rpow_mul hlogXnonneg (1 / 10 : ℝ) (4 : ℝ)).symm
      _ = (Real.log X) ^ (2 / 5 : ℝ) := by
        congr 1
        norm_num
  simpa only [Real.log_exp, hpower] using hproduct

end FractionalPrimes

end
