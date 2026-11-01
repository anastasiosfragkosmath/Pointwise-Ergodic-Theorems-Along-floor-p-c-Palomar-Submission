module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

/-- The power convention in the approved numerical bootstrap.  In particular,
the exponent-zero case is one even when the base is zero. -/
noncomputable def scalarBootstrapPower (B α : ℝ) : ℝ :=
  if α = 0 then 1 else B ^ α

/-- The scalar MSZ bootstrap inequality.  The power is the usual real power
for positive exponents, with the blueprint's explicit convention
`B ^ 0 = 1` also at `B = 0`. -/
theorem scalarBootstrap {B b H α : ℝ}
    (hB : 0 ≤ B) (hb : 0 < b) (hH : 0 ≤ H)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hineq : B ≤ b + H * scalarBootstrapPower B α) :
    B ≤ max (2 * b) ((2 * H) ^ (1 / (1 - α))) := by
  by_cases hsmall : B ≤ 2 * b
  · exact hsmall.trans (le_max_left _ _)
  · have hlarge : 2 * b < B := lt_of_not_ge hsmall
    have hBpos : 0 < B := lt_trans (mul_pos (by norm_num) hb) hlarge
    have hαgap : 0 < 1 - α := sub_pos.mpr hα1
    by_cases hαzero : α = 0
    · have hineq' : B ≤ b + H := by
        simpa [scalarBootstrapPower, hαzero] using hineq
      have hbound : B ≤ 2 * H := by
        linarith
      have htarget : B ≤ (2 * H) ^ (1 / (1 - α)) := by
        simpa [hαzero] using hbound
      exact htarget.trans (le_max_right _ _)
    · have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hαzero)
      have hineq' : B ≤ b + H * B ^ α := by
        simpa [scalarBootstrapPower, hαzero] using hineq
      have hhalf : B / 2 ≤ H * B ^ α := by
        linarith
      have hpowpos : 0 < B ^ α := Real.rpow_pos_of_pos hBpos α
      have hdiv : (B / 2) / Real.rpow B α ≤ H :=
        (div_le_iff₀ hpowpos).2 hhalf
      have hratio : Real.rpow B (1 - α) / 2 ≤ H := by
        calc
          B ^ (1 - α) / 2 = (B / 2) / B ^ α := by
            rw [Real.rpow_sub hBpos 1 α, Real.rpow_one]
            field_simp [ne_of_gt hpowpos]
          _ ≤ H := hdiv
      have hkey : B ^ (1 - α) ≤ 2 * H := by
        calc
          B ^ (1 - α) ≤ H * 2 :=
            (div_le_iff₀ (by norm_num : 0 < (2 : ℝ))).mp hratio
          _ = 2 * H := by ring
      have hcancel :
          (B ^ (1 - α)) ^ (1 / (1 - α)) = B := by
        simpa [one_div] using
          (Real.rpow_rpow_inv hB (ne_of_gt hαgap))
      have htarget : B ≤ (2 * H) ^ (1 / (1 - α)) := by
        rw [← hcancel]
        exact Real.rpow_le_rpow
          (Real.rpow_nonneg hB (1 - α)) hkey
          (div_nonneg (by norm_num) hαgap.le)
      exact htarget.trans (le_max_right _ _)

end FractionalPrimes.Literature.MSZ

end
