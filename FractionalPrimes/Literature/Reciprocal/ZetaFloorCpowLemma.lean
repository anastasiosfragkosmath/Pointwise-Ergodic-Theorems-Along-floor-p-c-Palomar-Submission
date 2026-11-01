module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

@[expose] public section

namespace FractionalPrimes.Literature.Reciprocal

/-- For a positive real base, multiplying the complex power with exponent
`-s - 1` by the base gives the power with exponent `-s`. This is the
positive-base step in the floor-correction formula for zeta. -/
theorem positiveReal_mul_cpow_neg_sub_one {t : ℝ} {s : ℂ} (ht : 0 < t) :
    (t : ℂ) * (t : ℂ) ^ (-s - 1) = (t : ℂ) ^ (-s) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hexp : -s - 1 = -s + (-1 : ℂ) := by ring
  calc
    (t : ℂ) * (t : ℂ) ^ (-s - 1) =
        (t : ℂ) * ((t : ℂ) ^ (-s) * (t : ℂ) ^ (-1 : ℂ)) := by
          rw [hexp, Complex.cpow_add _ _ htC]
    _ = (t : ℂ) ^ (-s) := by
      rw [Complex.cpow_neg_one]
      calc
        (t : ℂ) * ((t : ℂ) ^ (-s) * (t : ℂ)⁻¹) =
            ((t : ℂ) * (t : ℂ)⁻¹) * (t : ℂ) ^ (-s) := by ac_rfl
        _ = (t : ℂ) ^ (-s) := by rw [mul_inv_cancel₀ htC, one_mul]

/-- The exact pointwise floor-to-fractional-part identity used in the
principal zeta correction integral. -/
theorem natFloor_cpow_split {t : ℝ} {s : ℂ} (ht : 1 < t) :
    (Nat.floor t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (t : ℂ) ^ (-s) - ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
  have ht0 : 0 ≤ t := le_of_lt (lt_trans zero_lt_one ht)
  have hnat : ((Nat.floor t : ℕ) : ℝ) = (Int.floor t : ℝ) :=
    natCast_floor_eq_intCast_floor ht0
  have hfloor : (Int.floor t : ℝ) = t - Int.fract t :=
    (eq_sub_iff_add_eq).2 (Int.floor_add_fract t)
  have hfloorC : ((Nat.floor t : ℕ) : ℂ) = ((t - Int.fract t : ℝ) : ℂ) := by
    exact_mod_cast hnat.trans hfloor
  have htpos : 0 < t := lt_trans zero_lt_one ht
  calc
    (Nat.floor t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        ((t : ℂ) - ((Int.fract t : ℝ) : ℂ)) * (t : ℂ) ^ (-s - 1) := by
          rw [show -(s + 1) = -s - 1 by ring, hfloorC]
          push_cast
          rfl
    _ = (t : ℂ) ^ (-s) - ((Int.fract t : ℝ) : ℂ) *
          (t : ℂ) ^ (-s - 1) := by
            rw [sub_mul, positiveReal_mul_cpow_neg_sub_one htpos]

end FractionalPrimes.Literature.Reciprocal
