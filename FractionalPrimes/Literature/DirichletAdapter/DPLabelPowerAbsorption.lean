module

public import Mathlib.Tactic

@[expose] public section
namespace FractionalPrimes.Literature.DirichletAdapter
noncomputable section

/-- The twenty powers spent on the retained source labels are paid
from the component's twenty-one spare logarithmic powers. -/
theorem dpLabelPowerAbsorption
    {L X A C : ℝ} (hL : 1 ≤ L) (hC : 0 ≤ C) :
    10 * (8 * L) ^ 20 * (C * Real.sqrt X * L ^ (-(A + 21))) ≤
      (10 * (8 : ℝ) ^ 20 * C) * Real.sqrt X * L ^ (-A) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpow : L ^ (20 : ℕ) * L ^ (-(A + 21)) ≤ L ^ (-A) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hLpos]
    apply Real.rpow_le_rpow_of_exponent_le hL
    norm_num only [Nat.cast_ofNat]
    linarith
  calc
    _ = (10 * (8 : ℝ) ^ 20 * C * Real.sqrt X) *
          (L ^ (20 : ℕ) * L ^ (-(A + 21))) := by
      rw [mul_pow]
      ring
    _ ≤ (10 * (8 : ℝ) ^ 20 * C * Real.sqrt X) * L ^ (-A) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

#print axioms dpLabelPowerAbsorption
end
end FractionalPrimes.Literature.DirichletAdapter
