module

public import FractionalPrimes.Literature.Uniformity.DivisorMomentInequality
public import FractionalPrimes.Literature.Uniformity.DivisorSummatoryBound

/-!
# Explicit divisor moments

This module assembles the pointwise moment inequality and the constant-one
summatory divisor estimate into the exact bound in `lu:divisor-moments`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

/-- The exact explicit moment bound from `lu:divisor-moments`, with the real
cutoff represented by its natural floor. -/
theorem divisorMomentBound
    (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (Y : ℝ) (hY : 1 ≤ Y) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        ((divisorCoefficient k n : ℝ) ^ r)) ≤
      Y * (1 + Real.log Y) ^ (k ^ r - 1) := by
  have hkr : 1 ≤ k ^ r := by
    have hkpos : 0 < k := by omega
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero r (Nat.ne_of_gt hkpos))
  calc
    (∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        ((divisorCoefficient k n : ℝ) ^ r)) ≤
      ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        (divisorCoefficient (k ^ r) n : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
          have hpoint := divisorFunction_moment k r (by omega) (by omega)
            ⟨n, hnpos⟩
          have hnat : divisorCoefficient k n ^ r ≤
              divisorCoefficient (k ^ r) n := by
            rw [divisorCoefficient_eq_divisorFunction k n hnpos,
              divisorCoefficient_eq_divisorFunction (k ^ r) n hnpos]
            exact hpoint
          exact_mod_cast hnat
    _ ≤ Y * (1 + Real.log Y) ^ (k ^ r - 1) :=
      divisorSummatory_bound (k ^ r) hkr Y hY

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.divisorMomentBound
