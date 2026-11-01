module

public import FractionalPrimes.Literature.Uniformity.DivisorMomentInequality
public import FractionalPrimes.Literature.Uniformity.DivisorSummatoryBound

/-!
# Harmonic moments of divisor functions

This is the exact reciprocal-weighted estimate in
`ltw:harmonic-moment`, using the already checked pointwise divisor
moment and weighted summatory bounds.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity

/-- `ltw:harmonic-moment`, including the endpoint `Y=1` and the
constant-one bound from the approved blueprint. -/
theorem harmonicDivisorMoment
    (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (Y : ℝ) (hY : 1 ≤ Y) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        ((divisorCoefficient k n : ℝ) ^ r) / (n : ℝ)) ≤
      (1 + Real.log Y) ^ (k ^ r) := by
  calc
    (∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        ((divisorCoefficient k n : ℝ) ^ r) / (n : ℝ)) ≤
      ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        (divisorCoefficient (k ^ r) n : ℝ) / (n : ℝ) := by
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
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
          exact_mod_cast hnat
    _ ≤ (1 + Real.log Y) ^ (k ^ r) :=
      divisorWeightedSummatory_bound (k ^ r) Y hY

#print axioms harmonicDivisorMoment

end FractionalPrimes.Literature.Twisted

end
