module

public import FractionalPrimes.Chebyshev

@[expose] public section

namespace FractionalPrimes

/-- Convert the filtered reciprocal-prime sum to the weighted prime-indicator
sum, with the reciprocal written using division as in the Cramér cutoff proof. -/
theorem filtered_reciprocal_sum_eq_primeIndicator_weighted_sum (S : Finset ℕ) :
    (∑ p ∈ S.filter Nat.Prime, 1 / (p : ℝ)) =
      ∑ p ∈ S, (p : ℝ)⁻¹ * primeIndicator p := by
  calc
    (∑ p ∈ S.filter Nat.Prime, 1 / (p : ℝ)) =
        ∑ p ∈ S.filter Nat.Prime, (p : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro p hp
          exact one_div (p : ℝ)
    _ = ∑ p ∈ S, (p : ℝ)⁻¹ * primeIndicator p :=
      (primeIndicator_weighted_sum_eq_filter S).symm

end FractionalPrimes

end
