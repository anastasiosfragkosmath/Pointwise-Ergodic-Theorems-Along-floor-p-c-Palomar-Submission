module

public import FractionalPrimes.Literature.Uniformity.DivisorPrimePowerMoment
public import FractionalPrimes.Literature.Uniformity.DivisorMultiplicativeLift

/-!
# Divisor moment inequality

This module assembles the exact prime-power combinatorial estimate with the
multiplicative reduction to all positive integers.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

/-- For positive `k` and `r`, the `r`th pointwise moment of `d_k` is bounded
by `d_{k^r}` on every positive integer. -/
theorem divisorFunction_moment
    (k r : ℕ) (hk : 0 < k) (hr : 0 < r) (n : PositiveInteger) :
    divisorFunction k n ^ r ≤ divisorFunction (k ^ r) n := by
  exact divisorFunction_moment_of_prime_power_bounds
    (k := k) (r := r)
    (fun p a hp => by
      simpa only [divisorFunction] using
        (divisorFunction_prime_pow_moment p k r a hp hk hr))
    n

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.divisorFunction_moment
