module

public import FractionalPrimes.Literature.Uniformity.DivisorFunctions

/-!
# Multiplicative lift for divisor-function moment inequalities

This module isolates the exact multiplicative reduction from all positive
integers to prime powers for the divisor-function moment inequality.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

theorem divisorFunction_factorization (k : ℕ) (n : PositiveInteger) :
    divisorFunction k n =
      n.1.factorization.prod (fun p a => (ArithmeticFunction.zeta ^ k) (p ^ a)) := by
  change (ArithmeticFunction.zeta ^ k) n.1 =
    n.1.factorization.prod (fun p a => (ArithmeticFunction.zeta ^ k) (p ^ a))
  exact ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
    (ArithmeticFunction.IsMultiplicative.pow ArithmeticFunction.isMultiplicative_zeta)
    (Nat.ne_of_gt n.2)

theorem divisorFunction_pow_factorization (k r : ℕ) (n : PositiveInteger) :
    divisorFunction k n ^ r =
      n.1.factorization.prod
        (fun p a => ((ArithmeticFunction.zeta ^ k) (p ^ a)) ^ r) := by
  rw [divisorFunction_factorization]
  simp only [Finsupp.prod]
  rw [← Finset.prod_pow]

/-- Any pointwise prime-power inequality between these convolution powers
lifts to every positive integer by multiplicative factorization. -/
theorem divisorFunction_moment_of_prime_power_bounds
    {k r : ℕ}
    (hlocal : ∀ p a, p.Prime →
      ((ArithmeticFunction.zeta ^ k) (p ^ a)) ^ r ≤
        (ArithmeticFunction.zeta ^ (k ^ r)) (p ^ a))
    (n : PositiveInteger) :
    divisorFunction k n ^ r ≤ divisorFunction (k ^ r) n := by
  rw [divisorFunction_pow_factorization, divisorFunction_factorization]
  unfold Finsupp.prod
  apply Finset.prod_le_prod
  intro p hp
  exact hlocal p (n.1.factorization p)
    (Nat.prime_of_mem_primeFactors (by
      simpa only [Nat.support_factorization] using hp))

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.divisorFunction_factorization
#print axioms FractionalPrimes.Literature.Uniformity.divisorFunction_pow_factorization
#print axioms FractionalPrimes.Literature.Uniformity.divisorFunction_moment_of_prime_power_bounds
