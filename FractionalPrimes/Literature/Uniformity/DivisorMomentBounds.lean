module

public import FractionalPrimes.Literature.Uniformity.DivisorFunctions
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Divisor moment bounds

This file develops the exact prime-power formula used in the approved
divisor-moment argument.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

theorem divisorFunction_succ_prime_pow (p k a : ℕ) (hp : p.Prime) :
    (ArithmeticFunction.zeta ^ (k + 1)) (p ^ a) = (a + k).choose k := by
  induction k generalizing a with
  | zero =>
      rw [zero_add, pow_one]
      simpa [Nat.choose_zero_right] using
        ArithmeticFunction.zeta_apply_ne (pow_ne_zero _ hp.ne_zero)
  | succ k ih =>
      calc
        (ArithmeticFunction.zeta ^ ((k + 1) + 1)) (p ^ a) =
            ∑ d ∈ (p ^ a).divisors,
              (ArithmeticFunction.zeta ^ (k + 1)) d := by
                rw [pow_succ, ArithmeticFunction.mul_zeta_apply]
        _ = ∑ i ∈ Finset.range (a + 1),
              (ArithmeticFunction.zeta ^ (k + 1)) (p ^ i) := by
                rw [Nat.divisors_prime_pow hp, Finset.sum_map]
                apply Finset.sum_congr rfl
                intro i hi
                rfl
        _ = ∑ i ∈ Finset.range (a + 1), (i + k).choose k := by
              apply Finset.sum_congr rfl
              intro i hi
              exact ih i
        _ = (a + k + 1).choose (k + 1) := by
              simpa [Nat.add_assoc] using Nat.sum_range_add_choose a k

theorem positiveDivisorFunction_prime_pow (p k a : ℕ) (hp : p.Prime) :
    divisorFunction (k + 1) ⟨p ^ a, Nat.pow_pos hp.pos⟩ = (a + k).choose k := by
  change (ArithmeticFunction.zeta ^ (k + 1)) (p ^ a) = (a + k).choose k
  exact divisorFunction_succ_prime_pow p k a hp

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.divisorFunction_succ_prime_pow
#print axioms FractionalPrimes.Literature.Uniformity.positiveDivisorFunction_prime_pow
