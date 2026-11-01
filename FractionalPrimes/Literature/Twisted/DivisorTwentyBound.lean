module

public import FractionalPrimes.Literature.Uniformity.DivisorMomentBounds
public import FractionalPrimes.Literature.Uniformity.DivisorMultiplicativeLift
public import FractionalPrimes.Literature.Uniformity.DivisorSummatoryBound
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# The twenty-fold divisor coefficient bound

This is the prime-power inequality explicitly used in the approved
proof of `ltw:component-mass`, lifted through multiplicativity.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity

/-- At a prime power, the twenty-fold divisor count is at most the
twentieth power of the ordinary divisor count. -/
theorem divisorCoefficient_twenty_prime_pow_le
    (p e : ℕ) (hp : p.Prime) :
    divisorCoefficient 20 (p ^ e) ≤
      divisorCoefficient 2 (p ^ e) ^ 20 := by
  have hpos : 0 < p ^ e := Nat.pow_pos hp.pos
  rw [divisorCoefficient_eq_divisorFunction 20 (p ^ e) hpos,
    divisorCoefficient_eq_divisorFunction 2 (p ^ e) hpos]
  have h20 : divisorFunction 20 ⟨p ^ e, hpos⟩ =
      (e + 19).choose 19 := by
    simpa using positiveDivisorFunction_prime_pow p 19 e hp
  have h2 : divisorFunction 2 ⟨p ^ e, hpos⟩ = e + 1 := by
    simpa using positiveDivisorFunction_prime_pow p 1 e hp
  rw [h20, h2]
  calc
    (e + 19).choose 19 ≤ (e + 1) ^ 19 :=
      Nat.choose_add_le_add_one_pow e 19
    _ ≤ (e + 1) ^ 20 := by
      exact pow_le_pow_right₀ (by omega : 1 ≤ e + 1) (by omega)

/-- For every positive integer, `d₂₀(n) ≤ τ(n)^20` exactly as in the
blueprint proof of the selected-component mass estimate. -/
theorem divisorCoefficient_twenty_le_two_pow
    (n : ℕ) (hn : 0 < n) :
    divisorCoefficient 20 n ≤ divisorCoefficient 2 n ^ 20 := by
  rw [divisorCoefficient_eq_divisorFunction 20 n hn,
    divisorCoefficient_eq_divisorFunction 2 n hn,
    divisorFunction_factorization 20 ⟨n, hn⟩,
    divisorFunction_factorization 2 ⟨n, hn⟩]
  simp only [Finsupp.prod]
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod
  intro p hp'
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (by
    simpa only [Nat.support_factorization] using hp')
  have h := divisorCoefficient_twenty_prime_pow_le p (n.factorization p) hp
  simpa only [divisorCoefficient, pow_succ, pow_zero, mul_one] using h

#print axioms divisorCoefficient_twenty_prime_pow_le
#print axioms divisorCoefficient_twenty_le_two_pow

end FractionalPrimes.Literature.Twisted

end
