module
public import FractionalPrimes.Literature.Twisted.DivisorTwentyBound
@[expose] public section
namespace FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
theorem divisorCoefficient_succ_prime_pow_le_two_pow
    (k p e : ℕ) (hp : p.Prime) :
    divisorCoefficient (k + 1) (p ^ e) ≤
      divisorCoefficient 2 (p ^ e) ^ (k + 1) := by
  have hpos : 0 < p ^ e := Nat.pow_pos hp.pos
  rw [divisorCoefficient_eq_divisorFunction (k + 1) (p ^ e) hpos,
    divisorCoefficient_eq_divisorFunction 2 (p ^ e) hpos]
  have hk : divisorFunction (k + 1) ⟨p ^ e, hpos⟩ =
      (e + k).choose k := by
    simpa using positiveDivisorFunction_prime_pow p k e hp
  have h2 : divisorFunction 2 ⟨p ^ e, hpos⟩ = e + 1 := by
    simpa using positiveDivisorFunction_prime_pow p 1 e hp
  rw [hk, h2]
  calc
    (e + k).choose k ≤ (e + 1) ^ k :=
      Nat.choose_add_le_add_one_pow e k
    _ ≤ (e + 1) ^ (k + 1) := by
      exact pow_le_pow_right₀ (by omega : 1 ≤ e + 1) (by omega)

/-- The positive-order divisor coefficient is bounded by the corresponding
power of the ordinary divisor count. -/
theorem divisorCoefficient_succ_le_two_pow
    (k n : ℕ) (hn : 0 < n) :
    divisorCoefficient (k + 1) n ≤ divisorCoefficient 2 n ^ (k + 1) := by
  rw [divisorCoefficient_eq_divisorFunction (k + 1) n hn,
    divisorCoefficient_eq_divisorFunction 2 n hn,
    divisorFunction_factorization (k + 1) ⟨n, hn⟩,
    divisorFunction_factorization 2 ⟨n, hn⟩]
  simp only [Finsupp.prod]
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod
  intro p hp'
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (by
    simpa only [Nat.support_factorization] using hp')
  have h := divisorCoefficient_succ_prime_pow_le_two_pow k p (n.factorization p) hp
  simpa only [divisorCoefficient, pow_succ, pow_zero, mul_one] using h

#print axioms divisorCoefficient_succ_prime_pow_le_two_pow
#print axioms divisorCoefficient_succ_le_two_pow
end FractionalPrimes.Literature.Twisted
end
