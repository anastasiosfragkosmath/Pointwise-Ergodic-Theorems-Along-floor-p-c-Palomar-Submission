module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

namespace FractionalPrimes.Literature.MobiusToLong

/-- For one fixed prime, the total von Mangoldt weight of its positive powers
up to `x` is at most `log x`. The exponent cutoff is written with the exact
real logarithmic quotient used to count those powers. -/
theorem log_weight_prime_power_exponents_le {x : ℝ} (hx : 1 ≤ x)
    {p : ℕ} (hp : p.Prime) :
    (∑ _k ∈ Finset.Icc 1 (Nat.floor (Real.log x / Real.log (p : ℝ))),
      Real.log (p : ℝ)) ≤ Real.log x := by
  have hp_one : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp_one
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  let t : ℝ := Real.log x / Real.log (p : ℝ)
  have ht : 0 ≤ t := div_nonneg hlogx hlogp.le
  have hfloor : (Nat.floor t : ℝ) ≤ t := Nat.floor_le ht
  calc
    (∑ k ∈ Finset.Icc 1 (Nat.floor t), Real.log (p : ℝ)) =
        (Nat.floor t : ℝ) * Real.log (p : ℝ) := by simp
    _ ≤ t * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_right hfloor hlogp.le
    _ = Real.log x := by
      dsimp [t]
      field_simp [hlogp.ne']
  

/-- The sum of the logarithms of the distinct prime divisors of `q` is at
most `log q`. Mathlib's product of the distinct prime divisors divides `q`.
-/
theorem sum_log_primeFactors_le_log {q : ℕ} (hq : 0 < q) :
    (∑ p ∈ q.primeFactors, Real.log (p : ℝ)) ≤ Real.log (q : ℝ) := by
  have hprod_dvd : (∏ p ∈ q.primeFactors, p) ∣ q := Nat.prod_primeFactors_dvd q
  have hprod_le : (∏ p ∈ q.primeFactors, p) ≤ q := Nat.le_of_dvd hq hprod_dvd
  have hprod_pos : 0 < (∏ p ∈ q.primeFactors, (p : ℝ)) := by
    exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr (Nat.pos_of_mem_primeFactors hp)
  have hcast_le : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ (q : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hprod_le
  calc
    (∑ p ∈ q.primeFactors, Real.log (p : ℝ)) =
        Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
          symm
          apply Real.log_prod
          intro p hp
          exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_mem_primeFactors hp)))
    _ ≤ Real.log (q : ℝ) := Real.log_le_log hprod_pos hcast_le

/-- The number of distinct prime divisors of `q` is at most `log q / log 2`.
This is the count used in the principal-character correction. -/
theorem primeFactors_card_le_log_div_log_two {q : ℕ} (hq : 0 < q) :
    (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := by
  have hsum_lower :
      (q.primeFactors.card : ℝ) * Real.log 2 ≤
        ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
    calc
      (q.primeFactors.card : ℝ) * Real.log 2 =
          ∑ p ∈ q.primeFactors, Real.log 2 := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Real.log_le_log (by norm_num)
        exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hlog2).2
  exact hsum_lower.trans (sum_log_primeFactors_le_log hq)

/-- Summing the per-prime `log x` bound over the distinct prime divisors of
`q` gives the exact logarithmic modulus correction from the paper. -/
theorem sum_log_x_primeFactors_le {x : ℝ} (hx : 1 ≤ x) {q : ℕ} (hq : 0 < q) :
    (∑ _p ∈ q.primeFactors, Real.log x) ≤
      (Real.log (q : ℝ) / Real.log 2) * Real.log x := by
  calc
    (∑ p ∈ q.primeFactors, Real.log x) =
        (q.primeFactors.card : ℝ) * Real.log x := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Real.log (q : ℝ) / Real.log 2) * Real.log x :=
      mul_le_mul_of_nonneg_right (primeFactors_card_le_log_div_log_two hq)
        (Real.log_nonneg hx)

end FractionalPrimes.Literature.MobiusToLong

end
