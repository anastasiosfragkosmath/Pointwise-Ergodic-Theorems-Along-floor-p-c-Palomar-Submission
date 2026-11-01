module

public import FractionalPrimes.Literature.Polynomial.ResiduePrefixEnvelope

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open scoped BigOperators

/-- On an integer-centred interval, the residue prefix with modulus one,
residue zero, and full length is exactly the unrestricted interval sum.  This
is the discrete identity used by the degree-zero branch of
`lupo:conditional-integer`. -/
theorem residuePrefixSum_one_zero_eq_interval
    (X H : ℕ) (w : ℤ → ℂ) :
    residuePrefixSum X H 1 0 w =
      ∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ), w n := by
  classical
  have hinterval : realIntegerInterval (X : ℝ) (H : ℝ) =
      Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ) := by
    ext n
    rw [mem_realIntegerInterval_iff]
    simp only [Finset.mem_Ioc]
    constructor
    · rintro ⟨hnlo, hnhi⟩
      exact ⟨by exact_mod_cast hnlo, by exact_mod_cast hnhi⟩
    · rintro ⟨hnlo, hnhi⟩
      exact ⟨by exact_mod_cast hnlo, by exact_mod_cast hnhi⟩
  unfold residuePrefixSum
  rw [hinterval]
  simp [Int.modEq_one]

/-- The full interval sum is one of the residue-prefix values in the
envelope as soon as the allowed modulus range contains one. -/
theorem norm_sum_interval_le_residuePrefixEnvelope
    (X H : ℕ) (w : ℤ → ℂ) (Q : ℝ) (hQ : 1 ≤ Q) :
    ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ), w n‖ ≤
      residuePrefixEnvelope X H w Q := by
  rw [← residuePrefixSum_one_zero_eq_interval]
  classical
  let P := residuePrefixParameters H Q
  let values := P.image fun t =>
    ‖residuePrefixSum X t.2 t.1.1 t.1.2 w‖
  have hqfloor : 1 ≤ Nat.floor Q := by
    have hf := Nat.lt_floor_add_one Q
    by_contra hn
    have hzero : Nat.floor Q = 0 := by omega
    have hf' : Q < 1 := by simpa [hzero] using hf
    exact (not_lt_of_ge hQ) hf'
  have hmem : ((1, 0), H) ∈ P := by
    apply (residuePrefixParameters_mem_iff H Q 1 0 H).2
    exact ⟨by norm_num, hqfloor, by omega, le_rfl⟩
  have hvalue : ‖residuePrefixSum X H 1 0 w‖ ∈ insert 0 values := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨((1, 0), H), hmem, rfl⟩
  unfold residuePrefixEnvelope
  exact Finset.le_max' _ _ hvalue

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.residuePrefixSum_one_zero_eq_interval
#print axioms FractionalPrimes.Literature.Polynomial.norm_sum_interval_le_residuePrefixEnvelope
