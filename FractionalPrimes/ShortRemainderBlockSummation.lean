module

public import FractionalPrimes.ArithmeticBasics

/-! Finite nonnegative block aggregation used in the approved
`ar:short-remainder` proof. This isolates the partition bookkeeping
before the independent polynomial-uniformity input is supplied. -/

@[expose] public section

namespace FractionalPrimes

/-- On the exact full blocks of `ar:partition`, a nonnegative residual
sum is bounded by its sum over the full interval. No overlap or
endpoint error is introduced. -/
theorem exists_arithmetic_fullBlock_nonnegative_sum_le {c : ℝ}
    (hc : 1 < c) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
      ∀ K' : ℕ, K ≤ K' → K' ≤ 2 * K →
      let H : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)
      let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
      ∀ f : ℕ → ℝ, (∀ n, 0 ≤ f n) →
        (∑ v ∈ Finset.range q,
          ∑ n ∈ Finset.Ico (K + 1 + v * H)
            (K + 1 + (v + 1) * H), f n) ≤
          ∑ n ∈ Finset.Ico (K + 1) (K' + 1), f n := by
  obtain ⟨K₀, hK₀, hpartition⟩ :=
    exists_arithmetic_shortBlock_partition hc
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK K' hKK' hK'2
  let H : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)
  let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
  let r : ℕ := (K' - K) % H
  have hdata := hpartition K hK K' hKK' hK'2
  dsimp only at hdata ⊢
  intro f hf
  have hsum := hdata.1 f
  have htail : 0 ≤
      ∑ n ∈ Finset.Ico (K + 1 + q * H)
        (K + 1 + q * H + r), f n := by
    exact Finset.sum_nonneg (by intro n hn; exact hf n)
  dsimp only [H, q, r] at hsum htail
  linarith

end FractionalPrimes

#print axioms FractionalPrimes.exists_arithmetic_fullBlock_nonnegative_sum_le
