module
public import FractionalPrimes.Literature.Polynomial.ResiduePrefixMellinIndices
public import Mathlib.Tactic
@[expose] public section
namespace FractionalPrimes.Literature.Polynomial
open scoped BigOperators

theorem residuePrefixSum_norm_le_pointwise
    (X m q b : ℕ) (w : ℤ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n ∈ Finset.Ioc X (X + m), ‖w (n : ℤ)‖ ≤ B) :
    ‖residuePrefixSum X m q b w‖ ≤ (m : ℝ) * B := by
  rw [residuePrefixSum_eq_mellinWindowSum, mellinWindowAverageIndices_natCast]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc X (X + m),
        ‖w (n : ℤ) * (if Int.ModEq (q : ℤ) (n : ℤ) (b : ℤ) then 1 else 0)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc X (X + m), B := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs
      · simpa using hw n hn
      · simpa using hB
    _ = _ := by simp

/-- Exact integer cardinality gives `H B`, without the real-interval `+1` loss. -/
theorem residuePrefixEnvelope_le_pointwise
    (X H : ℕ) (w : ℤ → ℂ) {Q B : ℝ}
    (hQ : 1 ≤ Q) (hB : 0 ≤ B)
    (hw : ∀ n ∈ Finset.Ioc X (X + H), ‖w (n : ℤ)‖ ≤ B) :
    residuePrefixEnvelope X H w Q ≤ (H : ℝ) * B := by
  obtain ⟨q, b, m, hq, hqQ, hb, hm, hEq⟩ :=
    residuePrefixEnvelope_attained X H w Q hQ
  rw [hEq]
  have hsmall : ∀ n ∈ Finset.Ioc X (X + m), ‖w (n : ℤ)‖ ≤ B := by
    intro n hn
    apply hw n
    simp only [Finset.mem_Ioc] at hn ⊢
    omega
  exact (residuePrefixSum_norm_le_pointwise X m q b w hB hsmall).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hB)

#print axioms residuePrefixSum_norm_le_pointwise
#print axioms residuePrefixEnvelope_le_pointwise
end FractionalPrimes.Literature.Polynomial
end
