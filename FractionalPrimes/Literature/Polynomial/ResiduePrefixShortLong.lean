module
public import FractionalPrimes.Literature.Polynomial.ResiduePrefixEnvelope
public import Mathlib.Tactic
@[expose] public section
namespace FractionalPrimes.Literature.Polynomial

/-- Transfer a uniform prefix estimate to the exact finite residue maximum. -/
theorem residuePrefixEnvelope_le_of_prefixBounds
    (X H : ℕ) (w : ℤ → ℂ) {Q B : ℝ} (hQ : 1 ≤ Q)
    (hbound : ∀ q b m : ℕ, 1 ≤ q → (q : ℝ) ≤ Q → b < q → m ≤ H →
      ‖residuePrefixSum X m q b w‖ ≤ B) :
    residuePrefixEnvelope X H w Q ≤ B := by
  obtain ⟨q, b, m, hq, hqQ, hb, hm, hEq⟩ :=
    residuePrefixEnvelope_attained X H w Q hQ
  rw [hEq]
  exact hbound q b m hq hqQ hb hm

/-- The source split at `H log(X)^(-2a)`, with exact equality assigned to the
short branch and permitted in the long branch as well. -/
theorem residuePrefixEnvelope_le_of_short_long
    (X H : ℕ) (w : ℤ → ℂ) {Q cutoff B C : ℝ}
    (hQ : 1 ≤ Q) (hB : 0 ≤ B) (hC : 1 ≤ C)
    (hshort : ∀ q b m : ℕ, 1 ≤ q → (q : ℝ) ≤ Q → b < q → m ≤ H →
      (m : ℝ) ≤ cutoff → ‖residuePrefixSum X m q b w‖ ≤ B)
    (hlong : ∀ q b m : ℕ, 1 ≤ q → (q : ℝ) ≤ Q → b < q → m ≤ H →
      cutoff ≤ (m : ℝ) → ‖residuePrefixSum X m q b w‖ ≤ C * B) :
    residuePrefixEnvelope X H w Q ≤ C * B := by
  apply residuePrefixEnvelope_le_of_prefixBounds X H w hQ
  intro q b m hq hqQ hb hm
  by_cases hsmall : (m : ℝ) ≤ cutoff
  · exact (hshort q b m hq hqQ hb hm hsmall).trans
      (by simpa using mul_le_mul_of_nonneg_right hC hB)
  · exact hlong q b m hq hqQ hb hm (le_of_lt (not_le.mp hsmall))

#print axioms residuePrefixEnvelope_le_of_prefixBounds
#print axioms residuePrefixEnvelope_le_of_short_long
end FractionalPrimes.Literature.Polynomial
end
