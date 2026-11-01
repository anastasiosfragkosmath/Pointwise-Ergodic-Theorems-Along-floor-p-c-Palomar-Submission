module

public import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! The exact finite congruence reduction used when the other factors of a
smooth Heath--Brown component have been fixed. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

/-- If `m * n₀` lies in the target residue class modulo a positive `q`, then
the solutions in `n` are exactly the residue class of `n₀` modulo
`q / gcd(m,q)`. -/
theorem mul_congruence_iff_reduced_residue
    (m q a n₀ : ℕ) (hq : 0 < q)
    (hsol : m * n₀ ≡ a [MOD q]) :
    ∀ n : ℕ,
      (m * n ≡ a [MOD q]) ↔
        n ≡ n₀ [MOD q / Nat.gcd m q] := by
  intro n
  constructor
  · intro hn
    have hcompare : m * n ≡ m * n₀ [MOD q] := hn.trans hsol.symm
    have hcancelInput : n * m ≡ n₀ * m [MOD q] := by
      simpa [Nat.mul_comm] using hcompare
    simpa [Nat.gcd_comm] using hcancelInput.cancel_right_div_gcd hq
  · intro hn
    let g := Nat.gcd m q
    have hgm : g ∣ m := by
      exact Nat.gcd_dvd_left m q
    have hgq : g ∣ q := by
      exact Nat.gcd_dvd_right m q
    have hgmFactor : g * (m / g) = m := Nat.mul_div_cancel' hgm
    have hgqFactor : g * (q / g) = q := Nat.mul_div_cancel' hgq
    have hqDvd : q ∣ m * (q / g) := by
      refine ⟨m / g, ?_⟩
      calc
        m * (q / g) = (g * (m / g)) * (q / g) :=
          congrArg (fun x => x * (q / g)) hgmFactor.symm
        _ = (g * (q / g)) * (m / g) := by ac_rfl
        _ = q * (m / g) :=
          congrArg (fun x => x * (m / g)) hgqFactor
    have hmul : m * n ≡ m * n₀ [MOD m * (q / g)] := hn.mul_left' m
    have hmodQ : m * n ≡ m * n₀ [MOD q] := hmul.of_dvd hqDvd
    exact hmodQ.trans hsol

#print axioms mul_congruence_iff_reduced_residue

/-- The reduced modulus in the long-factor residue reduction is no larger
than the original modulus. -/
theorem mul_congruence_reduced_modulus_le (m q : ℕ) :
    q / Nat.gcd m q ≤ q := by
  exact Nat.div_le_self q (Nat.gcd m q)

#print axioms mul_congruence_reduced_modulus_le

/-- A fixed linear congruence modulo a positive natural modulus is either
insoluble or is exactly one class modulo the reduced modulus. -/
theorem mul_congruence_empty_or_single_residue
    (m q a : ℕ) (hq : 0 < q) :
    (∀ n : ℕ, ¬ m * n ≡ a [MOD q]) ∨
      ∃ n₀ : ℕ, ∀ n : ℕ,
        (m * n ≡ a [MOD q]) ↔
          n ≡ n₀ [MOD q / Nat.gcd m q] := by
  by_cases h : ∃ n₀ : ℕ, m * n₀ ≡ a [MOD q]
  · rcases h with ⟨n₀, hsol⟩
    exact Or.inr ⟨n₀, mul_congruence_iff_reduced_residue m q a n₀ hq hsol⟩
  · left
    intro n hn
    exact h ⟨n, hn⟩

#print axioms mul_congruence_empty_or_single_residue

end FractionalPrimes.Literature.DirichletAdapter

end
