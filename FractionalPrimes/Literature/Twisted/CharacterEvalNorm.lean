module

public import FractionalPrimes.Literature.Twisted.CharacterDataAdapter

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

/-- Dirichlet-character evaluation on integers has modulus at most one,
including nonunits, where the character is extended by zero. -/
theorem evalInt_norm_le_one {q : ℕ} (χ : BlueprintCharacter q) (n : ℤ) :
    ‖evalInt χ n‖ ≤ 1 := by
  simpa [evalInt] using χ.norm_le_one (n : ZMod q)

/-- Any remainder block of at most `q` consecutive integer character values
has total norm at most `q`. The start is an arbitrary natural offset, as in
the complete-period decomposition of `1,…,Nat.floor u`. -/
theorem evalInt_sum_range_norm_le_modulus {q r : ℕ}
    (χ : BlueprintCharacter q) (a : ℕ) (hrq : r ≤ q) :
    ‖∑ n ∈ Finset.range r, evalInt χ ((a + n : ℕ) : ℤ)‖ ≤ (q : ℝ) := by
  calc
    ‖∑ n ∈ Finset.range r, evalInt χ ((a + n : ℕ) : ℤ)‖ ≤
        ∑ n ∈ Finset.range r, ‖evalInt χ ((a + n : ℕ) : ℤ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range r, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact evalInt_norm_le_one χ _
    _ = (r : ℝ) := by simp
    _ ≤ (q : ℝ) := by exact_mod_cast hrq

#print axioms evalInt_norm_le_one
#print axioms evalInt_sum_range_norm_le_modulus

end FractionalPrimes.Literature.Twisted
