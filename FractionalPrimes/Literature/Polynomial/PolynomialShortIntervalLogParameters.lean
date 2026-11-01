module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Parameter selection for the positive-degree conditional integer branch

This isolates the first scalar choice in the positive-degree proof of
`lupo:conditional-integer`: choose `D`, define `E`, then choose `a` above the
PTW threshold and both source degree budgets.  The statement leaves all
arithmetic inverse and PMA constants as explicit parameters.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

/-- The exact logarithmic parameters selected at the beginning of the
positive-degree branch of `lupo:conditional-integer`.  In particular, the
strict maximum includes the source PTW threshold, `D+E+3`, and `d+3`, and
`a₀` is the prescribed source value. -/
theorem exists_conditionalIntegerLogParameters
    (d c b : ℕ) (A aStar : ℝ) :
    ∃ D E a : ℕ, ∃ a₀ : ℝ,
      A + (b : ℝ) + 5 < (D : ℝ) ∧
      E = 2 * c * D + 3 ∧
      max aStar (max ((D : ℝ) + (E : ℝ) + 3) ((d : ℝ) + 3)) < (a : ℝ) ∧
      a₀ = A + 2 * (E : ℝ) + 50 * (a : ℝ) + 3 := by
  obtain ⟨D, hD⟩ := exists_nat_gt (A + (b : ℝ) + 5)
  let E : ℕ := 2 * c * D + 3
  let M : ℝ :=
    max aStar (max ((D : ℝ) + (E : ℝ) + 3) ((d : ℝ) + 3))
  obtain ⟨a, ha⟩ := exists_nat_gt M
  refine ⟨D, E, a, A + 2 * (E : ℝ) + 50 * (a : ℝ) + 3,
    hD, ?_, ha, rfl⟩
  rfl

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.exists_conditionalIntegerLogParameters
