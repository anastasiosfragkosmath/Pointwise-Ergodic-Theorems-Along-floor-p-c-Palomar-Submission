module
public import OAI.NumberTheory.DirichletL.Nonvanishing
@[expose] public section

namespace FractionalPrimes.Literature.Reciprocal

/-- The exact imported E1 result, with Mathlib's root-qualified
Dirichlet `L`-function in the conclusion. This is the library-facing
adapter from the approved `lra:imported-nonvanishing` blueprint item. -/
theorem importedNonvanishing
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
    χ hs hpole

end FractionalPrimes.Literature.Reciprocal
