module

public import Mathlib

@[expose] public section

namespace FractionalPrimes.Literature.Reciprocal

/-- The partial sum of the constant-one sequence through `n` is `n`.
This is the finite-sum identity needed to turn Mathlib's L-series integral
into the floor integral in the zeta continuation formula. -/
theorem sum_one_Icc_eq_natCast (n : ℕ) :
    (∑ _ ∈ Finset.Icc 1 n, (1 : ℂ)) = (n : ℂ) := by
  simp [Finset.sum_const, Nat.card_Icc]

end FractionalPrimes.Literature.Reciprocal
