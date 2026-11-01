module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite multiplicativity of the source Mellin phase

The short-group transfer is a finite sum over factor tuples.  This file
records the exact identity that factors the source power of the tuple product
into the powers carried by the individual factors.  The proof uses Mathlib's
nonnegative-real complex-power product identity, so it includes zero inputs
as well as the positive source supports.
-/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open Finset

/-- A complex power of a finite product of natural inputs factors as the
product of the individual powers, with no positivity restriction. -/
theorem smoothGroupCpow_natProduct
    {ι : Type*} (S : Finset ι) (n : ι → ℕ) (s : ℂ) :
    ((∏ i ∈ S, n i : ℕ) : ℂ) ^ s =
      ∏ i ∈ S, (n i : ℂ) ^ s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, ih]

/-- The exact multiplicative phase appearing in the source summand
`n^(-1/2-it)` factors over any finite tuple of natural arguments. -/
theorem smoothGroupMellinPhase_finProduct
    {ι : Type*} (S : Finset ι) (n : ι → ℕ) (t : ℝ) :
    ((∏ i ∈ S, n i : ℕ) : ℂ) ^
        (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) =
      ∏ i ∈ S,
        (n i : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) :=
  smoothGroupCpow_natProduct S n
    (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))

end FractionalPrimes.Literature.DirichletAdapter

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothGroupCpow_natProduct
#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothGroupMellinPhase_finProduct
