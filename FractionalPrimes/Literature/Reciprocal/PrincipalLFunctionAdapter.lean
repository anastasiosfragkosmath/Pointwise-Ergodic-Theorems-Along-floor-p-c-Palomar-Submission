module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation

@[expose] public section

namespace FractionalPrimes.Literature.Reciprocal

/-- Mathlib's exact Euler-factor formula for the principal character,
stated with the explicit character and prime-factor product used by the
blueprint. The pole is excluded as in the blueprint. -/
theorem principalLFunction_eq_eulerProduct_riemannZeta
    {q : ℕ} [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    _root_.DirichletCharacter.LFunction (1 : _root_.DirichletCharacter ℂ q) s =
      (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * _root_.riemannZeta s := by
  simpa [_root_.DirichletCharacter.LFunctionTrivChar] using
    (_root_.DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
      (N := q) hs)

end FractionalPrimes.Literature.Reciprocal
