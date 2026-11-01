module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletZetaIdentification
public import FractionalPrimes.Literature.Reciprocal.PrincipalLFunctionAdapter
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

@[expose] public section

namespace FractionalPrimes.Literature.Reciprocal

/-- On the pole-excluded right half-plane, the finite-Euler-factor principal
branch agrees with Mathlib's named principal Dirichlet L-function. -/
theorem principalContinuedDirichletL_eq_LFunction
    {q : ℕ} [NeZero q] {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    principalContinuedDirichletL (q := q) s hs hs1 =
      _root_.DirichletCharacter.LFunction (1 : _root_.DirichletCharacter ℂ q) s := by
  rw [principalContinuedDirichletL,
    continuedDirichletZ_eq_riemannZeta hs hs1,
    principalLFunction_eq_eulerProduct_riemannZeta (q := q) hs1]
  ring

/-- In the half-plane of absolute convergence, the principal branch's exact
finite Euler product is its positive-integer Dirichlet series. -/
theorem principalContinuedDirichletL_eq_LSeries_of_one_lt_re
    {q : ℕ} [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    principalContinuedDirichletL (q := q) s (by linarith) (by
      intro hs1
      have hre := congrArg Complex.re hs1
      norm_num at hre
      linarith) =
      LSeries ((FractionalPrimes.Literature.Twisted.principalCharacter q) ·) s := by
  have hs1 : s ≠ 1 := by
    intro hs1
    have hre := congrArg Complex.re hs1
    norm_num at hre
    linarith
  calc
    principalContinuedDirichletL (q := q) s (by linarith) hs1 =
        _root_.DirichletCharacter.LFunction (1 : _root_.DirichletCharacter ℂ q) s :=
      principalContinuedDirichletL_eq_LFunction (q := q) (by linarith) hs1
    _ = LSeries ((FractionalPrimes.Literature.Twisted.principalCharacter q) ·) s := by
      simpa [FractionalPrimes.Literature.Twisted.principalCharacter] using
        (_root_.DirichletCharacter.LFunction_eq_LSeries
          (1 : _root_.DirichletCharacter ℂ q) hs)

#print axioms principalContinuedDirichletL_eq_LFunction
#print axioms principalContinuedDirichletL_eq_LSeries_of_one_lt_re

end FractionalPrimes.Literature.Reciprocal

end
