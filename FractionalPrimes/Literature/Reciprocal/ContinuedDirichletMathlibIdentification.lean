module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletLFunctionIdentification
public import FractionalPrimes.Literature.Reciprocal.PrincipalContinuedDirichletSeriesIdentity

@[expose] public section

namespace FractionalPrimes.Literature.Reciprocal

/-- The exact two-branch continuation from `lrc:dirichlet-data` agrees with
Mathlib's Dirichlet L-function on the positive half-plane away from the
principal pole. -/
theorem continuedDirichletL_eq_LFunction_of_pos_re
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re)
    (hnotpole : ¬ (χ = FractionalPrimes.Literature.Twisted.principalCharacter q ∧ s = 1)) :
    continuedDirichletL χ s hs hnotpole =
      _root_.DirichletCharacter.LFunction χ s := by
  classical
  unfold continuedDirichletL
  by_cases hχ : χ = FractionalPrimes.Literature.Twisted.principalCharacter q
  · have hs1 : s ≠ 1 := by
      intro hs1
      exact hnotpole ⟨hχ, hs1⟩
    simp only [dif_pos hχ]
    calc
      principalContinuedDirichletL (q := q) s hs _ =
          _root_.DirichletCharacter.LFunction
            (1 : _root_.DirichletCharacter ℂ q) s := by
              exact principalContinuedDirichletL_eq_LFunction hs hs1
      _ = _root_.DirichletCharacter.LFunction χ s := by
        simpa [hχ, FractionalPrimes.Literature.Twisted.principalCharacter]
  · simp only [dif_neg hχ]
    exact nonprincipalContinuedDirichletL_eq_LFunction_of_pos_re χ hχ hs

/-- In the absolute-convergence half-plane, the exact two-branch continuation
equals the positive-integer Dirichlet L-series. -/
theorem continuedDirichletL_eq_LSeries_of_one_lt_re
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    continuedDirichletL χ s (by linarith) (by
      rintro ⟨_, hs1⟩
      have hre := congrArg Complex.re hs1
      norm_num at hre
      linarith) = LSeries (χ ·) s := by
  have hnotpole :
      ¬ (χ = FractionalPrimes.Literature.Twisted.principalCharacter q ∧ s = 1) := by
    rintro ⟨_, hs1⟩
    have hre := congrArg Complex.re hs1
    norm_num at hre
    linarith
  rw [continuedDirichletL_eq_LFunction_of_pos_re χ (by linarith) hnotpole]
  exact _root_.DirichletCharacter.LFunction_eq_LSeries χ hs

#print axioms continuedDirichletL_eq_LFunction_of_pos_re
#print axioms continuedDirichletL_eq_LSeries_of_one_lt_re

end FractionalPrimes.Literature.Reciprocal

end
