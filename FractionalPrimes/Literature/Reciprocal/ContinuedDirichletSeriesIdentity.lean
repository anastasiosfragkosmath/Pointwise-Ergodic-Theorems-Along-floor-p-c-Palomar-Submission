module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletData
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

@[expose] public section

noncomputable section

open MeasureTheory Set Asymptotics Filter

namespace FractionalPrimes.Literature.Reciprocal

/-- On `Re(s) > 1`, the nonprincipal integral continuation in the approved
`lrc:dirichlet-data` definition equals Mathlib's Dirichlet L-function.
The proof uses Mathlib's partial-sum integral formula for L-series. -/
theorem nonprincipalContinuedDirichletL_eq_LSeries_of_one_lt_re
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q)
    (hχ : χ ≠ FractionalPrimes.Literature.Twisted.principalCharacter q)
    {s : ℂ} (hs : 1 < s.re) :
    nonprincipalContinuedDirichletL χ hχ s (by linarith) = LSeries (χ ·) s := by
  let f : ℕ → ℂ := fun n => χ (n : ZMod q)
  have hpartial : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ (q : ℝ) := by
    intro n
    by_cases hn : n = 0
    · simp [hn, f]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have h := continuedDirichletPartialSum_norm_le_modulus χ hχ (n : ℝ)
        (by exact_mod_cast hn1)
      simpa [continuedDirichletPartialSum, FractionalPrimes.Literature.Twisted.evalInt,
        f] using h
  have hO :
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
    refine Asymptotics.isBigO_iff.mpr ⟨(q : ℝ), ?_⟩
    filter_upwards [] with n
    simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (q : ℝ))] using hpartial n
  have hsum : LSeries f s =
      s * ∫ t : ℝ in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) := by
    exact LSeries_eq_mul_integral f (r := 0) (by norm_num) (by linarith)
      (by simpa [f] using _root_.DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs) hO
  have hcontinued : LSeries f s =
      nonprincipalContinuedDirichletL χ hχ s (by linarith) := by
    simpa [f, nonprincipalContinuedDirichletL,
      continuedDirichletPartialSumFormula,
      FractionalPrimes.Literature.Twisted.evalInt] using hsum
  exact hcontinued.symm

/-- Consequently, on `Re(s) > 1`, the nonprincipal integral continuation
agrees with Mathlib's named Dirichlet L-function. -/
theorem nonprincipalContinuedDirichletL_eq_LFunction_of_one_lt_re
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q)
    (hχ : χ ≠ FractionalPrimes.Literature.Twisted.principalCharacter q)
    {s : ℂ} (hs : 1 < s.re) :
    nonprincipalContinuedDirichletL χ hχ s (by linarith) =
      _root_.DirichletCharacter.LFunction χ s := by
  rw [_root_.DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact nonprincipalContinuedDirichletL_eq_LSeries_of_one_lt_re χ hχ hs

#print axioms nonprincipalContinuedDirichletL_eq_LSeries_of_one_lt_re
#print axioms nonprincipalContinuedDirichletL_eq_LFunction_of_one_lt_re

end FractionalPrimes.Literature.Reciprocal

end
