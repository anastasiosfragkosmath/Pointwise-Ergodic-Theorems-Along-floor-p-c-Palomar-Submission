module
public import FractionalPrimes.Literature.Reciprocal.E1Adapter
public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletMathlibIdentification
@[expose] public section

@[expose] public section

namespace FractionalPrimes.Literature.Reciprocal

/-- The exact fixed-half-plane nonvanishing property from blueprint
`lrc:fixed-half-plane`, discharged by the approved, explicitly imported E1
library theorem and the checked identification with Mathlib's L-function. -/
theorem fixedHalfPlaneOfOAISource
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q)
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (hnotpole :
      ¬ (χ = FractionalPrimes.Literature.Twisted.principalCharacter q ∧ s = 1)) :
    continuedDirichletL χ s (by linarith) hnotpole ≠ 0 := by
  have hpos : 0 < s.re := by linarith
  have hmathlibNotPole : ¬ (χ = (1 : _root_.DirichletCharacter ℂ q) ∧ s = 1) := by
    rintro ⟨hχ, hs1⟩
    exact hnotpole ⟨by simpa [FractionalPrimes.Literature.Twisted.principalCharacter] using hχ,
      hs1⟩
  have hL : _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
    importedNonvanishing χ hs hmathlibNotPole
  rw [continuedDirichletL_eq_LFunction_of_pos_re χ hpos hnotpole]
  exact hL

#print axioms fixedHalfPlaneOfOAISource

end FractionalPrimes.Literature.Reciprocal

end
