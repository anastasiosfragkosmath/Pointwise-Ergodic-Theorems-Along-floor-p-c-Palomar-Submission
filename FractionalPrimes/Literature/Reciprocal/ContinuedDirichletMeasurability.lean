module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletData
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

namespace FractionalPrimes.Literature.Reciprocal

/-- The finite partial-sum integrand in `lrc:continued-lseries` is measurable
as a function of its real endpoint. It factors through `Nat.floor`; each
function from the countable discrete type `ℕ` is measurable. -/
theorem measurable_continuedDirichletPartialSumFormula {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) :
    Measurable (continuedDirichletPartialSumFormula χ) := by
  let g : ℕ → ℂ := fun n =>
    ∑ k ∈ Finset.Icc 1 n,
      FractionalPrimes.Literature.Twisted.evalInt χ (k : ℤ)
  have hg : Measurable g := measurable_of_countable g
  change Measurable (fun u : ℝ => g (Nat.floor u))
  exact hg.comp Nat.measurable_floor

#print axioms measurable_continuedDirichletPartialSumFormula

end FractionalPrimes.Literature.Reciprocal
