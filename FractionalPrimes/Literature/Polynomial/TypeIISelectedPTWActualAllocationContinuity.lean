module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFiniteContinuity
public import Mathlib.Tactic
@[expose] public section

/-! Generic continuity of the selected three-group allocated Mellin
integrand. This adapter is stated for arbitrary factor lists and selected
index sets, so it can be used for either Möbius or von Mangoldt components. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- For arbitrary factor data `fs` and selected groups `I/J/J'`, the exact
finite character/allocation integrand in a dyadic window is continuous. No
Möbius or von Mangoldt witness is part of the statement. -/
theorem selectedDyadicPTWActualAllocationContinuity
    {X z : ℝ} (c : ℂ)
    (fs : List (DyadicArithmeticFactor X))
    (I J J' : Finset (Fin fs.length))
    {d Q q : ℕ} (rchar : ℤ) (T γ η η' : ℝ) :
    ∀ j k l,
      Continuous (fun t : ℝ =>
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            (((d : ℂ) ^
                (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
                (Q.totient : ℂ)) * (star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) (c := c)
                (selectedDyadicFactors fs I)
                (selectedDyadicFactors fs J)
                (selectedDyadicFactors fs J')
                r χ T γ η η' j k l t))) := by
  intro j k l
  exact selectedMobiusPTWActualAllocatedIntegrand_continuous
    (d := d) (Q := Q) (q := q) (z := z) (c := c)
    (selectedDyadicFactors fs I)
    (selectedDyadicFactors fs J)
    (selectedDyadicFactors fs J')
    rchar T γ η η' j k l

#print axioms selectedDyadicPTWActualAllocationContinuity

end FractionalPrimes.Literature.DirichletMean

end
