module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylInductionCoefficientControl

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- Join the lower- and top-coefficient bounds from the long induction
branch into the single quantified conclusion in `lbi:weyl-inverse`. This is
the final coefficient-packaging step after
`scalarWeyl_longInductionCoefficientControl`. -/
theorem scalarWeyl_joinLongCoefficientBounds
    {d N : ℕ} {F : ℝ} (P : Polynomial ℝ)
    (hcontrol :
      ∃ q : ℕ,
        1 ≤ q ∧
        (q : ℝ) ≤ F ∧
        (∀ j, 1 ≤ j → j < d →
          (N : ℝ) ^ j * realDistanceToIntegers
            ((q : ℝ) * P.coeff j) ≤ F) ∧
        (N : ℝ) ^ d * realDistanceToIntegers
          ((q : ℝ) * P.coeff d) ≤ F) :
    ∃ q : ℕ,
      1 ≤ q ∧
      (q : ℝ) ≤ F ∧
      (∀ j, 1 ≤ j → j ≤ d →
        (N : ℝ) ^ j * realDistanceToIntegers
          ((q : ℝ) * P.coeff j) ≤ F) := by
  rcases hcontrol with ⟨q, hq, hqF, hlow, htop⟩
  refine ⟨q, hq, hqF, ?_⟩
  intro j hj hjd
  by_cases hjeq : j = d
  · simpa [hjeq] using htop
  · exact hlow j hj (by omega)

end FractionalPrimes.Literature.Polynomial
