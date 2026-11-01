module

public import FractionalPrimes.Literature.Uniformity.UnitResidueShortLongBridge
public import FractionalPrimes.Literature.Uniformity.MajorArcUnitCharacterExpansion

/-! Exact normalization adapter between the finite unit-residue character
expansion and the normalized coefficient average used by the short-to-long
bridge. This is finite bookkeeping only; the twisted sums remain unestimated. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Uniformity

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Polynomial
open scoped BigOperators

/-- On integer parameters, the natural-index Mellin window is precisely the
paper's open-left, closed-right interval. -/
theorem mellinWindowAverageIndices_nat_eq_Ioc (X H : ℕ) :
    mellinWindowAverageIndices (X : ℝ) (H : ℝ) = Finset.Ioc X (X + H) := by
  ext n
  rw [mellinWindowAverageIndices, mellinIntervalIndices_mem_iff (by positivity)]
  simp only [Finset.mem_Ioc]
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨?_, ?_⟩
    · exact_mod_cast hlo
    · have hhi' : (n : ℝ) ≤ ((X + H : ℕ) : ℝ) := by
        simpa [Nat.cast_add] using hhi
      exact_mod_cast hhi'
  · rintro ⟨hlo, hhi⟩
    refine ⟨?_, ?_⟩
    · exact_mod_cast hlo
    · have hhi' : (n : ℝ) ≤ (X : ℝ) + (H : ℝ) := by
        exact_mod_cast hhi
      simpa [Nat.cast_add] using hhi'

/-- The normalized unit-residue `Λ - Cr_X` average is exactly the normalized
average of its character twists. The factor `H⁻¹` is the source interval
normalization; division by `φ(q)` comes from finite character orthogonality.
The Mellin-window value `N_H` is identified with this left side by
`unitResidueLambdaMinusCramerWindowData_average`. -/
theorem unitResidueLambdaMinusCramerAverage_characterExpansion
    (X H q : ℕ) (a : ℤ) (_hH : 0 < H) (hq : 0 < q)
    (ha : IsCoprime a (q : ℤ)) :
    unitResidueCoefficientAverage (X : ℝ) (H : ℝ) q a
        (fun n => paperLambda n - paperShortBlockCramerWeight (X : ℝ) n) =
      ((H⁻¹ : ℝ) : ℂ) *
        ((∑ χ : BlueprintCharacter q,
            star (evalInt χ a) *
              ∑ n ∈ (majorArcInterval X H).points,
                ((paperLambda n - paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ) *
                  evalInt χ n) / (q.totient : ℂ)) := by
  classical
  have hindices :
      mellinWindowAverageIndices (X : ℝ) (H : ℝ) = Finset.Ioc X (X + H) :=
    mellinWindowAverageIndices_nat_eq_Ioc X H
  have hsum :
      (∑ n ∈ (mellinWindowAverageIndices (X : ℝ) (H : ℝ)).filter
          (fun n : ℕ => Int.ModEq (q : ℤ) (n : ℤ) a),
        ((paperLambda (n : ℤ) -
          paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℝ) : ℂ)) =
      (∑ n ∈ ((majorArcInterval X H).points.filter
          (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)])),
        ((paperLambda n - paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ)) := by
    rw [hindices, majorArcInterval_points_eq_Ioc]
    rw [Finset.sum_filter, Finset.sum_filter]
    simpa using
      (cramerShortInterval_sum_nat_eq_int X H
        (fun n : ℤ =>
          if Int.ModEq (q : ℤ) n a then
            ((paperLambda n - paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ)
          else 0))
  rw [unitResidueCoefficientAverage, hsum]
  rw [majorArcUnitLambdaMinusCramer_characterExpansion X H q a hq ha]

#print axioms mellinWindowAverageIndices_nat_eq_Ioc
#print axioms unitResidueLambdaMinusCramerAverage_characterExpansion

end FractionalPrimes.Literature.Uniformity

end
