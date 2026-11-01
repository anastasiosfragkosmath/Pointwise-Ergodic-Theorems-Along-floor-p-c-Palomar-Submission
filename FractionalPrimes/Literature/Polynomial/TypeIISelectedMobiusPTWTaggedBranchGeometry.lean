module

public import FractionalPrimes.Literature.Uniformity.ArithmeticTypeDecomposition
public import FractionalPrimes.Literature.Twisted.GroupedFactorScaleBounds
public import Mathlib.Tactic

/-! Geometry retained by the selected tagged type-II branch. This bridge uses
the failed exponent-grouping inequality carried by that branch; it does not
assert failure of either arithmetic type-I predicate. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

namespace FractionalPrimes.Literature.DirichletMean

/-- The third tagged branch supplies the same distinguished original index
and selected major group as its type-II factorization, together with the
source scale range needed for the long-factor estimate. The only failed
branch information used here is `α j < 3/8`. -/
theorem selectedMobiusPTW_geometry_of_taggedTypeIIBranch
    {X z c δ : ℝ} (hX : 1 ≤ X)
    (fs : List (DyadicArithmeticFactor X))
    (α : Fin fs.length → ℝ)
    (hα : ∀ j, 0 ≤ α j)
    (hsum : ∑ j : Fin fs.length, α j = 1)
    (hscale : ∀ j,
      normalizedExponentConstant⁻¹ * X ^ α j ≤ dyadicFactorScale (fs.get j) ∧
        dyadicFactorScale (fs.get j) ≤ normalizedExponentConstant * X ^ α j)
    (hTaggedThird :
      largeTypeIIDyadicComponentData z c δ
        (groupedDyadicFactor z (c : ℂ) fs) fs α ∧
      ∀ j, α j < (3 / 8 : ℝ)) :
    ∃ I : Finset (Fin fs.length), ∃ i : Fin fs.length,
      ∃ v : ComplexPositiveIntegerFunction,
        i ∈ I ∧ (1 / 80 : ℝ) ≤ α i ∧
        v = groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I) ∧
        (2 ^ 23 : ℝ)⁻¹ * X ^ (1 / 80 : ℝ) ≤
          dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ (2 ^ 23 : ℝ) * X ^ (3 / 8 : ℝ) := by
  classical
  rcases hTaggedThird.1 with ⟨Aminus, Aplus, v, a, b1, γ, η, η', I, J, J', i,
    _htypeII, _hfactor, _hv, _ha, _hb1, _hAminus1, _hAminusAplus,
    _hAminusLow, _hAplusHigh, _hgammasum, _hgammaLo, _hgammaHi, _hmajorGap,
    _hvSupport, _haSupport, _hb1Support, hiI, hiAlpha⟩
  have hlen : 0 < fs.length :=
    Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  let w : GroupingPredicates fs.length := ⟨α, hlen, hα, hsum⟩
  have hnotI : ¬ w.I (5 / 8) := by
    intro hwI
    rcases hwI with ⟨j, hj⟩
    have hjlarge : (3 / 8 : ℝ) ≤ α j := by
      dsimp [w, GroupingPredicates.I] at hj
      linarith
    exact (not_lt_of_ge hjlarge) (hTaggedThird.2 j)
  have hrange := FractionalPrimes.Literature.Twisted.groupedFactorOriginalScaleBounds
    hX w hnotI i hiAlpha (hscale i)
  exact ⟨I, i, v, hiI, hiAlpha, _hv, hrange.1, hrange.2⟩

#print axioms selectedMobiusPTW_geometry_of_taggedTypeIIBranch

end FractionalPrimes.Literature.DirichletMean

end
