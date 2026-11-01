module

public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownRetention
public import Mathlib.Tactic

/-!
# Retained smooth Heath--Brown coefficient bookkeeping

This file records the finite label and coefficient mass bounds after the
support filter in `lda:smooth-hb`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open Finset
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- Support filtering cannot increase the number of smooth Möbius labels. -/
theorem smoothHeathBrownMobiusRetainedLabels_card_le (X : ℝ) :
    (smoothHeathBrownMobiusRetainedLabels X).card ≤
      10 * (smoothHeathBrownDepth X + 1) ^ 20 := by
  calc
    (smoothHeathBrownMobiusRetainedLabels X).card ≤
        Fintype.card (SmoothHeathBrownMobiusLabel X) := Finset.card_le_univ _
    _ ≤ 10 * (smoothHeathBrownDepth X + 1) ^ 20 :=
      (smoothHeathBrownComponentCount X).1

/-- Support filtering cannot increase the number of smooth von Mangoldt
labels. -/
theorem smoothHeathBrownVonMangoldtRetainedLabels_card_le (X : ℝ) :
    (smoothHeathBrownVonMangoldtRetainedLabels X).card ≤
      10 * (smoothHeathBrownDepth X + 1) ^ 20 := by
  calc
    (smoothHeathBrownVonMangoldtRetainedLabels X).card ≤
        Fintype.card (SmoothHeathBrownVonMangoldtLabel X) := Finset.card_le_univ _
    _ ≤ 10 * (smoothHeathBrownDepth X + 1) ^ 20 :=
      (smoothHeathBrownComponentCount X).2

private theorem smoothHeathBrown_retainedCoefficientMass_le
    {X : ℝ} {α : Type*} [Fintype α]
    (R : Finset α) (labelIndex : α → HeathBrownIndex)
    (hcard : R.card ≤ 10 * (smoothHeathBrownDepth X + 1) ^ 20) :
    (∑ ν ∈ R, |dyadicBinomialCoefficient (labelIndex ν)|) ≤
      (2 : ℝ) ^ 10 * (10 * (smoothHeathBrownDepth X + 1) ^ 20 : ℝ) := by
  classical
  have hcardReal : (R.card : ℝ) ≤
      (10 : ℝ) * (smoothHeathBrownDepth X + 1 : ℝ) ^ 20 := by
    exact_mod_cast hcard
  calc
    (∑ ν ∈ R, |dyadicBinomialCoefficient (labelIndex ν)|) ≤
        ∑ ν ∈ R, (2 : ℝ) ^ 10 := by
          apply Finset.sum_le_sum
          intro ν hν
          exact smoothHeathBrownComponentCoefficient_abs_le (labelIndex ν)
    _ = (2 : ℝ) ^ 10 * (R.card : ℝ) := by
          simp [Finset.sum_const, mul_comm]
    _ ≤ (2 : ℝ) ^ 10 *
          (10 * (smoothHeathBrownDepth X + 1) ^ 20 : ℝ) :=
          mul_le_mul_of_nonneg_left hcardReal (by positivity)

/-- The exact outer coefficient mass of either retained smooth
Heath--Brown expansion is bounded by the unfiltered label count times the
source binomial coefficient bound. -/
theorem smoothHeathBrownRetainedCoefficientMass_bounds (X : ℝ) :
    (smoothHeathBrownMobiusRetainedLabels X).card ≤
        10 * (smoothHeathBrownDepth X + 1) ^ 20 ∧
      (smoothHeathBrownVonMangoldtRetainedLabels X).card ≤
        10 * (smoothHeathBrownDepth X + 1) ^ 20 ∧
      (∑ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
        |dyadicBinomialCoefficient ν.1|) ≤
        (2 : ℝ) ^ 10 * (10 * (smoothHeathBrownDepth X + 1) ^ 20 : ℝ) ∧
      (∑ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
        |dyadicBinomialCoefficient ν.1|) ≤
        (2 : ℝ) ^ 10 * (10 * (smoothHeathBrownDepth X + 1) ^ 20 : ℝ) := by
  refine ⟨smoothHeathBrownMobiusRetainedLabels_card_le X,
    smoothHeathBrownVonMangoldtRetainedLabels_card_le X, ?_, ?_⟩
  · exact smoothHeathBrown_retainedCoefficientMass_le
      (X := X) (smoothHeathBrownMobiusRetainedLabels X)
      (fun ν => ν.1) (smoothHeathBrownMobiusRetainedLabels_card_le X)
  · exact smoothHeathBrown_retainedCoefficientMass_le
      (X := X) (smoothHeathBrownVonMangoldtRetainedLabels X)
      (fun ν => ν.1) (smoothHeathBrownVonMangoldtRetainedLabels_card_le X)

end FractionalPrimes.Literature.DirichletAdapter

end

#print axioms FractionalPrimes.Literature.DirichletAdapter.smoothHeathBrownRetainedCoefficientMass_bounds
