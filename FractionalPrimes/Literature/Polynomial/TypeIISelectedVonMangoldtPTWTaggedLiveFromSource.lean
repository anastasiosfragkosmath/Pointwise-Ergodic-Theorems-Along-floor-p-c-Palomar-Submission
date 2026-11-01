module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWTaggedLiveAggregate
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtMUFBlockThreshold
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedPTWActualAllocationContinuity
public import Mathlib.Tactic
@[expose] public section

/-! Fully sourced and continuous live aggregate for the tagged von Mangoldt
type-II branch. The OAISource first-factor estimate and the generic finite
continuity theorem are both applied to the same returned witness. -/

@[expose] public section

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

set_option maxHeartbeats 8000000 in
/-- The tagged von Mangoldt source aggregate with the first-factor estimate
instantiated from OAISource and continuity supplied for the same selected
`I/J/J'/i`. -/
theorem selectedVonMangoldtPTW_taggedThirdBranch_liveAggregate_from_OAISource
    {X U a eps T : ℝ} {d Q q : ℕ}
    (D : SelectedVonMangoldtPTWTaggedOuterDecomposition X)
    (ν : VonMangoldtDyadicLabel X)
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X))
    (haMUF : 2 ≤ a)
    (hXthreshold : selectedMobiusPTWFirstFactorMUFThreshold
      FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
      a haMUF ≤ X)
    (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hXlog : Real.exp (selectedMobiusPTWCellLogThreshold a eps) ≤ X)
    (hU0 : 2 ≤ U) (hUsource : U ≤ X ^ (3 / 8 - 2 * eps))
    (hd : 0 < d) (hQ : 0 < Q) (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (rchar : ℤ) (hrchar : IsCoprime rchar (Q : ℤ))
    (hfreq : ∀ t ∈ Set.Icc (-U) U,
      (Real.log X) ^ (45 * a) ≤ |T - t| ∧ |T - t| ≤ X ^ (a + 1))
    (hXsave : selectedMobiusPTWUncappedSavingThreshold a eps ≤ X)
    (hThird :
      largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        (selectedVonMangoldtPTWRawDyadicComponent ν)
        (vonMangoldtLabelFactors ν)
        (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents ∧
      ∀ j, (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents j <
        (3 / 8 : ℝ)) :
    ∃ W : SelectedVonMangoldtPTWTypeIIWitness ν
        (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents,
      W.toData = hThird.1 ∧
      W.i ∈ W.I ∧
      (1 / 80 : ℝ) ≤ (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents W.i ∧
      (2 ^ 23 : ℝ)⁻¹ * X ^ (1 / 80 : ℝ) ≤
        dyadicFactorScale ((vonMangoldtLabelFactors ν).get W.i) ∧
      dyadicFactorScale ((vonMangoldtLabelFactors ν).get W.i) ≤
        (2 ^ 23 : ℝ) * X ^ (3 / 8 : ℝ) ∧
      largeDyadicComponentTaggedPackage (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        (selectedVonMangoldtPTWRawDyadicComponent ν)
        (vonMangoldtLabelFactors ν)
        (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents ∧
      (∫ t in Set.Icc (-U) U,
        ‖((d : ℂ) ^
            (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
            (Q.totient : ℂ)) *
          (∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              star (evalInt χ rchar) *
                selectedMobiusPTWActualCommonCutoffTerm
                  (z := dyadicMobiusCutoff X)
                  (c := dyadicBinomialCoefficient ν.1)
                  (vonMangoldtLabelFactors ν) (q := q) r χ T t
                  W.gamma W.eta W.eta' W.I W.J W.J')‖ ∂volume) ≤
        (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 *
          ((divisorFunction 3 ⟨d, hd⟩ : ℝ) *
            (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
              selectedPTWFactorScale X d) *
            (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
                (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
              (2 * decompositionC) ^ (3 / 2 : ℝ) *
              (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
              Real.sqrt X / (d : ℝ) * (Real.log X) ^ (-5 * a / 4 : ℝ))) := by
  classical
  have hXlarge : (2 : ℝ) ^ 120 ≤ X := by
    unfold selectedMobiusPTWFirstFactorMUFThreshold at hXthreshold
    exact (le_max_left _ _).trans hXthreshold
  obtain ⟨W, hWdata, hiI, hiAlpha, hScaleLo, hScaleHi, hTagged,
    hContinue⟩ := selectedVonMangoldtPTW_taggedThirdBranch_liveAggregateInterface
      D ν hν hXlarge (by linarith [haMUF]) heps0 heps hXlog hU0 hUsource
      hd hQ hqfactor hqlog rchar hrchar hfreq hXsave hThird
  have hMUFblock : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (N : ℝ), 0 < N →
      ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| →
        |s| ≤ X ^ (a + 1) →
        ‖∑ n ∈ factorExtractionRealInterval
            (N / ((r.1 0).1 : ℝ))
            (2 * N / ((r.1 0).1 : ℝ)),
          toComplexArithmeticFunction
              (groupedDyadicFactor (dyadicMobiusCutoff X)
                (dyadicBinomialCoefficient ν.1 : ℂ)
                (selectedDyadicFactors (vonMangoldtLabelFactors ν) W.I))
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
          (Real.log X) ^ (-20 * a) *
            Real.sqrt (N / ((r.1 0).1 : ℝ)) := by
    intro r χ N hN s hslo hshi
    exact selectedVonMangoldtPTWAllocatedFirstFactorBlockFamily_from_OAISource
      haMUF hXthreshold ν
      (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents
      (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).nonnegative
      (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).sum_one
      (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).scale_bounds
      hThird.2 W.I W.i hiI hiAlpha hd hQ hqfactor hqlog
      r χ N hN s hslo hshi
  have hcont := selectedDyadicPTWActualAllocationContinuity
    (d := d) (Q := Q) (q := q)
    (z := dyadicMobiusCutoff X)
    (c := (dyadicBinomialCoefficient ν.1 : ℂ))
    (vonMangoldtLabelFactors ν) W.I W.J W.J' rchar T W.gamma W.eta W.eta'
  exact ⟨W, hWdata, hiI, hiAlpha, hScaleLo, hScaleHi, hTagged,
    hContinue hcont hMUFblock⟩

#print axioms selectedVonMangoldtPTW_taggedThirdBranch_liveAggregate_from_OAISource

end FractionalPrimes.Literature.DirichletMean

end
