module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTaggedLiveAggregate
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusMUFBlockThreshold
public import Mathlib.Tactic
@[expose] public section

/-! OAISource-instantiated tagged Möbius short-interval transfer.  The
deterministic MUF threshold is retained as an explicit hypothesis; continuity
of the finite allocation integrand remains an explicit input. -/

@[expose] public section

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

set_option maxHeartbeats 8000000 in
/-- The tagged type-II live aggregate with its first-factor block bound
instantiated from the checked OAISource Möbius family.  The exact deterministic
MUF threshold and the separate live-continuity hypothesis remain visible. -/
theorem selectedMobiusPTW_taggedThirdBranch_liveAggregate_from_OAISource
    {X U a eps T : ℝ} {d Q q : ℕ}
    (D : SelectedMobiusPTWTaggedOuterDecomposition X)
    (ν : MobiusDyadicLabel X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
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
        (selectedMobiusPTWRawDyadicComponent ν)
        (mobiusLabelFactors ν)
        (selectedMobiusPTWTaggedComponentOfOuter D ν hν).exponents ∧
      ∀ j, (selectedMobiusPTWTaggedComponentOfOuter D ν hν).exponents j <
        (3 / 8 : ℝ)) :
    ∃ W : SelectedMobiusPTWTypeIIWitness ν
        (selectedMobiusPTWTaggedComponentOfOuter D ν hν).exponents,
      W.toData = hThird.1 ∧
      W.i ∈ W.I ∧
      (1 / 80 : ℝ) ≤ (selectedMobiusPTWTaggedComponentOfOuter D ν hν).exponents W.i ∧
      (2 ^ 23 : ℝ)⁻¹ * X ^ (1 / 80 : ℝ) ≤
        dyadicFactorScale ((mobiusLabelFactors ν).get W.i) ∧
      dyadicFactorScale ((mobiusLabelFactors ν).get W.i) ≤
        (2 ^ 23 : ℝ) * X ^ (3 / 8 : ℝ) ∧
      largeDyadicComponentTaggedPackage (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        (selectedMobiusPTWRawDyadicComponent ν) (mobiusLabelFactors ν)
        (selectedMobiusPTWTaggedComponentOfOuter D ν hν).exponents ∧
      (∀ (hcont : ∀ j k l,
        Continuous (fun t : ℝ =>
          ∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              (((d : ℂ) ^
                  (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
                  (Q.totient : ℂ)) * (star (evalInt χ rchar) *
                selectedMobiusPTWActualAllocatedWindowTerm
                  (z := dyadicMobiusCutoff X) (q := q)
                  (c := (dyadicBinomialCoefficient ν.1 : ℂ))
                  (selectedDyadicFactors (mobiusLabelFactors ν) W.I)
                  (selectedDyadicFactors (mobiusLabelFactors ν) W.J)
                  (selectedDyadicFactors (mobiusLabelFactors ν) W.J')
                  r χ T W.gamma W.eta W.eta' j k l t)))),
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
                    (mobiusLabelFactors ν) (q := q) r χ T t
                    W.gamma W.eta W.eta' W.I W.J W.J')‖ ∂volume) ≤
          (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 *
            ((divisorFunction 3 ⟨d, hd⟩ : ℝ) *
              (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
                selectedPTWFactorScale X d) *
              (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
                  (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
                (2 * decompositionC) ^ (3 / 2 : ℝ) *
                (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
                Real.sqrt X / (d : ℝ) * (Real.log X) ^ (-5 * a / 4 : ℝ)))) := by
  classical
  have ha : 0 ≤ a := by linarith [haMUF]
  have hXlarge : (2 : ℝ) ^ 120 ≤ X := by
    have hbase : (2 : ℝ) ^ 120 ≤
        selectedMobiusPTWFirstFactorMUFThreshold
          FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
          a haMUF := by
      unfold selectedMobiusPTWFirstFactorMUFThreshold
      exact le_max_left _ _
    exact hbase.trans hXthreshold
  obtain ⟨W, hWdata, hiI, hiAlpha, hScaleLo, hScaleHi, hTagged, hContinue⟩ :=
    selectedMobiusPTW_taggedThirdBranch_liveAggregateInterface
      D ν hν hXlarge ha heps0 heps hXlog hU0 hUsource hd hQ hqfactor hqlog
      rchar hrchar hfreq hXsave hThird
  let S := selectedMobiusPTWTaggedComponentOfOuter D ν hν
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
                (selectedDyadicFactors (mobiusLabelFactors ν) W.I))
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
          (Real.log X) ^ (-20 * a) *
            Real.sqrt (N / ((r.1 0).1 : ℝ)) := by
    intro r χ N hN s hslo hshi
    exact selectedMobiusPTWAllocatedFirstFactorBlockFamily_from_OAISource
      haMUF hXthreshold ν S.exponents S.nonnegative S.sum_one S.scale_bounds
      hThird.2 W.I W.i hiI hiAlpha hd hQ hqfactor hqlog
      r χ N hN s hslo hshi
  refine ⟨W, hWdata, hiI, hiAlpha, hScaleLo, hScaleHi, hTagged, ?_⟩
  intro hcont
  exact hContinue hcont hMUFblock

#print axioms selectedMobiusPTW_taggedThirdBranch_liveAggregate_from_OAISource

end FractionalPrimes.Literature.DirichletMean

end
