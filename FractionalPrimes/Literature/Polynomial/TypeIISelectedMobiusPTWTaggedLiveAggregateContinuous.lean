module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTaggedLiveFromSource
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFiniteContinuity
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFinalThreshold
public import Mathlib.Tactic
@[expose] public section

/-! Fully source-instantiated tagged Möbius live aggregate. The same witness
supplies both the OAISource first-factor estimate and the finite-integrand
continuity needed by the live integral theorem. A companion threshold bundle
combines those MUF thresholds with the checked final source window. -/

@[expose] public section

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

set_option maxHeartbeats 8000000 in
/-- The OAISource tagged type-II aggregate with both the exact MUF block
family and the finite-integrand continuity discharged for the same returned
source witness. -/
theorem selectedMobiusPTW_taggedThirdBranch_liveAggregate_from_OAISource_continuous
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
              Real.sqrt X / (d : ℝ) * (Real.log X) ^ (-5 * a / 4 : ℝ))) := by
  classical
  obtain ⟨W, hWdata, hiI, hiAlpha, hScaleLo, hScaleHi, hTagged, hContinue⟩ :=
    selectedMobiusPTW_taggedThirdBranch_liveAggregate_from_OAISource
      D ν hν haMUF hXthreshold heps0 heps hXlog hU0 hUsource hd hQ
      hqfactor hqlog rchar hrchar hfreq hXsave hThird
  have hcont := selectedMobiusPTWActualAllocationContinuity_of_witness
    (d := d) (Q := Q) (q := q) W rchar T
  exact ⟨W, hWdata, hiI, hiAlpha, hScaleLo, hScaleHi, hTagged,
    hContinue hcont⟩

/-- The source's final short-interval threshold augmented by the exact
OAISource MUF threshold needed for the selected first-factor block estimate. -/
noncomputable def selectedMobiusPTWFinalSourceOAISourceThreshold
    (a eta : ℝ) (haMUF : 2 ≤ a) : ℝ :=
  max (selectedMobiusPTWFinalSourceThreshold a eta)
    (selectedMobiusPTWFirstFactorMUFThreshold
      FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
      a haMUF)

/-- A bound by the combined final source/OAISource threshold gives every
deterministic large-X, cell-log, saving, and outer-frequency premise used by
the fully sourced live aggregate, together with the exact first-factor MUF
threshold. -/
theorem selectedMobiusPTWFinalSourceOAISourceThreshold_facts
    {a eta X H T U : ℝ}
    (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (heta0 : 0 < eta) (heta : eta < 3 / 16)
    (haMUF : 2 ≤ a)
    (hX : selectedMobiusPTWFinalSourceOAISourceThreshold a eta haMUF ≤ X)
    (hHpos : 0 < H)
    (hHlower : X ^ (5 / 8 + eta) ≤ H)
    (hHupper : H ≤ X ^ (1 - eta))
    (hTlower : (X / H) * (Real.log X) ^ (50 * a) ≤ |T|)
    (hTupper : |T| ≤ X ^ a)
    (hU : U ∈ Set.Icc (X / H)
      ((X / H) * selectedMobiusPTWTransferW X a ^ 4)) :
    selectedMobiusPTWFirstFactorMUFThreshold
        FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
        a haMUF ≤ X ∧
      ((2 : ℝ) ^ 120 ≤ X ∧
        Real.exp (selectedMobiusPTWCellLogThreshold a (eta / 4)) ≤ X ∧
        selectedMobiusPTWUncappedSavingThreshold a (eta / 4) ≤ X ∧
        0 < eta / 4 ∧ eta / 4 ≤ 3 / 16 ∧ 2 ≤ U ∧
        U ≤ X ^ (3 / 8 - 2 * (eta / 4)) ∧
        ∀ t ∈ Set.Icc (-U) U,
          (Real.log X) ^ (45 * a) ≤ |T - t| ∧
            |T - t| ≤ X ^ (a + 1)) := by
  have hXfinal : selectedMobiusPTWFinalSourceThreshold a eta ≤ X := by
    unfold selectedMobiusPTWFinalSourceOAISourceThreshold at hX
    exact (le_max_left _ _).trans hX
  have hXMUF : selectedMobiusPTWFirstFactorMUFThreshold
      FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
      a haMUF ≤ X := by
    unfold selectedMobiusPTWFinalSourceOAISourceThreshold at hX
    exact (le_max_right _ _).trans hX
  exact ⟨hXMUF,
    selectedMobiusPTWFinalSourceThreshold_facts ha heta0 heta hXfinal
      hHpos hHlower hHupper hTlower hTupper hU⟩

#print axioms selectedMobiusPTW_taggedThirdBranch_liveAggregate_from_OAISource_continuous
#print axioms selectedMobiusPTWFinalSourceOAISourceThreshold_facts

end FractionalPrimes.Literature.DirichletMean

end
