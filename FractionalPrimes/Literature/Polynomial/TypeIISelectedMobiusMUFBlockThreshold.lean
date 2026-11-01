module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusAllocatedFirstFactorMUF
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFixedWitnessAssembly
public import FractionalPrimes.Literature.Uniformity.ArithmeticTypes
public import FractionalPrimes.Literature.Uniformity.DivisorTupleCount
public import FractionalPrimes.Literature.Reciprocal.MobiusUniformityOfE1
public import Mathlib.Tactic
@[expose] public section

/-! A threshold-packaged form of the checked fixed-index MUF adapter.
This produces the exact allocated first-group block premise consumed by the
live-conditional PTW assembly, with no change to its frequency or interval. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

namespace FractionalPrimes.Literature.DirichletMean

/-- The maximum of the three lower-scale conditions needed to apply MUF to an
allocated first-factor block: the fixed source scale, the original-factor
threshold selected from MUF, and the grouped-factor log-absorption threshold. -/
noncomputable def selectedMobiusPTWFirstFactorMUFThreshold
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    (a : ℝ) (ha : 2 ≤ a) : ℝ :=
  max ((2 : ℝ) ^ 120)
    (max (mobiusOriginalLongFactorThreshold hMUF a ha)
      (Real.exp (groupedMobiusFactorListAbsorptionThreshold a)))

/-- Under the explicit MUF-derived threshold, the source's selected
Möbius-labelled long factor supplies the exact block family `hMUFblock` used
by the live-conditional PTW integral theorem. -/
theorem selectedMobiusPTWAllocatedFirstFactorBlockFamily_from_MUF_threshold
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X : ℝ} (ha : 2 ≤ a)
    (hXthreshold : selectedMobiusPTWFirstFactorMUFThreshold hMUF a ha ≤ X)
    (ν : MobiusDyadicLabel X)
    (α : Fin (mobiusLabelFactors ν).length → ℝ)
    (hα : ∀ j, 0 ≤ α j)
    (hsum : ∑ j : Fin (mobiusLabelFactors ν).length, α j = 1)
    (hscale : ∀ j,
      normalizedExponentConstant⁻¹ * X ^ α j ≤
          dyadicFactorScale ((mobiusLabelFactors ν).get j) ∧
        dyadicFactorScale ((mobiusLabelFactors ν).get j) ≤
          normalizedExponentConstant * X ^ α j)
    (hNoIα : ∀ j, α j < (3 / 8 : ℝ))
    (I : Finset (Fin (mobiusLabelFactors ν).length))
    (i : Fin (mobiusLabelFactors ν).length) (hiI : i ∈ I)
    (hiAlpha : (1 / 80 : ℝ) ≤ α i)
    {d Q q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a) :
    ∀ (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q)
      (N : ℝ), 0 < N → ∀ s : ℝ,
        (Real.log X) ^ (45 * a) ≤ |s| →
        |s| ≤ X ^ (a + 1) →
        ‖∑ n ∈ factorExtractionRealInterval
            (N / ((r.1 0).1 : ℝ))
            (2 * N / ((r.1 0).1 : ℝ)),
          toComplexArithmeticFunction
              (groupedDyadicFactor (dyadicMobiusCutoff X)
                (dyadicBinomialCoefficient ν.1 : ℂ)
                (selectedDyadicFactors (mobiusLabelFactors ν) I))
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
          (Real.log X) ^ (-20 * a) *
            Real.sqrt (N / ((r.1 0).1 : ℝ)) := by
  have hXlarge : (2 : ℝ) ^ 120 ≤ X := by
    unfold selectedMobiusPTWFirstFactorMUFThreshold at hXthreshold
    exact (le_max_left _ _).trans hXthreshold
  have hXorig : mobiusOriginalLongFactorThreshold hMUF a ha ≤ X := by
    unfold selectedMobiusPTWFirstFactorMUFThreshold at hXthreshold
    calc
      mobiusOriginalLongFactorThreshold hMUF a ha ≤
          max (mobiusOriginalLongFactorThreshold hMUF a ha)
            (Real.exp (groupedMobiusFactorListAbsorptionThreshold a)) :=
        le_max_left _ _
      _ ≤ max ((2 : ℝ) ^ 120)
          (max (mobiusOriginalLongFactorThreshold hMUF a ha)
            (Real.exp (groupedMobiusFactorListAbsorptionThreshold a))) :=
        le_max_right _ _
      _ ≤ X := hXthreshold
  have hExpAbsorb :
      Real.exp (groupedMobiusFactorListAbsorptionThreshold a) ≤ X := by
    unfold selectedMobiusPTWFirstFactorMUFThreshold at hXthreshold
    calc
      Real.exp (groupedMobiusFactorListAbsorptionThreshold a) ≤
          max (mobiusOriginalLongFactorThreshold hMUF a ha)
            (Real.exp (groupedMobiusFactorListAbsorptionThreshold a)) :=
        le_max_right _ _
      _ ≤ max ((2 : ℝ) ^ 120)
          (max (mobiusOriginalLongFactorThreshold hMUF a ha)
            (Real.exp (groupedMobiusFactorListAbsorptionThreshold a))) :=
        le_max_right _ _
      _ ≤ X := hXthreshold
  have hXpos : 0 < X := by
    have hbase : 0 < (2 : ℝ) ^ 120 := by positivity
    exact lt_of_lt_of_le hbase hXlarge
  have hXabsorb :
      groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2 hExpAbsorb
  intro r χ N hN s hslo hshi
  exact selectedMobiusPTWAllocatedFirstFactorBlock_from_MUF_fixedIndex
    hMUF ha hXlarge hXorig hXabsorb ν α hα hsum hscale hNoIα
    I i hiI hiAlpha hd hQ hqfactor hqlog r (N₁ := N) hN χ s hslo hshi

/-- Source-instantiated version: the checked E1 adapter already supplies
`MobiusUniformity`, so callers need only the exact threshold derived from
that source theorem and the selected type-II data. -/
theorem selectedMobiusPTWAllocatedFirstFactorBlockFamily_from_OAISource
    {a X : ℝ} (ha : 2 ≤ a)
    (hXthreshold : selectedMobiusPTWFirstFactorMUFThreshold
      FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
      a ha ≤ X)
    (ν : MobiusDyadicLabel X)
    (α : Fin (mobiusLabelFactors ν).length → ℝ)
    (hα : ∀ j, 0 ≤ α j)
    (hsum : ∑ j : Fin (mobiusLabelFactors ν).length, α j = 1)
    (hscale : ∀ j,
      normalizedExponentConstant⁻¹ * X ^ α j ≤
          dyadicFactorScale ((mobiusLabelFactors ν).get j) ∧
        dyadicFactorScale ((mobiusLabelFactors ν).get j) ≤
          normalizedExponentConstant * X ^ α j)
    (hNoIα : ∀ j, α j < (3 / 8 : ℝ))
    (I : Finset (Fin (mobiusLabelFactors ν).length))
    (i : Fin (mobiusLabelFactors ν).length) (hiI : i ∈ I)
    (hiAlpha : (1 / 80 : ℝ) ≤ α i)
    {d Q q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a) :
    ∀ (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q)
      (N : ℝ), 0 < N → ∀ s : ℝ,
        (Real.log X) ^ (45 * a) ≤ |s| →
        |s| ≤ X ^ (a + 1) →
        ‖∑ n ∈ factorExtractionRealInterval
            (N / ((r.1 0).1 : ℝ))
            (2 * N / ((r.1 0).1 : ℝ)),
          toComplexArithmeticFunction
              (groupedDyadicFactor (dyadicMobiusCutoff X)
                (dyadicBinomialCoefficient ν.1 : ℂ)
                (selectedDyadicFactors (mobiusLabelFactors ν) I))
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
          (Real.log X) ^ (-20 * a) *
            Real.sqrt (N / ((r.1 0).1 : ℝ)) := by
  exact selectedMobiusPTWAllocatedFirstFactorBlockFamily_from_MUF_threshold
    FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
    ha hXthreshold ν α hα hsum hscale hNoIα I i hiI hiAlpha
    hd hQ hqfactor hqlog

#print axioms
  selectedMobiusPTWAllocatedFirstFactorBlockFamily_from_MUF_threshold
#print axioms
  selectedMobiusPTWAllocatedFirstFactorBlockFamily_from_OAISource

end FractionalPrimes.Literature.DirichletMean

end
