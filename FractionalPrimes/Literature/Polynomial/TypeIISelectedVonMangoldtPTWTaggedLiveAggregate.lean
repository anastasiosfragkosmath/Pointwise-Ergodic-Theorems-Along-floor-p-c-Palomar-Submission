module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWTaggedComponentAPI
public import FractionalPrimes.Literature.Twisted.SelectedVonMangoldtGroupCoefficientBound
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTaggedBranchGeometry
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWLiveConditionalAssembly
public import Mathlib.Tactic
@[expose] public section

/-! Conditional bridge from the retained tagged type-II branch to the
fixed-index geometry and live-cell source integral. The selected source tuple
is fixed once; the grouped-factor block estimate remains an explicit
continuation premise. -/

@[expose] public section

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- A value-level witness for the exact existential type-II data attached to
one selected Möbius dyadic component. Keeping the source groups and the
distinguished index as fields makes every later estimate refer to one and the
same `I/J/J'/i`. -/
structure SelectedVonMangoldtPTWTypeIIWitness
    {X : ℝ} (ν : VonMangoldtDyadicLabel X)
    (α : Fin (vonMangoldtLabelFactors ν).length → ℝ) where
  Aminus : ℝ
  Aplus : ℝ
  v : ComplexPositiveIntegerFunction
  a : ComplexPositiveIntegerFunction
  b1 : ComplexPositiveIntegerFunction
  gamma : ℝ
  eta : ℝ
  eta' : ℝ
  I : Finset (Fin (vonMangoldtLabelFactors ν).length)
  J : Finset (Fin (vonMangoldtLabelFactors ν).length)
  J' : Finset (Fin (vonMangoldtLabelFactors ν).length)
  i : Fin (vonMangoldtLabelFactors ν).length
  typeII : typeIIFunction (decompositionDelta X) Aminus Aplus
    (selectedVonMangoldtPTWRawDyadicComponent ν)
  factorization : selectedVonMangoldtPTWRawDyadicComponent ν =
    complexPositiveDirichletConvolution v
      (complexPositiveDirichletConvolution a b1)
  v_eq : v = groupedDyadicFactor (dyadicMobiusCutoff X)
    (dyadicBinomialCoefficient ν.1 : ℂ)
    (selectedDyadicFactors (vonMangoldtLabelFactors ν) I)
  a_eq : a = dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
    (selectedDyadicFactors (vonMangoldtLabelFactors ν) J)
  b1_eq : b1 = dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
    (selectedDyadicFactors (vonMangoldtLabelFactors ν) J')
  Aminus_one : 1 ≤ Aminus
  Aminus_le_Aplus : Aminus ≤ Aplus
  Aminus_lower : decompositionC⁻¹ * X ^ (3 / 8 : ℝ) ≤ Aminus
  Aplus_upper : Aplus ≤ decompositionC * X ^ (5 / 8 : ℝ)
  exponent_sum : gamma + eta + eta' = 1
  gamma_lower : (1 / 4 : ℝ) ≤ gamma
  gamma_upper : gamma ≤ 1 / 2
  major_gap : |eta - eta'| ≤ 1 / 4
  v_support : complexPositiveSupportedOnInterval v
    (decompositionC⁻¹ * X ^ gamma) (decompositionC * X ^ gamma)
  a_support : complexPositiveSupportedOnInterval a
    (decompositionC⁻¹ * X ^ eta) (decompositionC * X ^ eta)
  b1_support : complexPositiveSupportedOnInterval b1
    (decompositionC⁻¹ * X ^ eta') (decompositionC * X ^ eta')
  i_mem : i ∈ I
  i_exponent_lower : (1 / 80 : ℝ) ≤ α i

/-- The selected witness reconstructs the exact tagged source data predicate. -/
theorem SelectedVonMangoldtPTWTypeIIWitness.toData
    {X : ℝ} {ν : VonMangoldtDyadicLabel X}
    {α : Fin (vonMangoldtLabelFactors ν).length → ℝ}
    (W : SelectedVonMangoldtPTWTypeIIWitness ν α) :
    largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
      (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
      (selectedVonMangoldtPTWRawDyadicComponent ν)
      (vonMangoldtLabelFactors ν) α :=
  ⟨W.Aminus, W.Aplus, W.v, W.a, W.b1, W.gamma, W.eta, W.eta',
    W.I, W.J, W.J', W.i, W.typeII, W.factorization, W.v_eq, W.a_eq,
    W.b1_eq, W.Aminus_one, W.Aminus_le_Aplus, W.Aminus_lower,
    W.Aplus_upper, W.exponent_sum, W.gamma_lower, W.gamma_upper,
    W.major_gap, W.v_support, W.a_support, W.b1_support, W.i_mem,
    W.i_exponent_lower⟩

/-- A chosen value from the nonempty per-label data stored in the tagged
outer decomposition. -/
noncomputable def selectedVonMangoldtPTWTaggedComponentOfOuter
    {X : ℝ} (D : SelectedVonMangoldtPTWTaggedOuterDecomposition X)
    (ν : VonMangoldtDyadicLabel X)
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)) :
    SelectedVonMangoldtPTWTaggedComponentData ν :=
  Classical.choice (D.taggedComponent ν hν)

set_option maxHeartbeats 8000000 in
/-- The selected tagged type-II branch exposes its same source `I/J/J'/i`,
the fixed-index original-factor scale range, and the live-conditional source
integral interface. The only grouped-factor cancellation input is the
explicit `hMUFblock` continuation. -/
theorem selectedVonMangoldtPTW_taggedThirdBranch_liveAggregateInterface
    {X U a eps T : ℝ} {d Q q : ℕ}
    (D : SelectedVonMangoldtPTWTaggedOuterDecomposition X)
    (ν : VonMangoldtDyadicLabel X)
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X))
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
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
        (selectedVonMangoldtPTWRawDyadicComponent ν) (vonMangoldtLabelFactors ν)
        (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents ∧
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
                  (selectedDyadicFactors (vonMangoldtLabelFactors ν) W.I)
                  (selectedDyadicFactors (vonMangoldtLabelFactors ν) W.J)
                  (selectedDyadicFactors (vonMangoldtLabelFactors ν) W.J')
                  r χ T W.gamma W.eta W.eta' j k l t))))
        (hMUFblock : ∀ (r : divisorFactorTuples 3 d)
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
                Real.sqrt (N / ((r.1 0).1 : ℝ))),
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
                Real.sqrt X / (d : ℝ) * (Real.log X) ^ (-5 * a / 4 : ℝ)))) := by
  classical
  let S := selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν
  rcases hThird.1 with ⟨Aminus, Aplus, v, a₁, a₂, γ, η, η', I, J, J', i,
    htypeII, hfactor, hv, ha₁, ha₂, hAminusOne, hAminusAplus,
    hAminusLower, hAplusUpper, hExponentSum, hGammaLower, hGammaUpper,
    hMajorGap, hvSupport, ha₁Support, ha₂Support, hiI, hiAlpha⟩
  have hXthree : 3 ≤ X := by
    have hbase : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hbase.trans hXlarge
  let W : SelectedVonMangoldtPTWTypeIIWitness ν S.exponents :=
    { Aminus := Aminus
      Aplus := Aplus
      v := v
      a := a₁
      b1 := a₂
      gamma := γ
      eta := η
      eta' := η'
      I := I
      J := J
      J' := J'
      i := i
      typeII := htypeII
      factorization := hfactor
      v_eq := hv
      a_eq := ha₁
      b1_eq := ha₂
      Aminus_one := hAminusOne
      Aminus_le_Aplus := hAminusAplus
      Aminus_lower := hAminusLower
      Aplus_upper := hAplusUpper
      exponent_sum := hExponentSum
      gamma_lower := hGammaLower
      gamma_upper := hGammaUpper
      major_gap := hMajorGap
      v_support := hvSupport
      a_support := ha₁Support
      b1_support := ha₂Support
      i_mem := hiI
      i_exponent_lower := hiAlpha }
  have hWdata : W.toData = hThird.1 := by
    apply Subsingleton.elim
  have htaggedBranch : largeDyadicComponentTaggedPackage
      (dyadicMobiusCutoff X) (dyadicBinomialCoefficient ν.1)
      (decompositionDelta X) (selectedVonMangoldtPTWRawDyadicComponent ν)
      (vonMangoldtLabelFactors ν) S.exponents :=
    Or.inr (Or.inr ⟨W.toData, hThird.2⟩)
  have hXone : 1 ≤ X := by linarith [hXlarge]
  have hlen : 0 < (vonMangoldtLabelFactors ν).length :=
    Nat.lt_of_le_of_lt (Nat.zero_le W.i.val) W.i.isLt
  let w : GroupingPredicates (vonMangoldtLabelFactors ν).length :=
    ⟨S.exponents, hlen, S.nonnegative, S.sum_one⟩
  have hnotI : ¬ w.I (5 / 8) := by
    intro hwI
    rcases hwI with ⟨j, hj⟩
    have hjlarge : (3 / 8 : ℝ) ≤ S.exponents j := by
      dsimp [w, GroupingPredicates.I] at hj
      linarith
    exact (not_lt_of_ge hjlarge) (hThird.2 j)
  have hRange := groupedFactorOriginalScaleBounds hXone w hnotI W.i
    W.i_exponent_lower (S.scale_bounds W.i)
  have hSupport₁ : complexPositiveSupportedOnInterval
      (groupedDyadicFactor (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1 : ℂ)
        (selectedDyadicFactors (vonMangoldtLabelFactors ν) W.I))
      (decompositionC⁻¹ * X ^ W.gamma) (decompositionC * X ^ W.gamma) := by
    simpa only [← W.v_eq] using W.v_support
  have hSupport₂ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
        (selectedDyadicFactors (vonMangoldtLabelFactors ν) W.J))
      (decompositionC⁻¹ * X ^ W.eta) (decompositionC * X ^ W.eta) := by
    simpa only [← W.a_eq] using W.a_support
  have hSupport₃ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex (dyadicMobiusCutoff X)
        (selectedDyadicFactors (vonMangoldtLabelFactors ν) W.J'))
      (decompositionC⁻¹ * X ^ W.eta') (decompositionC * X ^ W.eta') := by
    simpa only [← W.b1_eq] using W.b1_support
  have hEta0 : 0 ≤ W.eta := by
    have hgap := abs_le.mp W.major_gap
    have hsumEta : (1 / 2 : ℝ) ≤ W.eta + W.eta' := by
      rw [← W.exponent_sum]
      linarith [W.gamma_upper]
    nlinarith
  have hEta'0 : 0 ≤ W.eta' := by
    have hgap := abs_le.mp W.major_gap
    have hsumEta : (1 / 2 : ℝ) ≤ W.eta + W.eta' := by
      rw [← W.exponent_sum]
      linarith [W.gamma_upper]
    nlinarith
  have hExpansion : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (t : ℝ),
      selectedMobiusPTWActualAllocationExpansionAt (X := X) (q := q)
        (z := dyadicMobiusCutoff X)
        (c := dyadicBinomialCoefficient ν.1) (vonMangoldtLabelFactors ν)
        r χ T t W.gamma W.eta W.eta' W.I W.J W.J' := by
    intro r χ t
    exact (selectedMobiusPTW_fixedActualAllocationExpansion_of_sourceWitness
      (z := dyadicMobiusCutoff X)
      (c := dyadicBinomialCoefficient ν.1)
      (δ := decompositionDelta X) hXthree r χ T t
      W.I W.J W.J' W.i W.gamma W.eta W.eta'
      W.i_mem W.i_exponent_lower W.v_eq W.a_eq W.b1_eq
      W.v_support W.a_support W.b1_support).2.2
  have hGroup (K : Finset (Fin (vonMangoldtLabelFactors ν).length)) :
      (selectedDyadicFactors (vonMangoldtLabelFactors ν) K).length ≤ 20 ∧
      dyadicFactorsMassWeight (selectedDyadicFactors (vonMangoldtLabelFactors ν) K) ≤
        Real.log (8 * X) := by
    constructor
    · rw [selectedDyadicFactors_length]
      have hcard : K.card ≤ (vonMangoldtLabelFactors ν).length := by
        simpa using Finset.card_le_univ K
      exact hcard.trans (vonMangoldtLabelFactorCount ν).2
    · exact selectedVonMangoldtGroup_massWeight_le hXthree ν K
  have hGroupI := hGroup W.I
  have hGroupJ := hGroup W.J
  have hGroupJ' := hGroup W.J'
  have hweightI := hGroupI.2
  have hweightJ := hGroupJ.2
  have hweightJ' := hGroupJ'.2
  have hc : ‖dyadicBinomialCoefficient ν.1‖ ≤ (2 : ℝ) ^ 10 := by
    simpa [Real.norm_eq_abs] using dyadicBinomialCoefficient_abs_le ν.1
  refine ⟨W, hWdata, W.i_mem, W.i_exponent_lower, hRange.1, hRange.2,
    htaggedBranch, ?_⟩
  intro hcont hMUFblock
  exact selectedMobiusPTW_actualSourceIntegral_le_of_MUF_liveCellBounds
    hd (vonMangoldtLabelFactors ν) W.I W.J W.J' rchar T W.gamma W.eta W.eta'
    hExpansion hcont hXlarge ha heps0 heps hXlog hU0 hUsource hQ hqfactor hqlog
    hrchar W.exponent_sum W.gamma_lower W.gamma_upper hEta0 hEta'0 W.major_gap
    hSupport₁ hSupport₂ hSupport₃ hc hGroupI.1 hGroupJ.1 hGroupJ'.1
    hweightI hweightJ hweightJ' hfreq hMUFblock hXsave

#print axioms selectedVonMangoldtPTW_taggedThirdBranch_liveAggregateInterface

end FractionalPrimes.Literature.DirichletMean

end
