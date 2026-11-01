module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWCommonCutoffMellinIdentity
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWTaggedLiveFromSource
public import FractionalPrimes.Literature.Polynomial.SelectedPTWSourceIntegralScalar
public import Mathlib.Tactic
@[expose] public section

/-! Compose the fully sourced selected von Mangoldt live integral with the
actual full-frequency residue identity and the shared PTW scalar estimate.
The displayed interval and source constants remain unchanged. -/

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

private theorem selectedVonMangoldtPTW_reducedResidue_gcdFacts
    {d Q q : ℕ} (hd : 0 < d) (hqfactor : d * Q = q)
    (rchar : ℤ) (hrchar : IsCoprime rchar (Q : ℤ)) :
    Nat.gcd ((d : ℤ) * rchar).natAbs q = d ∧
      q / d = Q ∧ ((d : ℤ) * rchar) / (d : ℤ) = rchar := by
  have hcop : Nat.Coprime rchar.natAbs Q := by
    have h := hrchar
    rw [Int.isCoprime_iff_nat_coprime] at h
    simpa using h
  have hresAbs : (((d : ℤ) * rchar).natAbs) = d * rchar.natAbs := by
    rw [Int.natAbs_mul]
    simp
  have hgcd : Nat.gcd ((d : ℤ) * rchar).natAbs q = d := by
    rw [hresAbs, ← hqfactor, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  have hquotient : q / d = Q := by
    rw [← hqfactor]
    exact Nat.mul_div_right Q hd
  have hdInt : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hresidue : ((d : ℤ) * rchar) / (d : ℤ) = rchar :=
    Int.mul_ediv_cancel_left _ hdInt
  exact ⟨hgcd, hquotient, hresidue⟩

set_option maxHeartbeats 6000000 in
/-- The fully sourced continuous selected von Mangoldt type-II estimate,
rewritten as the exact full-frequency Mellin polynomial integral. It retains
the original source scalar, divisor, block-count, and logarithmic constants. -/
theorem selectedVonMangoldtPTW_fullFrequencyIccIntegral_le_from_OAISource
    {X U a eps T H : ℝ} {d Q q : ℕ}
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
    (hH : 0 < H) (hHX : H ≤ X)
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
    let hXlarge : (2 : ℝ) ^ 120 ≤ X := by
      have hbase : (2 : ℝ) ^ 120 ≤
          selectedMobiusPTWFirstFactorMUFThreshold
            FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
            a haMUF := by
        unfold selectedMobiusPTWFirstFactorMUFThreshold
        exact le_max_left _ _
      exact hbase.trans hXthreshold
    let residue : ℤ := (d : ℤ) * rchar
    let fd := selectedVonMangoldtPTWFullFrequencyResidueData hXlarge hν H hH hHX
      q residue T
    ∃ W : SelectedVonMangoldtPTWTypeIIWitness ν
        (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents,
      W.toData = hThird.1 ∧
      W.i ∈ W.I ∧
      (1 / 80 : ℝ) ≤
        (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents W.i ∧
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
        ‖fullFrequencyMellinPolynomial fd t‖ ∂volume) ≤
        (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 *
          ((divisorFunction 3 ⟨d, hd⟩ : ℝ) *
            (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
              selectedPTWFactorScale X d) *
            (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
                (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
              (2 * decompositionC) ^ (3 / 2 : ℝ) *
              (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
              Real.sqrt X / (d : ℝ) * (Real.log X) ^ (-5 * a / 4 : ℝ)))
      ∧ (∫ t in Set.Icc (-U) U,
          ‖fullFrequencyMellinPolynomial fd t‖ ∂volume) ≤
        selectedPTWSourceIntegralConstant * Real.sqrt X *
          (Real.log X) ^ selectedMobiusPTWSourceIntegralExponent a := by
  classical
  let hXlarge : (2 : ℝ) ^ 120 ≤ X := by
    have hbase : (2 : ℝ) ^ 120 ≤
        selectedMobiusPTWFirstFactorMUFThreshold
          FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
          a haMUF := by
      unfold selectedMobiusPTWFirstFactorMUFThreshold
      exact le_max_left _ _
    exact hbase.trans hXthreshold
  let residue : ℤ := (d : ℤ) * rchar
  let fd := selectedVonMangoldtPTWFullFrequencyResidueData
    hXlarge hν H hH hHX q residue T
  have hsource := selectedVonMangoldtPTW_taggedThirdBranch_liveAggregate_from_OAISource
    D ν hν haMUF hXthreshold heps0 heps hXlog hU0 hUsource
    hd hQ hqfactor hqlog rchar hrchar hfreq hXsave hThird
  obtain ⟨W, hWdata, hiI, hiAlpha, hScaleLo, hScaleHi, hTagged,
    hLiveIntegral⟩ := hsource
  rcases selectedVonMangoldtPTW_reducedResidue_gcdFacts
      hd hqfactor rchar hrchar with
    ⟨hGcd, hQuotient, hReducedResidue⟩
  have hq : 0 < q := by
    rw [← hqfactor]
    exact Nat.mul_pos hd hQ
  have hpoly (t : ℝ) :
      fullFrequencyMellinPolynomial fd t =
        ((d : ℂ) ^
            (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
          (∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              star (evalInt χ rchar) *
                selectedMobiusPTWActualCommonCutoffTerm
                  (z := dyadicMobiusCutoff X)
                  (c := dyadicBinomialCoefficient ν.1)
                  (vonMangoldtLabelFactors ν) (q := q) r χ T t
                  W.gamma W.eta W.eta' W.I W.J W.J') := by
    change fullFrequencyMellinPolynomial
        (selectedVonMangoldtPTWFullFrequencyResidueData
          hXlarge hν H hH hHX q residue T) t = _
    calc
      _ = ((d : ℂ) ^
          (-((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ))) /
            (Q.totient : ℂ)) *
            (∑ r : divisorFactorTuples 3 d,
              ∑ χ : BlueprintCharacter Q,
                star (evalInt χ rchar) *
                  selectedMobiusPTWActualCommonCutoffTerm
                    (z := dyadicMobiusCutoff X)
                    (c := dyadicBinomialCoefficient ν.1)
                    (vonMangoldtLabelFactors ν) (q := q) r χ T t
                    W.gamma W.eta W.eta' W.I W.J W.J') := by
          exact selectedVonMangoldtPTW_fullFrequencyMellinPolynomial_eq_actualCommonCutoff_of_residuePrefix
            hXlarge hν W H hH hHX q residue T (g := d) (Q := Q)
            hq rchar hGcd hQuotient hReducedResidue t
      _ = _ := by
        rw [show -((1 / 2 : ℂ) +
            Complex.I * ((t - T : ℝ) : ℂ)) =
            -(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ) by ring]
  have hIntegralEq :
      (∫ t in Set.Icc (-U) U,
        ‖fullFrequencyMellinPolynomial fd t‖ ∂volume) =
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
                  W.gamma W.eta W.eta' W.I W.J W.J')‖ ∂volume) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact congrArg norm (hpoly t)
  have hfullBound :
      (∫ t in Set.Icc (-U) U,
        ‖fullFrequencyMellinPolynomial fd t‖ ∂volume) ≤
        (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 *
          ((divisorFunction 3 ⟨d, hd⟩ : ℝ) *
            (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
              selectedPTWFactorScale X d) *
            (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
                (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
              (2 * decompositionC) ^ (3 / 2 : ℝ) *
              (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
              Real.sqrt X / (d : ℝ) * (Real.log X) ^ (-5 * a / 4 : ℝ))) := by
    rw [hIntegralEq]
    exact hLiveIntegral
  have hX3 : 3 ≤ X := by
    have hbase : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hbase.trans hXlarge
  have hQone : 1 ≤ Q := Nat.succ_le_iff.mpr hQ
  have hdleq : d ≤ q := by
    rw [← hqfactor]
    calc
      d = d * 1 := by simp
      _ ≤ d * Q := Nat.mul_le_mul_left d hQone
  have hdleqReal : (d : ℝ) ≤ (q : ℝ) := by exact_mod_cast hdleq
  have hdlog : (d : ℝ) ≤ (Real.log X) ^ a := hdleqReal.trans hqlog
  have hscalar := selectedPTWSourceIntegralScalar_le hX3 hd hdlog
  refine ⟨W, hWdata, hiI, hiAlpha, hScaleLo, hScaleHi, hTagged, ?_⟩
  exact ⟨hfullBound, hfullBound.trans hscalar⟩

#print axioms selectedVonMangoldtPTW_reducedResidue_gcdFacts
#print axioms selectedVonMangoldtPTW_fullFrequencyIccIntegral_le_from_OAISource

end FractionalPrimes.Literature.DirichletMean

end
