module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFixedWitnessAssembly
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWCellLogThreshold
public import Mathlib.Tactic
@[expose] public section

/-! Per-cell selected-Möbius source transfer with logarithmic kernel
hypotheses discharged only after the cell is known to be live. -/

@[expose] public section

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

set_option maxHeartbeats 5000000 in
/-- A live-conditional block estimate. The quotient logarithm and large-base
conditions are derived from this cell's live support geometry, using the
uniform source log threshold. Empty cells are handled by the frozen
live-or-zero assembly and require no geometry. -/
theorem selectedMobiusPTW_actualAllocatedBlock_sourceScale_of_MUF_liveCell
    {X U eps a Tfreq z : ℝ} {d Q q : ℕ}
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hXlog : Real.exp (selectedMobiusPTWCellLogThreshold a eps) ≤ X)
    (hU0 : 2 ≤ U) (hUsource : U ≤ X ^ (3 / 8 - 2 * eps))
    (hd : 0 < d) (hQ : 0 < Q) (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (rchar : ℤ) (hrchar : IsCoprime rchar (Q : ℤ))
    (c : ℂ) (fs : List (DyadicArithmeticFactor X))
    (I J J' : Finset (Fin fs.length))
    (γ η η' : ℝ) (j k l : ℕ)
    (hγsum : γ + η + η' = 1)
    (hγlo : 1 / 4 ≤ γ) (hγhi : γ ≤ 1 / 2)
    (hηlo : 0 ≤ η) (hη'lo : 0 ≤ η')
    (hgap : |η - η'| ≤ 1 / 4)
    (hSupport₁ : complexPositiveSupportedOnInterval
      (groupedDyadicFactor z c (selectedDyadicFactors fs I))
      (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ))
    (hSupport₂ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
      (decompositionC⁻¹ * X ^ η) (decompositionC * X ^ η))
    (hSupport₃ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
      (decompositionC⁻¹ * X ^ η') (decompositionC * X ^ η'))
    (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (hlen₁ : (selectedDyadicFactors fs I).length ≤ 20)
    (hlen₂ : (selectedDyadicFactors fs J).length ≤ 20)
    (hlen₃ : (selectedDyadicFactors fs J').length ≤ 20)
    (hweight₁ : dyadicFactorsMassWeight (selectedDyadicFactors fs I) ≤
      Real.log (8 * X))
    (hweight₂ : dyadicFactorsMassWeight (selectedDyadicFactors fs J) ≤
      Real.log (8 * X))
    (hweight₃ : dyadicFactorsMassWeight (selectedDyadicFactors fs J') ≤
      Real.log (8 * X))
    (hfreq : ∀ t ∈ Set.Icc (-U) U,
      (Real.log X) ^ (45 * a) ≤ |Tfreq - t| ∧
        |Tfreq - t| ≤ X ^ (a + 1))
    (hMUFblock : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (N : ℝ), 0 < N →
      ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| →
        |s| ≤ X ^ (a + 1) →
        ‖∑ n ∈ factorExtractionRealInterval
            (N / ((r.1 0).1 : ℝ))
            (2 * N / ((r.1 0).1 : ℝ)),
          toComplexArithmeticFunction
              (groupedDyadicFactor z c (selectedDyadicFactors fs I))
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
          (Real.log X) ^ (-20 * a) *
            Real.sqrt (N / ((r.1 0).1 : ℝ)))
    (hXsave : selectedMobiusPTWUncappedSavingThreshold a eps ≤ X) :
    (∫ t in Set.Icc (-U) U,
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - Tfreq : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm (z := z) (q := q) c
                (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                (selectedDyadicFactors fs J') r χ Tfreq γ η η' j k l t‖
        ∂volume) ≤
      (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
        (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
          selectedPTWFactorScale X d) *
        (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
            (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
          (2 * decompositionC) ^ (3 / 2 : ℝ) *
            (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
              Real.sqrt X / (d : ℝ) * (Real.log X) ^ (-5 * a / 4 : ℝ)) := by
  classical
  let Y : ℝ :=
    (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
      ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
      ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ)
  let scalar : ℝ → ℂ := fun t =>
    ((d : ℂ) ^
      (-(1 / 2 : ℂ) - Complex.I * ((t - Tfreq : ℝ) : ℂ)) /
      (Q.totient : ℂ))
  have hC₀ : 1 ≤ (2 * decompositionC : ℝ) := by
    have hC : 1 ≤ decompositionC := by
      change 1 ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
      have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
          mul_le_mul h2 h81 (by norm_num) (by positivity)
    nlinarith
  have hdreal : 1 ≤ (d : ℝ) :=
    by exact_mod_cast (Nat.succ_le_iff.mpr hd)
  have hEbudget := selectedMobiusPTW_cellSourceLogBudget_of_threshold
    (X := X) ha heps0 hXlog
  have hXgtone : 1 < X := by
    have hbase : (1 : ℝ) < (2 : ℝ) ^ 120 := by norm_num
    exact lt_of_lt_of_le hbase hXlarge
  have hlogXpos : 0 < Real.log X := Real.log_pos hXgtone
  have hepsbound : eps / 1200 ≤ (1 / 2 : ℝ) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hepsbound hlogXpos.le
  have hE : 3 * Real.log (2 * decompositionC) +
      a * Real.log (Real.log X) ≤ Real.log X / 2 :=
    hEbudget.trans (by nlinarith [hmul])
  have hLiveBound :
      (∃ (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q) (t : ℝ),
        selectedMobiusPTWActualAllocatedWindowTerm
          (z := z) (q := q) c (selectedDyadicFactors fs I)
          (selectedDyadicFactors fs J) (selectedDyadicFactors fs J')
          r χ Tfreq γ η η' j k l t ≠ 0) →
      (∫ t in Set.Icc (-U) U,
        ‖scalar t *
          (∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              star (evalInt χ rchar) *
                selectedMobiusPTWActualAllocatedWindowTerm
                  (z := z) (q := q) c (selectedDyadicFactors fs I)
                  (selectedDyadicFactors fs J) (selectedDyadicFactors fs J')
                  r χ Tfreq γ η η' j k l t)‖ ∂volume) ≤
        (d : ℝ) ^ (-(1 / 2 : ℝ)) *
          (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
            ((selectedPTWFactorScale X d * selectedPTWFactorScale X d *
                selectedPTWFactorScale X d) *
              selectedDyadicPTWUncappedKernel X Y a eps) := by
    intro hLive
    have hconditions := selectedMobiusPTW_actualAllocatedCell_logConditions_of_live
      hXlarge ha heps0 heps hXlog hd hQ hqfactor hqlog γ η η' hγsum c fs I J J'
      Tfreq j k l hSupport₁ hSupport₂ hSupport₃ hLive
    rcases hconditions with ⟨_, hdev, hYlarge⟩
    have hdevFun : ∀ Y' : ℝ, Y' =
        (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
          ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
          ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ) →
      2 * (3 * Real.log (2 * decompositionC) +
        a * Real.log (Real.log X)) / Real.log Y' ≤ eps / 300 := by
      intro Y' hY'
      rw [hY']
      exact hdev
    have hYlarge' : (2 : ℝ) ^ 16 ≤
        (((2 : ℝ) ^ j * (X ^ γ / (4 * decompositionC))) *
          ((2 : ℝ) ^ k * (X ^ η / (4 * decompositionC))) *
          ((2 : ℝ) ^ l * (X ^ η' / (4 * decompositionC)))) / (d : ℝ) := by
      exact hYlarge
    have hkernel := selectedMobiusPTW_actualAllocatedBlockCharacterIntegral_of_live
      hXlarge ha heps0 heps hU0 hUsource hd hQ hqfactor hqlog
      rchar hrchar c fs I J J' γ η η' j k l hγsum hγlo hγhi hηlo hη'lo hgap
      hSupport₁ hSupport₂ hSupport₃ hE hdevFun hYlarge'
      hc hlen₁ hlen₂ hlen₃ hweight₁ hweight₂ hweight₃ hfreq hMUFblock hLive
    simpa [Y, scalar] using hkernel
  have hLiveGeometry :
      (∃ (r : divisorFactorTuples 3 d) (χ : BlueprintCharacter Q) (t : ℝ),
        selectedMobiusPTWActualAllocatedWindowTerm
          (z := z) (q := q) c (selectedDyadicFactors fs I)
          (selectedDyadicFactors fs J) (selectedDyadicFactors fs J')
          r χ Tfreq γ η η' j k l t ≠ 0) →
      X ^ (1 / 2 : ℝ) ≤ Y ∧ Y ≤ (2 * decompositionC) ^ 3 * X / (d : ℝ) := by
    intro hLive
    simpa [Y] using
      selectedMobiusPTW_actualAllocatedCell_sourceQuotientGeometry_of_live
        a γ η η' hXlarge ha hd hQ hqfactor hqlog hE hγsum c fs I J J'
        Tfreq j k l hSupport₁ hSupport₂ hSupport₃ hLive
  exact selectedMobiusPTW_actualAllocatedBlock_sourceScale_of_liveOrZero
    hd scalar c (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
    (selectedDyadicFactors fs J') rchar Tfreq γ η η' j k l
    hLiveBound hLiveGeometry hXlarge ha heps0 hE hC₀ hdreal hXsave

set_option maxHeartbeats 7000000 in
/-- Finite selected-Möbius source transfer with quotient-log conditions
derived only in live cells. Every block has its own quotient base. The
analytic grouped-factor estimate remains an explicit input. -/
theorem selectedMobiusPTW_actualSourceIntegral_le_of_MUF_liveCellBounds
    {X z c U a eps : ℝ} {d Q q : ℕ}
    (hd : 0 < d) (fs : List (DyadicArithmeticFactor X))
    (I J J' : Finset (Fin fs.length))
    (rchar : ℤ) (T γ η η' : ℝ)
    (hExpansion : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (t : ℝ),
      selectedMobiusPTWActualAllocationExpansionAt (X := X) (q := q)
        (z := z) (c := c) fs r χ T t γ η η' I J J')
    (hcont : ∀ j k l,
      Continuous (fun t : ℝ =>
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            (((d : ℂ) ^
                (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
                (Q.totient : ℂ)) * (star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) (c : ℂ)
                (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                (selectedDyadicFactors fs J') r χ T γ η η' j k l t))))
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (ha : 0 ≤ a) (heps0 : 0 < eps) (heps : eps ≤ 3 / 16)
    (hXlog : Real.exp (selectedMobiusPTWCellLogThreshold a eps) ≤ X)
    (hU0 : 2 ≤ U) (hUsource : U ≤ X ^ (3 / 8 - 2 * eps))
    (hQ : 0 < Q) (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (hrchar : IsCoprime rchar (Q : ℤ))
    (hγsum : γ + η + η' = 1)
    (hγlo : 1 / 4 ≤ γ) (hγhi : γ ≤ 1 / 2)
    (hηlo : 0 ≤ η) (hη'lo : 0 ≤ η')
    (hgap : |η - η'| ≤ 1 / 4)
    (hSupport₁ : complexPositiveSupportedOnInterval
      (groupedDyadicFactor z c (selectedDyadicFactors fs I))
      (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ))
    (hSupport₂ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
      (decompositionC⁻¹ * X ^ η) (decompositionC * X ^ η))
    (hSupport₃ : complexPositiveSupportedOnInterval
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
      (decompositionC⁻¹ * X ^ η') (decompositionC * X ^ η'))
    (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (hlen₁ : (selectedDyadicFactors fs I).length ≤ 20)
    (hlen₂ : (selectedDyadicFactors fs J).length ≤ 20)
    (hlen₃ : (selectedDyadicFactors fs J').length ≤ 20)
    (hweight₁ : dyadicFactorsMassWeight (selectedDyadicFactors fs I) ≤
      Real.log (8 * X))
    (hweight₂ : dyadicFactorsMassWeight (selectedDyadicFactors fs J) ≤
      Real.log (8 * X))
    (hweight₃ : dyadicFactorsMassWeight (selectedDyadicFactors fs J') ≤
      Real.log (8 * X))
    (hfreq : ∀ t ∈ Set.Icc (-U) U,
      (Real.log X) ^ (45 * a) ≤ |T - t| ∧
        |T - t| ≤ X ^ (a + 1))
    (hMUFblock : ∀ (r : divisorFactorTuples 3 d)
      (χ : BlueprintCharacter Q) (N : ℝ), 0 < N →
      ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| →
        |s| ≤ X ^ (a + 1) →
        ‖∑ n ∈ factorExtractionRealInterval
            (N / ((r.1 0).1 : ℝ))
            (2 * N / ((r.1 0).1 : ℝ)),
          toComplexArithmeticFunction
              (groupedDyadicFactor z c (selectedDyadicFactors fs I))
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
          (Real.log X) ^ (-20 * a) *
            Real.sqrt (N / ((r.1 0).1 : ℝ)))
    (hXsave : selectedMobiusPTWUncappedSavingThreshold a eps ≤ X) :
    (∫ t in Set.Icc (-U) U,
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        (∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ rchar) *
              selectedMobiusPTWActualCommonCutoffTerm
                (z := z) (c := c) fs (q := q) r χ T t γ η η' I J J')‖
      ∂volume) ≤
      (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 *
        ((divisorFunction 3 ⟨d, hd⟩ : ℝ) *
          (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
            selectedPTWFactorScale X d) *
          (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
              (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
            (2 * decompositionC) ^ (3 / 2 : ℝ) *
              (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
                Real.sqrt X / (d : ℝ) *
                  (Real.log X) ^ (-5 * a / 4 : ℝ))) := by
  classical
  let scalar : ℝ → ℂ := fun t =>
    ((d : ℂ) ^
      (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
      (Q.totient : ℂ))
  have hC₀ : 1 ≤ (2 * decompositionC : ℝ) := by
    have hC : 1 ≤ decompositionC := by
      change 1 ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 200 := one_le_pow₀ (by norm_num)
      have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 := one_le_pow₀ (by norm_num)
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
          mul_le_mul h2 h81 (by norm_num) (by positivity)
    nlinarith
  have hcComplex : ‖(c : ℂ)‖ ≤ (2 : ℝ) ^ 10 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hc
  have hblock : ∀ j ∈ Finset.range
      (selectedMobiusPTWDyadicBlockCount decompositionC),
      ∀ k ∈ Finset.range
      (selectedMobiusPTWDyadicBlockCount decompositionC),
      ∀ l ∈ Finset.range
      (selectedMobiusPTWDyadicBlockCount decompositionC),
        (∫ t in Set.Icc (-U) U,
          ‖∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              scalar t * (star (evalInt χ rchar) *
                selectedMobiusPTWActualAllocatedWindowTerm
                  (z := z) (q := q) (c : ℂ)
                  (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                  (selectedDyadicFactors fs J') r χ T γ η η' j k l t)‖
          ∂volume) ≤
          (divisorFunction 3 ⟨d, hd⟩ : ℝ) *
            (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
              selectedPTWFactorScale X d) *
            (2 * (FractionalPrimes.Literature.DirichletMean.J 20 *
                (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
              (2 * decompositionC) ^ (3 / 2 : ℝ) *
                (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
                  Real.sqrt X / (d : ℝ) *
                    (Real.log X) ^ (-5 * a / 4 : ℝ)) := by
    intro j hj k hk l hl
    have hcell := selectedMobiusPTW_actualAllocatedBlock_sourceScale_of_MUF_liveCell
      hXlarge ha heps0 heps hXlog hU0 hUsource hd hQ hqfactor hqlog
      rchar hrchar c fs I J J' γ η η' j k l hγsum hγlo hγhi hηlo hη'lo hgap
      hSupport₁ hSupport₂ hSupport₃ hcComplex
      hlen₁ hlen₂ hlen₃ hweight₁ hweight₂ hweight₃ hfreq hMUFblock hXsave
    have hsum (t : ℝ) :
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            scalar t * (star (evalInt χ rchar) *
              selectedMobiusPTWActualAllocatedWindowTerm
                (z := z) (q := q) (c : ℂ)
                (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                (selectedDyadicFactors fs J') r χ T γ η η' j k l t) =
          scalar t *
            (∑ r : divisorFactorTuples 3 d,
              ∑ χ : BlueprintCharacter Q,
                star (evalInt χ rchar) *
                  selectedMobiusPTWActualAllocatedWindowTerm
                    (z := z) (q := q) (c : ℂ)
                    (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                    (selectedDyadicFactors fs J') r χ T γ η η' j k l t) := by
      simp only [Finset.mul_sum]
    have hintegral :
        (∫ t in Set.Icc (-U) U,
          ‖∑ r : divisorFactorTuples 3 d,
            ∑ χ : BlueprintCharacter Q,
              scalar t * (star (evalInt χ rchar) *
                selectedMobiusPTWActualAllocatedWindowTerm
                  (z := z) (q := q) (c : ℂ)
                  (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                  (selectedDyadicFactors fs J') r χ T γ η η' j k l t)‖
          ∂volume) =
        (∫ t in Set.Icc (-U) U,
          ‖scalar t *
            (∑ r : divisorFactorTuples 3 d,
              ∑ χ : BlueprintCharacter Q,
                star (evalInt χ rchar) *
                  selectedMobiusPTWActualAllocatedWindowTerm
                    (z := z) (q := q) (c : ℂ)
                    (selectedDyadicFactors fs I) (selectedDyadicFactors fs J)
                    (selectedDyadicFactors fs J') r χ T γ η η' j k l t)‖
          ∂volume) := by
      apply integral_congr_ae
      filter_upwards with t
      exact congrArg norm (hsum t)
    rw [hintegral]
    exact hcell
  exact selectedMobiusPTW_actualSourceIntegral_le_of_sourceScaleBlockBounds
    hd fs I J J' rchar scalar T γ η η' hExpansion hcont hXlarge hC₀ hblock

end FractionalPrimes.Literature.DirichletMean

#print axioms FractionalPrimes.Literature.DirichletMean.selectedMobiusPTW_actualAllocatedBlock_sourceScale_of_MUF_liveCell
#print axioms FractionalPrimes.Literature.DirichletMean.selectedMobiusPTW_actualSourceIntegral_le_of_MUF_liveCellBounds
