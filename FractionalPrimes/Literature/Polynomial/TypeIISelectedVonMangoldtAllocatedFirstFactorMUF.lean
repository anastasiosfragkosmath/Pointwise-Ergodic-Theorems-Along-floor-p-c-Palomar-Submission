module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtFirstFactorBlock
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusAllocatedFirstFactorMUF
@[expose] public section

@[expose] public section
noncomputable section
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators
namespace FractionalPrimes.Literature.DirichletMean

theorem selectedVonMangoldtPTWAllocatedFirstFactorBlock_fixed
    {a X N : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXabsorb : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (ν : VonMangoldtDyadicLabel X)
    (I : Finset (Fin (vonMangoldtLabelFactors ν).length))
    (i : Fin (vonMangoldtLabelFactors ν).length) (hiI : i ∈ I)
    (hOriginal : ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| →
      |s| ≤ X ^ (a + 1) →
      OriginalLongFactorAt X
        (dyadicFactorScale ((vonMangoldtLabelFactors ν).get i)) s a)
    {d Q q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (r : divisorFactorTuples 3 d)
    (hN : 0 < N)
    (χ : BlueprintCharacter Q) (s : ℝ)
    (hslo : (Real.log X) ^ (45 * a) ≤ |s|)
    (hshi : |s| ≤ X ^ (a + 1)) :
    ‖∑ n ∈ factorExtractionRealInterval
        (N / ((r.1 0).1 : ℝ)) (2 * (N / ((r.1 0).1 : ℝ))),
      toComplexArithmeticFunction
          (groupedDyadicFactor (dyadicMobiusCutoff X)
            (dyadicBinomialCoefficient ν.1 : ℂ)
            (selectedDyadicFactors (vonMangoldtLabelFactors ν) I))
          ((r.1 0).1 * n) *
        factorExtractionMellinWeight
          (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
      (Real.log X) ^ (-20 * a) *
        Real.sqrt (N / ((r.1 0).1 : ℝ)) := by
  have hrpos : 0 < (r.1 0).1 := (r.1 0).2
  have hrposR : 0 < ((r.1 0).1 : ℝ) := by exact_mod_cast hrpos
  have hMpos : 0 < N / ((r.1 0).1 : ℝ) := div_pos hN hrposR
  have hsourceLength :
      (N / ((r.1 0).1 : ℝ)) * ((r.1 0).1 : ℝ) = N := by
    field_simp [ne_of_gt hrposR]
  have hblock := selectedVonMangoldtPTWFirstFactorMellinBlock_fixed
    ha hXlarge hXabsorb ν I i hiI hOriginal
    hd hQ hqfactor hqlog r (N / ((r.1 0).1 : ℝ)) hMpos χ s hslo hshi
  simpa using hblock

theorem selectedVonMangoldtPTWAllocatedFirstFactorBlock_from_MUF_fixedIndex
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXorig : mobiusOriginalLongFactorThreshold hMUF a ha ≤ X)
    (hXabsorb : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (ν : VonMangoldtDyadicLabel X)
    (α : Fin (vonMangoldtLabelFactors ν).length → ℝ)
    (hα : ∀ j, 0 ≤ α j)
    (hsum : ∑ j : Fin (vonMangoldtLabelFactors ν).length, α j = 1)
    (hscale : ∀ j,
      normalizedExponentConstant⁻¹ * X ^ α j ≤
          dyadicFactorScale ((vonMangoldtLabelFactors ν).get j) ∧
        dyadicFactorScale ((vonMangoldtLabelFactors ν).get j) ≤
          normalizedExponentConstant * X ^ α j)
    (hNoIα : ∀ j, α j < (3 / 8 : ℝ))
    (I : Finset (Fin (vonMangoldtLabelFactors ν).length))
    (i : Fin (vonMangoldtLabelFactors ν).length) (hiI : i ∈ I)
    (hiAlpha : (1 / 80 : ℝ) ≤ α i)
    {d Q q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (r : divisorFactorTuples 3 d) {N₁ : ℝ} (hN₁ : 0 < N₁)
    (χ : BlueprintCharacter Q) (s : ℝ)
    (hslo : (Real.log X) ^ (45 * a) ≤ |s|)
    (hshi : |s| ≤ X ^ (a + 1)) :
    ‖∑ n ∈ factorExtractionRealInterval
        (N₁ / ((r.1 0).1 : ℝ))
        (2 * N₁ / ((r.1 0).1 : ℝ)),
      toComplexArithmeticFunction
          (groupedDyadicFactor (dyadicMobiusCutoff X)
            (dyadicBinomialCoefficient ν.1 : ℂ)
            (selectedDyadicFactors (vonMangoldtLabelFactors ν) I))
          ((r.1 0).1 * n) *
        factorExtractionMellinWeight
          (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
      (Real.log X) ^ (-20 * a) *
        Real.sqrt (N₁ / ((r.1 0).1 : ℝ)) := by
  have hXone : 1 ≤ X := by linarith [hXlarge]
  have hlen : 0 < (vonMangoldtLabelFactors ν).length :=
    Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  let w : GroupingPredicates (vonMangoldtLabelFactors ν).length :=
    ⟨α, hlen, hα, hsum⟩
  have hnotI : ¬ w.I (5 / 8) := by
    intro hwI
    rcases hwI with ⟨j, hj⟩
    have hjlarge : (3 / 8 : ℝ) ≤ α j := by
      dsimp [w, GroupingPredicates.I] at hj
      linarith
    exact (not_lt_of_ge hjlarge) (hNoIα j)
  have hNrange := groupedFactorOriginalScaleBounds hXone w hnotI i
    hiAlpha (hscale i)
  have hOriginal : ∀ s : ℝ,
      (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
        OriginalLongFactorAt X
          (dyadicFactorScale ((vonMangoldtLabelFactors ν).get i)) s a := by
    intro s hslo hshi
    exact originalLongFactorAt_of_MUF_threshold hMUF ha hXorig
      hNrange.1 hNrange.2
  have hblock := selectedVonMangoldtPTWAllocatedFirstFactorBlock_fixed
    ha hXlarge hXabsorb ν I i hiI hOriginal
    hd hQ hqfactor hqlog r (N := N₁) hN₁ χ s hslo hshi
  have hupper : 2 * N₁ / ((r.1 0).1 : ℝ) =
      2 * (N₁ / ((r.1 0).1 : ℝ)) := by ring
  simpa [hupper] using hblock

#print axioms selectedVonMangoldtPTWAllocatedFirstFactorBlock_fixed
#print axioms selectedVonMangoldtPTWAllocatedFirstFactorBlock_from_MUF_fixedIndex
end FractionalPrimes.Literature.DirichletMean
end
