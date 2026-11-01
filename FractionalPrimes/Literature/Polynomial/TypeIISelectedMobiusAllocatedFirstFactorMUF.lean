module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusAllocatedFirstFactor
public import FractionalPrimes.Literature.Twisted.GroupedFactorScaleBounds
@[expose] public section

/-! The actual selected-Möbius type-II data and MUF discharge the first-factor
Mellin block at the quotient length of every allocated support block. The
original long-factor scale range and the global modulus bounds remain visible
in the hypotheses used to construct the estimate. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- Under the retained type-II source hypotheses and MUF, the selected first
group has a fixed distinguished original factor whose grouped-Mellin estimate
holds at every allocated quotient length `N₁/r₁`. The source factor's range
`(2^23)⁻¹ X^(1/80) ≤ scale ≤ 2^23 X^(3/8)` is obtained from the tagged
type-II data; the global `q ≤ log(X)^a` condition is retained for the
allocation and residual-character bounds. -/
theorem selectedMobiusPTWAllocatedFirstFactorBlock_from_MUF
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXorig : mobiusOriginalLongFactorThreshold hMUF a ha ≤ X)
    (hXabsorb : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (ν : MobiusDyadicLabel X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
    (hNoI : ¬ typeIFunction (decompositionDelta X)
      (decompositionC * X ^ (5 / 8 : ℝ))
      (fun n : PositiveInteger =>
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)))
    (hNoI2 : ¬ typeI2Function (decompositionDelta X)
      (decompositionC * X ^ (7 / 16 : ℝ))
      (fun n : PositiveInteger =>
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)))
    {d Q q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (hqfactor : d * Q = q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (r : divisorFactorTuples 3 d) {N₁ : ℝ} (hN₁ : 0 < N₁)
    (χ : BlueprintCharacter Q) (s : ℝ)
    (hslo : (Real.log X) ^ (45 * a) ≤ |s|)
    (hshi : |s| ≤ X ^ (a + 1)) :
    ∃ I : Finset (Fin (mobiusLabelFactors ν).length),
      ∃ i : Fin (mobiusLabelFactors ν).length,
        i ∈ I ∧
        ‖∑ n ∈ factorExtractionRealInterval
            (N₁ / ((r.1 0).1 : ℝ))
            (2 * N₁ / ((r.1 0).1 : ℝ)),
          toComplexArithmeticFunction
              (groupedDyadicFactor (dyadicMobiusCutoff X)
                (dyadicBinomialCoefficient ν.1 : ℂ)
                (selectedDyadicFactors (mobiusLabelFactors ν) I))
              ((r.1 0).1 * n) *
            factorExtractionMellinWeight
              (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
          (Real.log X) ^ (-20 * a) *
            Real.sqrt (N₁ / ((r.1 0).1 : ℝ)) := by
  classical
  have hXone : 1 ≤ X := by linarith [hXlarge]
  let z := dyadicMobiusCutoff X
  let c : ℂ := (dyadicBinomialCoefficient ν.1 : ℂ)
  let component : ComplexPositiveIntegerFunction := fun n =>
    ((mobiusDyadicComponent z ν n.1 : ℝ) : ℂ)
  obtain ⟨α, hα, hsum, hscale, _hmob, htagged⟩ :=
    largeMobiusDyadicComponentTypesTagged hXlarge ν hν
  have hNoI' : ¬ typeIFunction (decompositionDelta X)
      (decompositionC * X ^ (5 / 8 : ℝ)) component := by
    simpa [component, z] using hNoI
  have hNoI2' : ¬ typeI2Function (decompositionDelta X)
      (decompositionC * X ^ (7 / 16 : ℝ)) component := by
    simpa [component, z] using hNoI2
  have hcomponent : component = groupedDyadicFactor z c
      (mobiusLabelFactors ν) := by
    funext n
    simp [component, z, c, groupedDyadicFactor,
      mobiusDyadicComponent_apply]
  rcases htagged with hTypeI | hTypeI2 | ⟨hdata, hNoIα⟩
  · exact False.elim (hNoI' hTypeI)
  · exact False.elim (hNoI2' hTypeI2)
  · have hdata' : largeTypeIIDyadicComponentData z
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        (groupedDyadicFactor z c (mobiusLabelFactors ν))
        (mobiusLabelFactors ν) α := by
      change largeTypeIIDyadicComponentData z (dyadicBinomialCoefficient ν.1)
        (decompositionDelta X) component (mobiusLabelFactors ν) α at hdata
      rw [hcomponent] at hdata
      exact hdata
    obtain ⟨I, i, _v, hiI, _hiAlpha, _hv, hNlow, hNhigh⟩ :=
      largeTypeIIDyadicData_hasOriginalLongFactorIndexRange hXone
        (mobiusLabelFactors ν) α hα hsum hscale hNoIα hdata'
    have hOriginal : ∀ s : ℝ,
        (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
          OriginalLongFactorAt X
            (dyadicFactorScale ((mobiusLabelFactors ν).get i)) s a := by
      intro s hslo hshi
      exact originalLongFactorAt_of_MUF_threshold hMUF ha hXorig
        hNlow hNhigh
    have hblock := selectedMobiusPTWAllocatedFirstFactorBlock_fixed
      ha hXlarge hXabsorb ν I i hiI hOriginal
      hd hQ hqfactor hqlog r (N := N₁) hN₁ χ s hslo hshi
    have hupper : 2 * N₁ / ((r.1 0).1 : ℝ) =
        2 * (N₁ / ((r.1 0).1 : ℝ)) := by ring
    exact ⟨I, i, hiI, by simpa [hupper] using hblock⟩

/-- Fixed-witness MUF adapter for the actual type-II grouping. Unlike the
existential adapter above, this keeps the exact source subset `I` and index
`i` supplied by the already-selected type-II data. The source exponent/scale
comparison first gives the original-factor range required by MUF, and the
block estimate then uses the true allocated quotient `N₁/r₁`. -/
theorem selectedMobiusPTWAllocatedFirstFactorBlock_from_MUF_fixedIndex
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXorig : mobiusOriginalLongFactorThreshold hMUF a ha ≤ X)
    (hXabsorb : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
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
            (selectedDyadicFactors (mobiusLabelFactors ν) I))
          ((r.1 0).1 * n) *
        factorExtractionMellinWeight
          (selectedPTWAllocationCharacterWeight q r χ 0) s n‖ ≤
      (Real.log X) ^ (-20 * a) *
        Real.sqrt (N₁ / ((r.1 0).1 : ℝ)) := by
  have hXone : 1 ≤ X := by linarith [hXlarge]
  have hlen : 0 < (mobiusLabelFactors ν).length :=
    Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  let w : GroupingPredicates (mobiusLabelFactors ν).length :=
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
          (dyadicFactorScale ((mobiusLabelFactors ν).get i)) s a := by
    intro s hslo hshi
    exact originalLongFactorAt_of_MUF_threshold hMUF ha hXorig
      hNrange.1 hNrange.2
  have hblock := selectedMobiusPTWAllocatedFirstFactorBlock_fixed
    ha hXlarge hXabsorb ν I i hiI hOriginal
    hd hQ hqfactor hqlog r (N := N₁) hN₁ χ s hslo hshi
  have hupper : 2 * N₁ / ((r.1 0).1 : ℝ) =
      2 * (N₁ / ((r.1 0).1 : ℝ)) := by ring
  simpa [hupper] using hblock

#print axioms selectedMobiusPTWAllocatedFirstFactorBlock_from_MUF
#print axioms selectedMobiusPTWAllocatedFirstFactorBlock_from_MUF_fixedIndex

end FractionalPrimes.Literature.DirichletMean

end
