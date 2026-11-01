module
public import FractionalPrimes.Literature.Twisted.GroupedSmallFactorTypeIIPackage
@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

namespace FractionalPrimes.Literature.Twisted

/-- The scale/index witness in the tagged type-II data is independent of the
frequency. This is the structural part of the selected-factor argument: the
failed type-I exponent condition puts the same distinguished index in the
source scale range. -/
theorem largeTypeIIDyadicData_hasOriginalLongFactorIndexRange
    {X z c δ : ℝ} (hX : 1 ≤ X)
    (fs : List (DyadicArithmeticFactor X))
    (α : Fin fs.length → ℝ)
    (hα : ∀ j, 0 ≤ α j)
    (hsum : ∑ j : Fin fs.length, α j = 1)
    (hscale : ∀ j,
      normalizedExponentConstant⁻¹ * X ^ α j ≤ dyadicFactorScale (fs.get j) ∧
        dyadicFactorScale (fs.get j) ≤ normalizedExponentConstant * X ^ α j)
    (hNoI : ∀ j, α j < (3 / 8 : ℝ))
    (hdata : largeTypeIIDyadicComponentData z c δ
      (groupedDyadicFactor z (c : ℂ) fs) fs α) :
    ∃ I : Finset (Fin fs.length), ∃ i : Fin fs.length,
      ∃ v : ComplexPositiveIntegerFunction,
      i ∈ I ∧ (1 / 80 : ℝ) ≤ α i ∧
        v = groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I) ∧
        (2 ^ 23 : ℝ)⁻¹ * X ^ (1 / 80 : ℝ) ≤
          dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ (2 ^ 23 : ℝ) * X ^ (3 / 8 : ℝ) := by
  classical
  rcases hdata with ⟨Aminus, Aplus, v, f₁, f₂, γ, η, η', I, J, J', i,
    htypeII, hfactor, hv, hf₁, hf₂, hAminus1, hAminusAplus,
    hAminusLow, hAplusHigh, hgammasum, hgammaLo, hgammaHi, hmajorGap,
    hvSupport, hf₁Support, hf₂Support, hiI, hiAlpha⟩
  have hlen : 0 < fs.length :=
    Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  let w : GroupingPredicates fs.length := ⟨α, hlen, hα, hsum⟩
  have hnotI : ¬ w.I (5 / 8) := by
    intro hwI
    rcases hwI with ⟨j, hj⟩
    have hjlarge : (3 / 8 : ℝ) ≤ α j := by
      dsimp [w, GroupingPredicates.I] at hj
      linarith
    exact (not_lt_of_ge hjlarge) (hNoI j)
  have hrange := groupedFactorOriginalScaleBounds hX w hnotI i hiAlpha (hscale i)
  exact ⟨I, i, v, hiI, hiAlpha, hv, hrange.1, hrange.2⟩

/-- With the selected subset and distinguished factor fixed, the absorbed
Möbius group estimate is uniform throughout the original high-frequency
window. Its only frequency-dependent input is the original-factor estimate
for that same fixed index. -/
theorem groupedMobiusFactorListExtractionAbsorbed_uniform
    {X a z N₁ : ℝ} (hX3 : 3 ≤ X) (ha : 2 ≤ a) (hz : 0 ≤ z)
    (hthreshold : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (hN₁ : 0 < N₁) (ν : MobiusDyadicLabel X)
    (I : Finset (Fin (mobiusLabelFactors ν).length))
    (i : Fin (mobiusLabelFactors ν).length) (hiI : i ∈ I)
    {r Q : ℕ} (hr : 1 ≤ r)
    (hrlog : (r : ℝ) ≤ (Real.log X) ^ a)
    (χ : BlueprintCharacter Q) (hQ : 1 ≤ Q)
    (hQlog : (Q : ℝ) ≤ (Real.log X) ^ a)
    (hOriginal : ∀ s : ℝ,
      (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
        OriginalLongFactorAt X
          (dyadicFactorScale ((mobiusLabelFactors ν).get i)) s a)
    (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10) :
    ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
      ‖c * ∑ m ∈ factorExtractionRealInterval
          (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
          dyadicFactorComplexProduct z
            (selectedDyadicFactors (mobiusLabelFactors ν) I) (r * m) *
            factorExtractionMellinWeight
              (fun m => evalInt χ (m : ℤ)) s m‖ ≤
        (Real.log X) ^ (-20 * a) * Real.sqrt (N₁ / (r : ℝ)) := by
  classical
  let factors := selectedDyadicFactors (mobiusLabelFactors ν) I
  have hfs : factors ≠ [] := by
    intro hempty
    have hlen : factors.length = I.card := by simp [factors]
    have hIpos : 0 < I.card := Finset.card_pos.mpr ⟨i, hiI⟩
    rw [hempty] at hlen
    simp at hlen
    exact (Nat.ne_of_gt hIpos) hlen.symm
  intro s hfreqlo hfreqhi
  let raw := ∑ m ∈ factorExtractionRealInterval
      (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
      dyadicFactorComplexProduct z factors (r * m) *
        factorExtractionMellinWeight
          (fun m => evalInt χ (m : ℤ)) s m
  by_cases hzero : raw = 0
  · have hlog : 0 < Real.log X := Real.log_pos (by linarith)
    have hnonneg :
        0 ≤ (Real.log X) ^ (-20 * a) * Real.sqrt (N₁ / (r : ℝ)) := by
      positivity
    have hsum :
        (∑ m ∈ factorExtractionRealInterval
          (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
          dyadicFactorComplexProduct z factors (r * m) *
            factorExtractionMellinWeight
              (fun m => evalInt χ (m : ℤ)) s m) = 0 := by
      simpa [raw] using hzero
    simpa [factors, hsum] using hnonneg
  · have hprod := groupedDyadicProductScale_le_of_nonzeroBlockSum
      hN₁ factors hfs hr χ (by simpa [raw, factors] using hzero)
    have hAbs := groupedMobiusFactorListExtractionAbsorbed
      hX3 ha hz hthreshold hN₁ ν I i hiI hr hrlog χ hQ hQlog
      hfreqlo hfreqhi (hOriginal s hfreqlo hfreqhi) c hc hprod
    simpa [raw, factors] using hAbs

/-- The retained Möbius component supplies one tagged type-II grouping and
one distinguished original factor before the frequency variable is
introduced. The resulting selected-block saving therefore uses the same
subset and index at every frequency in the source window. -/
theorem largeMobiusTypeIIGroupedSmallFactor_uniform
    (hMUF : FractionalPrimes.Literature.Reciprocal.MobiusUniformity)
    {a X N₁ : ℝ} (ha : 2 ≤ a)
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
    (hN₁ : 0 < N₁) {r Q : ℕ} (hr : 1 ≤ r)
    (hrlog : (r : ℝ) ≤ (Real.log X) ^ a)
    (χ : BlueprintCharacter Q) (hQ : 1 ≤ Q)
    (hQlog : (Q : ℝ) ≤ (Real.log X) ^ a) :
    ∃ α : Fin (mobiusLabelFactors ν).length → ℝ,
      (∀ j, 0 ≤ α j) ∧
      (∑ j : Fin (mobiusLabelFactors ν).length, α j = 1) ∧
      (∀ j, α j < (3 / 8 : ℝ)) ∧
      ∃ I : Finset (Fin (mobiusLabelFactors ν).length),
        ∃ i : Fin (mobiusLabelFactors ν).length,
        ∃ v : ComplexPositiveIntegerFunction,
          i ∈ I ∧ (1 / 80 : ℝ) ≤ α i ∧
          v = groupedDyadicFactor (dyadicMobiusCutoff X)
            (dyadicBinomialCoefficient ν.1 : ℂ)
            (selectedDyadicFactors (mobiusLabelFactors ν) I) ∧
          ∀ s : ℝ,
            (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
            ‖(dyadicBinomialCoefficient ν.1 : ℂ) *
              ∑ m ∈ factorExtractionRealInterval
                (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
                dyadicFactorComplexProduct (dyadicMobiusCutoff X)
                  (selectedDyadicFactors (mobiusLabelFactors ν) I) (r * m) *
                  factorExtractionMellinWeight
                    (fun m => evalInt χ (m : ℤ)) s m‖ ≤
              (Real.log X) ^ (-20 * a) *
                Real.sqrt (N₁ / (r : ℝ)) := by
  classical
  have hX3 : 3 ≤ X := by
    have : (3 : ℝ) ≤ 2 ^ 120 := by norm_num
    exact this.trans hXlarge
  have hXone : 1 ≤ X := by linarith
  have hz : 0 ≤ dyadicMobiusCutoff X := by
    unfold dyadicMobiusCutoff
    positivity
  let component : ComplexPositiveIntegerFunction := fun n =>
    ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)
  obtain ⟨α, hα, hsum, hscale, _hmob, htagged⟩ :=
    largeMobiusDyadicComponentTypesTagged hXlarge ν hν
  have hNoI' : ¬ typeIFunction (decompositionDelta X)
      (decompositionC * X ^ (5 / 8 : ℝ)) component := by
    simpa [component] using hNoI
  have hNoI2' : ¬ typeI2Function (decompositionDelta X)
      (decompositionC * X ^ (7 / 16 : ℝ)) component := by
    simpa [component] using hNoI2
  have hcomponent : component = groupedDyadicFactor
      (dyadicMobiusCutoff X) (dyadicBinomialCoefficient ν.1 : ℂ)
      (mobiusLabelFactors ν) := by
    funext n
    simp [component, groupedDyadicFactor, mobiusDyadicComponent_apply]
  rcases htagged with hI | hI2 | ⟨hdata, hNoIα⟩
  · exact False.elim (hNoI' hI)
  · exact False.elim (hNoI2' hI2)
  · have hdata' : largeTypeIIDyadicComponentData
        (dyadicMobiusCutoff X) (dyadicBinomialCoefficient ν.1)
        (decompositionDelta X)
        (groupedDyadicFactor (dyadicMobiusCutoff X)
          (dyadicBinomialCoefficient ν.1 : ℂ)
          (mobiusLabelFactors ν))
        (mobiusLabelFactors ν) α := by
      change largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        component (mobiusLabelFactors ν) α at hdata
      rw [hcomponent] at hdata
      exact hdata
    obtain ⟨I, i, v, hiI, hiAlpha, hv, hNlow, hNhigh⟩ :=
      largeTypeIIDyadicData_hasOriginalLongFactorIndexRange
        hXone (mobiusLabelFactors ν) α hα hsum hscale hNoIα hdata'
    have hOriginal : ∀ s : ℝ,
        OriginalLongFactorAt X
          (dyadicFactorScale ((mobiusLabelFactors ν).get i)) s a := by
      intro s
      exact originalLongFactorAt_of_MUF_threshold hMUF ha hXorig
        hNlow hNhigh
    have hscalar : ‖(dyadicBinomialCoefficient ν.1 : ℂ)‖ ≤
        (2 : ℝ) ^ 10 := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using
        dyadicBinomialCoefficient_abs_le ν.1
    have hbound := groupedMobiusFactorListExtractionAbsorbed_uniform
      hX3 ha hz hXabsorb hN₁ ν I i hiI hr hrlog χ hQ hQlog
      (fun s _ _ => hOriginal s)
      (dyadicBinomialCoefficient ν.1 : ℂ) hscalar
    exact ⟨α, hα, hsum, hNoIα, I, i, v, hiI, hiAlpha, hv, hbound⟩

#print axioms groupedMobiusFactorListExtractionAbsorbed_uniform
#print axioms largeTypeIIDyadicData_hasOriginalLongFactorIndexRange
#print axioms largeMobiusTypeIIGroupedSmallFactor_uniform

end FractionalPrimes.Literature.Twisted

end

