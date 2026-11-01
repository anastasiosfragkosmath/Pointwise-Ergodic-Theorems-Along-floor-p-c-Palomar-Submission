module
public import FractionalPrimes.Literature.Twisted.SelectedVonMangoldtOriginalFactorAbsorbed
public import FractionalPrimes.Literature.Twisted.GroupedSmallFactorUniform
@[expose] public section

noncomputable section
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
namespace FractionalPrimes.Literature.Twisted
/-- Same selected von Mangoldt subset and original index at every frequency;
empty or disjoint blocks are treated exactly as zero. -/
theorem selectedVonMangoldtGroup_originalFactorExtractionAbsorbed_uniform
    {X a z N₁ : ℝ} (hX3 : 3 ≤ X) (ha : 2 ≤ a) (hz : 0 ≤ z)
    (hthreshold : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (hN₁ : 0 < N₁) (ν : VonMangoldtDyadicLabel X)
    (I : Finset (Fin (vonMangoldtLabelFactors ν).length))
    (i : Fin (vonMangoldtLabelFactors ν).length) (hiI : i ∈ I)
    {r Q : ℕ} (hr : 1 ≤ r)
    (hrlog : (r : ℝ) ≤ (Real.log X) ^ a)
    (χ : BlueprintCharacter Q) (hQ : 1 ≤ Q)
    (hQlog : (Q : ℝ) ≤ (Real.log X) ^ a)
    (hOriginal : ∀ s : ℝ,
      (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
        OriginalLongFactorAt X
          (dyadicFactorScale ((vonMangoldtLabelFactors ν).get i)) s a)
    :
    ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| → |s| ≤ X ^ (a + 1) →
      ‖(dyadicBinomialCoefficient ν.1 : ℂ) * ∑ m ∈ factorExtractionRealInterval
          (N₁ / (r : ℝ)) (2 * N₁ / (r : ℝ)),
          dyadicFactorComplexProduct z
            (selectedDyadicFactors (vonMangoldtLabelFactors ν) I) (r * m) *
            factorExtractionMellinWeight
              (fun m => evalInt χ (m : ℤ)) s m‖ ≤
        (Real.log X) ^ (-20 * a) * Real.sqrt (N₁ / (r : ℝ)) := by
  classical
  let factors := selectedDyadicFactors (vonMangoldtLabelFactors ν) I
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
    obtain ⟨i₀, hi₀⟩ := selectedDyadicFactors_get_of_mem
      (vonMangoldtLabelFactors ν) I hiI
    have horig : OriginalLongFactorAt X
        (dyadicFactorScale ((selectedDyadicFactors (vonMangoldtLabelFactors ν) I).get i₀)) s a := by
      rw [hi₀]
      exact hOriginal s hfreqlo hfreqhi
    have hAbs := selectedVonMangoldtGroup_originalFactorExtractionAbsorbed
      hX3 ν I i₀ hr χ hN₁ hz ha hthreshold hrlog hQ hQlog
      hfreqlo hfreqhi horig hprod
    simpa [raw, factors] using hAbs

#print axioms selectedVonMangoldtGroup_originalFactorExtractionAbsorbed_uniform
end FractionalPrimes.Literature.Twisted
