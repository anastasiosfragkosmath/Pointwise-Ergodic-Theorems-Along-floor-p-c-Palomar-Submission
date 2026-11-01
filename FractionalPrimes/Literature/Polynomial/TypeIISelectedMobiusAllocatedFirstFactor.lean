module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusFirstFactorBlock
@[expose] public section

/-! Quotient-scale specialization of the checked selected Möbius first-factor
Mellin block estimate. The source long-factor length is recovered exactly as
`(N/r₁) * r₁ = N`; the modulus bound and source lower-scale estimate remain
the hypotheses of the checked fixed-witness theorem. -/

@[expose] public section

noncomputable section

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- Apply the selected Möbius first-factor estimate at the quotient length
`M=N/r₁`. The existing fixed-witness theorem sees the corresponding original
length `M*r₁=N` and retains its exact `q≤log(X)^a` modulus condition. -/
theorem selectedMobiusPTWAllocatedFirstFactorBlock_fixed
    {a X N : ℝ} (ha : 2 ≤ a)
    (hXlarge : (2 : ℝ) ^ 120 ≤ X)
    (hXabsorb : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    (ν : MobiusDyadicLabel X)
    (I : Finset (Fin (mobiusLabelFactors ν).length))
    (i : Fin (mobiusLabelFactors ν).length) (hiI : i ∈ I)
    (hOriginal : ∀ s : ℝ, (Real.log X) ^ (45 * a) ≤ |s| →
      |s| ≤ X ^ (a + 1) →
      OriginalLongFactorAt X
        (dyadicFactorScale ((mobiusLabelFactors ν).get i)) s a)
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
            (selectedDyadicFactors (mobiusLabelFactors ν) I))
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
  have hblock := selectedMobiusPTWFirstFactorMellinBlock_fixed
    ha hXlarge hXabsorb ν I i hiI hOriginal
    hd hQ hqfactor hqlog r (N / ((r.1 0).1 : ℝ)) hMpos χ s hslo hshi
  simpa using hblock

#print axioms selectedMobiusPTWAllocatedFirstFactorBlock_fixed

end FractionalPrimes.Literature.DirichletMean

end
