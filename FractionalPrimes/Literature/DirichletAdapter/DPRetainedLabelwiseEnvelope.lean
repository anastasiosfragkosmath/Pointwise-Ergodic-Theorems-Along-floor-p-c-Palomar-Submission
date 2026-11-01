module
public import FractionalPrimes.Literature.DirichletAdapter.DPSourceComponentIntResidue
public import FractionalPrimes.Literature.DirichletAdapter.DPLabelFactorProperties
@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
noncomputable section

/-- Apply the actual source component estimate to every retained Möbius
label, preserving its coefficient and integer residue class. -/
theorem smoothHeathBrownMobiusRetainedLabel_logEnvelope
    {A B κ D η : ℝ} (hB : 0 < B) (hκ : 0 < κ)
    (hD : 2 * κ + 10 ≤ D) (hη : 0 < η)
    (hηsmall : η < 3 / 16) (hA : 0 < A)
    (hκabs : 16 * (((A + 22) + 20 * B) +
        (smoothHeathBrownDPBlockLogExponent : ℝ)) ≤ κ)
    (hDabs : ((A + 22) + 20 * B) +
        (smoothHeathBrownDPBlockLogExponent : ℝ) ≤ D) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧
      ∀ {X : ℝ}, X₀ ≤ X → (2 : ℝ) ^ 35 ≤ X →
        1 ≤ Real.log X →
        2 * Real.log (logAbsorptionM 1 (A + 22)) ≤ Real.log X →
        ∀ {H W : ℝ}, X ^ ((5 / 8 : ℝ) + η) ≤ H →
          W = (Real.log X) ^ D → 2 ≤ W → W ≤ X / H →
          ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
          ∀ (a : ℤ) (j : ℕ), 2 ≤ j →
            (A + 22) ≤ D * ((j : ℝ) - 1) →
            8 ≤ (j : ℝ) * η →
            ∀ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
            dirichletMeanEnvelopeOfA_X
              (smoothHeathBrownComponentOuterCutoffMellinPolynomial
                X q a (smoothHeathBrownMobiusComponent
                  (dyadicMobiusCutoff X) ν))
              (X / H) W ≤
                (2 * dpSourceTypeIConstant j +
                    (2 : ℝ) ^ 12 * dpSourceIImajConstant) *
                  Real.sqrt X * (Real.log X) ^ (-(A + 21)) := by
  obtain ⟨X₀, hX₀, hcomp⟩ :=
    smoothHeathBrownDPSourceComponent_logEnvelope_intResidue
      hB hκ hD hη hηsmall hA hκabs hDabs
  refine ⟨X₀, hX₀, ?_⟩
  intro X hX hX35 hL hlarge H W hH hWdef hW hWT q hq hqlog a j hj hDtail hjη ν hν
  have hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X)
      (smoothHeathBrownMobiusLabelFactors ν) := by
    simpa [smoothHeathBrownMobiusRetainedLabels] using hν
  have hlen := (smoothHeathBrownMobiusFactorCount ν).2
  have hne : smoothHeathBrownMobiusLabelFactors ν ≠ [] := by
    have hpos := (smoothHeathBrownMobiusFactorCount ν).1
    intro heq
    simp [heq] at hpos
  have hE := smoothHeathBrownRetainedExponentSum_pos hX35 hlen hne hret
  have hlog : (smoothHeathBrownMobiusLabelFactors ν).countP
      smoothHeathBrownTypeILogFactor ≤ 1 := by
    rw [smoothHeathBrownMobiusLabel_logFactorCount_zero]
    omega
  have hc := smoothHeathBrownComponentCoefficient_abs_le ν.1
  have hbound := hcomp hX hL hlarge
    (smoothHeathBrownMobiusLabelFactors ν) hlen hne hret hE hlog
    hH hWdef hW hWT q hq hqlog a
    (dyadicBinomialCoefficient ν.1) j hj hc hDtail hjη
  have hfun : (fun n => dyadicBinomialCoefficient ν.1 *
      smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X)
        (smoothHeathBrownMobiusLabelFactors ν) n) =
      smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν := by
    funext n
    exact (smoothHeathBrownMobiusComponent_apply _ ν n).symm
  rw [← hfun]
  exact hbound

/-- Apply the same source component estimate to every retained von
Mangoldt label, including its single logarithmic factor. -/
theorem smoothHeathBrownVonMangoldtRetainedLabel_logEnvelope
    {A B κ D η : ℝ} (hB : 0 < B) (hκ : 0 < κ)
    (hD : 2 * κ + 10 ≤ D) (hη : 0 < η)
    (hηsmall : η < 3 / 16) (hA : 0 < A)
    (hκabs : 16 * (((A + 22) + 20 * B) +
        (smoothHeathBrownDPBlockLogExponent : ℝ)) ≤ κ)
    (hDabs : ((A + 22) + 20 * B) +
        (smoothHeathBrownDPBlockLogExponent : ℝ) ≤ D) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧
      ∀ {X : ℝ}, X₀ ≤ X → (2 : ℝ) ^ 35 ≤ X →
        1 ≤ Real.log X →
        2 * Real.log (logAbsorptionM 1 (A + 22)) ≤ Real.log X →
        ∀ {H W : ℝ}, X ^ ((5 / 8 : ℝ) + η) ≤ H →
          W = (Real.log X) ^ D → 2 ≤ W → W ≤ X / H →
          ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
          ∀ (a : ℤ) (j : ℕ), 2 ≤ j →
            (A + 22) ≤ D * ((j : ℝ) - 1) →
            8 ≤ (j : ℝ) * η →
            ∀ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
            dirichletMeanEnvelopeOfA_X
              (smoothHeathBrownComponentOuterCutoffMellinPolynomial
                X q a (smoothHeathBrownVonMangoldtComponent
                  (dyadicMobiusCutoff X) ν))
              (X / H) W ≤
                (2 * dpSourceTypeIConstant j +
                    (2 : ℝ) ^ 12 * dpSourceIImajConstant) *
                  Real.sqrt X * (Real.log X) ^ (-(A + 21)) := by
  obtain ⟨X₀, hX₀, hcomp⟩ :=
    smoothHeathBrownDPSourceComponent_logEnvelope_intResidue
      hB hκ hD hη hηsmall hA hκabs hDabs
  refine ⟨X₀, hX₀, ?_⟩
  intro X hX hX35 hL hlarge H W hH hWdef hW hWT q hq hqlog a j hj hDtail hjη ν hν
  have hret : smoothHeathBrownSupportRetained
      (X := X) (z := dyadicMobiusCutoff X)
      (smoothHeathBrownVonMangoldtLabelFactors ν) := by
    simpa [smoothHeathBrownVonMangoldtRetainedLabels] using hν
  have hlen := (smoothHeathBrownVonMangoldtFactorCount ν).2
  have hne : smoothHeathBrownVonMangoldtLabelFactors ν ≠ [] := by
    have hpos := (smoothHeathBrownVonMangoldtFactorCount ν).1
    intro heq
    simp [heq] at hpos
  have hE := smoothHeathBrownRetainedExponentSum_pos hX35 hlen hne hret
  have hlog : (smoothHeathBrownVonMangoldtLabelFactors ν).countP
      smoothHeathBrownTypeILogFactor ≤ 1 := by
    rw [smoothHeathBrownVonMangoldtLabel_logFactorCount_one]
  have hc := smoothHeathBrownComponentCoefficient_abs_le ν.1
  have hbound := hcomp hX hL hlarge
    (smoothHeathBrownVonMangoldtLabelFactors ν) hlen hne hret hE hlog
    hH hWdef hW hWT q hq hqlog a
    (dyadicBinomialCoefficient ν.1) j hj hc hDtail hjη
  have hfun : (fun n => dyadicBinomialCoefficient ν.1 *
      smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X)
        (smoothHeathBrownVonMangoldtLabelFactors ν) n) =
      smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν := by
    funext n
    exact (smoothHeathBrownVonMangoldtComponent_apply _ ν n).symm
  rw [← hfun]
  exact hbound

#print axioms smoothHeathBrownMobiusRetainedLabel_logEnvelope
#print axioms smoothHeathBrownVonMangoldtRetainedLabel_logEnvelope
end
end FractionalPrimes.Literature.DirichletAdapter
