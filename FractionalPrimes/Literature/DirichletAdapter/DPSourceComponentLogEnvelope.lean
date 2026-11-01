module
public import FractionalPrimes.Literature.DirichletAdapter.DPSourceBranchConstants
@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open MeasureTheory
noncomputable section

/-- Source-faithful DP saving for one actual retained smooth component.
The extra log threshold is still explicit here; the final task chooses
one threshold uniformly before the residue and frequency parameters. -/
theorem smoothHeathBrownDPSourceComponent_logEnvelope
    {A B κ D η : ℝ} (hB : 0 < B) (hκ : 0 < κ)
    (hD : 2 * κ + 10 ≤ D) (hη : 0 < η)
    (hηsmall : η < 3 / 16) (hA : 0 < A)
    (hκabs : 16 * (((A + 22) + 20 * B) +
        (smoothHeathBrownDPBlockLogExponent : ℝ)) ≤ κ)
    (hDabs : ((A + 22) + 20 * B) +
        (smoothHeathBrownDPBlockLogExponent : ℝ) ≤ D) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧
      ∀ {X : ℝ}, X₀ ≤ X →
        1 ≤ Real.log X →
        2 * Real.log (logAbsorptionM 1 (A + 22)) ≤ Real.log X →
        (fs : List (SmoothHeathBrownFactor X)) →
        fs.length ≤ 20 → fs ≠ [] →
        smoothHeathBrownSupportRetained
          (X := X) (z := dyadicMobiusCutoff X) fs →
        (hE : 0 < smoothHeathBrownExponentSum fs) →
        fs.countP smoothHeathBrownTypeILogFactor ≤ 1 →
        ∀ {H W : ℝ}, X ^ ((5 / 8 : ℝ) + η) ≤ H →
          W = (Real.log X) ^ D → 2 ≤ W → W ≤ X / H →
          ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
          ∀ (a : ℕ) (c : ℝ) (j : ℕ), 2 ≤ j →
            |c| ≤ (2 : ℝ) ^ 10 →
            (A + 22) ≤ D * ((j : ℝ) - 1) →
            8 ≤ (j : ℝ) * η →
            dirichletMeanEnvelopeOfA_X
              (smoothHeathBrownComponentOuterCutoffMellinPolynomial
                X q (a : ℤ) (fun n =>
                  c * smoothHeathBrownConvolutionFactors
                    (dyadicMobiusCutoff X) fs n))
              (X / H) W ≤
                (2 * dpSourceTypeIConstant j +
                    (2 : ℝ) ^ 12 * dpSourceIImajConstant) *
                  Real.sqrt X * (Real.log X) ^ (-(A + 21)) := by
  obtain ⟨X₀, hX₀, hbranch⟩ :=
    smoothHeathBrownDPSourceComponent_branchEnvelope
      hB hκ hD hη hηsmall (by linarith : 0 < A + 22)
      hκabs hDabs
  refine ⟨X₀, hX₀, ?_⟩
  intro X hX hL hlarge fs hlen hne hret hE hlog H W hH hWdef hW hWT
    q hq hqlog a c j hj hc hDtail hjη
  have hraw := hbranch hX fs hlen hne hret hE hlog hH hWdef hW hWT
    q hq hqlog a c j hj hc
  have hXone : 1 ≤ X := by linarith
  have hnum := dpBranchLogarithmicAbsorption
    (X := X) (W := W) (A := A) (B := B) (D := D) (η := η)
    (K₁ := dpSourceTypeIConstant j)
    (K₂ := dpSourceIImajConstant) (c := c)
    (k := fs.countP smoothHeathBrownTypeILogFactor) (j := j)
    hXone hL hA (dpSourceTypeIConstant_nonneg j)
    dpSourceIImajConstant_nonneg hWdef hDtail hjη hlarge hlog hc
  dsimp only at hraw
  have hnorm :
      max
        (((2 : ℝ) ^ 40 * 5 ^ 20 * Twisted.smoothDyadicC j) *
          Real.sqrt X * Real.log X *
            (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)))
        (‖(c : ℂ) * (((4 * Real.log X) ^
              fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ)‖ *
          ((2 * Real.pi : ℝ)⁻¹ *
            ((40 : ℝ) * (40 * 40) *
              Real.rpow (Real.log X) (B * 20) *
              (3 * smoothHeathBrownDPBlockFourierConstant *
                Real.sqrt X * (Real.log X) ^ (-((A + 22) + 20 * B)))))) =
      max
        (dpSourceTypeIConstant j * Real.sqrt X * Real.log X *
          (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)))
        (dpSourceIImajConstant * Real.sqrt X *
          (‖(c : ℂ) * (((4 * Real.log X) ^
              fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ)‖ *
            (Real.log X) ^ (20 * B) *
            (Real.log X) ^ (-(A + 22 + 20 * B)))) := by
    congr 1
    unfold dpSourceIImajConstant
    have hrpow : Real.rpow (Real.log X) (B * 20) =
        (Real.log X) ^ (20 * B) := by
      rw [show B * 20 = 20 * B by ring]
      rfl
    rw [hrpow]
    ring
  exact hraw.trans (hnorm.le.trans hnum)

#print axioms smoothHeathBrownDPSourceComponent_logEnvelope
end
end FractionalPrimes.Literature.DirichletAdapter
