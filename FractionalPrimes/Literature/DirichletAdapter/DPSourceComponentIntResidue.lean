module
public import FractionalPrimes.Literature.DirichletAdapter.DPSourceComponentLogEnvelope
public import FractionalPrimes.Literature.DirichletAdapter.DPResidueRepresentative
@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
noncomputable section

/-- The source component estimate with the paper's arbitrary integer residue.
The residue class is unchanged: the natural representative is used only
to invoke the already checked component branch. -/
theorem smoothHeathBrownDPSourceComponent_logEnvelope_intResidue
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
          ∀ (a : ℤ) (c : ℝ) (j : ℕ), 2 ≤ j →
            |c| ≤ (2 : ℝ) ^ 10 →
            (A + 22) ≤ D * ((j : ℝ) - 1) →
            8 ≤ (j : ℝ) * η →
            dirichletMeanEnvelopeOfA_X
              (smoothHeathBrownComponentOuterCutoffMellinPolynomial
                X q a (fun n =>
                  c * smoothHeathBrownConvolutionFactors
                    (dyadicMobiusCutoff X) fs n))
              (X / H) W ≤
                (2 * dpSourceTypeIConstant j +
                    (2 : ℝ) ^ 12 * dpSourceIImajConstant) *
                  Real.sqrt X * (Real.log X) ^ (-(A + 21)) := by
  obtain ⟨X₀, hX₀, hcomp⟩ :=
    smoothHeathBrownDPSourceComponent_logEnvelope
      hB hκ hD hη hηsmall hA hκabs hDabs
  refine ⟨X₀, hX₀, ?_⟩
  intro X hX hL hlarge fs hlen hne hret hE hlog H W hH hWdef hW hWT
    q hq hqlog a c j hj hc hDtail hjη
  have hqpos : 0 < q := by omega
  rw [dirichletMeanEnvelopeOfA_X_residueRepresentative hqpos X (X / H) W a
    (fun n => c * smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X) fs n)]
  exact hcomp hX hL hlarge fs hlen hne hret hE hlog
    hH hWdef hW hWT q hq hqlog (dpResidueRepresentative q a)
    c j hj hc hDtail hjη

#print axioms smoothHeathBrownDPSourceComponent_logEnvelope_intResidue
end
end FractionalPrimes.Literature.DirichletAdapter
