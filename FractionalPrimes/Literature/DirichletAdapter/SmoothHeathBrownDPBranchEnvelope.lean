module
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownDPBlockEnvelopeAccumulation
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownDPTypeIEnvelope
public import Mathlib.Tactic
@[expose] public section

/-! Exact Type-I/IImaj split for one retained source component. -/

namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open MeasureTheory
noncomputable section

theorem smoothHeathBrownDPSourceComponent_branchEnvelope
    {A B κ D η : ℝ} (hB : 0 < B) (hκ : 0 < κ)
    (hD : 2 * κ + 10 ≤ D) (hη : 0 < η)
    (hηsmall : η < 3 / 16) (hA : 0 < A)
    (hκabs : 16 * ((A + 20 * B) +
        (smoothHeathBrownDPBlockLogExponent : ℝ)) ≤ κ)
    (hDabs : (A + 20 * B) +
        (smoothHeathBrownDPBlockLogExponent : ℝ) ≤ D) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧
      ∀ {X : ℝ}, X₀ ≤ X →
        (fs : List (SmoothHeathBrownFactor X)) →
        fs.length ≤ 20 → fs ≠ [] →
        smoothHeathBrownSupportRetained
          (X := X) (z := dyadicMobiusCutoff X) fs →
        (hE : 0 < smoothHeathBrownExponentSum fs) →
        fs.countP smoothHeathBrownTypeILogFactor ≤ 1 →
        ∀ {H W : ℝ}, X ^ ((5 / 8 : ℝ) + η) ≤ H →
          W = (Real.log X) ^ D → 2 ≤ W → W ≤ X / H →
          ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
          ∀ (a : ℕ) (c : ℝ) (j : ℕ), 2 ≤ j → |c| ≤ (2 : ℝ) ^ 10 →
          let F := smoothHeathBrownComponentOuterCutoffMellinPolynomial
            X q (a : ℤ) (fun n =>
              c * smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X) fs n)
          let TI := ((2 : ℝ) ^ 40 * 5 ^ 20 * Twisted.smoothDyadicC j) *
            Real.sqrt X * Real.log X *
              (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4))
          let II := ‖(c : ℂ) * (((4 * Real.log X) ^
              fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ)‖ *
            ((2 * Real.pi : ℝ)⁻¹ *
              ((40 : ℝ) * (40 * 40) *
                Real.rpow (Real.log X) (B * 20) *
                (3 * smoothHeathBrownDPBlockFourierConstant *
                  Real.sqrt X * (Real.log X) ^ (-(A + 20 * B)))))
          dirichletMeanEnvelopeOfA_X F (X / H) W ≤ max TI II := by
  obtain ⟨XII, hXII, hII⟩ :=
    smoothHeathBrownDPProductWindowEnvelope_of_IImaj
      hB hκ hD hη hηsmall hA hκabs hDabs
  let X₀ := max XII (smoothLongFactorTypeIThreshold B D η)
  refine ⟨X₀, le_trans hXII (le_max_left _ _), ?_⟩
  intro X hX fs hlen hne hret hE hlog H W hH hWdef hW hWT q hq hqlog a c j hj hc
  dsimp only
  have hXIIX : XII ≤ X := (le_max_left _ _).trans hX
  have hXtype : smoothLongFactorTypeIThreshold B D η ≤ X :=
    (le_max_right _ _).trans hX
  have hXthree : 3 ≤ X := hXII.trans hXIIX
  have hqpos : 0 < q := by omega
  have hT : X / H ≤ X ^ ((3 / 8 : ℝ) - η) :=
    sourceDirichletT0_le_typeIUpper (by linarith) hH
  rcases smoothHeathBrown_longScale_or_IImaj fs hE with ⟨s, hs⟩ | hIImaj
  · exact (smoothHeathBrownTypeIComponentEnvelope_le B D η hXtype
      fs s hlen hret hs hlog q a hqpos (X / H) W j
      hη hB.le (by linarith) hj hWdef hW hWT hT hqlog c hc).trans
      (le_max_left _ _)
  · have hscale (t : ℝ) := smoothHeathBrownRawComponentMellin_eq_scaledProduct
      hXthree fs (by cases fs with | nil => contradiction | cons _ _ => simp)
      q hqpos (a : ℤ) c t
    have hz : 0 ≤ dyadicMobiusCutoff X := by
      unfold dyadicMobiusCutoff
      exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 4 * X) _
    have hbound := hII hXIIX hz
      fs hlen hne hret hE hIImaj hH hWdef hW hWT q hq hqlog
      (a : ℤ) ((c : ℂ) * (((4 * Real.log X) ^
        fs.countP smoothHeathBrownTypeILogFactor : ℝ) : ℂ))
      (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q (a : ℤ)
        (fun n => c * smoothHeathBrownConvolutionFactors (dyadicMobiusCutoff X) fs n))
      hXthree hscale
    exact hbound.trans (le_max_right _ _)

#print axioms smoothHeathBrownDPSourceComponent_branchEnvelope
end
end FractionalPrimes.Literature.DirichletAdapter
