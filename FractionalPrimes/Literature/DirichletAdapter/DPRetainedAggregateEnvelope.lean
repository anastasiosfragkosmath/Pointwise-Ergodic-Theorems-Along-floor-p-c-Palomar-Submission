module
public import FractionalPrimes.Literature.DirichletAdapter.DPRetainedLabelwiseEnvelope
public import FractionalPrimes.Literature.DirichletAdapter.DPLabelSumLogBound
public import FractionalPrimes.Literature.DirichletAdapter.DPLabelPowerAbsorption
@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
noncomputable section

/-- Sum the checked source component bounds over the exact retained
Möbius and von Mangoldt expansions. The threshold conditions here are
subsequently supplied uniformly by the source parameter choice. -/
theorem smoothHeathBrownDPSourceRetained_aggregateEnvelope
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
        ∀ {H W : ℝ}, (hHpos : 0 < H) → (hHX : H ≤ X) →
          X ^ ((5 / 8 : ℝ) + η) ≤ H →
          W = (Real.log X) ^ D → 2 ≤ W → W ≤ X / H →
          ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
          ∀ (a : ℤ) (j : ℕ), 2 ≤ j →
            (A + 22) ≤ D * ((j : ℝ) - 1) →
            8 ≤ (j : ℝ) * η →
          ∀ (rho : ℝ → ℝ) (hX3 : 3 ≤ X) (hqpos : 0 < q),
            let C : ℝ := 10 * (8 : ℝ) ^ 20 *
              (2 * dpSourceTypeIConstant j +
                (2 : ℝ) ^ 12 * dpSourceIImajConstant)
            dirichletMeanEnvelope
              (outerCutoffWindowData rho X H q a
                (fun n => (paperMu n : ℝ)) hX3 hHpos hHX
                hqpos (Or.inr rfl)) (X / H) W ≤
              C * Real.sqrt X * (Real.log X) ^ (-A) ∧
            dirichletMeanEnvelope
              (outerCutoffWindowData rho X H q a paperLambda hX3
                hHpos hHX hqpos (Or.inl rfl))
                (X / H) W ≤
              C * Real.sqrt X * (Real.log X) ^ (-A) := by
  obtain ⟨Xμ, hXμ, hμ⟩ :=
    smoothHeathBrownMobiusRetainedLabel_logEnvelope
      hB hκ hD hη hηsmall hA hκabs hDabs
  obtain ⟨XΛ, hXΛ, hΛ⟩ :=
    smoothHeathBrownVonMangoldtRetainedLabel_logEnvelope
      hB hκ hD hη hηsmall hA hκabs hDabs
  let X₀ := max Xμ XΛ
  refine ⟨X₀, le_trans hXμ (le_max_left _ _), ?_⟩
  intro X hX hX35 hL hlarge H W hHpos hHX hHlower hWdef hW hWT
    q hq hqlog a j hj hDtail hjη rho hX3 hqpos
  dsimp only
  let C₀ : ℝ := 2 * dpSourceTypeIConstant j +
      (2 : ℝ) ^ 12 * dpSourceIImajConstant
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact add_nonneg
      (mul_nonneg (by norm_num) (dpSourceTypeIConstant_nonneg j))
      (mul_nonneg (by norm_num) dpSourceIImajConstant_nonneg)
  let E : ℝ := C₀ * Real.sqrt X * (Real.log X) ^ (-(A + 21))
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg hC₀ (Real.sqrt_nonneg X))
      (Real.rpow_nonneg (by linarith : 0 ≤ Real.log X) _)
  have hμX : Xμ ≤ X := (le_max_left _ _).trans hX
  have hΛX : XΛ ≤ X := (le_max_right _ _).trans hX
  have hμlabel := hμ hμX hX35 hL hlarge hHlower hWdef hW hWT
    q hq hqlog a j hj hDtail hjη
  have hΛlabel := hΛ hΛX hX35 hL hlarge hHlower hWdef hW hWT
    q hq hqlog a j hj hDtail hjη
  have hsum := dpRetainedLabelEnvelopeSums_le
    (X := X) (T0 := X / H) (W := W) (q := q) (a := a)
    (C := E) hX3 hE hμlabel hΛlabel
  have habs := dpLabelPowerAbsorption
    (L := Real.log X) (X := X) (A := A) (C := C₀) hL hC₀
  have hμouter := outerCutoffMobiusWindowData_envelope_le_retainedComponentEnvelopes
    rho hX3 hHpos hHX q hqpos a hW hWT
  have hΛouter := outerCutoffVonMangoldtWindowData_envelope_le_retainedComponentEnvelopes
    rho hX3 hHpos hHX q hqpos a hW hWT
  constructor
  · exact hμouter.trans (hsum.1.trans (by simpa [E, C₀, mul_assoc] using habs))
  · exact hΛouter.trans (hsum.2.trans (by simpa [E, C₀, mul_assoc] using habs))

#print axioms smoothHeathBrownDPSourceRetained_aggregateEnvelope
end
end FractionalPrimes.Literature.DirichletAdapter
