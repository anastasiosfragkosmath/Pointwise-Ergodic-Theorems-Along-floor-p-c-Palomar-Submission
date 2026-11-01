module

public import FractionalPrimes.Literature.JSW.PositiveReflectedVectorBound

/-!
# Reflected positive-family difference as a finite-vector adjoint test

The two raw reflected convolution outputs are combined only after each
has its independently checked probability-vector estimate.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The adjoint test required by the lower-exponent signed-vector
transfer, from two finite-family positive maximal-majorant bounds. -/
theorem finiteProbabilityDifference_reflected_dual_test
    {ι : Type*} [Fintype ι] {r s : ℝ} (hr : 2 < r)
    (hrs : (r / 2).HolderConjugate s)
    (μσ μψ : ι → Measure ℝ)
    (hμσ : ∀ i, IsProbabilityMeasure (μσ i))
    (hμψ : ∀ i, IsProbabilityMeasure (μψ i))
    (Bσ Bψ : ℝ) (hBσ : 0 ≤ Bσ) (hBψ : 0 ≤ Bψ)
    (hMaxσ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal s) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal s) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μσ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal s) volume ≤
          Bσ * lpNorm g (ENNReal.ofReal s) volume)
    (hMaxψ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal s) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal s) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μψ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal s) volume ≤
          Bψ * lpNorm g (ENNReal.ofReal s) volume) :
    ∀ G : ℝ → EuclideanSpace ℂ ι,
      MemLp G (ENNReal.ofReal r) volume →
      ∃ Vσ Vψ : ℝ → EuclideanSpace ℂ ι,
        MemLp Vσ (ENNReal.ofReal r) volume ∧
        MemLp Vψ (ENNReal.ofReal r) volume ∧
        (∀ i, (fun x => Vσ x i) =ᵐ[volume]
          (fun x => ∫ y, G (x + y) i ∂(μσ i))) ∧
        (∀ i, (fun x => Vψ x i) =ᵐ[volume]
          (fun x => ∫ y, G (x + y) i ∂(μψ i))) ∧
        lpNorm (fun x => Vσ x - Vψ x) (ENNReal.ofReal r) volume ≤
          (Real.sqrt Bσ + Real.sqrt Bψ) *
            lpNorm G (ENNReal.ofReal r) volume := by
  intro G hG
  obtain ⟨Vσ, hVσ, hVσraw, hVσnorm⟩ :=
    finiteProbabilityConvolution_reflected_vector_lp_bound hr hrs
      μσ hμσ G hG Bσ hBσ hMaxσ
  obtain ⟨Vψ, hVψ, hVψraw, hVψnorm⟩ :=
    finiteProbabilityConvolution_reflected_vector_lp_bound hr hrs
      μψ hμψ G hG Bψ hBψ hMaxψ
  have hσadd (i : ι) : (fun x => Vσ x i) =ᵐ[volume]
      (fun x => ∫ y, G (x + y) i ∂(μσ i)) := by
    letI : IsProbabilityMeasure (μσ i) := hμσ i
    exact (hVσraw i).trans
      (jswConvolution_reflected_ae_eq_add (μσ i)
        (fun x => G x i) (hG.eval_piLp i).aestronglyMeasurable)
  have hψadd (i : ι) : (fun x => Vψ x i) =ᵐ[volume]
      (fun x => ∫ y, G (x + y) i ∂(μψ i)) := by
    letI : IsProbabilityMeasure (μψ i) := hμψ i
    exact (hVψraw i).trans
      (jswConvolution_reflected_ae_eq_add (μψ i)
        (fun x => G x i) (hG.eval_piLp i).aestronglyMeasurable)
  refine ⟨Vσ, Vψ, hVσ, hVψ, hσadd, hψadd, ?_⟩
  calc
    lpNorm (fun x => Vσ x - Vψ x) (ENNReal.ofReal r) volume ≤
        lpNorm Vσ (ENNReal.ofReal r) volume +
          lpNorm Vψ (ENNReal.ofReal r) volume :=
      lpNorm_sub_le hVσ
        (ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ r))
    _ ≤ Real.sqrt Bσ * lpNorm G (ENNReal.ofReal r) volume +
          Real.sqrt Bψ * lpNorm G (ENNReal.ofReal r) volume :=
      add_le_add hVσnorm hVψnorm
    _ = (Real.sqrt Bσ + Real.sqrt Bψ) *
          lpNorm G (ENNReal.ofReal r) volume := by ring

#print axioms finiteProbabilityDifference_reflected_dual_test

end

end FractionalPrimes.Literature.JSW

end
