module

public import FractionalPrimes.Literature.JSW.SmoothPsiAtomSupport

/-! Reflection preserves the exact smooth-density translation modulus. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothPsiReflectedDensity
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (τ x : ℝ) : ℝ :=
  smoothPsiDilatedDensity σ τ (-x)

theorem smoothPsiReflectedDensity_integrable
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) : Integrable (smoothPsiReflectedDensity σ τ) volume :=
  (Measure.measurePreserving_neg volume).integrable_comp_of_integrable
    (smoothPsiDilatedDensity_integrable hSupp hτ)

theorem smoothPsiReflectedDensity_L1_translation
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (y c : ℝ) :
    Integrable (fun x : ℝ => smoothPsiReflectedDensity σ τ (x-y)-
      smoothPsiReflectedDensity σ τ (x-c)) volume ∧
    lpNorm (fun x : ℝ => smoothPsiReflectedDensity σ τ (x-y)-
      smoothPsiReflectedDensity σ τ (x-c)) 1 volume ≤
      (|y-c|/τ)*lpNorm (deriv φ) 1 volume := by
  obtain ⟨hInt,hbound⟩ := smoothPsiDilatedDensity_L1_translation hSupp hτ (-y) (-c)
  have heq : (fun x : ℝ => smoothPsiReflectedDensity σ τ (x-y)-
      smoothPsiReflectedDensity σ τ (x-c)) =
      (fun z : ℝ => smoothPsiDilatedDensity σ τ (z-(-y))-
        smoothPsiDilatedDensity σ τ (z-(-c))) ∘ Neg.neg := by
    funext x
    simp only [smoothPsiReflectedDensity, Function.comp_apply, neg_sub, sub_neg_eq_add]
    congr 2 <;> ring
  refine ⟨heq ▸ (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hInt, ?_⟩
  rw [heq, lpNorm_one_eq_integral_norm
    ((Measure.measurePreserving_neg volume).integrable_comp_of_integrable hInt).aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hInt.aestronglyMeasurable] at *
  change (∫ x : ℝ, ‖smoothPsiDilatedDensity σ τ (-x-(-y))-
    smoothPsiDilatedDensity σ τ (-x-(-c))‖) ≤ _
  rw [(Measure.measurePreserving_neg volume).integral_comp
    (Homeomorph.neg ℝ).measurableEmbedding
    (fun z : ℝ => ‖smoothPsiDilatedDensity σ τ (z-(-y))-
      smoothPsiDilatedDensity σ τ (z-(-c))‖)]
  simpa only [neg_sub_neg, abs_sub_comm] using hbound

#print axioms smoothPsiReflectedDensity_L1_translation
end
end FractionalPrimes.Literature.JSW
end
