module

public import FractionalPrimes.Literature.JSW.SmoothL1Translation
public import FractionalPrimes.Literature.JSW.MeasureSplitting

/-! Exact L1 translation modulus of the actual smooth splitting density. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem measureSplittingPsi_deriv_integrable
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    Integrable (deriv (measureSplittingPsi σ)) volume := by
  have hc : HasCompactSupport (measureSplittingPsi σ) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    exact (subset_tsupport _).trans (measureSplittingPsi_tsupport_subset σ hSupp)
  have hd : Continuous (deriv (measureSplittingPsi σ)) := by
    simpa only [iteratedDeriv_one] using
      (measureSplittingPsi_contDiff σ).continuous_iteratedDeriv 1 (by norm_num)
  exact hd.integrable_of_hasCompactSupport hc.deriv

theorem measureSplittingPsi_L1_translation
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (y c : ℝ) :
    Integrable (fun x : ℝ => measureSplittingPsi σ (x-y)-measureSplittingPsi σ (x-c)) volume ∧
    lpNorm (fun x : ℝ => measureSplittingPsi σ (x-y)-measureSplittingPsi σ (x-c)) 1 volume ≤
      |y-c| *lpNorm (deriv φ) 1 volume := by
  have hf1 : ContDiff ℝ 1 (measureSplittingPsi σ) :=
    (measureSplittingPsi_contDiff σ).of_le (by norm_num)
  have hd := measureSplittingPsi_deriv_integrable hSupp
  obtain ⟨hint,hbound⟩ := integrable_sub_translate_and_norm_le_deriv
    (measureSplittingPsi σ) hf1 hd (c-y)
  have harg (x : ℝ) : x-c+(c-y) = x-y := by ring
  have hint' : Integrable (fun x : ℝ => measureSplittingPsi σ (x-y)-measureSplittingPsi σ (x-c)) volume := by
    simpa only [harg] using hint.comp_sub_right c
  have htrans : (∫ x : ℝ, ‖measureSplittingPsi σ (x-y)-measureSplittingPsi σ (x-c)‖ ∂volume) =
      ∫ x : ℝ, ‖measureSplittingPsi σ (x+(c-y))-measureSplittingPsi σ x‖ ∂volume := by
    simpa only [harg] using integral_sub_right_eq_self
      (fun z : ℝ => ‖measureSplittingPsi σ (z+(c-y))-measureSplittingPsi σ z‖) c
  have hDmeas : AEStronglyMeasurable (deriv (measureSplittingPsi σ)) volume := hd.aestronglyMeasurable
  have hDnorm : lpNorm (deriv (measureSplittingPsi σ)) 1 volume ≤ lpNorm (deriv φ) 1 volume := by
    simpa only [iteratedDeriv_one] using measureSplittingPsi_iteratedDeriv_lpNorm_one_le σ hSupp 1
  refine ⟨hint', ?_⟩
  rw [lpNorm_one_eq_integral_norm hint'.aestronglyMeasurable, htrans]
  calc
    _ ≤ |c-y| *(∫ x : ℝ, ‖deriv (measureSplittingPsi σ) x‖ ∂volume) := hbound
    _ = |y-c| *lpNorm (deriv (measureSplittingPsi σ)) 1 volume := by
      rw [abs_sub_comm c y, lpNorm_one_eq_integral_norm hDmeas]
    _ ≤ _ := mul_le_mul_of_nonneg_left hDnorm (abs_nonneg _)

#print axioms measureSplittingPsi_L1_translation
#print axioms measureSplittingPsi_deriv_integrable
end
end FractionalPrimes.Literature.JSW
end
