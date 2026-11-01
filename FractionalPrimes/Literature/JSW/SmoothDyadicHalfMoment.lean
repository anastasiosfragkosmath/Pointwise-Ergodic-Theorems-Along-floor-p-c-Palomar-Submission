module

public import FractionalPrimes.Literature.JSW.MeasureSplitting

/-! The exact half-moment used in the smooth-to-dyadic comparison. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem measureSplittingPsi_halfMoment
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    Integrable (fun x : ℝ => Real.sqrt |x| * measureSplittingPsi σ x) volume ∧
    (∫ x : ℝ, Real.sqrt |x| * measureSplittingPsi σ x ∂volume) ≤ Real.sqrt 2 := by
  have hpoint (x : ℝ) : Real.sqrt |x| * measureSplittingPsi σ x ≤
      Real.sqrt 2 * measureSplittingPsi σ x := by
    by_cases hx : measureSplittingPsi σ x = 0
    · simp [hx]
    · have hxS : x ∈ tsupport (measureSplittingPsi σ) :=
        subset_tsupport _ (Function.mem_support.mpr hx)
      have hxI := measureSplittingPsi_tsupport_subset σ hSupp hxS
      have hxabs : |x| ≤ 2 := abs_le.mpr ⟨by linarith [hxI.1], hxI.2⟩
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hxabs)
        (measureSplittingPsi_nonneg σ x)
  have hdom : Integrable (fun x => Real.sqrt 2 * measureSplittingPsi σ x) volume :=
    (measureSplittingPsi_integrable σ hSupp).const_mul _
  have hint : Integrable (fun x : ℝ => Real.sqrt |x| * measureSplittingPsi σ x) volume := by
    apply hdom.mono' (by
      have hc := (measureSplittingPsi_contDiff σ).continuous
      exact (Real.continuous_sqrt.comp continuous_abs |>.mul hc).aestronglyMeasurable)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (measureSplittingPsi_nonneg σ x))]
    exact hpoint x
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ x : ℝ, Real.sqrt 2 * measureSplittingPsi σ x ∂volume :=
      integral_mono_ae hint hdom (ae_of_all volume hpoint)
    _ = Real.sqrt 2 := by rw [integral_const_mul, measureSplittingPsi_integral, mul_one]

#print axioms measureSplittingPsi_halfMoment
end
end FractionalPrimes.Literature.JSW
end
