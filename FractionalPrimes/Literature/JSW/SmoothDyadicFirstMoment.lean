module

public import FractionalPrimes.Literature.JSW.SmoothDyadicHalfMoment
public import FractionalPrimes.Literature.JSW.PositiveMaximalPsiAdapters

/-! First moments of the actual smooth splitting probability and its dilates. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem initialSquarePsiProbabilityMeasure_abs_le_two_ae
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    ∀ᵐ x ∂initialSquarePsiProbabilityMeasure σ, |x| ≤ 2 := by
  have hm : Measurable (fun x => ENNReal.ofReal (measureSplittingPsi σ x)) :=
    ENNReal.measurable_ofReal.comp (measureSplittingPsi_contDiff σ).continuous.measurable
  apply (ae_withDensity_iff hm).2
  filter_upwards [] with x hx
  have hψ : measureSplittingPsi σ x ≠ 0 := by
    intro hz
    simp [hz] at hx
  have hxS : x ∈ tsupport (measureSplittingPsi σ) := subset_tsupport _ (Function.mem_support.mpr hψ)
  have hxI := measureSplittingPsi_tsupport_subset σ hSupp hxS
  exact abs_le.mpr ⟨by linarith [hxI.1], hxI.2⟩

theorem initialSquarePsiDilate_firstMoment
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun t : ℝ => |t|)
      (Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)) ∧
    (∫ t : ℝ, |t| ∂Measure.map (fun z : ℝ => τ*z)
      (initialSquarePsiProbabilityMeasure σ)) ≤ 2*τ := by
  let μ := initialSquarePsiProbabilityMeasure σ
  letI : IsProbabilityMeasure μ := initialSquarePsiProbabilityMeasure_isProbability hSupp
  have hbound : ∀ᵐ x ∂μ, |x| ≤ 2 := initialSquarePsiProbabilityMeasure_abs_le_two_ae hSupp
  have hint : Integrable (fun x : ℝ => |x|) μ := by
    apply (integrable_const (2 : ℝ)).mono' (by fun_prop)
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_abs] using hx
  have hmean : (∫ x : ℝ, |x| ∂μ) ≤ 2 := by
    simpa using integral_mono_ae hint (integrable_const (2 : ℝ)) hbound
  have hscaled : Integrable (fun x : ℝ => |τ*x|) μ := by
    simpa only [abs_mul, abs_of_pos hτ] using hint.const_mul τ
  have hmapInt : Integrable (fun t : ℝ => |t|) (Measure.map (fun z : ℝ => τ*z) μ) := by
    exact (integrable_map_measure (by fun_prop) (by fun_prop)).2 hscaled
  refine ⟨hmapInt, ?_⟩
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_mul, abs_of_pos hτ]
  rw [integral_const_mul]
  nlinarith [mul_le_mul_of_nonneg_left hmean hτ.le]

#print axioms initialSquarePsiDilate_firstMoment
#print axioms initialSquarePsiProbabilityMeasure_abs_le_two_ae
end
end FractionalPrimes.Literature.JSW
end
