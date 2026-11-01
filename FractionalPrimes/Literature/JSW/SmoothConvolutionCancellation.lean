module

public import FractionalPrimes.Literature.JSW.ConvolutionCZBound

/-! Integrated mean-zero cancellation from an exact L1 translation bound. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem convolution_meanZero_integral_norm_le
    {K u : ℝ → ℂ} {Q : Set ℝ} {c L : ℝ}
    (hK : Integrable K volume) (hu : Integrable u volume)
    (hmean : ∫ y, u y ∂volume = 0)
    (hsupp : ∀ y, y ∉ Q → u y = 0)
    (hshift : ∀ y ∈ Q, (∫ x : ℝ, ‖K (x-y)-K (x-c)‖ ∂volume) ≤ L) :
    Integrable (fun x : ℝ => ∫ y, K (x-y)*u y ∂volume) volume ∧
    (∫ x : ℝ, ‖∫ y, K (x-y)*u y ∂volume‖ ∂volume) ≤
      L*(∫ y, ‖u y‖ ∂volume) := by
  have hbase : Integrable (fun z : ℝ × ℝ => K z.1*u z.2) (volume.prod volume) := hK.mul_prod hu
  have hraw : Integrable (fun z : ℝ × ℝ => K (z.1-z.2)*u z.2) (volume.prod volume) :=
    ((measurePreserving_sub_prod volume volume).integrable_comp hbase.aestronglyMeasurable).2 hbase
  have hcenter : Integrable (fun z : ℝ × ℝ => K (z.1-c)*u z.2) (volume.prod volume) :=
    (hK.comp_sub_right c).mul_prod hu
  have hdiff : Integrable (fun z : ℝ × ℝ => (K (z.1-z.2)-K (z.1-c))*u z.2)
      (volume.prod volume) := by
    have heq : (fun z : ℝ × ℝ => (K (z.1-z.2)-K (z.1-c))*u z.2) =
        (fun z : ℝ × ℝ => K (z.1-z.2)*u z.2) - (fun z : ℝ × ℝ => K (z.1-c)*u z.2) := by
      funext z
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    exact hraw.sub hcenter
  have hnorm : Integrable (fun z : ℝ × ℝ => ‖K (z.1-z.2)-K (z.1-c)‖*‖u z.2‖)
      (volume.prod volume) := by simpa only [norm_mul] using hdiff.norm
  have hpoint : ∀ᵐ x ∂volume,
      ‖∫ y, K (x-y)*u y ∂volume‖ ≤ ∫ y, ‖K (x-y)-K (x-c)‖*‖u y‖ ∂volume := by
    filter_upwards [hraw.prod_right_ae] with x hx
    have hh := convolutionKernelOnCell_cancelledPointwiseBound (c := c)
      (Q := Set.univ) MeasurableSet.univ hx.integrableOn hu.integrableOn
      (by simpa only [Measure.restrict_univ] using hmean)
    simpa only [Measure.restrict_univ] using hh
  refine ⟨hraw.integral_prod_left, ?_⟩
  calc
    _ ≤ ∫ x, ∫ y, ‖K (x-y)-K (x-c)‖*‖u y‖ ∂volume ∂volume :=
      integral_mono_ae hraw.integral_prod_left.norm hnorm.integral_prod_left hpoint
    _ = ∫ y, ∫ x, ‖K (x-y)-K (x-c)‖*‖u y‖ ∂volume ∂volume :=
      integral_integral_swap hnorm
    _ ≤ ∫ y, L*‖u y‖ ∂volume := by
      apply integral_mono_ae hnorm.integral_prod_right (hu.norm.const_mul L)
      filter_upwards [] with y
      rw [integral_mul_const]
      by_cases hy : y ∈ Q
      · exact mul_le_mul_of_nonneg_right (hshift y hy) (norm_nonneg _)
      · simp [hsupp y hy]
    _ = _ := integral_const_mul _ _

#print axioms convolution_meanZero_integral_norm_le
end
end FractionalPrimes.Literature.JSW
end
