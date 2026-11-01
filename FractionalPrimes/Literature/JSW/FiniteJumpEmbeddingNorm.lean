module

public import FractionalPrimes.Literature.JSW.FiniteJumpMomentBridge

/-! Finite ordered subsequences can only decrease the source jump-control Lp norm. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem finiteJumpControl_eLpNorm_comp_orderEmbedding_le
    {I J : Type*} [LinearOrder I] [Fintype I] [LinearOrder J] [Fintype J]
    (e : I ↪o J) (F : J → ℝ → ℂ) (hF : ∀ i, Measurable (F i))
    {t : ℝ} (ht : 0 ≤ t) (p : ℝ≥0∞) :
    eLpNorm (finiteJumpControl (fun i => F (e i)) t) p volume ≤
      eLpNorm (finiteJumpControl F t) p volume := by
  apply eLpNorm_mono_ae_real
    (finiteJumpControl_measurable _ t (fun i => hF (e i))).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (finiteJumpControl_nonneg _ ht x)]
  apply mul_le_mul_of_nonneg_left _ ht
  apply Real.sqrt_le_sqrt
  exact_mod_cast finiteSeparatedJumpCount_comp_orderEmbedding_le e (fun j => F j x) t

#print axioms finiteJumpControl_eLpNorm_comp_orderEmbedding_le
end
end FractionalPrimes.Literature.JSW
end
