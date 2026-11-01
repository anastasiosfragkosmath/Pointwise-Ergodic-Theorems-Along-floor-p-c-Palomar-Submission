module

public import FractionalPrimes.Literature.JSW.SmoothDyadicRawMajorant
public import FractionalPrimes.Literature.JSW.SmoothLargeScaleSum

/-! The exact source scalar large-scale majorant integral. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothDyadicOffSupportConstant (a : ℝ) (ha : 0 < a) : ℝ :=
  (lpNorm (deriv φ) 1 volume/2)*(jswB a ha/(jswB a ha-1))

theorem smoothDyadicOffSupportConstant_nonneg {a : ℝ} (ha : 0 < a) :
    0 ≤ smoothDyadicOffSupportConstant a ha := by
  have hb := jswB_gt_one ha
  exact mul_nonneg (div_nonneg lpNorm_nonneg (by norm_num))
    (div_nonneg (by linarith) (by linarith))

theorem smoothDyadic_atom_majorant_integral
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ) (m j : ℤ) {u : ℝ → ℂ}
    (hu : Integrable u volume) (hmean : ∫ y, u y ∂volume = 0)
    (hsupp : ∀ y, y ∉ dyadicInterval m j → u y = 0) :
    let S := K.filter (fun k => (2 : ℝ)^m < jswTau a ha k)
    let M := fun x => ∑ k ∈ S, ‖smoothPsiDensityConvolution σ (jswTau a ha k) u x‖
    Integrable M volume ∧ (∫ x, M x ∂volume) ≤
      smoothDyadicOffSupportConstant a ha*(∫ x, ‖u x‖ ∂volume) := by
  classical
  let S := K.filter (fun k => (2 : ℝ)^m < jswTau a ha k)
  let M := fun x => ∑ k ∈ S, ‖smoothPsiDensityConvolution σ (jswTau a ha k) u x‖
  have hτ (k : ℤ) : 0 < jswTau a ha k := zpow_pos (by linarith [jswB_gt_one ha]) _
  have hcomp (k : ℤ) := smoothPsiDensityConvolution_atom_L1_bound hSupp (hτ k) m j hu hmean hsupp
  have hInt : Integrable M volume := integrable_finset_sum S (fun k _ => (hcomp k).1.norm)
  refine ⟨hInt, ?_⟩
  calc
    _ = ∑ k ∈ S, ∫ x, ‖smoothPsiDensityConvolution σ (jswTau a ha k) u x‖ ∂volume :=
      integral_finset_sum S (fun k _ => (hcomp k).1.norm)
    _ ≤ ∑ k ∈ S, ((2 : ℝ)^m/(2*jswTau a ha k))*lpNorm (deriv φ) 1 volume*lpNorm u 1 volume := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← lpNorm_one_eq_integral_norm (hcomp k).1.aestronglyMeasurable]
      exact (hcomp k).2
    _ = (lpNorm (deriv φ) 1 volume/2)*(∑ k ∈ S, (2 : ℝ)^m/jswTau a ha k)*lpNorm u 1 volume := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (lpNorm (deriv φ) 1 volume/2)*(jswB a ha/(jswB a ha-1))*lpNorm u 1 volume := by
      apply mul_le_mul_of_nonneg_right _ lpNorm_nonneg
      exact mul_le_mul_of_nonneg_left
        (jswTau_finite_largeScale_reciprocal_sum ha (zpow_pos (by norm_num) _) K)
        (div_nonneg lpNorm_nonneg (by norm_num))
    _ = _ := by rw [lpNorm_one_eq_integral_norm hu.aestronglyMeasurable]; rfl

#print axioms smoothDyadic_atom_majorant_integral
end
end FractionalPrimes.Literature.JSW
end
