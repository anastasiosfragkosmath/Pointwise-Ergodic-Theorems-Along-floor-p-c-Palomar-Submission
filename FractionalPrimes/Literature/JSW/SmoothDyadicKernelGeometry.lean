module

public import FractionalPrimes.Literature.JSW.DyadicAverage
public import FractionalPrimes.Literature.JSW.MeasureSplitting
public import Mathlib.Analysis.Calculus.MeanValue

/-! Cell-center geometry and the actual smooth cancellation kernel. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothDyadicCellCenter (j : ℤ) (y : ℝ) : ℝ :=
  ((dyadicIntervalIndex j y : ℝ)+1/2)*(2 : ℝ)^j

theorem smoothDyadicCellCenter_distance (j : ℤ) (y : ℝ) :
    |y-smoothDyadicCellCenter j y| ≤ (2 : ℝ)^j/2 := by
  have hy := mem_dyadicIntervalIndex j y
  change (dyadicIntervalIndex j y : ℝ)*(2 : ℝ)^j ≤ y ∧
    y < (((dyadicIntervalIndex j y+1 : ℤ) : ℝ)*(2 : ℝ)^j) at hy
  unfold smoothDyadicCellCenter
  push_cast at hy
  apply abs_le.mpr
  constructor <;> nlinarith [hy.1, hy.2]

theorem measureSplittingPsi_lipschitz_bound
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (u v : ℝ) :
    |measureSplittingPsi σ u-measureSplittingPsi σ v| ≤
      lpNorm (deriv φ) ∞ volume * |u-v| := by
  have hd : Differentiable ℝ (measureSplittingPsi σ) :=
    (measureSplittingPsi_contDiff σ).differentiable (by norm_num)
  have hb (x : ℝ) : ‖deriv (measureSplittingPsi σ) x‖ ≤ lpNorm (deriv φ) ∞ volume := by
    simpa only [iteratedDeriv_one] using measureSplittingPsi_iteratedDeriv_pointwise_bound σ 1 x
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ Set.univ) => hd x) (fun x _ => hb x) convex_univ
    (Set.mem_univ v) (Set.mem_univ u)

def smoothDyadicCancellationKernel
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (τ : ℝ) (j : ℤ) (x y : ℝ) : ℂ :=
  Complex.ofReal (τ⁻¹ * (measureSplittingPsi σ ((x-y)/τ)-
    measureSplittingPsi σ ((x-smoothDyadicCellCenter j y)/τ)))

theorem smoothDyadicCancellationKernel_bound
    (σ : Measure ℝ) [IsProbabilityMeasure σ] {τ : ℝ} (hτ : 0 < τ)
    (j : ℤ) (x y : ℝ) :
    ‖smoothDyadicCancellationKernel σ τ j x y‖ ≤
      ((2 : ℝ)^j / τ^2) * lpNorm (deriv φ) ∞ volume := by
  have hd := smoothDyadicCellCenter_distance j y
  have hL := measureSplittingPsi_lipschitz_bound σ ((x-y)/τ)
    ((x-smoothDyadicCellCenter j y)/τ)
  have hdiff : (x-y)/τ-(x-smoothDyadicCellCenter j y)/τ =
      (smoothDyadicCellCenter j y-y)/τ := by ring
  rw [hdiff, abs_div, abs_of_pos hτ, show |smoothDyadicCellCenter j y-y| =
    |y-smoothDyadicCellCenter j y| from abs_sub_comm _ _] at hL
  have hp : 0 < (2 : ℝ)^j := zpow_pos (by norm_num) _
  have hden : 0 < τ^2 := sq_pos_of_pos hτ
  unfold smoothDyadicCancellationKernel
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hτ]
  calc
    _ ≤ τ⁻¹ * (lpNorm (deriv φ) ∞ volume * (|y-smoothDyadicCellCenter j y|/τ)) :=
      mul_le_mul_of_nonneg_left hL (inv_nonneg.mpr hτ.le)
    _ ≤ τ⁻¹ * (lpNorm (deriv φ) ∞ volume * (((2 : ℝ)^j/2)/τ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hd hτ.le) lpNorm_nonneg) (inv_nonneg.mpr hτ.le)
    _ ≤ _ := by
      have heq : τ⁻¹ * (lpNorm (deriv φ) ∞ volume * (((2 : ℝ)^j/2)/τ)) =
          (((2 : ℝ)^j / τ^2) * lpNorm (deriv φ) ∞ volume)/2 := by ring
      rw [heq]
      have hnonneg : 0 ≤ ((2 : ℝ)^j/τ^2)*lpNorm (deriv φ) ∞ volume :=
        mul_nonneg (div_nonneg hp.le hden.le) lpNorm_nonneg
      linarith

#print axioms smoothDyadicCellCenter_distance
#print axioms smoothDyadicCancellationKernel_bound
end
end FractionalPrimes.Literature.JSW
end
