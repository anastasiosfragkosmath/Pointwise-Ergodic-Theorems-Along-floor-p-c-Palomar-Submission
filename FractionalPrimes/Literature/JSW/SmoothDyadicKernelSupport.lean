module

public import FractionalPrimes.Literature.JSW.SmoothDyadicKernelGeometry
public import Mathlib.MeasureTheory.Function.Floor

/-! Measurability and finite-band support of the source cancellation kernel. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem smoothDyadicCellCenter_measurable (j : ℤ) : Measurable (smoothDyadicCellCenter j) := by
  have hf := Int.measurable_floor.comp (measurable_id.div_const ((2 : ℝ)^j))
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  exact ((hcast.comp hf).add_const (1/2 : ℝ)).mul_const ((2 : ℝ)^j)

theorem smoothDyadicCancellationKernel_measurable
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (τ : ℝ) (j : ℤ) :
    Measurable (Function.uncurry (smoothDyadicCancellationKernel σ τ j)) := by
  have hc := smoothDyadicCellCenter_measurable j
  have hψ := (measureSplittingPsi_contDiff σ).continuous.measurable
  unfold Function.uncurry smoothDyadicCancellationKernel
  fun_prop

theorem smoothDyadicCancellationKernel_eq_zero
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (j : ℤ) (x y : ℝ)
    (hfar : 2*τ+(2 : ℝ)^j < |x-y|) :
    smoothDyadicCancellationKernel σ τ j x y = 0 := by
  have hd := smoothDyadicCellCenter_distance j y
  have hp : 0 < (2 : ℝ)^j := zpow_pos (by norm_num) _
  have hnear : 2*τ < |x-smoothDyadicCellCenter j y| := by
    have htri := abs_sub_le x (smoothDyadicCellCenter j y) y
    rw [abs_sub_comm (smoothDyadicCellCenter j y) y] at htri
    linarith
  have hout (z : ℝ) (hz : 2*τ < |z|) : z/τ ∉ Set.Icc (-(2 : ℝ)) 2 := by
    intro hi
    have habs : |z/τ| ≤ 2 := abs_le.mpr hi
    rw [abs_div, abs_of_pos hτ] at habs
    have := (div_le_iff₀ hτ).1 habs
    linarith
  have h₁ := measureSplittingPsi_eq_zero_of_not_mem_Icc σ hSupp
    (hout (x-y) (by linarith))
  have h₂ := measureSplittingPsi_eq_zero_of_not_mem_Icc σ hSupp
    (hout (x-smoothDyadicCellCenter j y) hnear)
  simp [smoothDyadicCancellationKernel, h₁, h₂]

#print axioms smoothDyadicCancellationKernel_eq_zero
#print axioms smoothDyadicCancellationKernel_measurable
end
end FractionalPrimes.Literature.JSW
end
