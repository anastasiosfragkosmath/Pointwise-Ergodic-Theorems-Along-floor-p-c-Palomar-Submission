module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

open MeasureTheory
open scoped Interval

namespace FractionalPrimes.Literature.LongArithmetic

/-- A pointwise upper bound on a nonnegative real integrand over `[-1,1]`
gives the corresponding interval-integral bound. -/
theorem intervalIntegral_le_of_Icc_nonneg_upper_bound
    {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t ∧ f t ≤ C) :
    (∫ t in (-1 : ℝ)..1, f t) ≤ 2 * C := by
  have hpoint : ∀ t ∈ Ι (-1 : ℝ) 1, ‖f t‖ ≤ C := by
    intro t ht
    have htIoc : t ∈ Set.Ioc (-1 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
    rcases hf t htIcc with ⟨hnonneg, hbound⟩
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hbound
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hnorm' : ‖∫ t in (-1 : ℝ)..1, f t‖ ≤ 2 * C := by
    calc
      ‖∫ t in (-1 : ℝ)..1, f t‖ ≤ C * |(1 : ℝ) - (-1)| := hnorm
      _ = 2 * C := by norm_num; ring
  have hle : (∫ t in (-1 : ℝ)..1, f t) ≤ ‖∫ t in (-1 : ℝ)..1, f t‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  exact hle.trans hnorm'

end FractionalPrimes.Literature.LongArithmetic
