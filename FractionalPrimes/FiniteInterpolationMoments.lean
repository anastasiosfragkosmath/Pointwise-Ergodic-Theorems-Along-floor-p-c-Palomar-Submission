module

public import FractionalPrimes.FiniteInterpolationSplit
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Moment bounds for the finite interpolation split

These are the finite low/high input moment estimates used after splitting at
the positive height `a * λ` in the approved proof of `lem:interpolation`.
-/

namespace FractionalPrimes

open scoped BigOperators

noncomputable section

/-- For `1 < p < 2`, the low part's second moment is bounded by the
`(2-p)`-power of the cutoff times the original `p`-moment. -/
theorem finiteLowPart_sum_sq_le_rpow_mul_sum_rpow
    {p c : ℝ} (hp2 : p < 2) (hc : 0 ≤ c)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    (∑ k ∈ s, ‖finiteLowPart s c f k‖ ^ 2) ≤
      c ^ (2 - p) * ∑ k ∈ s, ‖f k‖ ^ p := by
  rw [sum_norm_sq_finiteLowPart]
  calc
    (∑ k ∈ s.filter (fun k => ‖f k‖ ≤ c), ‖f k‖ ^ 2) ≤
        ∑ k ∈ s.filter (fun k => ‖f k‖ ≤ c),
          c ^ (2 - p) * ‖f k‖ ^ p := by
      apply Finset.sum_le_sum
      intro k hk
      have hkcut : ‖f k‖ ≤ c := (Finset.mem_filter.mp hk).2
      have hxnonneg : 0 ≤ ‖f k‖ := norm_nonneg _
      by_cases hx : ‖f k‖ = 0
      · simp [hx]
        positivity
      · have hxpos : 0 < ‖f k‖ := lt_of_le_of_ne hxnonneg (Ne.symm hx)
        have hpow : ‖f k‖ ^ (2 - p) ≤ c ^ (2 - p) :=
          Real.rpow_le_rpow hxnonneg hkcut (by linarith)
        have hfactor : ‖f k‖ ^ p * ‖f k‖ ^ (2 - p) ≤
            ‖f k‖ ^ p * c ^ (2 - p) :=
          mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hxnonneg p)
        calc
          ‖f k‖ ^ 2 = ‖f k‖ ^ p * ‖f k‖ ^ (2 - p) := by
            rw [← Real.rpow_two, ← Real.rpow_add hxpos]
            congr 1
            ring
          _ ≤ ‖f k‖ ^ p * c ^ (2 - p) := hfactor
          _ = c ^ (2 - p) * ‖f k‖ ^ p := by ring
    _ ≤ c ^ (2 - p) * ∑ k ∈ s, ‖f k‖ ^ p := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun k => ‖f k‖ ≤ c) s)
      intro k hk hnot
      exact mul_nonneg (Real.rpow_nonneg hc _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- For `1 < p < 2` and positive cutoff, the high part's first moment is
bounded by the `(1-p)`-power of the cutoff times the original `p`-moment.
Positivity is essential because this exponent is negative. -/
theorem finiteHighPart_sum_norm_le_rpow_mul_sum_rpow
    {p c : ℝ} (hp1 : 1 < p) (hc : 0 < c)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    (∑ k ∈ s, ‖finiteHighPart s c f k‖) ≤
      c ^ (1 - p) * ∑ k ∈ s, ‖f k‖ ^ p := by
  rw [sum_norm_finiteHighPart]
  calc
    (∑ k ∈ s.filter (fun k => c < ‖f k‖), ‖f k‖) ≤
        ∑ k ∈ s.filter (fun k => c < ‖f k‖),
          c ^ (1 - p) * ‖f k‖ ^ p := by
      apply Finset.sum_le_sum
      intro k hk
      have hkcut : c < ‖f k‖ := (Finset.mem_filter.mp hk).2
      have hcx : 0 < ‖f k‖ := hc.trans hkcut
      have hexp : 0 < p - 1 := by linarith
      have hpow : c ^ (p - 1) ≤ ‖f k‖ ^ (p - 1) :=
        Real.rpow_le_rpow hc.le hkcut.le hexp.le
      have hcPowPos : 0 < c ^ (p - 1) := Real.rpow_pos_of_pos hc _
      have hratio : 1 ≤ ‖f k‖ ^ (p - 1) / c ^ (p - 1) :=
        (one_le_div hcPowPos).2 hpow
      calc
        ‖f k‖ = ‖f k‖ * 1 := by ring
        _ ≤ ‖f k‖ * (‖f k‖ ^ (p - 1) / c ^ (p - 1)) :=
          mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
        _ = c ^ (1 - p) * ‖f k‖ ^ p := by
          have hcpow : c ^ (1 - p) = (c ^ (p - 1))⁻¹ := by
            rw [show 1 - p = -(p - 1) by ring, Real.rpow_neg hc.le]
          have hxpow : ‖f k‖ ^ p = ‖f k‖ * ‖f k‖ ^ (p - 1) := by
            calc
              ‖f k‖ ^ p = ‖f k‖ ^ (1 + (p - 1)) := by
                congr 1
                ring
              _ = ‖f k‖ ^ (1 : ℝ) * ‖f k‖ ^ (p - 1) :=
                Real.rpow_add hcx 1 (p - 1)
              _ = ‖f k‖ * ‖f k‖ ^ (p - 1) := by rw [Real.rpow_one]
          rw [hcpow, hxpow]
          simp [div_eq_mul_inv]
          ring
    _ ≤ c ^ (1 - p) * ∑ k ∈ s, ‖f k‖ ^ p := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun k => c < ‖f k‖) s)
      intro k hk hnot
      exact mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (norm_nonneg _) _)

end

end FractionalPrimes
