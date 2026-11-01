module

public import FractionalPrimes.Operators

@[expose] public section

/-!
# Counting-measure `Lᵖ` norm of a finite-support sequence

This is an exact finite-sum formula for the input pieces used in the
interpolation argument. It reuses Mathlib's counting-measure integral and
`eLpNorm` integral formula.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

theorem eLpNorm_finiteSupport_eq_sum_rpow
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    eLpNorm (fun k : ℤ => if k ∈ s then f k else 0) p Measure.count =
      (∑ k ∈ s, ‖f k‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
  have hf : AEStronglyMeasurable
      (fun k : ℤ => if k ∈ s then f k else 0) Measure.count := by
    exact (measurable_of_countable _).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hf, lintegral_count]
  congr 1
  calc
    ∑' k : ℤ, ‖if k ∈ s then f k else 0‖ₑ ^ p.toReal =
        ∑ k ∈ s, ‖if k ∈ s then f k else 0‖ₑ ^ p.toReal := by
      apply tsum_eq_sum (s := s)
      intro k hk
      simp [hk, ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp0 hpTop)]
    _ = ∑ k ∈ s, ‖f k‖ₑ ^ p.toReal := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [hk]

theorem eLpNorm_finiteSupport_one_eq_sum
    (s : Finset ℤ) (f : ℤ → ℂ) :
    eLpNorm (fun k : ℤ => if k ∈ s then f k else 0) 1 Measure.count =
      ∑ k ∈ s, ‖f k‖ₑ := by
  rw [eLpNorm_finiteSupport_eq_sum_rpow (p := (1 : ℝ≥0∞)) (by norm_num)
    (by norm_num) s f]
  simp

theorem eLpNorm_finiteSupport_two_eq_sum_sq_sqrt
    (s : Finset ℤ) (f : ℤ → ℂ) :
    eLpNorm (fun k : ℤ => if k ∈ s then f k else 0) 2 Measure.count =
      (∑ k ∈ s, ‖f k‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_finiteSupport_eq_sum_rpow (p := (2 : ℝ≥0∞)) (by norm_num)
    (by norm_num) s f]
  norm_num

end FractionalPrimes
