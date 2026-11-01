module

public import FractionalPrimes.FiniteLpDuality
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-!
# Finite-support norming dual vectors

This is the reverse finite-duality ingredient in the `p > 2` branch of
blueprint `lem:interpolation`.  Mathlib's `NNReal.isGreatest_Lp` supplies the
nonnegative finite maximizer; multiplying it by the complex phase of the
input gives a complex norming vector supported on the same finite set.
-/

namespace FractionalPrimes

open scoped BigOperators ComplexConjugate ENNReal NNReal

noncomputable section

private theorem complex_phase_pairing (w : ℝ≥0) (z : ℂ) :
    z * starRingEnd ℂ ((w : ℂ) * (z / (‖z‖ : ℂ))) =
      ((‖z‖₊ * w : ℝ≥0) : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [map_mul, map_div₀]
    simp only [Complex.conj_ofReal]
    rw [show z * ((w : ℂ) * (starRingEnd ℂ z / (‖z‖ : ℂ))) =
        (w : ℂ) * (z * starRingEnd ℂ z) / (‖z‖ : ℂ) by ring]
    rw [Complex.mul_conj']
    field_simp [norm_ne_zero_iff.mpr hz]
    norm_cast
    rw [NNReal.coe_mul]
    simp only [coe_nnnorm]
    ring

private theorem complex_phase_nnnorm_le (w : ℝ≥0) (z : ℂ) :
    ‖(w : ℂ) * (z / (‖z‖ : ℂ))‖₊ ≤ w := by
  change ‖(w : ℂ) * (z / (‖z‖ : ℂ))‖ ≤ (w : ℝ)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hw : (0 : ℝ) ≤ (w : ℝ) := NNReal.zero_le_coe
  rw [abs_of_nonneg hw]
  have hphase : ‖z / (‖z‖ : ℂ)‖ ≤ 1 := by
    by_cases hz : z = 0
    · simp [hz]
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg z), div_self (norm_ne_zero_iff.mpr hz)]
  calc
    (w : ℝ) * ‖z / (‖z‖ : ℂ)‖ ≤ (w : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hphase hw
    _ = (w : ℝ) := mul_one _

/-- A complex vector on a finite set has a norming dual vector at the exact
conjugate exponent.  The witness is zero off the prescribed finite support. -/
theorem exists_finite_complex_norming_dual
    (s : Finset ℤ) (f : ℤ → ℂ) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∃ g : ℤ → ℂ,
      (∀ k, k ∉ s → g k = 0) ∧
      (∑ k ∈ s, ‖g k‖₊ ^ q) ≤ 1 ∧
      ∑ k ∈ s, f k * starRingEnd ℂ (g k) =
        (((∑ k ∈ s, ‖f k‖₊ ^ p) ^ (1 / p) : ℝ≥0) : ℂ) := by
  rcases (NNReal.isGreatest_Lp s (fun k : ℤ => ‖f k‖₊) hpq).1 with
    ⟨w, hw, hnorm⟩
  let g : ℤ → ℂ := fun k =>
    if k ∈ s then (w k : ℂ) * (f k / (‖f k‖ : ℂ)) else 0
  refine ⟨g, ?_, ?_, ?_⟩
  · intro k hk
    simp [g, hk]
  · calc
      ∑ k ∈ s, ‖g k‖₊ ^ q ≤ ∑ k ∈ s, w k ^ q := by
        apply Finset.sum_le_sum
        intro k hk
        rw [show g k = (w k : ℂ) * (f k / (‖f k‖ : ℂ)) by simp [g, hk]]
        exact NNReal.rpow_le_rpow (complex_phase_nnnorm_le (w k) (f k)) hpq.symm.nonneg
      _ ≤ 1 := hw
  · rw [show (∑ k ∈ s, f k * starRingEnd ℂ (g k)) =
        ∑ k ∈ s, ((‖f k‖₊ * w k : ℝ≥0) : ℂ) by
          apply Finset.sum_congr rfl
          intro k hk
          rw [show g k = (w k : ℂ) * (f k / (‖f k‖ : ℂ)) by simp [g, hk]]
          exact complex_phase_pairing (w k) (f k)]
    norm_cast

end

end FractionalPrimes
