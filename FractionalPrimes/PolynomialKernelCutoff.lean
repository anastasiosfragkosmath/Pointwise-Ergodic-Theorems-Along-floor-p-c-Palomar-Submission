module

public import FractionalPrimes.PolynomialKernelScaling
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section

open Set
open scoped ContDiff

namespace FractionalPrimes

/-- The exact cutoff in blueprint `lup:kernel-data`, expressed using
Mathlib's smooth extension of `exp (-1/x)` by zero on `x ≤ 0`. -/
noncomputable def polynomialKernelCutoff (t : ℝ) : ℝ :=
  expNegInvGlue (1 - 4 * t ^ 2)

/-- The positivity region of the exact denominator is precisely the strict
interval in the blueprint cutoff, including its endpoint convention. -/
theorem abs_lt_half_iff_one_sub_four_sq_pos (t : ℝ) :
    |t| < (1 / 2 : ℝ) ↔ 0 < 1 - 4 * t ^ 2 := by
  constructor
  · intro ht
    have hsquare : t ^ 2 < (1 / 2 : ℝ) ^ 2 := by
      exact (sq_lt_sq).2 (by simpa using ht)
    nlinarith
  · intro ht
    have hsquare : t ^ 2 < (1 / 2 : ℝ) ^ 2 := by nlinarith
    exact abs_lt_of_sq_lt_sq hsquare (by norm_num)

/-- Pointwise equality with the approved piecewise formula. This checks that
the `expNegInvGlue` encoding has exactly the original cutoff and normalization. -/
theorem polynomialKernelCutoff_eq_blueprint (t : ℝ) :
    polynomialKernelCutoff t =
      if |t| < (1 / 2 : ℝ) then
        Real.exp (-(1 - 4 * t ^ 2)⁻¹) else 0 := by
  by_cases ht : |t| < (1 / 2 : ℝ)
  · have hpos : 0 < 1 - 4 * t ^ 2 :=
      abs_lt_half_iff_one_sub_four_sq_pos t |>.1 ht
    have hden : ¬ 1 ≤ 4 * t ^ 2 := by nlinarith
    simp only [ite_eq_left ht]
    simp [polynomialKernelCutoff, expNegInvGlue, hden]
  · have hnonpos : 1 - 4 * t ^ 2 ≤ 0 := by
      by_contra h
      exact ht ((abs_lt_half_iff_one_sub_four_sq_pos t).2 (lt_of_not_ge h))
    have hden : 1 ≤ 4 * t ^ 2 := by linarith
    simp only [ite_eq_right ht]
    simp [polynomialKernelCutoff, expNegInvGlue, hden]

/-- The support of the exact cutoff is the open interval `(-1/2,1/2)`, so
its support closure lies in the blueprint's compact closed interval. -/
theorem polynomialKernelCutoff_support :
    Function.support polynomialKernelCutoff = Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
  ext t
  simp only [Function.mem_support, Set.mem_Ioo]
  rw [polynomialKernelCutoff_eq_blueprint]
  by_cases ht : |t| < (1 / 2 : ℝ)
  · simp [abs_lt]
  · simp [abs_lt]

theorem polynomialKernelCutoff_hasCompactSupport : HasCompactSupport polynomialKernelCutoff := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  rw [polynomialKernelCutoff_support]
  exact Set.Ioo_subset_Icc_self

theorem polynomialKernelCutoff_contDiff : ContDiff ℝ ∞ polynomialKernelCutoff := by
  unfold polynomialKernelCutoff
  exact expNegInvGlue.contDiff.comp (by fun_prop)

/-- Schwartz-map realization of the exact compactly supported cutoff from
`lup:kernel-data`. -/
noncomputable def polynomialKernelCutoffSchwartz : SchwartzMap ℝ ℝ :=
  polynomialKernelCutoff_hasCompactSupport.toSchwartzMap polynomialKernelCutoff_contDiff

@[simp]
theorem polynomialKernelCutoffSchwartz_apply (t : ℝ) :
    polynomialKernelCutoffSchwartz t =
      if |t| < (1 / 2 : ℝ) then
        Real.exp (-(1 - 4 * t ^ 2)⁻¹) else 0 := by
  change polynomialKernelCutoff t = _
  exact polynomialKernelCutoff_eq_blueprint t

end FractionalPrimes
