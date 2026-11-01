module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothDyadicResidueQuadrature
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The exact one-sided power-tail integral used in `lda:type-i`. -/

@[expose] public section

open MeasureTheory intervalIntegral
open scoped Interval

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The positive-frequency tail of `|t|^{-j}` has the blueprint's
`W^{1-j}/(j-1)` bound for `j≥2`. -/
theorem smoothLongFactor_positiveTailIntegral_le
    (W U : ℝ) (j : ℕ) (hW : 0 < W) (hWU : W ≤ U) (hj : 2 ≤ j) :
    (∫ t in W..U, t ^ (-(j : ℝ))) ≤
      W ^ (1 - (j : ℝ)) / ((j : ℝ) - 1) := by
  have hU : 0 < U := lt_of_lt_of_le hW hWU
  have hjreal : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hne : -(j : ℝ) ≠ -1 := by linarith
  have hzero : (0 : ℝ) ∉ [[W, U]] :=
    Set.notMem_uIcc_of_lt hW hU
  have hformula := (integral_rpow
    (a := W) (b := U) (r := -(j : ℝ)) (Or.inr ⟨hne, hzero⟩))
  have hpow : 0 ≤ U ^ (1 - (j : ℝ)) := Real.rpow_nonneg hU.le _
  have hden : 0 < (j : ℝ) - 1 := by linarith
  have hexp : -(j : ℝ) + 1 = 1 - (j : ℝ) := by ring
  rw [hformula]
  calc
    (U ^ (-(j : ℝ) + 1) - W ^ (-(j : ℝ) + 1)) /
        (-(j : ℝ) + 1) =
      (W ^ (1 - (j : ℝ)) - U ^ (1 - (j : ℝ))) /
        ((j : ℝ) - 1) := by
          rw [hexp]
          have hdeneq : 1 - (j : ℝ) = -((j : ℝ) - 1) := by ring
          have hdeninv : (1 - (j : ℝ))⁻¹ = -(((j : ℝ) - 1)⁻¹) := by
            rw [hdeneq, inv_neg]
          rw [div_eq_mul_inv, div_eq_mul_inv, hdeninv]
          ring
    _ ≤ W ^ (1 - (j : ℝ)) / ((j : ℝ) - 1) := by
      apply (div_le_div_iff_of_pos_right hden).mpr
      linarith

/-- Both signed frequency tails together have the exact factor two
used in the Type-I mean estimate. -/
theorem smoothLongFactor_twoTailIntegral_le
    (W U : ℝ) (j : ℕ) (hW : 0 < W) (hWU : W ≤ U) (hj : 2 ≤ j) :
    (∫ t in -U..-W, |t| ^ (-(j : ℝ))) +
      (∫ t in W..U, |t| ^ (-(j : ℝ))) ≤
        2 * (W ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) := by
  have hposEq :
      (∫ t in W..U, |t| ^ (-(j : ℝ))) =
        ∫ t in W..U, t ^ (-(j : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htW : W ≤ t := by
      simpa only [min_eq_left hWU] using ht.1
    change |t| ^ (-(j : ℝ)) = t ^ (-(j : ℝ))
    rw [abs_of_pos (lt_of_lt_of_le hW htW)]
  have hnegEq :
      (∫ t in -U..-W, |t| ^ (-(j : ℝ))) =
        ∫ t in W..U, |t| ^ (-(j : ℝ)) := by
    have h := intervalIntegral.integral_comp_neg
      (a := W) (b := U) (f := fun t : ℝ => |t| ^ (-(j : ℝ)))
    simpa only [abs_neg] using h.symm
  rw [hnegEq, hposEq]
  nlinarith [smoothLongFactor_positiveTailIntegral_le W U j hW hWU hj]

/-- The blueprint's integrated envelope for a power tail plus a constant
quadrature error, still over the two exact signed intervals. -/
theorem smoothLongFactor_twoTailPlusConstant_le
    (W U δ : ℝ) (j : ℕ) (hW : 0 < W) (hWU : W ≤ U)
    (hδ : 0 ≤ δ) (hj : 2 ≤ j) :
    (∫ t in -U..-W, |t| ^ (-(j : ℝ)) + δ) +
      (∫ t in W..U, |t| ^ (-(j : ℝ)) + δ) ≤
        2 * (W ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) + 2 * U * δ := by
  have hUpos : 0 < U := lt_of_lt_of_le hW hWU
  have hInt (a b : ℝ) (hzero : (0 : ℝ) ∉ [[a, b]]) :
      IntervalIntegrable (fun t : ℝ => |t| ^ (-(j : ℝ))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have htne : t ≠ 0 := by
      intro heq
      subst t
      exact hzero ht
    have habs : |t| ≠ 0 := abs_ne_zero.mpr htne
    exact ((Real.continuousAt_rpow_const |t| (-(j : ℝ)) (Or.inl habs)).comp
      continuous_abs.continuousAt).continuousWithinAt
  have hnegInt := hInt (-U) (-W)
    (Set.notMem_uIcc_of_gt (by linarith) (by linarith))
  have hposInt := hInt W U (Set.notMem_uIcc_of_lt hW hUpos)
  rw [intervalIntegral.integral_add hnegInt intervalIntegrable_const,
    intervalIntegral.integral_add hposInt intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  have htail := smoothLongFactor_twoTailIntegral_le W U j hW hWU hj
  nlinarith

#print axioms smoothLongFactor_positiveTailIntegral_le
#print axioms smoothLongFactor_twoTailIntegral_le
#print axioms smoothLongFactor_twoTailPlusConstant_le

end FractionalPrimes.Literature.DirichletAdapter

end
