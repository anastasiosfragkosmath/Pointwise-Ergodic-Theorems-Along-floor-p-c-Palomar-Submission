module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownSmallGroupData
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic

/-!
# Normalized smooth Heath--Brown factor masses

This file verifies the coefficient bound needed to feed the actual tagged
smooth Heath--Brown factors into the finite inverse-square-root mass estimate.
The selected-factor interval estimate and the floor/reindex bridge remain
separate inputs.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

private theorem smoothHeathBrownFactorMass_arg_bounds
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X) {n : ℕ}
    (hn : n ∈ smoothFactorMassWindow (smoothHeathBrownFactorScale f)) :
    0 < (n : ℝ) ∧ (n : ℝ) ≤ 16 * X := by
  have hN := smoothHeathBrownFactorScale_ge_one f
  have hNnonneg : 0 ≤ smoothHeathBrownFactorScale f := by linarith
  have hwindow := (mem_smoothFactorMassWindow hNnonneg n).mp hn
  have hscale := smoothHeathBrownFactorScale_le_eightX hX f
  constructor
  · exact lt_trans (by positivity : 0 < smoothHeathBrownFactorScale f / 2)
      hwindow.1
  · calc
      (n : ℝ) ≤ 2 * smoothHeathBrownFactorScale f := hwindow.2
      _ ≤ 2 * (8 * X) := by nlinarith
      _ = 16 * X := by ring

private theorem smoothHeathBrownLog_le_four_log
    {X : ℝ} (hX : 3 ≤ X) {n : ℕ} (hnpos : 0 < (n : ℝ))
    (hnle : (n : ℝ) ≤ 16 * X) :
    0 ≤ Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ 4 * Real.log X := by
  have hXpos : 0 < X := by linarith
  have hXgt : 1 < X := by linarith
  have hnOne : 1 ≤ (n : ℝ) := by
    have hnNat : 1 ≤ n := by exact_mod_cast hnpos
    exact_mod_cast hnNat
  have hlognnonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnOne
  have hcube : (16 : ℝ) ≤ X ^ 3 := by
    have hfactor : 0 ≤ (X - 3) * (X ^ 2 + 3 * X + 9) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  have hlog16 : Real.log 16 ≤ 3 * Real.log X := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hcube
    rw [Real.log_pow] at h
    exact h
  have hlognle : Real.log (n : ℝ) ≤ Real.log (16 * X) :=
    Real.log_le_log hnpos hnle
  have hlogmul : Real.log (16 * X) = Real.log 16 + Real.log X := by
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hXpos.ne']
  constructor
  · exact hlognnonneg
  · rw [hlogmul] at hlognle
    linarith

private theorem truncatedMobius_abs_le_one {z : ℝ} (n : ℕ) :
    |truncatedMobius z n| ≤ 1 := by
  by_cases hn : (n : ℝ) ≤ z
  · rw [truncatedMobius_apply_of_le hn]
    have hμ : |ArithmeticFunction.moebius n| ≤ 1 :=
      ArithmeticFunction.abs_moebius_le_one
    exact_mod_cast hμ
  · rw [truncatedMobius_apply_of_not_le hn]
    simp

/-- On the exact finite support window, each tagged factor coefficient has
modulus at most one after the source normalization for its possible logarithm. -/
theorem smoothHeathBrownNormalizedFactorCoefficient_norm_le_one
    {X z : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X) {n : ℕ}
    (hn : n ∈ smoothFactorMassWindow (smoothHeathBrownFactorScale f)) :
    ‖(smoothHeathBrownNormalizedFactorCoefficient (z := z) f n : ℂ)‖ ≤ 1 := by
  have harg := smoothHeathBrownFactorMass_arg_bounds hX f hn
  have hnNatPos : 0 < n := by exact_mod_cast harg.1
  have hnNatNe : n ≠ 0 := Nat.ne_of_gt hnNatPos
  have htheta (j : SmoothHeathBrownScaleIndex X) :
      0 ≤ smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ∧
      smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ≤ 1 :=
    ⟨smoothDyadicTheta_nonneg _, smoothDyadicTheta_le_one _⟩
  cases f with
  | theta j =>
      have ht := htheta j
      have hnorm :
          ‖(smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact ht.2
      simpa [smoothHeathBrownNormalizedFactorCoefficient,
        smoothHeathBrownThetaFactor, hnNatNe] using hnorm
  | logarithm j =>
      have ht := htheta j
      have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
      have hdenpos : 0 < 4 * Real.log X := by positivity
      have hlog := smoothHeathBrownLog_le_four_log hX harg.1 harg.2
      have hratio_nonneg : 0 ≤ Real.log (n : ℝ) / (4 * Real.log X) :=
        div_nonneg hlog.1 (le_of_lt hdenpos)
      have hratio_le : Real.log (n : ℝ) / (4 * Real.log X) ≤ 1 :=
        (div_le_one hdenpos).2 hlog.2
      have hproduct_nonneg :
          0 ≤ (Real.log (n : ℝ) / (4 * Real.log X)) *
            smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) :=
        mul_nonneg hratio_nonneg ht.1
      have hproduct_le :
          (Real.log (n : ℝ) / (4 * Real.log X)) *
            smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ≤ 1 := by
        calc
          _ ≤ Real.log (n : ℝ) / (4 * Real.log X) * 1 :=
            mul_le_mul_of_nonneg_left ht.2 hratio_nonneg
          _ ≤ 1 := by simpa using hratio_le
      have hvalue :
          smoothHeathBrownLogFactor j n / (4 * Real.log X) =
            (Real.log (n : ℝ) / (4 * Real.log X)) *
              smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) := by
        simp [smoothHeathBrownLogFactor, hnNatNe, ArithmeticFunction.log_apply]
        field_simp [ne_of_gt hdenpos]
      rw [smoothHeathBrownNormalizedFactorCoefficient, hvalue]
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hproduct_nonneg] using hproduct_le
  | mobius j =>
      have ht := htheta j
      have hproduct :
          |truncatedMobius z n *
            smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg ht.1]
        calc
          |truncatedMobius z n| *
              smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val) ≤ 1 * 1 :=
            mul_le_mul (truncatedMobius_abs_le_one n) ht.2
              ht.1 (by norm_num)
          _ = 1 := by norm_num
      have hnorm :
          ‖((truncatedMobius z n *
            smoothDyadicTheta ((n : ℝ) / (2 : ℝ) ^ j.val)) : ℂ)‖ ≤ 1 := by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
          using hproduct
      simpa [smoothHeathBrownNormalizedFactorCoefficient,
        smoothHeathBrownMobiusFactor, hnNatNe] using hnorm

/-- The actual normalized smooth Heath--Brown factor has the source inverse
square-root mass bound `5 sqrt N` on its finite dyadic support. -/
theorem smoothHeathBrownNormalizedFactor_inverseSqrtMass
    {X z : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X) :
    (∑ n ∈ smoothHeathBrownFactorFiniteSupport f,
      ‖(smoothHeathBrownNormalizedFactorCoefficient (z := z) f n : ℂ)‖ /
        Real.sqrt (n : ℝ)) ≤ 5 * Real.sqrt (smoothHeathBrownFactorScale f) := by
  rw [smoothHeathBrownFactorFiniteSupport_eq_massWindow]
  apply smoothFactorInverseSqrtMass (smoothHeathBrownFactorScale_ge_one f)
  intro n hn
  exact smoothHeathBrownNormalizedFactorCoefficient_norm_le_one hX f hn

#print axioms smoothHeathBrownNormalizedFactorCoefficient_norm_le_one
#print axioms smoothHeathBrownNormalizedFactor_inverseSqrtMass

end FractionalPrimes.Literature.DirichletAdapter

end
