module

public import FractionalPrimes.Literature.Variation.WeakVariationOfJumpLp

/-!
# Root normalization of the weak-variation constant

The blueprint defines `W_{p,r}` through its `p`th power.  These lemmas make
the nonnegative root explicit and rewrite the checked weak level-set
coefficient into the exact form required by layer-cake interpolation.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open scoped ENNReal

noncomputable section

/-- The nonnegative constant whose `p`th power is the coefficient in
`lv:weak-variation`. -/
def weakVariationConstant (p r A B : ℝ) : ℝ :=
  Real.rpow (weakVariationConstantPow p r A B) (1 / p)

theorem weakVariationGamma_pos {r : ℝ} (hr : 2 < r) :
    0 < weakVariationGamma r := by
  unfold weakVariationGamma
  linarith

theorem weakVariationD_pos_public {r : ℝ} (hr : 2 < r) :
    0 < weakVariationD r := by
  have hgamma := weakVariationGamma_pos hr
  have hrho : Real.rpow 2 (-weakVariationGamma r) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold weakVariationD
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.sqrt_pos_of_pos (sub_pos.mpr hrho))

/-- Positivity of the denominator in the dyadic geometric-series term. -/
theorem weakVariationConstant_denominator_pos
    {p r : ℝ} (hp : 0 < p) (hr : 2 < r) :
    0 < 1 - Real.rpow 2 (-weakVariationGamma r * p / 2) := by
  have hgamma := weakVariationGamma_pos hr
  have hexp : -weakVariationGamma r * p / 2 < 0 := by
    have : 0 < weakVariationGamma r * p / 2 := by positivity
    linarith
  exact sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp)

theorem weakVariationConstantPow_nonneg
    {p r A B : ℝ} (hp : 0 < p) (hr : 2 < r)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ weakVariationConstantPow p r A B := by
  unfold weakVariationConstantPow
  have hden := (weakVariationConstant_denominator_pos hp hr).le
  have hD := (weakVariationD_pos_public hr).le
  exact add_nonneg
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (add_nonneg (Real.rpow_nonneg hB _) (Real.rpow_nonneg hA _)))
    (div_nonneg
      (mul_nonneg (Real.rpow_nonneg hD _) (Real.rpow_nonneg hA _)) hden)

theorem weakVariationConstant_nonneg
    {p r A B : ℝ} (hp : 0 < p) (hr : 2 < r)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ weakVariationConstant p r A B := by
  unfold weakVariationConstant
  exact Real.rpow_nonneg (weakVariationConstantPow_nonneg hp hr hA hB) _

/-- The explicit root has exactly the prescribed `p`th power. -/
theorem weakVariationConstant_rpow
    {p r A B : ℝ} (hp : 0 < p) (hr : 2 < r)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (weakVariationConstant p r A B) ^ p =
      weakVariationConstantPow p r A B := by
  have hC := weakVariationConstantPow_nonneg hp hr hA hB
  unfold weakVariationConstant
  rw [Real.rpow_eq_pow]
  simpa only [one_div] using Real.rpow_inv_rpow hC hp.ne'

/-- The `W_{p,r}^p t^{-p}` weak coefficient is exactly `(W_{p,r}/t)^p`
in `ℝ≥0∞`. -/
theorem weakVariationConstant_levelCoefficient
    {p r A B t : ℝ} (hp : 0 < p) (hr : 2 < r)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 < t) :
    ENNReal.ofReal (weakVariationConstantPow p r A B) *
        (ENNReal.ofReal t) ^ (-p) =
      (ENNReal.ofReal (weakVariationConstant p r A B / t)) ^ p := by
  have hC := weakVariationConstant_nonneg hp hr hA hB
  have hCpow := weakVariationConstant_rpow hp hr hA hB
  calc
    ENNReal.ofReal (weakVariationConstantPow p r A B) *
        (ENNReal.ofReal t) ^ (-p) =
      (ENNReal.ofReal (weakVariationConstant p r A B)) ^ p *
        (ENNReal.ofReal t) ^ (-p) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hC hp.le, hCpow]
    _ = (ENNReal.ofReal (weakVariationConstant p r A B)) ^ p /
        (ENNReal.ofReal t) ^ p := by
          rw [div_eq_mul_inv, ENNReal.rpow_neg]
    _ = (ENNReal.ofReal (weakVariationConstant p r A B) /
        ENNReal.ofReal t) ^ p := by
          rw [ENNReal.div_rpow_of_nonneg _ _ hp.le]
    _ = (ENNReal.ofReal (weakVariationConstant p r A B / t)) ^ p := by
          rw [ENNReal.ofReal_div_of_pos ht]

end

end FractionalPrimes.Literature.Variation

end
