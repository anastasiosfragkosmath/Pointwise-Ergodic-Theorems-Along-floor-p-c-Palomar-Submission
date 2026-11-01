module

public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownCoefficientBookkeeping
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section
namespace FractionalPrimes.Literature.DirichletAdapter
noncomputable section

/-- The exact smooth Heath--Brown dyadic depth costs one logarithm.
The constant eight is deliberately explicit for the later twentyfold
label-count bound. -/
theorem smoothHeathBrownDepth_add_one_le_eight_log
    {X : ℝ} (hX : 3 ≤ X) :
    (smoothHeathBrownDepth X + 1 : ℝ) ≤ 8 * Real.log X := by
  have hXpos : 0 < X := by linarith
  have hL : 1 ≤ Real.log X := by
    have hthree := Real.log_three_gt_d9
    have hmon := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hX
    linarith
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hlogtwopos : 0 < Real.log 2 := by linarith
  have harg : 1 ≤ 4 * X := by nlinarith
  have hlogbound : Real.log (4 * X) ≤ 3 * Real.log X := by
    have hsq : (4 : ℝ) ≤ X ^ 2 := by nlinarith
    have hfour := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hsq
    rw [Real.log_pow] at hfour
    norm_num only [Nat.cast_ofNat] at hfour
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hXpos)]
    linarith
  have hlogb : Real.logb 2 (4 * X) ≤ 6 * Real.log X := by
    rw [Real.logb]
    apply (div_le_iff₀ hlogtwopos).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.log X)
      (by linarith : 0 ≤ Real.log 2 - 1 / 2)]
  have hceil : (smoothHeathBrownDepth X : ℝ) <
      Real.logb 2 (4 * X) + 1 := by
    dsimp [smoothHeathBrownDepth]
    exact Nat.ceil_lt_add_one (by
      rw [Real.logb]
      exact div_nonneg (Real.log_nonneg harg) hlogtwopos.le)
  have hcast : (smoothHeathBrownDepth X + 1 : ℝ) =
      (smoothHeathBrownDepth X : ℝ) + 1 := by simp
  rw [hcast]
  linarith

/-- The actual retained μ and Λ label sets each cost at most twenty
logarithmic powers, with the source coefficient `10` retained. -/
theorem smoothHeathBrownRetainedLabels_card_le_log_power
    {X : ℝ} (hX : 3 ≤ X) :
    ((smoothHeathBrownMobiusRetainedLabels X).card : ℝ) ≤
        10 * (8 * Real.log X) ^ 20 ∧
      ((smoothHeathBrownVonMangoldtRetainedLabels X).card : ℝ) ≤
        10 * (8 * Real.log X) ^ 20 := by
  have hdepth := smoothHeathBrownDepth_add_one_le_eight_log hX
  have hpow : ((smoothHeathBrownDepth X + 1 : ℝ) ^ 20) ≤
      (8 * Real.log X) ^ 20 := by gcongr
  have hμ := smoothHeathBrownMobiusRetainedLabels_card_le X
  have hΛ := smoothHeathBrownVonMangoldtRetainedLabels_card_le X
  have hμR : ((smoothHeathBrownMobiusRetainedLabels X).card : ℝ) ≤
      10 * (smoothHeathBrownDepth X + 1 : ℝ) ^ 20 := by
    exact_mod_cast hμ
  have hΛR : ((smoothHeathBrownVonMangoldtRetainedLabels X).card : ℝ) ≤
      10 * (smoothHeathBrownDepth X + 1 : ℝ) ^ 20 := by
    exact_mod_cast hΛ
  constructor
  · exact hμR.trans (by gcongr)
  · exact hΛR.trans (by gcongr)

#print axioms smoothHeathBrownDepth_add_one_le_eight_log
#print axioms smoothHeathBrownRetainedLabels_card_le_log_power
end
end FractionalPrimes.Literature.DirichletAdapter
