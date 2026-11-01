module

public import FractionalPrimes.Literature.Analytic.ExplicitLogarithmRadii

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Analytic

/-- The explicit logarithm-radius constant is bounded by the exact
reciprocal-strip majorant from the approved blueprint. -/
theorem explicitLogarithmConstant_le_reciprocalStripMajorant {M : ℝ}
    (hM : 0 ≤ M) :
    explicitLogarithmConstant M ≤
      600 * (1 + M) ^ explicitLogarithmTheta := by
  have htheta_pos : 0 < explicitLogarithmTheta := by
    unfold explicitLogarithmTheta
    apply div_pos
    · exact Real.log_pos (by norm_num)
    · exact Real.log_pos (by norm_num)
  have htheta_lt : explicitLogarithmTheta < 1 := by
    have hden : 0 < Real.log (17 / 8 : ℝ) := Real.log_pos (by norm_num)
    have hnumlt : Real.log (67 / 32 : ℝ) < Real.log (17 / 8 : ℝ) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    unfold explicitLogarithmTheta
    exact (div_lt_one hden).2 hnumlt
  have hlinear : 483 + 68 * M ≤ 551 * (1 + M) := by
    nlinarith [hM]
  have hpower :
      (483 + 68 * M) ^ explicitLogarithmTheta ≤
        (551 * (1 + M)) ^ explicitLogarithmTheta :=
    Real.rpow_le_rpow (by nlinarith [hM]) hlinear htheta_pos.le
  have hseven :
      (7 : ℝ) ^ (1 - explicitLogarithmTheta) ≤
        551 ^ (1 - explicitLogarithmTheta) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by linarith)
  have hcoeff :
      (7 : ℝ) ^ (1 - explicitLogarithmTheta) *
          551 ^ explicitLogarithmTheta ≤ 551 := by
    calc
      7 ^ (1 - explicitLogarithmTheta) * 551 ^ explicitLogarithmTheta ≤
          551 ^ (1 - explicitLogarithmTheta) * 551 ^ explicitLogarithmTheta :=
        mul_le_mul_of_nonneg_right hseven
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 551) _)
      _ = 551 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 551)]
        rw [show (1 - explicitLogarithmTheta) + explicitLogarithmTheta = 1 by ring,
          Real.rpow_one]
  calc
    explicitLogarithmConstant M =
        7 ^ (1 - explicitLogarithmTheta) *
          (483 + 68 * M) ^ explicitLogarithmTheta := rfl
    _ ≤ 7 ^ (1 - explicitLogarithmTheta) *
          (551 * (1 + M)) ^ explicitLogarithmTheta :=
        mul_le_mul_of_nonneg_left hpower
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 7) _)
    _ = (7 ^ (1 - explicitLogarithmTheta) *
          551 ^ explicitLogarithmTheta) * (1 + M) ^ explicitLogarithmTheta := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 551)
          (by linarith [hM] : (0 : ℝ) ≤ 1 + M)]
        ring
    _ ≤ 551 * (1 + M) ^ explicitLogarithmTheta :=
      mul_le_mul_of_nonneg_right hcoeff
        (Real.rpow_nonneg (by linarith [hM] : (0 : ℝ) ≤ 1 + M) _)
    _ ≤ 600 * (1 + M) ^ explicitLogarithmTheta :=
      mul_le_mul_of_nonneg_right (by norm_num : (551 : ℝ) ≤ 600)
        (Real.rpow_nonneg (by linarith [hM] : (0 : ℝ) ≤ 1 + M) _)

/-- A point in the approved vertical strip lies in the exact radius-65/64
closed disk used for the logarithmic-derivative estimate. -/
theorem reciprocalStrip_point_mem_closedBall {σ t : ℝ}
    (hσlo : (63 / 64 : ℝ) ≤ σ) (hσhi : σ ≤ 3 / 2) :
    (σ : ℂ) + (t : ℂ) * Complex.I ∈
      Metric.closedBall (2 + (t : ℂ) * Complex.I) (65 / 64 : ℝ) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hreal : |σ - 2| ≤ (65 / 64 : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith
  calc
    ‖(σ : ℂ) + (t : ℂ) * Complex.I - (2 + (t : ℂ) * Complex.I)‖ =
        |σ - 2| := by
          rw [show (σ : ℂ) + (t : ℂ) * Complex.I -
              (2 + (t : ℂ) * Complex.I) = ((σ - 2 : ℝ) : ℂ) by push_cast <;> ring,
            Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 65 / 64 := hreal

#print axioms explicitLogarithmConstant_le_reciprocalStripMajorant
#print axioms reciprocalStrip_point_mem_closedBall

end FractionalPrimes.Literature.Analytic

end
