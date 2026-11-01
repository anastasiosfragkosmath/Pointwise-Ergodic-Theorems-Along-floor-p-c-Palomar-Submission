module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Exact optimization of the interpolation split scale

This records the algebraic substitution prescribed in blueprint
`lem:interpolation`; it does not alter the theorem's constant or hypotheses.
-/

namespace FractionalPrimes

theorem interpolation_low_scale_rpow_identity
    {p B epsilon : ℝ} (hB : 0 < B) (he : 0 < epsilon) :
    epsilon ^ 2 * (B / epsilon ^ 2) ^ (2 - p) =
      B ^ (2 - p) * epsilon ^ (2 * p - 2) := by
  have he2 : 0 < epsilon ^ 2 := sq_pos_of_pos he
  have hden : (epsilon ^ 2 : ℝ) ^ (2 - p) =
      epsilon ^ (2 * (2 - p)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul he.le (2 : ℝ) (2 - p)]
  have hscale : (B / epsilon ^ 2) ^ (2 - p) =
      B ^ (2 - p) * epsilon ^ (2 * p - 4) := by
    rw [Real.div_rpow hB.le he2.le, hden,
      show 2 * (2 - p) = -(2 * p - 4) by ring,
      Real.rpow_neg he.le]
    simp [div_eq_mul_inv]
  rw [hscale]
  have hcombine : epsilon ^ 2 * epsilon ^ (2 * p - 4) =
      epsilon ^ (2 * p - 2) := by
    rw [← Real.rpow_two, ← Real.rpow_add he (2 : ℝ) (2 * p - 4)]
    congr 1
    ring
  calc
    epsilon ^ 2 * (B ^ (2 - p) * epsilon ^ (2 * p - 4)) =
        B ^ (2 - p) * (epsilon ^ 2 * epsilon ^ (2 * p - 4)) := by ring
    _ = B ^ (2 - p) * epsilon ^ (2 * p - 2) := by rw [hcombine]

theorem interpolation_high_scale_rpow_identity
    {p B epsilon : ℝ} (hB : 0 < B) (he : 0 < epsilon) :
    B * (B / epsilon ^ 2) ^ (1 - p) =
      B ^ (2 - p) * epsilon ^ (2 * p - 2) := by
  have he2 : 0 < epsilon ^ 2 := sq_pos_of_pos he
  have hden : (epsilon ^ 2 : ℝ) ^ (1 - p) =
      epsilon ^ (2 * (1 - p)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul he.le (2 : ℝ) (1 - p)]
  have hscale : (B / epsilon ^ 2) ^ (1 - p) =
      B ^ (1 - p) * epsilon ^ (2 * p - 2) := by
    rw [Real.div_rpow hB.le he2.le, hden,
      show 2 * (1 - p) = -(2 * p - 2) by ring,
      Real.rpow_neg he.le]
    simp [div_eq_mul_inv]
  have hBcombine : B * B ^ (1 - p) = B ^ (2 - p) := by
    calc
      B * B ^ (1 - p) = B ^ (1 : ℝ) * B ^ (1 - p) := by rw [Real.rpow_one]
      _ = B ^ (1 + (1 - p)) := by rw [Real.rpow_add hB 1 (1 - p)]
      _ = B ^ (2 - p) := by congr 1; ring
  rw [hscale]
  calc
    B * (B ^ (1 - p) * epsilon ^ (2 * p - 2)) =
        (B * B ^ (1 - p)) * epsilon ^ (2 * p - 2) := by ring
    _ = B ^ (2 - p) * epsilon ^ (2 * p - 2) := by rw [hBcombine]

/-- The chosen split scale `a = B / ε²` produces the exact coefficient in
the approved `1 < p < 2` interpolation estimate. -/
theorem interpolation_optimal_scale_coefficient
    {p B epsilon : ℝ} (hB : 0 < B) (he : 0 < epsilon) :
    (4 * p / (2 - p)) * epsilon ^ 2 * (B / epsilon ^ 2) ^ (2 - p) +
        (2 * p / (p - 1)) * B * (B / epsilon ^ 2) ^ (1 - p) =
      (4 * p / (2 - p) + 2 * p / (p - 1)) *
        B ^ (2 - p) * epsilon ^ (2 * p - 2) := by
  calc
    _ = (4 * p / (2 - p)) *
          (epsilon ^ 2 * (B / epsilon ^ 2) ^ (2 - p)) +
        (2 * p / (p - 1)) * (B * (B / epsilon ^ 2) ^ (1 - p)) := by ring
    _ = (4 * p / (2 - p)) *
          (B ^ (2 - p) * epsilon ^ (2 * p - 2)) +
        (2 * p / (p - 1)) *
          (B ^ (2 - p) * epsilon ^ (2 * p - 2)) := by
          rw [interpolation_low_scale_rpow_identity hB he,
            interpolation_high_scale_rpow_identity hB he]
    _ = _ := by ring

/-- Taking the p-th root of the optimized moment coefficient gives the
paper's separate B and epsilon powers in the `1<p<2` range. -/
theorem interpolation_optimal_coefficient_rpow
    {p B epsilon : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hB : 0 < B) (he : 0 < epsilon) :
    ((4 * p / (2 - p) + 2 * p / (p - 1)) *
        B ^ (2 - p) * epsilon ^ (2 * p - 2)) ^ (1 / p) =
      (4 * p / (2 - p) + 2 * p / (p - 1)) ^ (1 / p) *
        B ^ (2 / p - 1) * epsilon ^ (2 - 2 / p) := by
  let C : ℝ := 4 * p / (2 - p) + 2 * p / (p - 1)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hBpow : 0 < B ^ (2 - p) := Real.rpow_pos_of_pos hB _
  have hepow : 0 < epsilon ^ (2 * p - 2) := Real.rpow_pos_of_pos he _
  have hBroot : (B ^ (2 - p)) ^ (1 / p) = B ^ (2 / p - 1) := by
    rw [← Real.rpow_mul hB.le]
    congr 1
    field_simp [ne_of_gt hp1]
  have heroot : (epsilon ^ (2 * p - 2)) ^ (1 / p) =
      epsilon ^ (2 - 2 / p) := by
    rw [← Real.rpow_mul he.le]
    congr 1
    field_simp [ne_of_gt hp1]
  calc
    (C * B ^ (2 - p) * epsilon ^ (2 * p - 2)) ^ (1 / p) =
        (C * B ^ (2 - p)) ^ (1 / p) *
          (epsilon ^ (2 * p - 2)) ^ (1 / p) := by
            rw [show C * B ^ (2 - p) * epsilon ^ (2 * p - 2) =
              (C * B ^ (2 - p)) * epsilon ^ (2 * p - 2) by ring,
              Real.mul_rpow (le_of_lt (mul_pos hC hBpow)) (le_of_lt hepow)]
    _ = C ^ (1 / p) * (B ^ (2 - p)) ^ (1 / p) *
          (epsilon ^ (2 * p - 2)) ^ (1 / p) := by
            rw [Real.mul_rpow (le_of_lt hC) hBpow.le]
    _ = C ^ (1 / p) * B ^ (2 / p - 1) * epsilon ^ (2 - 2 / p) := by
          rw [hBroot, heroot]
    _ = _ := by simpa [C]

end FractionalPrimes
