module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

/-!
# Explicit constants for arithmetic grouping

This file records the absolute constants and logarithmic threshold from
blueprint item `lucomb:constants`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity.Combinatorics

noncomputable section

/-- The explicit absolute constant `2^200 * 81^160000`. -/
def decompositionC : ℝ := (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000

/-- The logarithmic exponent in the arithmetic type moment bound. -/
def decompositionB : ℕ := 160100

/-- The explicit arithmetic type moment bound `C * (log X)^b`. -/
def decompositionDType (X : ℝ) : ℝ :=
  decompositionC * (Real.log X) ^ decompositionB

/-- The reciprocal threshold used in the arithmetic type predicates. -/
def decompositionDelta (X : ℝ) : ℝ := (decompositionDType X)⁻¹

/-- The constants of `lucomb:constants` give a threshold strictly between
zero and one for every real scale `X ≥ 3`. -/
theorem decompositionConstants {X : ℝ} (hX : 3 ≤ X) :
    0 < decompositionDelta X ∧ decompositionDelta X < 1 := by
  have hlog3 : 1 < Real.log 3 := by
    linarith [Real.log_three_gt_d9]
  have hlogX : 1 < Real.log X :=
    lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hX)
  have hpow2 : 1 < (2 : ℝ) ^ 200 :=
    one_lt_pow₀ (by norm_num) (by norm_num)
  have hpow81 : 1 < (81 : ℝ) ^ 160000 :=
    one_lt_pow₀ (by norm_num) (by norm_num)
  have hC : 1 < decompositionC := by
    change 1 < (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000
    calc
      1 < (2 : ℝ) ^ 200 := hpow2
      _ = (2 : ℝ) ^ 200 * 1 := by ring
      _ < (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
        mul_lt_mul_of_pos_left hpow81 (by positivity)
  have hCpos : 0 < decompositionC := zero_lt_one.trans hC
  have hlogPow : 1 < (Real.log X) ^ decompositionB := by
    change 1 < (Real.log X) ^ 160100
    exact one_lt_pow₀ hlogX (by norm_num)
  have hD : 1 < decompositionDType X := by
    change 1 < decompositionC * (Real.log X) ^ decompositionB
    calc
      1 < decompositionC := hC
      _ = decompositionC * 1 := by simp
      _ < decompositionC * (Real.log X) ^ decompositionB :=
        mul_lt_mul_of_pos_left hlogPow hCpos
  constructor
  · exact inv_pos.mpr (zero_lt_one.trans hD)
  · exact inv_lt_one_of_one_lt₀ hD

end

end FractionalPrimes.Literature.Uniformity.Combinatorics

#print axioms FractionalPrimes.Literature.Uniformity.Combinatorics.decompositionConstants
