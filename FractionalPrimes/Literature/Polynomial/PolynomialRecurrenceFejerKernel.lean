module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylInverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- The Fejér kernel is at least `K/4` when its argument is within `ε` of
zero and `K ε ≤ 17/64`. This is the pointwise analytic estimate used in the
finite Fejér detection argument. -/
theorem polynomialRecurrence_fejerKernel_lower
    (K : ℕ) (hK : 1 ≤ K) {t ε : ℝ}
    (ht : |t| ≤ ε)
    (hKε : (K : ℝ) * ε ≤ 17 / 64) :
    (K : ℝ) / 4 ≤
      ‖∑ j ∈ Finset.range K, unitFrequencyPhase ((j : ℝ) * t)‖ ^ 2 /
        (K : ℝ) := by
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hKabs : |(K : ℝ)| = (K : ℝ) := abs_of_nonneg (Nat.cast_nonneg K)
  have htK : |(K : ℝ) * t| ≤ 1 / 2 := by
    calc
      |(K : ℝ) * t| = (K : ℝ) * |t| := by rw [abs_mul, hKabs]
      _ ≤ (K : ℝ) * ε := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg K)
      _ ≤ 17 / 64 := hKε
      _ ≤ 1 / 2 := by norm_num
  have hsmall : |t| ≤ 1 / 2 := by
    have hKt : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hsmall' : |t| ≤ (K : ℝ) * |t| := by
      nlinarith [abs_nonneg t]
    have hKtε : (K : ℝ) * |t| ≤ 17 / 64 := by
      calc
        (K : ℝ) * |t| ≤ (K : ℝ) * ε :=
          mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg K)
        _ ≤ 17 / 64 := hKε
    exact (hsmall'.trans (hKtε.trans (by norm_num)))
  let z : ℂ := unitFrequencyPhase t
  let S : ℂ := ∑ j ∈ Finset.range K, unitFrequencyPhase ((j : ℝ) * t)
  have hsum : S = ∑ j ∈ Finset.range K, z ^ j := by
    dsimp [S]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [z]
    rw [unitFrequencyPhase_nat_mul]
  have hS : (2 * (K : ℝ) / Real.pi) ≤ ‖S‖ := by
    by_cases ht0 : t = 0
    · subst t
      have hSval : S = (K : ℂ) := by
        dsimp [S]
        simp [unitFrequencyPhase]
      rw [hSval, Complex.norm_natCast]
      have hpi : 2 ≤ Real.pi := Real.two_le_pi
      have hKnonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
      apply (div_le_iff₀ Real.pi_pos).2
      nlinarith [hpi, hKnonneg]
    · have hdist : realDistanceToIntegers t = |t| :=
        realDistanceToIntegers_eq_abs_of_abs_le_half hsmall
      have hdistpos : 0 < realDistanceToIntegers t := by
        rw [hdist]
        exact abs_pos.mpr ht0
      have hchordt :=
        four_mul_realDistanceToIntegers_le_norm_one_sub_unitFrequencyPhase
          hsmall
      have hzneq : z ≠ 1 := by
        intro hz
        have hzero : ‖1 - z‖ = 0 := by simp [hz]
        have hflip : ‖1 - z‖ = ‖z - 1‖ := by
          rw [show (1 : ℂ) - z = -(z - 1) by ring, norm_neg]
        rw [hdist] at hchordt
        rw [hflip, hz] at hchordt
        simp at hchordt
        have : 0 < 4 * |t| := mul_pos (by norm_num) (abs_pos.mpr ht0)
        linarith
      have hdistK : realDistanceToIntegers ((K : ℝ) * t) =
          |(K : ℝ) * t| :=
        realDistanceToIntegers_eq_abs_of_abs_le_half htK
      have hphaseK : z ^ K =
          unitFrequencyPhase ((K : ℝ) * t) := by
        dsimp [z]
        rw [unitFrequencyPhase_nat_mul]
      have hnum : 4 * (K : ℝ) * |t| ≤ ‖z ^ K - 1‖ := by
        have hchordK :=
          four_mul_realDistanceToIntegers_le_norm_one_sub_unitFrequencyPhase
            htK
        rw [hdistK] at hchordK
        have hflip :
            ‖1 - unitFrequencyPhase ((K : ℝ) * t)‖ =
              ‖unitFrequencyPhase ((K : ℝ) * t) - 1‖ := by
          rw [show (1 : ℂ) - unitFrequencyPhase ((K : ℝ) * t) =
            -(unitFrequencyPhase ((K : ℝ) * t) - 1) by ring, norm_neg]
        calc
          4 * (K : ℝ) * |t| = 4 * |(K : ℝ) * t| := by
            rw [abs_mul, hKabs]
            ring
          _ ≤ ‖1 - unitFrequencyPhase ((K : ℝ) * t)‖ := hchordK
          _ = ‖z ^ K - 1‖ := by rw [hflip, ← hphaseK]
      have hdenUpper : ‖z - 1‖ ≤ 2 * Real.pi * |t| := by
        have h := norm_one_sub_unitFrequencyPhase_neg_le (-t)
        have hflip : ‖1 - unitFrequencyPhase t‖ =
            ‖unitFrequencyPhase t - 1‖ := by
          rw [show (1 : ℂ) - unitFrequencyPhase t =
            -(unitFrequencyPhase t - 1) by ring, norm_neg]
        simpa [z, abs_neg, hflip] using h
      have hdenPos : 0 < ‖z - 1‖ := by
        have hpos : 0 < 4 * realDistanceToIntegers t :=
          mul_pos (by norm_num) hdistpos
        have hle := hchordt
        have hflip : ‖1 - z‖ = ‖z - 1‖ := by
          rw [show (1 : ℂ) - z = -(z - 1) by ring, norm_neg]
        rw [hflip] at hle
        exact lt_of_lt_of_le hpos hle
      have hgeom : ‖S‖ = ‖z ^ K - 1‖ / ‖z - 1‖ := by
        rw [hsum, geom_sum_eq hzneq K, norm_div]
      rw [hgeom]
      apply (le_div_iff₀ hdenPos).2
      calc
        (2 * (K : ℝ) / Real.pi) * ‖z - 1‖ ≤
            (2 * (K : ℝ) / Real.pi) * (2 * Real.pi * |t|) :=
          mul_le_mul_of_nonneg_left hdenUpper (by positivity)
        _ = 4 * (K : ℝ) * |t| := by
          field_simp [ne_of_gt Real.pi_pos]
          ring
        _ ≤ ‖z ^ K - 1‖ := hnum
  have hSnonneg : 0 ≤ ‖S‖ := norm_nonneg _
  have hlowNonneg : 0 ≤ 2 * (K : ℝ) / Real.pi := by positivity
  have hSsq : (2 * (K : ℝ) / Real.pi) ^ 2 ≤ ‖S‖ ^ 2 := by
    nlinarith [mul_self_le_mul_self hlowNonneg hS]
  have hkernel : 4 * (K : ℝ) / Real.pi ^ 2 ≤ ‖S‖ ^ 2 / (K : ℝ) := by
    calc
      4 * (K : ℝ) / Real.pi ^ 2 =
          (2 * (K : ℝ) / Real.pi) ^ 2 / (K : ℝ) := by
            field_simp [ne_of_gt hKpos, ne_of_gt Real.pi_pos]
            ring
      _ ≤ ‖S‖ ^ 2 / (K : ℝ) :=
        div_le_div_of_nonneg_right hSsq (le_of_lt hKpos)
  have hπsq : Real.pi ^ 2 ≤ 16 := by
    calc
      Real.pi ^ 2 = Real.pi * Real.pi := by ring
      _ ≤ Real.pi * 4 :=
        mul_le_mul_of_nonneg_left (le_of_lt Real.pi_lt_four) Real.pi_pos.le
      _ ≤ 4 * 4 :=
        mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four)
          (by norm_num : (0 : ℝ) ≤ 4)
      _ = 16 := by norm_num
  have hcoef : (K : ℝ) / 4 ≤ 4 * (K : ℝ) / Real.pi ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4)
      (sq_pos_of_pos Real.pi_pos)]
    nlinarith [hπsq, (Nat.cast_nonneg K : (0 : ℝ) ≤ (K : ℝ))]
  have hSrewrite : S =
      ∑ j ∈ Finset.range K, unitFrequencyPhase ((j : ℝ) * t) := rfl
  rw [← hSrewrite]
  exact hcoef.trans hkernel

end FractionalPrimes.Literature.Polynomial
