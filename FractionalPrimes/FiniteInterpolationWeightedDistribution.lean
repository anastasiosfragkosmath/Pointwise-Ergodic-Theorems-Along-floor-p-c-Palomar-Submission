module

public import FractionalPrimes.FiniteInterpolationDistribution
public import FractionalPrimes.InterpolationWeightedLayercake

@[expose] public section

/-!
# ENNReal weighted distribution bridge for elementary interpolation

This module feeds the checked finite weighted layer-cake theorem with the
all-output strict-superlevel estimate obtained from the finite low/high
convolution bound. The cutoff conventions remain `‖f k‖ ≤ a*t` for the low
part and `a*t < ‖f k‖` for the high part, with constants 4 and 2.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem finite_low_moment_ennreal_eq_ofReal
    (s : Finset ℤ) (f : ℤ → ℂ) (c : ℝ) :
    (∑ k ∈ s, if ‖f k‖ ≤ c then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) =
      ENNReal.ofReal (∑ k ∈ s, if ‖f k‖ ≤ c then ‖f k‖ ^ 2 else 0) := by
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases h : ‖f k‖ ≤ c <;> simp [h]
  · intro k hk
    by_cases h : ‖f k‖ ≤ c <;> simp [h]

private theorem finite_high_moment_ennreal_eq_ofReal
    (s : Finset ℤ) (f : ℤ → ℂ) (c : ℝ) :
    (∑ k ∈ s, if c < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) =
      ENNReal.ofReal (∑ k ∈ s, if c < ‖f k‖ then ‖f k‖ else 0) := by
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases h : c < ‖f k‖ <;> simp [h]
  · intro k hk
    by_cases h : c < ‖f k‖ <;> simp [h]

private theorem finite_low_moment_eq_split
    (s : Finset ℤ) (f : ℤ → ℂ) (c : ℝ) :
    (∑ k ∈ s, if ‖f k‖ ≤ c then ‖f k‖ ^ 2 else 0) =
      ∑ k ∈ s, ‖finiteLowPart s c f k‖ ^ 2 := by
  rw [sum_norm_sq_finiteLowPart, Finset.sum_filter]

private theorem finite_high_moment_eq_split
    (s : Finset ℤ) (f : ℤ → ℂ) (c : ℝ) :
    (∑ k ∈ s, if c < ‖f k‖ then ‖f k‖ else 0) =
      ∑ k ∈ s, ‖finiteHighPart s c f k‖ := by
  rw [sum_norm_finiteHighPart, Finset.sum_filter]

private theorem finite_rpow_div_two
    {t p : ℝ} (ht : 0 < t) : t ^ (p - 1) / t ^ 2 = t ^ (p - 3) := by
  rw [← Real.rpow_natCast t 2, ← Real.rpow_sub ht]
  congr 1
  ring

private theorem finite_rpow_div_one
    {t p : ℝ} (ht : 0 < t) : t ^ (p - 1) / t = t ^ (p - 2) := by
  calc
    t ^ (p - 1) / t = t ^ (p - 1) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = t ^ ((p - 1) - 1) := (Real.rpow_sub ht (p - 1) 1).symm
    _ = t ^ (p - 2) := by congr 1; ring

/-- The exact finite-output ENNReal distribution hypothesis needed by
`finite_weighted_distribution_integral_le`, deduced from the all-of-ℤ
strict-superlevel estimate for the concrete finite-support convolution.

The low input condition is `‖f k‖ ≤ a*t`, the high condition is the strict
complement `a*t < ‖f k‖`, and the endpoint constants are exactly 4 and 2.
-/
theorem finiteIntegerKernelConvolution_weighted_distribution
    {p a B epsilon : ℝ}
    (K : IntegerL1Kernel) (s out : Finset ℤ) (f : ℤ → ℂ)
    (hB : ∑' m : ℤ, ‖K.coeff m‖ ≤ B)
    (hBpos : 0 < B) (hepsilon : 0 < epsilon)
    (hL2 : ∀ g : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm (integerKernelConvolution K (g : ℤ → ℂ)) 2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (g : ℤ → ℂ) 2 Measure.count) :
    ∀ t : ℝ, 0 < t →
      ((out.filter fun k => t < ‖integerKernelConvolution K
          (finiteSupportCountLpTwo s f : ℤ → ℂ) k‖).card : ℝ≥0∞) *
          ENNReal.ofReal (t ^ (p - 1)) ≤
        4 * ENNReal.ofReal (epsilon ^ 2) *
            (∑ k ∈ s, if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) *
              ENNReal.ofReal t ^ (p - 3) +
          2 * ENNReal.ofReal B *
            (∑ k ∈ s, if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) *
              ENNReal.ofReal t ^ (p - 2) := by
  intro t ht
  have hdist := finiteIntegerKernelConvolution_low_high_distribution
    (K := K) (s := s) (f := f) (B := B) (epsilon := epsilon)
    (a := a) (lambda := t) hB hBpos hepsilon ht hL2
  obtain ⟨hE, hEcard⟩ := hdist
  let level : Finset ℤ := out.filter fun k =>
    t < ‖integerKernelConvolution K (finiteSupportCountLpTwo s f : ℤ → ℂ) k‖
  have hlevelSub : level ⊆ hE.toFinset := by
    intro k hk
    have hmem := (Finset.mem_filter.mp hk).2
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hmem
  have hlevelCardNat : level.card ≤ hE.toFinset.card := Finset.card_le_card hlevelSub
  have hlevelCardReal : (level.card : ℝ) ≤ (hE.toFinset.card : ℝ) := by
    exact_mod_cast hlevelCardNat

  let lowMoment : ℝ := ∑ k ∈ s, if ‖f k‖ ≤ a * t then ‖f k‖ ^ 2 else 0
  let highMoment : ℝ := ∑ k ∈ s, if a * t < ‖f k‖ then ‖f k‖ else 0
  have hlowNonneg : 0 ≤ lowMoment := by
    dsimp [lowMoment]
    apply Finset.sum_nonneg
    intro k hk
    by_cases h : ‖f k‖ ≤ a * t <;> simp [h]
  have hhighNonneg : 0 ≤ highMoment := by
    dsimp [highMoment]
    apply Finset.sum_nonneg
    intro k hk
    by_cases h : a * t < ‖f k‖ <;> simp [h]

  have hrealBound : (level.card : ℝ) ≤
      4 * epsilon ^ 2 / t ^ 2 * lowMoment +
        2 * B / t * highMoment := by
    calc
      (level.card : ℝ) ≤ (hE.toFinset.card : ℝ) := hlevelCardReal
      _ ≤ 4 * epsilon ^ 2 / t ^ 2 *
            (∑ k ∈ s, ‖finiteLowPart s (a * t) f k‖ ^ 2) +
          2 * B / t *
            (∑ k ∈ s, ‖finiteHighPart s (a * t) f k‖) := hEcard
      _ = 4 * epsilon ^ 2 / t ^ 2 * lowMoment + 2 * B / t * highMoment := by
        simp [lowMoment, highMoment, finite_low_moment_eq_split,
          finite_high_moment_eq_split]

  have hweightedReal :
      (level.card : ℝ) * t ^ (p - 1) ≤
        4 * epsilon ^ 2 * lowMoment * t ^ (p - 3) +
          2 * B * highMoment * t ^ (p - 2) := by
    have hmul := mul_le_mul_of_nonneg_right hrealBound
      (Real.rpow_nonneg ht.le (p - 1))
    calc
      (level.card : ℝ) * t ^ (p - 1) ≤
          (4 * epsilon ^ 2 / t ^ 2 * lowMoment +
            2 * B / t * highMoment) * t ^ (p - 1) := hmul
      _ = 4 * epsilon ^ 2 * lowMoment * t ^ (p - 3) +
            2 * B * highMoment * t ^ (p - 2) := by
        rw [add_mul]
        rw [show (4 * epsilon ^ 2 / t ^ 2 * lowMoment) * t ^ (p - 1) =
            4 * epsilon ^ 2 * lowMoment * (t ^ (p - 1) / t ^ 2) by ring]
        rw [show (2 * B / t * highMoment) * t ^ (p - 1) =
            2 * B * highMoment * (t ^ (p - 1) / t) by ring]
        rw [finite_rpow_div_two ht, finite_rpow_div_one ht]

  have hlowENN :
      (∑ k ∈ s, if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) =
        ENNReal.ofReal lowMoment := by
    simpa [lowMoment] using finite_low_moment_ennreal_eq_ofReal s f (a * t)
  have hhighENN :
      (∑ k ∈ s, if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) =
        ENNReal.ofReal highMoment := by
    simpa [highMoment] using finite_high_moment_ennreal_eq_ofReal s f (a * t)

  have hleft :
      (level.card : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 1)) =
        ENNReal.ofReal ((level.card : ℝ) * t ^ (p - 1)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

  have hlowRhs :
      4 * ENNReal.ofReal (epsilon ^ 2) *
          (∑ k ∈ s, if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) *
            ENNReal.ofReal t ^ (p - 3) =
        ENNReal.ofReal (4 * epsilon ^ 2 * lowMoment * t ^ (p - 3)) := by
    calc
      _ = ENNReal.ofReal (4 * epsilon ^ 2) * ENNReal.ofReal lowMoment *
            ENNReal.ofReal (t ^ (p - 3)) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), hlowENN,
          ENNReal.ofReal_rpow_of_pos ht]
      _ = ENNReal.ofReal (4 * epsilon ^ 2 * lowMoment * t ^ (p - 3)) := by
        calc
          _ = ENNReal.ofReal (4 * epsilon ^ 2 * lowMoment) *
                ENNReal.ofReal (t ^ (p - 3)) := by
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * epsilon ^ 2)]
          _ = ENNReal.ofReal (4 * epsilon ^ 2 * lowMoment * t ^ (p - 3)) := by
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * epsilon ^ 2 * lowMoment)]

  have hhighRhs :
      2 * ENNReal.ofReal B *
          (∑ k ∈ s, if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) *
            ENNReal.ofReal t ^ (p - 2) =
        ENNReal.ofReal (2 * B * highMoment * t ^ (p - 2)) := by
    calc
      _ = ENNReal.ofReal (2 * B) * ENNReal.ofReal highMoment *
            ENNReal.ofReal (t ^ (p - 2)) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), hhighENN,
          ENNReal.ofReal_rpow_of_pos ht]
      _ = ENNReal.ofReal (2 * B * highMoment * t ^ (p - 2)) := by
        calc
          _ = ENNReal.ofReal (2 * B * highMoment) *
                ENNReal.ofReal (t ^ (p - 2)) := by
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * B)]
          _ = ENNReal.ofReal (2 * B * highMoment * t ^ (p - 2)) := by
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * B * highMoment)]

  have hlowTermNonneg : 0 ≤ 4 * epsilon ^ 2 * lowMoment * t ^ (p - 3) := by
    have hcoeff : 0 ≤ 4 * epsilon ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg hcoeff hlowNonneg)
      (Real.rpow_nonneg ht.le (p - 3))
  have hhighTermNonneg : 0 ≤ 2 * B * highMoment * t ^ (p - 2) := by
    have hcoeff : 0 ≤ 2 * B := by positivity
    exact mul_nonneg (mul_nonneg hcoeff hhighNonneg)
      (Real.rpow_nonneg ht.le (p - 2))

  have hsumENN :
      ENNReal.ofReal (4 * epsilon ^ 2 * lowMoment * t ^ (p - 3)) +
        ENNReal.ofReal (2 * B * highMoment * t ^ (p - 2)) =
          ENNReal.ofReal (4 * epsilon ^ 2 * lowMoment * t ^ (p - 3) +
            2 * B * highMoment * t ^ (p - 2)) := by
    rw [← ENNReal.ofReal_add hlowTermNonneg hhighTermNonneg]

  have hboundENN :
      ENNReal.ofReal ((level.card : ℝ) * t ^ (p - 1)) ≤
        ENNReal.ofReal (4 * epsilon ^ 2 * lowMoment * t ^ (p - 3) +
          2 * B * highMoment * t ^ (p - 2)) :=
    (ENNReal.ofReal_le_ofReal_iff (add_nonneg hlowTermNonneg hhighTermNonneg)).2 hweightedReal

  have hgoal := hboundENN
  rw [← hleft, ← hsumENN] at hgoal
  rw [← hlowRhs, ← hhighRhs] at hgoal
  simpa [level] using hgoal

end

end FractionalPrimes
