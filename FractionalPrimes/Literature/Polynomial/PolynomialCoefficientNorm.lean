module

public import Mathlib.Analysis.Normed.Group.InfiniteSum

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Weighted coefficient sums for real polynomials

This file supplies the finite coefficient-convolution estimate used in the
large-`M` Type-I₂ degree descent.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

/-- The weighted `ℓ¹` sum of the coefficients of a real polynomial. The
definition is written as a `tsum`; polynomial finite support makes it an
ordinary finite sum. -/
noncomputable def polynomialWeightedCoefficientSum
    (L : ℝ) (P : Polynomial ℝ) : ℝ :=
  ∑' n : ℕ, L ^ n * |P.coeff n|

theorem polynomialWeightedCoefficientSum_summable
    (L : ℝ) (P : Polynomial ℝ) :
    Summable fun n : ℕ => L ^ n * |P.coeff n| := by
  apply summable_of_ne_finset_zero (s := P.support)
  intro n hn
  have hcoeff : P.coeff n = 0 := by
    by_contra hne
    exact hn (Polynomial.mem_support_iff.mpr hne)
  simp [hcoeff]

theorem polynomialWeightedCoefficientSum_nonneg
    (L : ℝ) (hL : 0 ≤ L) (P : Polynomial ℝ) :
    0 ≤ polynomialWeightedCoefficientSum L P := by
  exact tsum_nonneg fun n => mul_nonneg (pow_nonneg hL n) (abs_nonneg _)

@[simp] theorem polynomialWeightedCoefficientSum_one
    (L : ℝ) :
    polynomialWeightedCoefficientSum L (1 : Polynomial ℝ) = 1 := by
  rw [polynomialWeightedCoefficientSum, tsum_eq_single 0]
  · simp
  · intro n hn
    rw [Polynomial.coeff_one]
    simp [hn]

/-- Weighted coefficient `ℓ¹` is submultiplicative. -/
theorem polynomialWeightedCoefficientSum_mul_le
    (L : ℝ) (hL : 0 ≤ L) (P Q : Polynomial ℝ) :
    polynomialWeightedCoefficientSum L (P * Q) ≤
      polynomialWeightedCoefficientSum L P *
        polynomialWeightedCoefficientSum L Q := by
  let f : ℕ → ℝ := fun n => L ^ n * |P.coeff n|
  let g : ℕ → ℝ := fun n => L ^ n * |Q.coeff n|
  have hf : Summable f := by
    simpa [f] using polynomialWeightedCoefficientSum_summable L P
  have hg : Summable g := by
    simpa [g] using polynomialWeightedCoefficientSum_summable L Q
  have hf0 (n : ℕ) : 0 ≤ f n := by
    exact mul_nonneg (pow_nonneg hL n) (abs_nonneg _)
  have hg0 (n : ℕ) : 0 ≤ g n := by
    exact mul_nonneg (pow_nonneg hL n) (abs_nonneg _)
  have hfnorm : Summable fun n => ‖f n‖ := by
    apply hf.congr
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 n)]
  have hgnorm : Summable fun n => ‖g n‖ := by
    apply hg.congr
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 n)]
  have hright : Summable fun n : ℕ =>
      ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2 :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hfnorm hgnorm).of_norm
  have hleft : Summable fun n : ℕ =>
      L ^ n * |(P * Q).coeff n| :=
    polynomialWeightedCoefficientSum_summable L (P * Q)
  have hpoint (n : ℕ) :
      L ^ n * |(P * Q).coeff n| ≤
        ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2 := by
    rw [Polynomial.coeff_mul]
    calc
      L ^ n * |∑ ij ∈ Finset.antidiagonal n,
          P.coeff ij.1 * Q.coeff ij.2| ≤
          L ^ n * ∑ ij ∈ Finset.antidiagonal n,
            |P.coeff ij.1 * Q.coeff ij.2| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (pow_nonneg hL n)
      _ = ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ij hij
        have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
        rw [abs_mul, ← hadd, pow_add]
        simp only [f, g]
        ring
  have htsum := hleft.tsum_le_tsum hpoint hright
  have hcauchy :=
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfnorm hgnorm
  simpa [polynomialWeightedCoefficientSum, f, g] using htsum.trans_eq hcauchy.symm

/-- The weighted coefficient sum of a power is bounded by the corresponding
power of the weighted coefficient sum. -/
theorem polynomialWeightedCoefficientSum_pow_le
    (L : ℝ) (hL : 0 ≤ L) (P : Polynomial ℝ) :
    ∀ j : ℕ,
      polynomialWeightedCoefficientSum L (P ^ j) ≤
        polynomialWeightedCoefficientSum L P ^ j
  | 0 => by simp
  | j + 1 => by
      rw [pow_succ, pow_succ]
      calc
        polynomialWeightedCoefficientSum L (P ^ j * P) ≤
            polynomialWeightedCoefficientSum L (P ^ j) *
              polynomialWeightedCoefficientSum L P :=
          polynomialWeightedCoefficientSum_mul_le L hL _ _
        _ ≤ polynomialWeightedCoefficientSum L P ^ j *
              polynomialWeightedCoefficientSum L P :=
          mul_le_mul_of_nonneg_right
            (polynomialWeightedCoefficientSum_pow_le L hL P j)
            (polynomialWeightedCoefficientSum_nonneg L hL P)

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.polynomialWeightedCoefficientSum_mul_le
#print axioms FractionalPrimes.Literature.Polynomial.polynomialWeightedCoefficientSum_pow_le
