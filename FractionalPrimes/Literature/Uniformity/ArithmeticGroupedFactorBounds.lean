module

public import FractionalPrimes.Literature.Uniformity.ArithmeticGroupingConstants
public import FractionalPrimes.Literature.Uniformity.ArithmeticDyadicComponents
public import FractionalPrimes.Literature.Uniformity.ArithmeticTypes
public import FractionalPrimes.Literature.Uniformity.DivisorMomentBound
public import FractionalPrimes.Literature.Uniformity.TypeMonotonicity
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic


/-!
# Moments and variation of grouped dyadic arithmetic factors

This file formalizes blueprint item `lucomb:group-bounds`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity.Combinatorics

open FractionalPrimes.Literature.Uniformity
open ArithmeticFunction

noncomputable section

/-- A tagged real dyadic arithmetic factor, viewed as a complex-valued
arithmetic function on the positive integers. -/
def dyadicFactorComplexFunction {X : ℝ} (z : ℝ)
    (f : DyadicArithmeticFactor X) : ArithmeticFunction ℂ :=
  ⟨fun n => (dyadicFactorFunction z f n : ℂ), by simp⟩

/-- The ordered complex Dirichlet convolution of a selected list of tagged
dyadic factors. -/
def dyadicFactorComplexProduct {X : ℝ} (z : ℝ)
    (fs : List (DyadicArithmeticFactor X)) : ArithmeticFunction ℂ :=
  (fs.map (dyadicFactorComplexFunction z)).prod

/-- A selected convolution group, with an optional component coefficient
attached to this designated group. -/
def groupedDyadicFactor {X : ℝ} (z : ℝ)
    (c : ℂ) (fs : List (DyadicArithmeticFactor X)) :
    ComplexPositiveIntegerFunction :=
  fun n => c * ((dyadicConvolutionFactors z fs n.1 : ℝ) : ℂ)

theorem log_eightX_gt_one {X : ℝ} (hX : 3 ≤ X) :
    1 < Real.log (8 * X) := by
  have hlog3 : 1 < Real.log 3 := by
    linarith [Real.log_three_gt_d9]
  have h3le : 3 ≤ 8 * X := by nlinarith
  exact hlog3.trans_le (Real.log_le_log (by norm_num) h3le)

theorem dyadicUpperNat_le_eightX {X : ℝ} (hX : 3 ≤ X)
    (j : DyadicIndex X) :
    (dyadicUpperNat j.val.val : ℝ) ≤ 8 * X := by
  have hscale : dyadicScale j.val.val < 4 * X := j.property
  by_cases hj : j.val.val = 0
  · simp [dyadicUpperNat, hj]
    nlinarith [hX]
  · have hpred : Nat.succ j.val.val.pred = j.val.val :=
      Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hj)
    have hupper :
        (dyadicUpperNat j.val.val : ℝ) = 2 * dyadicScale j.val.val := by
      have hnat : dyadicUpperNat j.val.val =
          2 * dyadicUpperNat j.val.val.pred := by
        change 2 ^ j.val.val = 2 * 2 ^ j.val.val.pred
        calc
          2 ^ j.val.val = 2 ^ Nat.succ j.val.val.pred :=
            congrArg (fun m : ℕ => (2 : ℕ) ^ m) hpred.symm
          _ = 2 ^ j.val.val.pred * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ j.val.val.pred := Nat.mul_comm _ _
      rw [dyadicUpperNat, dyadicScale, if_neg hj]
      norm_cast at hnat ⊢
    rw [hupper]
    nlinarith

private theorem dyadicFactorComplex_ne_zero_support {X : ℝ} (hX : 3 ≤ X)
    (z : ℝ) (f : DyadicArithmeticFactor X) (n : PositiveInteger)
    (hn : dyadicFactorComplexFunction z f n.1 ≠ 0) :
    (n.1 : ℝ) ≤ 8 * X := by
  cases f with
  | one j =>
      have hinterval : inDyadicInterval j.val.val n.1 := by
        by_contra hnot
        apply hn
        simp [dyadicFactorComplexFunction, dyadicFactorFunction,
          dyadicOneFactor_apply, hnot]
      have hnat : n.1 ≤ dyadicUpperNat j.val.val := hinterval.2
      have hcast : (n.1 : ℝ) ≤ dyadicUpperNat j.val.val := by exact_mod_cast hnat
      exact hcast.trans (dyadicUpperNat_le_eightX hX j)
  | logarithm j =>
      have hinterval : inDyadicInterval j.val.val n.1 := by
        by_contra hnot
        apply hn
        simp [dyadicFactorComplexFunction, dyadicFactorFunction,
          dyadicLogFactor_apply, hnot]
      have hnat : n.1 ≤ dyadicUpperNat j.val.val := hinterval.2
      have hcast : (n.1 : ℝ) ≤ dyadicUpperNat j.val.val := by exact_mod_cast hnat
      exact hcast.trans (dyadicUpperNat_le_eightX hX j)
  | mobius j =>
      have hinterval : inDyadicInterval j.val.val n.1 := by
        by_contra hnot
        apply hn
        simp [dyadicFactorComplexFunction, dyadicFactorFunction,
          dyadicMobiusFactor_apply, hnot]
      have hnat : n.1 ≤ dyadicUpperNat j.val.val := hinterval.2
      have hcast : (n.1 : ℝ) ≤ dyadicUpperNat j.val.val := by exact_mod_cast hnat
      exact hcast.trans (dyadicUpperNat_le_eightX hX j)

private theorem dyadicFactorComplex_norm_le {X : ℝ} (hX : 3 ≤ X)
    (z : ℝ) (f : DyadicArithmeticFactor X) (n : PositiveInteger) :
    ‖dyadicFactorComplexFunction z f n.1‖ ≤ Real.log (8 * X) := by
  have hL : 1 < Real.log (8 * X) := log_eightX_gt_one hX
  cases f with
  | one j =>
      by_cases hI : inDyadicInterval j.val.val n.1
      · simp [dyadicFactorComplexFunction, dyadicFactorFunction,
          dyadicOneFactor_apply, hI]
        linarith
      · simp [dyadicFactorComplexFunction, dyadicFactorFunction,
          dyadicOneFactor_apply, hI]
        exact le_trans (by norm_num) hL.le
  | logarithm j =>
      by_cases hI : inDyadicInterval j.val.val n.1
      · have hnat : n.1 ≤ dyadicUpperNat j.val.val := hI.2
        have hcast : (n.1 : ℝ) ≤ dyadicUpperNat j.val.val := by exact_mod_cast hnat
        have hsupport : (n.1 : ℝ) ≤ 8 * X :=
          hcast.trans (dyadicUpperNat_le_eightX hX j)
        have hnpos : (0 : ℝ) < (n.1 : ℝ) := by exact_mod_cast n.2
        have hlog : Real.log (n.1 : ℝ) ≤ Real.log (8 * X) :=
          Real.log_le_log hnpos hsupport
        have hlognonneg : 0 ≤ Real.log (n.1 : ℝ) := Real.log_natCast_nonneg _
        have hfactor : dyadicFactorComplexFunction z (.logarithm j) n.1 =
            (Real.log (n.1 : ℝ) : ℂ) := by
          simp [dyadicFactorComplexFunction, dyadicFactorFunction,
            dyadicLogFactor_apply, hI]
        rw [hfactor, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlognonneg]
        exact hlog
      · simp [dyadicFactorComplexFunction, dyadicFactorFunction,
          dyadicLogFactor_apply, hI]
        linarith
  | mobius j =>
      by_cases hI : inDyadicInterval j.val.val n.1 ∧
          (n.1 : ℝ) ≤ z
      · have hfactor : dyadicFactorComplexFunction z (.mobius j) n.1 =
            ((ArithmeticFunction.moebius n.1 : ℝ) : ℂ) := by
          simp [dyadicFactorComplexFunction, dyadicFactorFunction,
            dyadicMobiusFactor_apply, hI]
        rw [hfactor, Complex.norm_real, Real.norm_eq_abs]
        have hμ : |(ArithmeticFunction.moebius n.1 : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n.1)
        exact le_trans hμ hL.le
      · simp [dyadicFactorComplexFunction, dyadicFactorFunction,
          dyadicMobiusFactor_apply, hI]
        linarith

private theorem dyadicFactorFunction_abs_le {X : ℝ} (hX : 3 ≤ X)
    (z : ℝ) (f : DyadicArithmeticFactor X) (n : ℕ) :
    |dyadicFactorFunction z f n| ≤ Real.log (8 * X) := by
  by_cases hn : n = 0
  · subst n
    cases f <;> simp [dyadicFactorFunction, dyadicOneFactor, dyadicLogFactor,
      dyadicMobiusFactor, inDyadicInterval, dyadicLowerNat] <;>
      linarith [log_eightX_gt_one hX]
  · have h := dyadicFactorComplex_norm_le hX z f ⟨n, Nat.pos_of_ne_zero hn⟩
    simpa [dyadicFactorComplexFunction, Complex.norm_real, Real.norm_eq_abs] using h

theorem divisorCoefficient_succ_divisor_sum (k n : ℕ) :
    divisorCoefficient (k + 1) n =
      ∑ d ∈ n.divisors, divisorCoefficient k d := by
  dsimp [divisorCoefficient]
  rw [pow_succ, ArithmeticFunction.mul_zeta_apply]

theorem divisorCoefficient_mono {k l n : ℕ} (hn : 0 < n)
    (hkl : k ≤ l) : divisorCoefficient k n ≤ divisorCoefficient l n := by
  have hsucc (m : ℕ) : divisorCoefficient m n ≤ divisorCoefficient (m + 1) n := by
    rw [divisorCoefficient_succ_divisor_sum]
    apply Finset.single_le_sum (fun d hd => Nat.zero_le _)
    exact Nat.mem_divisors.mpr ⟨dvd_refl n, Nat.ne_of_gt hn⟩
  induction l generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      exact le_rfl
  | succ l ih =>
      by_cases hkle : k ≤ l
      · exact (ih hkle).trans (by simpa [Nat.succ_eq_add_one] using hsucc l)
      · have hk : k = l + 1 := by omega
        subst k
        exact le_rfl

private theorem dyadicConvolutionFactors_abs_le {X : ℝ} (hX : 3 ≤ X)
    (z : ℝ) (fs : List (DyadicArithmeticFactor X)) (n : PositiveInteger) :
    |dyadicConvolutionFactors z fs n.1| ≤
      Real.log (8 * X) ^ fs.length *
        (divisorCoefficient fs.length n.1 : ℝ) := by
  revert n
  induction fs with
  | nil =>
      intro n
      by_cases hn1 : n.1 = 1
      · simp [dyadicConvolutionFactors, divisorCoefficient,
          ArithmeticFunction.one_apply, hn1] <;> norm_num
      · simp [dyadicConvolutionFactors, divisorCoefficient,
          ArithmeticFunction.one_apply, hn1] <;> norm_num
  | cons f fs ih =>
      intro n
      have hfactor := dyadicFactorFunction_abs_le hX z f
      rw [dyadicConvolutionFactors, List.map_cons, List.prod_cons]
      have hsum :
          |∑ d ∈ n.1.divisors,
            dyadicConvolutionFactors z fs d * dyadicFactorFunction z f (n.1 / d)| ≤
            ∑ d ∈ n.1.divisors,
              Real.log (8 * X) ^ fs.length *
                (divisorCoefficient fs.length d : ℝ) * Real.log (8 * X) := by
        calc
          _ ≤ ∑ d ∈ n.1.divisors,
                |dyadicConvolutionFactors z fs d * dyadicFactorFunction z f (n.1 / d)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro d hd
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
            have hqpos : 0 < n.1 / d :=
              Nat.div_pos (Nat.le_of_dvd n.2 (Nat.mem_divisors.mp hd).1) hdpos
            have htail := ih ⟨d, hdpos⟩
            have hhead := hfactor (n.1 / d)
            have hLnonneg : 0 ≤ Real.log (8 * X) := by
              linarith [log_eightX_gt_one hX]
            have hupperNonneg :
                0 ≤ Real.log (8 * X) ^ fs.length *
                  (divisorCoefficient fs.length d : ℝ) :=
              mul_nonneg (pow_nonneg hLnonneg _) (Nat.cast_nonneg _)
            rw [abs_mul]
            exact mul_le_mul htail hhead (abs_nonneg _) hupperNonneg
      have hrec := divisorCoefficient_succ_divisor_sum fs.length n.1
      have hsum' :
          ∑ d ∈ n.1.divisors,
            Real.log (8 * X) ^ fs.length *
              (divisorCoefficient fs.length d : ℝ) * Real.log (8 * X) =
            Real.log (8 * X) ^ (fs.length + 1) *
              (divisorCoefficient (fs.length + 1) n.1 : ℝ) := by
        calc
          _ = (∑ d ∈ n.1.divisors,
                Real.log (8 * X) ^ fs.length *
                  (divisorCoefficient fs.length d : ℝ)) * Real.log (8 * X) := by
                rw [← Finset.sum_mul]
          _ = (Real.log (8 * X) ^ fs.length *
                ∑ d ∈ n.1.divisors, (divisorCoefficient fs.length d : ℝ)) *
                Real.log (8 * X) := by
                congr 1
                rw [Finset.mul_sum]
          _ = Real.log (8 * X) ^ (fs.length + 1) *
                (divisorCoefficient (fs.length + 1) n.1 : ℝ) := by
                rw [← Nat.cast_sum, hrec, pow_succ]
                ring
      rw [List.length_cons]
      change |(dyadicFactorFunction z f * dyadicConvolutionFactors z fs) n.1| ≤ _
      rw [mul_comm, ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal
          (f := fun a b => dyadicConvolutionFactors z fs a *
            dyadicFactorFunction z f b)]
      calc
        |∑ d ∈ n.1.divisors,
            dyadicConvolutionFactors z fs d * dyadicFactorFunction z f (n.1 / d)|
            ≤ ∑ d ∈ n.1.divisors,
                Real.log (8 * X) ^ fs.length *
                  (divisorCoefficient fs.length d : ℝ) * Real.log (8 * X) := hsum
        _ = Real.log (8 * X) ^ (fs.length + 1) *
              (divisorCoefficient (fs.length + 1) n.1 : ℝ) := hsum'

private theorem dyadicFactorFunction_support_upper {X : ℝ} (hX : 3 ≤ X)
    (z : ℝ) (f : DyadicArithmeticFactor X) {n : ℕ}
    (hne : dyadicFactorFunction z f n ≠ 0) :
    (n : ℝ) ≤ 8 * X := by
  cases f with
  | one j =>
      have hI : inDyadicInterval j.val.val n := by
        by_contra hI
        apply hne
        simp [dyadicFactorFunction, dyadicOneFactor_apply, hI]
      have hnat : n ≤ dyadicUpperNat j.val.val := hI.2
      have hcast : (n : ℝ) ≤ dyadicUpperNat j.val.val := by exact_mod_cast hnat
      exact hcast.trans (dyadicUpperNat_le_eightX hX j)
  | logarithm j =>
      have hI : inDyadicInterval j.val.val n := by
        by_contra hI
        apply hne
        simp [dyadicFactorFunction, dyadicLogFactor_apply, hI]
      have hnat : n ≤ dyadicUpperNat j.val.val := hI.2
      have hcast : (n : ℝ) ≤ dyadicUpperNat j.val.val := by exact_mod_cast hnat
      exact hcast.trans (dyadicUpperNat_le_eightX hX j)
  | mobius j =>
      have hI : inDyadicInterval j.val.val n := by
        by_contra hI
        apply hne
        simp [dyadicFactorFunction, dyadicMobiusFactor_apply, hI]
      have hnat : n ≤ dyadicUpperNat j.val.val := hI.2
      have hcast : (n : ℝ) ≤ dyadicUpperNat j.val.val := by exact_mod_cast hnat
      exact hcast.trans (dyadicUpperNat_le_eightX hX j)

private theorem arithmeticFunction_mul_apply_ne_zero {f g : ArithmeticFunction ℝ}
    {n : ℕ} (hne : (f * g) n ≠ 0) :
    ∃ x ∈ n.divisorsAntidiagonal, f x.1 ≠ 0 ∧ g x.2 ≠ 0 := by
  rw [ArithmeticFunction.mul_apply] at hne
  by_contra hnone
  have hterms : ∀ x ∈ n.divisorsAntidiagonal, f x.1 = 0 ∨ g x.2 = 0 := by
    intro x hx
    by_cases hf : f x.1 = 0
    · exact Or.inl hf
    · right
      by_contra hg
      exact hnone ⟨x, hx, hf, hg⟩
  have hsum : (∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rcases hterms x hx with hf | hg
    · simp [hf]
    · simp [hg]
  exact hne hsum

private theorem dyadicConvolutionFactors_support_upper {X : ℝ}
    (hX : 3 ≤ X) (z : ℝ) (fs : List (DyadicArithmeticFactor X))
    {n : ℕ} (hn : 0 < n)
    (hne : dyadicConvolutionFactors z fs n ≠ 0) :
    (n : ℝ) ≤ (8 * X) ^ fs.length := by
  induction fs generalizing n with
  | nil =>
      have hn1 : n = 1 := by
        by_contra hn1
        apply hne
        simp [dyadicConvolutionFactors, hn1]
      subst n
      simp [dyadicConvolutionFactors]
  | cons f fs ih =>
      rw [dyadicConvolutionFactors, List.map_cons, List.prod_cons] at hne
      obtain ⟨x, hx, hfirst, htail⟩ := arithmeticFunction_mul_apply_ne_zero hne
      have hpair := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have hx1pos : 0 < x.1 := Nat.pos_of_ne_zero
        (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx)
      have hx2pos : 0 < x.2 := Nat.pos_of_ne_zero
        (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx)
      have hfirstUpper : (x.1 : ℝ) ≤ 8 * X :=
        dyadicFactorFunction_support_upper hX z f hfirst
      have htailUpper : (x.2 : ℝ) ≤ (8 * X) ^ fs.length :=
        ih hx2pos htail
      have hpairReal : (n : ℝ) = (x.1 : ℝ) * (x.2 : ℝ) := by
        exact_mod_cast hpair.symm
      have hproductUpper :
          (x.1 : ℝ) * (x.2 : ℝ) ≤ (8 * X) * (8 * X) ^ fs.length :=
        mul_le_mul hfirstUpper htailUpper (by positivity) (by positivity)
      rw [List.length_cons, pow_succ]
      nlinarith

private theorem groupedDyadicFactor_norm_le {X : ℝ} (hX : 3 ≤ X)
    (z : ℝ) (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (fs : List (DyadicArithmeticFactor X)) (hlen : fs.length ≤ 20)
    (n : PositiveInteger) :
    ‖groupedDyadicFactor z c fs n‖ ≤
      (2 : ℝ) ^ 10 * Real.log (8 * X) ^ 20 *
        (divisorCoefficient 20 n.1 : ℝ) := by
  have hL : 1 < Real.log (8 * X) := log_eightX_gt_one hX
  have hconv := dyadicConvolutionFactors_abs_le hX z fs n
  have hpow : Real.log (8 * X) ^ fs.length ≤ Real.log (8 * X) ^ 20 :=
    pow_le_pow_right₀ hL.le hlen
  have hdivNat : divisorCoefficient fs.length n.1 ≤ divisorCoefficient 20 n.1 :=
    divisorCoefficient_mono n.2 hlen
  have hdiv : (divisorCoefficient fs.length n.1 : ℝ) ≤
      (divisorCoefficient 20 n.1 : ℝ) := by exact_mod_cast hdivNat
  have hLnonneg : 0 ≤ Real.log (8 * X) := by linarith
  have hinner :=
    calc
      Real.log (8 * X) ^ fs.length *
          (divisorCoefficient fs.length n.1 : ℝ) ≤
        Real.log (8 * X) ^ 20 *
          (divisorCoefficient fs.length n.1 : ℝ) :=
            mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
      _ ≤ Real.log (8 * X) ^ 20 *
          (divisorCoefficient 20 n.1 : ℝ) :=
            mul_le_mul_of_nonneg_left hdiv (pow_nonneg hLnonneg _)
  change ‖c * ((dyadicConvolutionFactors z fs n.1 : ℝ) : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real]
  calc
    ‖c‖ * |dyadicConvolutionFactors z fs n.1| ≤
        (2 : ℝ) ^ 10 *
          (Real.log (8 * X) ^ fs.length *
            (divisorCoefficient fs.length n.1 : ℝ)) :=
      mul_le_mul hc hconv (abs_nonneg _) (by positivity)
    _ ≤ (2 : ℝ) ^ 10 *
          (Real.log (8 * X) ^ 20 *
            (divisorCoefficient 20 n.1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (2 : ℝ) ^ 10 * Real.log (8 * X) ^ 20 *
          (divisorCoefficient 20 n.1 : ℝ) := by ring

private theorem groupedDyadicFactor_supportedBelow {X : ℝ} (hX : 3 ≤ X)
    (z : ℝ) (c : ℂ) (fs : List (DyadicArithmeticFactor X))
    (hlen : fs.length ≤ 20) (n : PositiveInteger)
    (hne : groupedDyadicFactor z c fs n ≠ 0) :
    (n.1 : ℝ) ≤ (8 * X) ^ 20 := by
  have hconv : dyadicConvolutionFactors z fs n.1 ≠ 0 := by
    intro hzero
    apply hne
    simp [groupedDyadicFactor, hzero]
  have hconvUpper := dyadicConvolutionFactors_support_upper hX z fs n.2 hconv
  have hbase : 1 ≤ 8 * X := by linarith [hX]
  have hpow : (8 * X) ^ fs.length ≤ (8 * X) ^ 20 :=
    pow_le_pow_right₀ hbase hlen
  exact hconvUpper.trans hpow

private theorem complexPositiveSecondMoment_stopsAtSupport
    (f : ComplexPositiveIntegerFunction) {Y₀ Y : ℝ} (hY₀Y : Y₀ ≤ Y)
    (hsupp : ∀ n, f n ≠ 0 → (n.1 : ℝ) ≤ Y₀) :
    complexPositiveSecondMoment f Y = complexPositiveSecondMoment f Y₀ := by
  unfold complexPositiveSecondMoment
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.floor_mono hY₀Y))
  intro n hnBig hnNotSmall
  have hmem := Finset.mem_Icc.mp hnBig
  have hnpos : 0 < n := by omega
  have hnFloorLt : Nat.floor Y₀ < n := by
    by_contra hn
    apply hnNotSmall
    exact Finset.mem_Icc.mpr ⟨hmem.1, by omega⟩
  have hnat : Nat.floor Y₀ + 1 ≤ n := Nat.succ_le_iff.mpr hnFloorLt
  have hcast : (Nat.floor Y₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnat
  have hY₀n : Y₀ < (n : ℝ) := (Nat.lt_floor_add_one Y₀).trans_le hcast
  have hfzero : f ⟨n, hnpos⟩ = 0 := by
    by_contra hf
    exact (not_le_of_gt hY₀n) (hsupp ⟨n, hnpos⟩ hf)
  simp [complexPositiveSecondMomentSummand, hnpos, hfzero]

private theorem complexPositiveFourthMoment_stopsAtSupport
    (f : ComplexPositiveIntegerFunction) {Y₀ Y : ℝ} (hY₀Y : Y₀ ≤ Y)
    (hsupp : ∀ n, f n ≠ 0 → (n.1 : ℝ) ≤ Y₀) :
    complexPositiveFourthMoment f Y = complexPositiveFourthMoment f Y₀ := by
  unfold complexPositiveFourthMoment
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.floor_mono hY₀Y))
  intro n hnBig hnNotSmall
  have hmem := Finset.mem_Icc.mp hnBig
  have hnpos : 0 < n := by omega
  have hnFloorLt : Nat.floor Y₀ < n := by
    by_contra hn
    apply hnNotSmall
    exact Finset.mem_Icc.mpr ⟨hmem.1, by omega⟩
  have hnat : Nat.floor Y₀ + 1 ≤ n := Nat.succ_le_iff.mpr hnFloorLt
  have hcast : (Nat.floor Y₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnat
  have hY₀n : Y₀ < (n : ℝ) := (Nat.lt_floor_add_one Y₀).trans_le hcast
  have hfzero : f ⟨n, hnpos⟩ = 0 := by
    by_contra hf
    exact (not_le_of_gt hY₀n) (hsupp ⟨n, hnpos⟩ hf)
  simp [complexPositiveFourthMomentSummand, hnpos, hfzero]

private theorem log_X_gt_one {X : ℝ} (hX : 3 ≤ X) :
    1 < Real.log X := by
  have hlog3 : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
  exact hlog3.trans_le (Real.log_le_log (by norm_num) hX)

private theorem log_eightX_le_four_logX {X : ℝ} (hX : 3 ≤ X) :
    Real.log (8 * X) ≤ 4 * Real.log X := by
  have hXpos : 0 < X := by linarith
  have hX3 : (8 : ℝ) ≤ X ^ 3 := by
    calc
      8 ≤ 3 ^ 3 := by norm_num
      _ ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
  have harg : 8 * X ≤ X ^ 4 := by
    calc
      8 * X ≤ X ^ 3 * X := mul_le_mul_of_nonneg_right hX3 hXpos.le
      _ = X ^ 4 := by ring
  have hlog := Real.log_le_log (by positivity : 0 < 8 * X) harg
  have hlogpow : Real.log (X ^ 4) = 4 * Real.log X := by
    rw [Real.log_pow X 4]
    norm_num
  rw [hlogpow] at hlog
  exact hlog

private theorem one_add_log_eightXpow_le {X : ℝ} (hX : 3 ≤ X) :
    1 + Real.log ((8 * X) ^ 20) ≤ 81 * Real.log X := by
  have hlogX := log_X_gt_one hX
  have hlog8 := log_eightX_le_four_logX hX
  have hlogpow : Real.log ((8 * X) ^ 20) = 20 * Real.log (8 * X) := by
    rw [Real.log_pow (8 * X) 20]
    norm_num
  rw [hlogpow]
  nlinarith

private theorem natPow_mono_base {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (n : ℕ) : a ^ n ≤ b ^ n := by
  have h := Real.rpow_le_rpow ha hab (by positivity : 0 ≤ (n : ℝ))
  simpa only [Real.rpow_natCast] using h

private theorem natPow_mono_exponent {a : ℝ} (ha : 1 ≤ a) {m n : ℕ}
    (hmn : m ≤ n) : a ^ m ≤ a ^ n := by
  have hgap : 1 ≤ a ^ (n - m) := one_le_pow₀ ha
  calc
    a ^ m = a ^ m * 1 := by simp
    _ ≤ a ^ m * a ^ (n - m) :=
      mul_le_mul_of_nonneg_left hgap (pow_nonneg (by linarith) _)
    _ = a ^ n := by
      rw [← pow_add]
      congr 1
      omega

private theorem natPow_mono_base_159999 {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : a ^ 159999 ≤ b ^ 159999 := by
  have h399 : a ^ 399 ≤ b ^ 399 := natPow_mono_base ha hab 399
  have h400 : (a ^ 399) ^ 400 ≤ (b ^ 399) ^ 400 :=
    natPow_mono_base (pow_nonneg ha _) h399 400
  calc
    a ^ 159999 = (a ^ 399) ^ 400 * a ^ 399 := by
      rw [show 159999 = 399 * 400 + 399 by norm_num, pow_add, pow_mul]
    _ ≤ (b ^ 399) ^ 400 * b ^ 399 :=
      mul_le_mul h400 h399 (pow_nonneg ha _)
        (pow_nonneg (pow_nonneg (le_trans ha hab) _) _)
    _ = b ^ 159999 := by
      rw [show 159999 = 399 * 400 + 399 by norm_num, pow_add, pow_mul]

private theorem decompositionDType_dominates_second {X : ℝ} (hX : 3 ≤ X) :
    (2 : ℝ) ^ 100 * (81 : ℝ) ^ 399 * (Real.log X) ^ 439 ≤
      decompositionDType X := by
  have hlogX := log_X_gt_one hX
  simp only [decompositionDType, decompositionC, decompositionB]
  have hpow2 : (2 : ℝ) ^ 100 ≤ 2 ^ 200 :=
    natPow_mono_exponent (by norm_num) (by omega)
  have hpow81 : (81 : ℝ) ^ 399 ≤ 81 ^ 160000 :=
    natPow_mono_exponent (by norm_num) (by omega)
  have hpowlog : (Real.log X) ^ 439 ≤ (Real.log X) ^ 160100 :=
    natPow_mono_exponent (le_of_lt hlogX) (by omega)
  calc
    _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 399 * (Real.log X) ^ 439 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow2
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 81) _))
        (pow_nonneg (by linarith [hlogX]) _)
    _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 * (Real.log X) ^ 439 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow81 (by positivity))
        (pow_nonneg (by linarith [hlogX]) _)
    _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 * (Real.log X) ^ 160100 :=
      mul_le_mul_of_nonneg_left hpowlog (by positivity)

private theorem decompositionDType_dominates_fourth {X : ℝ} (hX : 3 ≤ X) :
    (2 : ℝ) ^ 200 * (81 : ℝ) ^ 159999 * (Real.log X) ^ 160079 ≤
      decompositionDType X := by
  have hlogX := log_X_gt_one hX
  simp only [decompositionDType, decompositionC, decompositionB]
  have hpow81 : (81 : ℝ) ^ 159999 ≤ 81 ^ 160000 :=
    natPow_mono_exponent (by norm_num) (by omega)
  have hpowlog : (Real.log X) ^ 160079 ≤ (Real.log X) ^ 160100 :=
    natPow_mono_exponent (le_of_lt hlogX) (by omega)
  calc
    _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 * (Real.log X) ^ 160079 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow81 (by positivity))
        (pow_nonneg (by linarith [hlogX]) _)
    _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 * (Real.log X) ^ 160100 :=
      mul_le_mul_of_nonneg_left hpowlog (by positivity)

private theorem groupedDyadicFactor_secondMoment_small {X : ℝ}
    (hX : 3 ≤ X) (z : ℝ) (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (fs : List (DyadicArithmeticFactor X)) (hlen : fs.length ≤ 20)
    (Y : ℝ) (hY : 1 ≤ Y) (hYsmall : Y ≤ (8 * X) ^ 20) :
    complexPositiveSecondMoment (groupedDyadicFactor z c fs) Y ≤
      decompositionDType X * Y := by
  let A : ℝ := (2 : ℝ) ^ 10 * Real.log (8 * X) ^ 20
  have hlogX := log_X_gt_one hX
  have hlog8 := log_eightX_le_four_logX hX
  have hlogYnonneg : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hlogYbound : 1 + Real.log Y ≤ 81 * Real.log X := by
    have hlogmono : Real.log Y ≤ Real.log ((8 * X) ^ 20) :=
      Real.log_le_log (by linarith) hYsmall
    have hbound := one_add_log_eightXpow_le hX
    linarith
  have hA2 : A ^ 2 ≤ (2 : ℝ) ^ 100 * (Real.log X) ^ 40 := by
    dsimp [A]
    calc
      ((2 : ℝ) ^ 10 * Real.log (8 * X) ^ 20) ^ 2 =
          (2 : ℝ) ^ 20 * Real.log (8 * X) ^ 40 := by ring
      _ ≤ (2 : ℝ) ^ 20 * (4 * Real.log X) ^ 40 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith [log_eightX_gt_one hX]) hlog8 40)
          (by positivity)
      _ = (2 : ℝ) ^ 100 * (Real.log X) ^ 40 := by ring
  have hlogterm2 : (1 + Real.log Y) ^ 399 ≤
      (81 : ℝ) ^ 399 * (Real.log X) ^ 399 := by
    calc
      (1 + Real.log Y) ^ 399 ≤ (81 * Real.log X) ^ 399 :=
        natPow_mono_base (by linarith [hlogYnonneg]) hlogYbound 399
      _ = (81 : ℝ) ^ 399 * (Real.log X) ^ 399 := by rw [mul_pow]
  have hsmall2 : A ^ 2 * (1 + Real.log Y) ^ 399 ≤ decompositionDType X := by
    calc
      A ^ 2 * (1 + Real.log Y) ^ 399 ≤
          ((2 : ℝ) ^ 100 * (Real.log X) ^ 40) *
            ((81 : ℝ) ^ 399 * (Real.log X) ^ 399) :=
        mul_le_mul hA2 hlogterm2 (by positivity) (by positivity)
      _ = (2 : ℝ) ^ 100 * (81 : ℝ) ^ 399 *
            ((Real.log X) ^ 40 * (Real.log X) ^ 399) := by ac_rfl
      _ = (2 : ℝ) ^ 100 * (81 : ℝ) ^ 399 *
            (Real.log X) ^ 439 := by
              rw [← pow_add]
      _ ≤ decompositionDType X := decompositionDType_dominates_second hX
  have hdiv2 := divisorMomentBound 20 2 (by norm_num) (by norm_num) Y hY
  have hsecond :
      complexPositiveSecondMoment (groupedDyadicFactor z c fs) Y ≤
        A ^ 2 * Y * (1 + Real.log Y) ^ 399 := by
    unfold complexPositiveSecondMoment
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
            A ^ 2 * (divisorCoefficient 20 n : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
          have hnorm := groupedDyadicFactor_norm_le hX z c hc fs hlen ⟨n, hnpos⟩
          have hterm := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
          have hterm' :
              ‖groupedDyadicFactor z c fs ⟨n, hnpos⟩‖ ^ 2 ≤
                A ^ 2 * (divisorCoefficient 20 n : ℝ) ^ 2 := by
            calc
              _ ≤ (A * (divisorCoefficient 20 n : ℝ)) ^ 2 := by
                simpa [A] using hterm
              _ = _ := by ring
          simpa only [complexPositiveSecondMomentSummand, dite_eq_left hnpos] using hterm'
      _ = A ^ 2 * ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
            (divisorCoefficient 20 n : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ A ^ 2 * (Y * (1 + Real.log Y) ^ 399) :=
        mul_le_mul_of_nonneg_left hdiv2 (sq_nonneg A)
      _ = A ^ 2 * Y * (1 + Real.log Y) ^ 399 := by ac_rfl
  calc
    complexPositiveSecondMoment (groupedDyadicFactor z c fs) Y ≤
        A ^ 2 * Y * (1 + Real.log Y) ^ 399 := hsecond
    _ = Y * (A ^ 2 * (1 + Real.log Y) ^ 399) := by ac_rfl
    _ ≤ Y * decompositionDType X := mul_le_mul_of_nonneg_left hsmall2 (by linarith)
    _ = decompositionDType X * Y := mul_comm _ _

private theorem groupedDyadicFactor_fourthTermBound {X : ℝ} (hX : 3 ≤ X)
    (z : ℝ) (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (fs : List (DyadicArithmeticFactor X)) (hlen : fs.length ≤ 20)
    (n : PositiveInteger) :
    ‖groupedDyadicFactor z c fs n‖ ^ 4 ≤
      ((2 : ℝ) ^ 10 * Real.log (8 * X) ^ 20) ^ 4 *
        (divisorCoefficient 20 n.1 : ℝ) ^ 4 := by
  have hnorm := groupedDyadicFactor_norm_le hX z c hc fs hlen n
  calc
    ‖groupedDyadicFactor z c fs n‖ ^ 4 ≤
        ((2 : ℝ) ^ 10 * Real.log (8 * X) ^ 20 *
          (divisorCoefficient 20 n.1 : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 4
    _ = _ := by rw [mul_pow]

private theorem groupedDyadicFactor_fourthMoment_raw {X : ℝ}
    (hX : 3 ≤ X) (z : ℝ) (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (fs : List (DyadicArithmeticFactor X)) (hlen : fs.length ≤ 20)
    (Y : ℝ) (hY : 1 ≤ Y) :
    complexPositiveFourthMoment (groupedDyadicFactor z c fs) Y ≤
      Y * (((2 : ℝ) ^ 10 * Real.log (8 * X) ^ 20) ^ 4 *
        (1 + Real.log Y) ^ 159999) := by
  let A : ℝ := (2 : ℝ) ^ 10 * Real.log (8 * X) ^ 20
  have hlog8pos : 0 < Real.log (8 * X) := by
    linarith [log_eightX_gt_one hX]
  have hAnonneg : 0 ≤ A := by dsimp [A]; positivity
  have hdiv4 := divisorMomentBound 20 4 (by norm_num) (by norm_num) Y hY
  have hfourth :
      complexPositiveFourthMoment (groupedDyadicFactor z c fs) Y ≤
        A ^ 4 * Y * (1 + Real.log Y) ^ 159999 := by
    unfold complexPositiveFourthMoment
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
            A ^ 4 * (divisorCoefficient 20 n : ℝ) ^ 4 := by
          apply Finset.sum_le_sum
          intro n hn
          have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
          have hterm := groupedDyadicFactor_fourthTermBound hX z c hc fs hlen
            ⟨n, hnpos⟩
          simpa only [A, complexPositiveFourthMomentSummand, dite_eq_left hnpos]
            using hterm
      _ = A ^ 4 * ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
            (divisorCoefficient 20 n : ℝ) ^ 4 := by rw [Finset.mul_sum]
      _ ≤ A ^ 4 * (Y * (1 + Real.log Y) ^ 159999) :=
        mul_le_mul_of_nonneg_left hdiv4 (pow_nonneg hAnonneg 4)
      _ = A ^ 4 * Y * (1 + Real.log Y) ^ 159999 :=
        (mul_assoc _ _ _).symm
  have hrawA :
      complexPositiveFourthMoment (groupedDyadicFactor z c fs) Y ≤
        Y * (A ^ 4 * (1 + Real.log Y) ^ 159999) := by
    calc
      _ ≤ A ^ 4 * Y * (1 + Real.log Y) ^ 159999 := hfourth
      _ = Y * A ^ 4 * (1 + Real.log Y) ^ 159999 := by
        rw [mul_comm (A ^ 4) Y]
      _ = Y * (A ^ 4 * (1 + Real.log Y) ^ 159999) := by
        rw [← mul_assoc]
  simpa only [A] using hrawA

private theorem groupedDyadicFactor_fourthCoefficient_small {X : ℝ}
    (hX : 3 ≤ X) (Y : ℝ) (hY : 1 ≤ Y)
    (hYsmall : Y ≤ (8 * X) ^ 20) :
    ((2 : ℝ) ^ 10 * Real.log (8 * X) ^ 20) ^ 4 *
        (1 + Real.log Y) ^ 159999 ≤ decompositionDType X := by
  have hlogX := log_X_gt_one hX
  have hlog8 := log_eightX_le_four_logX hX
  have hlogYnonneg : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hlogYbound : 1 + Real.log Y ≤ 81 * Real.log X := by
    have hlogmono : Real.log Y ≤ Real.log ((8 * X) ^ 20) :=
      Real.log_le_log (by linarith) hYsmall
    have hbound := one_add_log_eightXpow_le hX
    linarith
  have hA4 : ((2 : ℝ) ^ 10 * Real.log (8 * X) ^ 20) ^ 4 ≤
      (2 : ℝ) ^ 200 * (Real.log X) ^ 80 := by
    calc
      ((2 : ℝ) ^ 10 * Real.log (8 * X) ^ 20) ^ 4 =
          (2 : ℝ) ^ 40 * Real.log (8 * X) ^ 80 := by ring
      _ ≤ (2 : ℝ) ^ 40 * (4 * Real.log X) ^ 80 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith [log_eightX_gt_one hX]) hlog8 80)
          (by positivity)
      _ = (2 : ℝ) ^ 200 * (Real.log X) ^ 80 := by ring
  have hlogterm4 : (1 + Real.log Y) ^ 159999 ≤
      (81 : ℝ) ^ 159999 * (Real.log X) ^ 159999 := by
    calc
      (1 + Real.log Y) ^ 159999 ≤ (81 * Real.log X) ^ 159999 :=
        natPow_mono_base_159999 (by linarith [hlogYnonneg]) hlogYbound
      _ = (81 : ℝ) ^ 159999 * (Real.log X) ^ 159999 := by rw [mul_pow]
  calc
    _ ≤ ((2 : ℝ) ^ 200 * (Real.log X) ^ 80) *
          ((81 : ℝ) ^ 159999 * (Real.log X) ^ 159999) :=
      mul_le_mul hA4 hlogterm4 (by positivity) (by positivity)
    _ = (2 : ℝ) ^ 200 *
          ((Real.log X) ^ 80 *
            ((81 : ℝ) ^ 159999 * (Real.log X) ^ 159999)) := by rw [mul_assoc]
    _ = (2 : ℝ) ^ 200 *
          ((81 : ℝ) ^ 159999 *
            ((Real.log X) ^ 80 * (Real.log X) ^ 159999)) := by ac_rfl
    _ = (2 : ℝ) ^ 200 * ((81 : ℝ) ^ 159999 *
          (Real.log X) ^ 160079) := by rw [← pow_add]
    _ = (2 : ℝ) ^ 200 * (81 : ℝ) ^ 159999 *
          (Real.log X) ^ 160079 := by rw [mul_assoc]
    _ ≤ decompositionDType X := decompositionDType_dominates_fourth hX

private theorem groupedFourthMoment_finalGlue {M A L D Y : ℝ}
    (hraw : M ≤ Y * (A * L)) (hsmall : A * L ≤ D) (hY : 0 ≤ Y) :
    M ≤ D * Y := by
  calc
    M ≤ Y * (A * L) := hraw
    _ ≤ Y * D := mul_le_mul_of_nonneg_left hsmall hY
    _ = D * Y := mul_comm _ _

private theorem groupedDyadicFactor_fourthMoment_small {X : ℝ}
    (hX : 3 ≤ X) (z : ℝ) (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (fs : List (DyadicArithmeticFactor X)) (hlen : fs.length ≤ 20)
    (Y : ℝ) (hY : 1 ≤ Y) (hYsmall : Y ≤ (8 * X) ^ 20) :
    complexPositiveFourthMoment (groupedDyadicFactor z c fs) Y ≤
      decompositionDType X * Y := by
  have hraw := groupedDyadicFactor_fourthMoment_raw hX z c hc fs hlen Y hY
  have hsmall := groupedDyadicFactor_fourthCoefficient_small hX Y hY hYsmall
  have hYnonneg : 0 ≤ Y := le_trans (by norm_num) hY
  exact groupedFourthMoment_finalGlue hraw hsmall hYnonneg

private theorem groupedDyadicFactor_moments_small {X : ℝ}
    (hX : 3 ≤ X) (z : ℝ) (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (fs : List (DyadicArithmeticFactor X)) (hlen : fs.length ≤ 20)
    (Y : ℝ) (hY : 1 ≤ Y) (hYsmall : Y ≤ (8 * X) ^ 20) :
    complexPositiveSecondMoment (groupedDyadicFactor z c fs) Y ≤
        decompositionDType X * Y ∧
      complexPositiveFourthMoment (groupedDyadicFactor z c fs) Y ≤
        decompositionDType X * Y := by
  exact ⟨groupedDyadicFactor_secondMoment_small hX z c hc fs hlen Y hY hYsmall,
    groupedDyadicFactor_fourthMoment_small hX z c hc fs hlen Y hY hYsmall⟩

private theorem decompositionDType_gt_one {X : ℝ} (hX : 3 ≤ X) :
    1 < decompositionDType X := by
  rcases decompositionConstants hX with ⟨hδpos, hδlt⟩
  change 0 < (decompositionDType X)⁻¹ at hδpos
  change (decompositionDType X)⁻¹ < 1 at hδlt
  have hDpos : 0 < decompositionDType X := inv_pos.mp hδpos
  exact (inv_lt_one₀ hDpos).mp hδlt

/-- The grouped second and fourth moment estimates for every real cutoff.
The fourth-moment statement is the blueprint's bound with the square of the
type constant. -/
theorem groupedDyadicFactor_momentBounds {X : ℝ}
    (hX : 3 ≤ X) (z : ℝ) (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (fs : List (DyadicArithmeticFactor X)) (hlen : fs.length ≤ 20)
    (Y : ℝ) (hY : 1 ≤ Y) :
    complexPositiveSecondMoment (groupedDyadicFactor z c fs) Y ≤
        decompositionDType X * Y ∧
      complexPositiveFourthMoment (groupedDyadicFactor z c fs) Y ≤
        (decompositionDType X) ^ 2 * Y := by
  let Y₀ : ℝ := (8 * X) ^ 20
  have hY₀ : 1 ≤ Y₀ := by
    dsimp [Y₀]
    have hbase : 1 ≤ 8 * X := by nlinarith [hX]
    exact one_le_pow₀ hbase
  have hDgt := decompositionDType_gt_one hX
  have hDnonneg : 0 ≤ decompositionDType X :=
    le_trans (by norm_num) (le_of_lt hDgt)
  have hDsq : decompositionDType X ≤ (decompositionDType X) ^ 2 := by
    calc
      decompositionDType X = 1 * decompositionDType X := by ring
      _ ≤ decompositionDType X * decompositionDType X :=
        mul_le_mul_of_nonneg_right (le_of_lt hDgt) hDnonneg
      _ = (decompositionDType X) ^ 2 := by ring
  have hYnonneg : 0 ≤ Y := le_trans (by norm_num) hY
  by_cases hsmall : Y ≤ Y₀
  · have hsmallY : Y ≤ (8 * X) ^ 20 := by simpa [Y₀] using hsmall
    have hmom := groupedDyadicFactor_moments_small hX z c hc fs hlen Y hY hsmallY
    constructor
    · exact hmom.1
    · calc
        complexPositiveFourthMoment (groupedDyadicFactor z c fs) Y ≤
            decompositionDType X * Y := hmom.2
        _ ≤ (decompositionDType X) ^ 2 * Y :=
          mul_le_mul_of_nonneg_right hDsq hYnonneg

  · have hY₀Y : Y₀ ≤ Y := le_of_not_ge hsmall
    have hsmallY₀ : Y₀ ≤ (8 * X) ^ 20 := by rfl
    have hmom₀ :=
      groupedDyadicFactor_moments_small hX z c hc fs hlen Y₀ hY₀ hsmallY₀
    have hsupp : ∀ n, groupedDyadicFactor z c fs n ≠ 0 → (n.1 : ℝ) ≤ Y₀ := by
      intro n hn
      have h := groupedDyadicFactor_supportedBelow hX z c fs hlen n hn
      simpa [Y₀] using h
    have hsecondStop := complexPositiveSecondMoment_stopsAtSupport
      (groupedDyadicFactor z c fs) hY₀Y hsupp
    have hfourthStop := complexPositiveFourthMoment_stopsAtSupport
      (groupedDyadicFactor z c fs) hY₀Y hsupp
    constructor
    · rw [hsecondStop]
      calc
        complexPositiveSecondMoment (groupedDyadicFactor z c fs) Y₀ ≤
            decompositionDType X * Y₀ := hmom₀.1
        _ ≤ decompositionDType X * Y :=
          mul_le_mul_of_nonneg_left hY₀Y hDnonneg
    · rw [hfourthStop]
      calc
        complexPositiveFourthMoment (groupedDyadicFactor z c fs) Y₀ ≤
            decompositionDType X * Y₀ := hmom₀.2
        _ ≤ decompositionDType X * Y :=
          mul_le_mul_of_nonneg_left hY₀Y hDnonneg
        _ ≤ (decompositionDType X) ^ 2 * Y :=
          mul_le_mul_of_nonneg_right hDsq hYnonneg

private def listMonotoneIncrementSum (h : ℤ → ℝ) (a : ℤ) : List ℤ → ℝ
  | [] => 0
  | b :: bs => (h b - h a) + listMonotoneIncrementSum h b bs

private theorem listMonotoneIncrementSum_bounds (h : ℤ → ℝ) (L : ℝ)
    (hmono : ∀ a b, a ≤ b → h a ≤ h b)
    (hhi : ∀ a, h a ≤ L) :
    ∀ {a : ℤ} (bs : List ℤ), List.Pairwise (· ≤ ·) (a :: bs) →
      0 ≤ listMonotoneIncrementSum h a bs ∧
        h a + listMonotoneIncrementSum h a bs ≤ L := by
  intro a bs
  induction bs generalizing a with
  | nil =>
      intro hs
      constructor
      · simp [listMonotoneIncrementSum]
      · simpa [listMonotoneIncrementSum] using hhi a
  | cons b bs ih =>
      intro hs
      have hparts := List.pairwise_cons.mp hs
      have hab : a ≤ b := hparts.1 b (by simp)
      have htail : List.Pairwise (· ≤ ·) (b :: bs) := hparts.2
      have htailBound := ih (a := b) htail
      have hdiff : 0 ≤ h b - h a := sub_nonneg.mpr (hmono a b hab)
      constructor
      · exact add_nonneg hdiff htailBound.1
      · change h a + ((h b - h a) + listMonotoneIncrementSum h b bs) ≤ L
        calc
          h a + ((h b - h a) + listMonotoneIncrementSum h b bs) =
              h b + listMonotoneIncrementSum h b bs := by ring
          _ ≤ L := htailBound.2

private theorem listAdjacentVariation_cons_cons (g : ℤ → ℂ) (a b : ℤ)
    (bs : List ℤ) :
    listAdjacentVariation g (a :: b :: bs) =
      ‖g b - g a‖ + listAdjacentVariation g (b :: bs) := by
  simp [listAdjacentVariation, List.consecutivePairs, List.zip, List.tail]

private theorem listAdjacentVariation_sub_monotone_le
    (A B : ℤ → ℝ) (a : ℤ) (bs : List ℤ)
    (hmonoA : ∀ x y, x ≤ y → A x ≤ A y)
    (hmonoB : ∀ x y, x ≤ y → B x ≤ B y)
    (hsorted : List.Pairwise (· ≤ ·) (a :: bs)) :
    listAdjacentVariation (fun n => ((A n - B n : ℝ) : ℂ)) (a :: bs) ≤
      listMonotoneIncrementSum A a bs + listMonotoneIncrementSum B a bs := by
  induction bs generalizing a with
  | nil => simp [listAdjacentVariation, listMonotoneIncrementSum,
      List.consecutivePairs]
  | cons b bs ih =>
      have hparts := List.pairwise_cons.mp hsorted
      have hab : a ≤ b := hparts.1 b (by simp)
      have htail : List.Pairwise (· ≤ ·) (b :: bs) := hparts.2
      have hA : 0 ≤ A b - A a := sub_nonneg.mpr (hmonoA a b hab)
      have hB : 0 ≤ B b - B a := sub_nonneg.mpr (hmonoB a b hab)
      have hstep :
          ‖((A b - B b : ℝ) : ℂ) - ((A a - B a : ℝ) : ℂ)‖ ≤
            (A b - A a) + (B b - B a) := by
        have hcast :
            ((A b - B b : ℝ) : ℂ) - ((A a - B a : ℝ) : ℂ) =
              (((A b - A a) - (B b - B a) : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_le]
        constructor <;> linarith
      rw [listAdjacentVariation_cons_cons]
      have htailBound := ih (a := b) htail
      simp only [listMonotoneIncrementSum] at htailBound ⊢
      calc
        ‖((A b - B b : ℝ) : ℂ) - ((A a - B a : ℝ) : ℂ)‖ +
            listAdjacentVariation (fun n => ((A n - B n : ℝ) : ℂ)) (b :: bs) ≤
          (A b - A a) + (B b - B a) +
            (listMonotoneIncrementSum A b bs + listMonotoneIncrementSum B b bs) :=
          add_le_add hstep htailBound
        _ = (A b - A a + listMonotoneIncrementSum A b bs) +
            (B b - B a + listMonotoneIncrementSum B b bs) := by ring

private theorem listSupNorm_le_of_pointwise (g : ℤ → ℂ) (ns : List ℤ)
    (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ n ∈ ns, ‖g n‖ ≤ L) : listSupNorm g ns ≤ L := by
  have hfold : ∀ (l : List ℤ) (b : ℝ), b ≤ L →
      (∀ n ∈ l, ‖g n‖ ≤ L) →
        ((l.map fun n => ‖g n‖).foldl max b) ≤ L := by
    intro l
    induction l with
    | nil => intro b hb _; simpa using hb
    | cons n ns ih =>
        intro b hb hns
        simp only [List.map_cons, List.foldl_cons]
        apply ih
        · exact max_le hb (hns n (by simp))
        · intro m hm
          exact hns m (by simp [hm])
  simpa [listSupNorm] using hfold ns 0 hL hbound

private theorem orderedTotalVariation_sub_monotone_le
    (P : Set ℤ) (g : ℤ → ℂ) (A B : ℤ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hmonoA : ∀ x y, x ≤ y → A x ≤ A y)
    (hmonoB : ∀ x y, x ≤ y → B x ≤ B y)
    (hloA : ∀ x, 0 ≤ A x) (hloB : ∀ x, 0 ≤ B x)
    (hhiA : ∀ x, A x ≤ L) (hhiB : ∀ x, B x ≤ L)
    (hAB : ∀ x ∈ P, B x ≤ A x)
    (hg : ∀ x ∈ P, g x = ((A x - B x : ℝ) : ℂ)) :
    orderedTotalVariation P g ≤ ENNReal.ofReal (3 * L) := by
  unfold orderedTotalVariation
  apply iSup_le
  intro F
  let ns := F.1.sort (· ≤ ·)
  have hsorted : List.Pairwise (· ≤ ·) ns := Finset.pairwise_sort F.1 (· ≤ ·)
  have hmem : ∀ n ∈ ns, n ∈ P := by
    intro n hn
    exact F.2 n ((Finset.mem_sort (s := F.1) (r := (· ≤ ·))).1 hn)
  let g' : ℤ → ℂ := fun n => ((A n - B n : ℝ) : ℂ)
  have hsup : listSupNorm g' ns ≤ L := by
    apply listSupNorm_le_of_pointwise g' ns L hL
    intro n hn
    simp only [g', Complex.norm_real, Real.norm_eq_abs]
    have hnonneg : 0 ≤ A n - B n := sub_nonneg.mpr (hAB n (hmem n hn))
    rw [abs_of_nonneg hnonneg]
    linarith [hhiA n, hloB n]
  have hadj : listAdjacentVariation g' ns ≤ 2 * L := by
    cases hs : ns with
    | nil => simp [listAdjacentVariation]; positivity
    | cons a tail =>
        have hsorted' : List.Pairwise (· ≤ ·) (a :: tail) := by simpa [hs] using hsorted
        have hvar := listAdjacentVariation_sub_monotone_le A B a tail
          hmonoA hmonoB hsorted'
        have hApath := listMonotoneIncrementSum_bounds A L hmonoA hhiA tail hsorted'
        have hBpath := listMonotoneIncrementSum_bounds B L hmonoB hhiB tail hsorted'
        have hAupper : listMonotoneIncrementSum A a tail ≤ L := by
          have := hApath.2
          linarith [hloA a]
        have hBupper : listMonotoneIncrementSum B a tail ≤ L := by
          have := hBpath.2
          linarith [hloB a]
        have htarget : listAdjacentVariation g' (a :: tail) ≤ 2 * L := by
          change listAdjacentVariation
            (fun n => ((A n - B n : ℝ) : ℂ)) (a :: tail) ≤ 2 * L
          calc
            listAdjacentVariation (fun n => ((A n - B n : ℝ) : ℂ)) (a :: tail) ≤
                listMonotoneIncrementSum A a tail + listMonotoneIncrementSum B a tail := hvar
            _ ≤ L + L := add_le_add hAupper hBupper
            _ = 2 * L := by ring
        simpa [hs] using htarget
  have hfinite : finiteOrderedTotalVariation F.1 g ≤ 3 * L := by
    rw [finiteOrderedTotalVariation_congr_on_logPhase F.1 g g'
      (fun n hn => hg n (F.2 n hn))]
    unfold finiteOrderedTotalVariation
    change listSupNorm g' ns + listAdjacentVariation g' ns ≤ 3 * L
    linarith
  exact ENNReal.ofReal_le_ofReal hfinite

private def dyadicOneEntry (lo : ℕ) (n : ℤ) : ℝ :=
  if (lo : ℤ) < n then 1 else 0

private def dyadicOneExit (hi : ℕ) (n : ℤ) : ℝ :=
  if (hi : ℤ) < n then 1 else 0

private def dyadicLogEntry (lo hi : ℕ) (n : ℤ) : ℝ :=
  if (lo : ℤ) < n then
    Real.log (min (max (1 : ℝ) (n : ℝ)) (hi : ℝ)) else 0

private def dyadicLogExit (hi : ℕ) (n : ℤ) : ℝ :=
  if (hi : ℤ) < n then Real.log (hi : ℝ) else 0

private theorem dyadicLowerNat_le_upperNat (j : ℕ) :
    dyadicLowerNat j ≤ dyadicUpperNat j := by
  cases j with
  | zero => norm_num [dyadicLowerNat, dyadicUpperNat]
  | succ j =>
      simp [dyadicLowerNat, dyadicUpperNat]
      calc
        2 ^ j ≤ 2 ^ j * 2 := Nat.le_mul_of_pos_right _ (by decide)
        _ = 2 ^ Nat.succ j := by rw [pow_succ]

private theorem dyadicFactorFunction_one_difference {X : ℝ} (z : ℝ)
    (j : DyadicIndex X) (n : ℕ) :
    dyadicFactorFunction z (.one j) n =
      dyadicOneEntry (dyadicLowerNat j.val.val) (n : ℤ) -
        dyadicOneExit (dyadicUpperNat j.val.val) (n : ℤ) := by
  let lo := dyadicLowerNat j.val.val
  let hi := dyadicUpperNat j.val.val
  have hlohi : lo ≤ hi := dyadicLowerNat_le_upperNat j.val.val
  by_cases hL : lo < n
  · by_cases hU : hi < n
    · simp [dyadicFactorFunction, dyadicOneFactor_apply, dyadicOneEntry,
        dyadicOneExit, inDyadicInterval, lo, hi, hL, hU]
    · simp [dyadicFactorFunction, dyadicOneFactor_apply, dyadicOneEntry,
        dyadicOneExit, inDyadicInterval, lo, hi, hL, hU]
  · have hU : ¬ hi < n := by
      intro h
      exact hL (lt_of_le_of_lt hlohi h)
    simp [dyadicFactorFunction, dyadicOneFactor_apply, dyadicOneEntry,
      dyadicOneExit, inDyadicInterval, lo, hi, hL, hU]

private theorem dyadicFactorFunction_log_difference {X : ℝ} (z : ℝ)
    (j : DyadicIndex X) (n : ℕ) :
    dyadicFactorFunction z (.logarithm j) n =
      dyadicLogEntry (dyadicLowerNat j.val.val) (dyadicUpperNat j.val.val)
          (n : ℤ) -
        dyadicLogExit (dyadicUpperNat j.val.val) (n : ℤ) := by
  let lo := dyadicLowerNat j.val.val
  let hi := dyadicUpperNat j.val.val
  have hlohi : lo ≤ hi := dyadicLowerNat_le_upperNat j.val.val
  have hhi1 : 1 ≤ hi := by
    dsimp [hi, dyadicUpperNat]
    exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hhiReal : 1 ≤ (hi : ℝ) := by exact_mod_cast hhi1
  by_cases hL : lo < n
  · by_cases hU : hi < n
    · have hUInt : (hi : ℤ) < (n : ℤ) := by exact_mod_cast hU
      have hLInt : (lo : ℤ) < (n : ℤ) := by
        exact_mod_cast lt_of_le_of_lt hlohi hU
      have hUReal : (hi : ℝ) < (n : ℝ) := by exact_mod_cast hU
      have hmax : max (1 : ℝ) (n : ℝ) = (n : ℝ) :=
        max_eq_right (hhiReal.trans hUReal.le)
      have hmin : min (n : ℝ) (hi : ℝ) = (hi : ℝ) :=
        min_eq_right hUReal.le
      simp [dyadicFactorFunction, dyadicLogFactor_apply, dyadicLogEntry,
        dyadicLogExit, inDyadicInterval, lo, hi, hL, hU, hLInt, hUInt,
        hmax, hmin]
    · have hUle : n ≤ hi := Nat.le_of_not_gt hU
      have hUReal : (n : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hUle
      have hmax : max (1 : ℝ) (n : ℝ) = (n : ℝ) := by
        apply max_eq_right
        have hn1 : 1 ≤ n := by omega
        exact_mod_cast hn1
      have hmin : min (n : ℝ) (hi : ℝ) = (n : ℝ) := min_eq_left hUReal
      simp [dyadicFactorFunction, dyadicLogFactor_apply, dyadicLogEntry,
        dyadicLogExit, inDyadicInterval, lo, hi, hL, hU, hmax, hmin]
  · have hU : ¬ hi < n := by
      intro h
      exact hL (lt_of_le_of_lt hlohi h)
    simp [dyadicFactorFunction, dyadicLogFactor_apply, dyadicLogEntry,
      dyadicLogExit, inDyadicInterval, lo, hi, hL, hU]

private theorem dyadicOneEntry_mono (lo : ℕ) :
    ∀ x y : ℤ, x ≤ y → dyadicOneEntry lo x ≤ dyadicOneEntry lo y := by
  intro x y hxy
  by_cases hx : (lo : ℤ) < x
  · have hy : (lo : ℤ) < y := lt_of_lt_of_le hx hxy
    simp [dyadicOneEntry, hx, hy]
  · by_cases hy : (lo : ℤ) < y
    · simp [dyadicOneEntry, hx, hy]
    · simp [dyadicOneEntry, hx, hy]

private theorem dyadicOneExit_mono (hi : ℕ) :
    ∀ x y : ℤ, x ≤ y → dyadicOneExit hi x ≤ dyadicOneExit hi y := by
  intro x y hxy
  by_cases hx : (hi : ℤ) < x
  · have hy : (hi : ℤ) < y := lt_of_lt_of_le hx hxy
    simp [dyadicOneExit, hx, hy]
  · by_cases hy : (hi : ℤ) < y
    · simp [dyadicOneExit, hx, hy]
    · simp [dyadicOneExit, hx, hy]

private theorem dyadicLogEntry_mono (lo hi : ℕ) :
    1 ≤ hi →
      ∀ x y : ℤ, x ≤ y → dyadicLogEntry lo hi x ≤ dyadicLogEntry lo hi y := by
  intro hhi x y hxy
  have hhiReal : 1 ≤ (hi : ℝ) := by exact_mod_cast hhi
  have hmax : max (1 : ℝ) (x : ℝ) ≤ max (1 : ℝ) (y : ℝ) :=
    max_le_max le_rfl (Int.cast_le.mpr hxy)
  have hmin : min (max (1 : ℝ) (x : ℝ)) (hi : ℝ) ≤
      min (max (1 : ℝ) (y : ℝ)) (hi : ℝ) := min_le_min hmax le_rfl
  by_cases hx : (lo : ℤ) < x
  · have hy : (lo : ℤ) < y := lt_of_lt_of_le hx hxy
    simp only [dyadicLogEntry, hx, hy]
    exact Real.log_le_log (by positivity) hmin
  · by_cases hy : (lo : ℤ) < y
    · have hminPos : 1 ≤ min (max (1 : ℝ) (y : ℝ)) (hi : ℝ) :=
        le_min (le_max_left _ _) hhiReal
      simp [dyadicLogEntry, hx, hy]
      exact Real.log_nonneg hminPos
    · simp [dyadicLogEntry, hx, hy]

private theorem dyadicLogEntry_bounds (lo hi : ℕ) (L : ℝ)
    (hhi : 1 ≤ hi) (hloghi : Real.log (hi : ℝ) ≤ L) (n : ℤ) :
    0 ≤ dyadicLogEntry lo hi n ∧ dyadicLogEntry lo hi n ≤ L := by
  have hhiReal : 1 ≤ (hi : ℝ) := by exact_mod_cast hhi
  by_cases hn : (lo : ℤ) < n
  · have hminPos : 1 ≤ min (max (1 : ℝ) (n : ℝ)) (hi : ℝ) :=
      le_min (le_max_left _ _) hhiReal
    simp only [dyadicLogEntry, hn]
    constructor
    · exact Real.log_nonneg hminPos
    · exact (Real.log_le_log (by positivity) (min_le_right _ _)).trans hloghi
  · simp only [dyadicLogEntry, hn, if_false]
    exact ⟨le_rfl, (Real.log_natCast_nonneg hi).trans hloghi⟩

private theorem dyadicLogExit_mono (hi : ℕ) :
    0 ≤ Real.log (hi : ℝ) →
      ∀ x y : ℤ, x ≤ y → dyadicLogExit hi x ≤ dyadicLogExit hi y := by
  intro hlog x y hxy
  by_cases hx : (hi : ℤ) < x
  · have hy : (hi : ℤ) < y := lt_of_lt_of_le hx hxy
    simp [dyadicLogExit, hx, hy]
  · by_cases hy : (hi : ℤ) < y
    · simp [dyadicLogExit, hx, hy, hlog]
    · simp [dyadicLogExit, hx, hy]

private theorem dyadicLogExit_bounds (hi : ℕ) (L : ℝ)
    (hloghi : 0 ≤ Real.log (hi : ℝ))
    (hloghiL : Real.log (hi : ℝ) ≤ L) (n : ℤ) :
    0 ≤ dyadicLogExit hi n ∧ dyadicLogExit hi n ≤ L := by
  by_cases hn : (hi : ℤ) < n
  · simp [dyadicLogExit, hn, hloghi, hloghiL]
  · simp only [dyadicLogExit, hn, if_false]
    exact ⟨le_rfl, (Real.log_natCast_nonneg hi).trans hloghiL⟩

private theorem dyadicLogExit_le_entry (lo hi : ℕ)
    (hlohi : lo ≤ hi) (hhi : 1 ≤ hi) (n : ℤ) :
    dyadicLogExit hi n ≤ dyadicLogEntry lo hi n := by
  by_cases hn : (hi : ℤ) < n
  · have hlo : (lo : ℤ) < n := lt_of_le_of_lt (by exact_mod_cast hlohi) hn
    have hhiReal : 1 ≤ (hi : ℝ) := by exact_mod_cast hhi
    have hhiN : (hi : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt hn)
    have hmax : max (1 : ℝ) (n : ℝ) = (n : ℝ) := max_eq_right (hhiReal.trans hhiN)
    have hmin : min (n : ℝ) (hi : ℝ) = (hi : ℝ) := min_eq_right hhiN
    simp [dyadicLogExit, dyadicLogEntry, hn, hlo, hmax, hmin]
  · simp only [dyadicLogExit, hn, if_false]
    exact (dyadicLogEntry_bounds lo hi (Real.log (hi : ℝ)) hhi le_rfl n).1

private theorem dyadicOneExit_le_entry (lo hi : ℕ)
    (hlohi : lo ≤ hi) (n : ℤ) : dyadicOneExit hi n ≤ dyadicOneEntry lo n := by
  by_cases hn : (hi : ℤ) < n
  · have hlo : (lo : ℤ) < n := lt_of_le_of_lt (by exact_mod_cast hlohi) hn
    simp [dyadicOneExit, dyadicOneEntry, hn, hlo]
  · simp only [dyadicOneExit, hn, if_false]
    unfold dyadicOneEntry
    split_ifs <;> norm_num

private theorem decompositionDType_dominates_twelve_logX {X : ℝ}
    (hX : 3 ≤ X) : 12 * Real.log X ≤ decompositionDType X := by
  have hlogX : 1 < Real.log X := log_X_gt_one hX
  have hlogNonneg : 0 ≤ Real.log X := le_trans (by norm_num) hlogX.le
  have hC : 12 ≤ decompositionC := by
    dsimp [decompositionC]
    have h2 : 12 ≤ (2 : ℝ) ^ 200 := by norm_num
    have h81 : 1 ≤ (81 : ℝ) ^ 160000 :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 81)
    calc
      12 ≤ (2 : ℝ) ^ 200 := h2
      _ = (2 : ℝ) ^ 200 * 1 := by ring
      _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
        mul_le_mul_of_nonneg_left h81 (by positivity)
  have hpow : 1 ≤ (Real.log X) ^ 160099 :=
    one_le_pow₀ hlogX.le
  have hlogPow : Real.log X ≤ (Real.log X) ^ 160099 * Real.log X := by
    calc
      Real.log X = 1 * Real.log X := by ring
      _ ≤ (Real.log X) ^ 160099 * Real.log X :=
        mul_le_mul_of_nonneg_right hpow hlogNonneg
  have hexp : (Real.log X) ^ 160100 =
      (Real.log X) ^ 160099 * Real.log X := by
    rw [show 160100 = 160099 + 1 by norm_num, pow_add, pow_one]
  change 12 * Real.log X ≤
    decompositionC * (Real.log X) ^ decompositionB
  rw [show decompositionB = 160100 by rfl, hexp]
  calc
    12 * Real.log X ≤ 12 * ((Real.log X) ^ 160099 * Real.log X) :=
      mul_le_mul_of_nonneg_left hlogPow (by norm_num)
    _ ≤ decompositionC * ((Real.log X) ^ 160099 * Real.log X) :=
      mul_le_mul_of_nonneg_right hC
        (mul_nonneg (pow_nonneg hlogNonneg _) hlogNonneg)

private theorem complexPositiveIntegerResidueVariation_one_eq
    (f : ComplexPositiveIntegerFunction) :
    complexPositiveIntegerResidueVariation f 1 (by decide) =
      orderedTotalVariation {n : ℤ | 0 < n}
        (complexPositiveIntegerZeroExtension f) := by
  have hclass : integerResidueClass 1 0 = Set.univ := by
    ext n
    constructor
    · intro _
      simp
    · intro _
      refine ⟨n, ?_⟩
      simp [integerResidueClass]
  unfold complexPositiveIntegerResidueVariation positiveIntegerResidueTotalVariation
    residueClassTotalVariation
  simp only [Finset.range_one, Finset.sum_singleton]
  rw [hclass]
  simp

/-- The constant-one factor on a dyadic interval has the exact positive-
integer residue variation required by the arithmetic type bound. -/
theorem dyadicOneFactor_residueVariation_bound {X : ℝ} (hX : 3 ≤ X)
    (z : ℝ) (j : DyadicIndex X) :
    complexPositiveIntegerResidueVariation
      (fun n : PositiveInteger => dyadicFactorComplexFunction z (.one j) n.1)
      1 (by decide) ≤ ENNReal.ofReal (decompositionDType X) := by
  let lo := dyadicLowerNat j.val.val
  let hi := dyadicUpperNat j.val.val
  let L := Real.log (8 * X)
  let A : ℤ → ℝ := dyadicOneEntry lo
  let B : ℤ → ℝ := dyadicOneExit hi
  have hlohi : lo ≤ hi := dyadicLowerNat_le_upperNat j.val.val
  have hL : 0 ≤ L := by dsimp [L]; linarith [log_eightX_gt_one hX]
  have hLgt : 1 < L := by dsimp [L]; exact log_eightX_gt_one hX
  have hmonoA : ∀ x y, x ≤ y → A x ≤ A y := by
    simpa [A] using dyadicOneEntry_mono lo
  have hmonoB : ∀ x y, x ≤ y → B x ≤ B y := by
    simpa [B] using dyadicOneExit_mono hi
  have hAlo : ∀ n, 0 ≤ A n := by
    intro n
    unfold A dyadicOneEntry
    split_ifs <;> norm_num
  have hBlo : ∀ n, 0 ≤ B n := by
    intro n
    unfold B dyadicOneExit
    split_ifs <;> norm_num
  have hAhi : ∀ n, A n ≤ 1 := by
    intro n
    unfold A dyadicOneEntry
    split_ifs <;> norm_num
  have hBhi : ∀ n, B n ≤ 1 := by
    intro n
    unfold B dyadicOneExit
    split_ifs <;> norm_num
  have hAB : ∀ n, B n ≤ A n := by
    intro n
    simpa [A, B] using dyadicOneExit_le_entry lo hi hlohi n
  have hAhiL : ∀ n, A n ≤ L := by
    intro n
    exact (hAhi n).trans (le_of_lt hLgt)
  have hBhiL : ∀ n, B n ≤ L := by
    intro n
    exact (hBhi n).trans (le_of_lt hLgt)
  let P : Set ℤ := {n | 0 < n}
  let g : ℤ → ℂ := complexPositiveIntegerZeroExtension
    (fun n : PositiveInteger => dyadicFactorComplexFunction z (.one j) n.1)
  have hg : ∀ n ∈ P, g n = ((A n - B n : ℝ) : ℂ) := by
    intro n hn
    change 0 < n at hn
    have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
    have hzext :
        complexPositiveIntegerZeroExtension
            (fun m : PositiveInteger => dyadicFactorComplexFunction z (.one j) m.1) n =
          dyadicFactorComplexFunction z (.one j) n.toNat := by
      simp [complexPositiveIntegerZeroExtension, hn]
    change complexPositiveIntegerZeroExtension
        (fun m : PositiveInteger => dyadicFactorComplexFunction z (.one j) m.1) n = _
    rw [hzext]
    change ((dyadicFactorFunction z (.one j) n.toNat : ℝ) : ℂ) = _
    rw [dyadicFactorFunction_one_difference, hncast]
  have htv := orderedTotalVariation_sub_monotone_le P g A B L hL
    hmonoA hmonoB hAlo hBlo
    hAhiL hBhiL (fun n _ => hAB n) hg
  have hsmall : 3 * L ≤ decompositionDType X := by
    dsimp [L]
    calc
      3 * Real.log (8 * X) ≤ 3 * (4 * Real.log X) :=
        mul_le_mul_of_nonneg_left (log_eightX_le_four_logX hX) (by norm_num)
      _ = 12 * Real.log X := by ring
      _ ≤ decompositionDType X := decompositionDType_dominates_twelve_logX hX
  rw [complexPositiveIntegerResidueVariation_one_eq]
  change orderedTotalVariation P g ≤ ENNReal.ofReal (decompositionDType X)
  exact htv.trans (ENNReal.ofReal_le_ofReal hsmall)

/-- The logarithmic factor on a dyadic interval has the exact positive-
integer residue variation required by the arithmetic type bound. -/
theorem dyadicLogFactor_residueVariation_bound {X : ℝ} (hX : 3 ≤ X)
    (z : ℝ) (j : DyadicIndex X) :
    complexPositiveIntegerResidueVariation
      (fun n : PositiveInteger => dyadicFactorComplexFunction z (.logarithm j) n.1)
      1 (by decide) ≤ ENNReal.ofReal (decompositionDType X) := by
  let lo := dyadicLowerNat j.val.val
  let hi := dyadicUpperNat j.val.val
  let L := Real.log (8 * X)
  let A : ℤ → ℝ := dyadicLogEntry lo hi
  let B : ℤ → ℝ := dyadicLogExit hi
  have hlohi : lo ≤ hi := dyadicLowerNat_le_upperNat j.val.val
  have hhi : 1 ≤ hi := by
    dsimp [hi, dyadicUpperNat]
    exact one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hhiReal : 0 < (hi : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hhi)
  have hloghi : 0 ≤ Real.log (hi : ℝ) := Real.log_natCast_nonneg _
  have hupper : (hi : ℝ) ≤ 8 * X := dyadicUpperNat_le_eightX hX j
  have hloghiL : Real.log (hi : ℝ) ≤ L := by
    dsimp [L]
    exact Real.log_le_log hhiReal hupper
  have hL : 0 ≤ L := by dsimp [L]; linarith [log_eightX_gt_one hX]
  have hmonoA : ∀ x y, x ≤ y → A x ≤ A y := by
    simpa [A] using dyadicLogEntry_mono lo hi hhi
  have hmonoB : ∀ x y, x ≤ y → B x ≤ B y := by
    simpa [B] using dyadicLogExit_mono hi hloghi
  have hAlo : ∀ n, 0 ≤ A n := by
    intro n
    exact (dyadicLogEntry_bounds lo hi L hhi hloghiL n).1
  have hBlo : ∀ n, 0 ≤ B n := by
    intro n
    exact (dyadicLogExit_bounds hi L hloghi hloghiL n).1
  have hAhi : ∀ n, A n ≤ L := by
    intro n
    exact (dyadicLogEntry_bounds lo hi L hhi hloghiL n).2
  have hBhi : ∀ n, B n ≤ L := by
    intro n
    exact (dyadicLogExit_bounds hi L hloghi hloghiL n).2
  have hAB : ∀ n, B n ≤ A n := by
    intro n
    simpa [A, B] using dyadicLogExit_le_entry lo hi hlohi hhi n
  let P : Set ℤ := {n | 0 < n}
  let g : ℤ → ℂ := complexPositiveIntegerZeroExtension
    (fun n : PositiveInteger => dyadicFactorComplexFunction z (.logarithm j) n.1)
  have hg : ∀ n ∈ P, g n = ((A n - B n : ℝ) : ℂ) := by
    intro n hn
    change 0 < n at hn
    have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
    have hzext :
        complexPositiveIntegerZeroExtension
            (fun m : PositiveInteger => dyadicFactorComplexFunction z (.logarithm j) m.1) n =
          dyadicFactorComplexFunction z (.logarithm j) n.toNat := by
      simp [complexPositiveIntegerZeroExtension, hn]
    change complexPositiveIntegerZeroExtension
        (fun m : PositiveInteger => dyadicFactorComplexFunction z (.logarithm j) m.1) n = _
    rw [hzext]
    change ((dyadicFactorFunction z (.logarithm j) n.toNat : ℝ) : ℂ) = _
    rw [dyadicFactorFunction_log_difference, hncast]
  have htv := orderedTotalVariation_sub_monotone_le P g A B L hL
    hmonoA hmonoB hAlo hBlo hAhi hBhi (fun n _ => hAB n) hg
  have hsmall : 3 * L ≤ decompositionDType X := by
    dsimp [L]
    calc
      3 * Real.log (8 * X) ≤ 3 * (4 * Real.log X) :=
        mul_le_mul_of_nonneg_left (log_eightX_le_four_logX hX) (by norm_num)
      _ = 12 * Real.log X := by ring
      _ ≤ decompositionDType X := decompositionDType_dominates_twelve_logX hX
  rw [complexPositiveIntegerResidueVariation_one_eq]
  change orderedTotalVariation P g ≤ ENNReal.ofReal (decompositionDType X)
  exact htv.trans (ENNReal.ofReal_le_ofReal hsmall)

/-- Every non-Möbius tagged dyadic factor obeys the exact modulus-one
variation bound in `lucomb:group-bounds`. -/
theorem nonMobiusDyadicFactor_residueVariation_bound {X : ℝ}
    (hX : 3 ≤ X) (z : ℝ) (f : DyadicArithmeticFactor X)
    (hnonmobius : ∀ j, f ≠ .mobius j) :
    complexPositiveIntegerResidueVariation
      (fun n : PositiveInteger => dyadicFactorComplexFunction z f n.1)
      1 (by decide) ≤ ENNReal.ofReal (decompositionDType X) := by
  cases f with
  | one j => exact dyadicOneFactor_residueVariation_bound hX z j
  | logarithm j => exact dyadicLogFactor_residueVariation_bound hX z j
  | mobius j => exact (hnonmobius j rfl).elim
end

end FractionalPrimes.Literature.Uniformity.Combinatorics

end

#print axioms FractionalPrimes.Literature.Uniformity.Combinatorics.groupedDyadicFactor_momentBounds
#print axioms FractionalPrimes.Literature.Uniformity.Combinatorics.dyadicOneFactor_residueVariation_bound
#print axioms FractionalPrimes.Literature.Uniformity.Combinatorics.dyadicLogFactor_residueVariation_bound
#print axioms FractionalPrimes.Literature.Uniformity.Combinatorics.nonMobiusDyadicFactor_residueVariation_bound
