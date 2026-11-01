module

public import FractionalPrimes.Literature.Uniformity.ArithmeticGrouping
public import FractionalPrimes.Literature.Uniformity.ArithmeticGroupedFactorBounds
public import FractionalPrimes.Literature.Uniformity.ArithmeticNormalizedExponents
public import FractionalPrimes.Literature.Uniformity.ArithmeticTypes
public import Mathlib.Tactic

/-!
# Exact elementary arithmetic type decomposition

This file formalizes blueprint item `lucomb:type-decomposition`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity.Combinatorics

open FractionalPrimes.Literature.Uniformity
open ArithmeticFunction
open scoped ENNReal
open scoped BigOperators

noncomputable section

/-- The complex positive-integer function obtained from a real dyadic
convolution product. -/
def dyadicConvolutionPositiveComplex {X : ℝ} (z : ℝ)
    (fs : List (DyadicArithmeticFactor X)) : ComplexPositiveIntegerFunction :=
  fun n => ((dyadicConvolutionFactors z fs n.1 : ℝ) : ℂ)

private theorem dyadicFactorIntervalSupport {X z : ℝ}
    (f : DyadicArithmeticFactor X) {n : ℕ}
    (hne : dyadicFactorFunction z f n ≠ 0) :
    dyadicFactorScale f < (n : ℝ) ∧
      (n : ℝ) ≤ 2 * dyadicFactorScale f := by
  cases f with
  | one j =>
      have hInt : inDyadicInterval j.val.val n := by
        by_contra hInt
        apply hne
        simp [dyadicFactorFunction, dyadicOneFactor_apply, hInt]
      by_cases hj : j.val.val = 0
      · have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hInt.1
        have hnle : n ≤ 1 := by
          simpa [inDyadicInterval, dyadicUpperNat, hj] using hInt.2
        have hn : n = 1 := by omega
        simp [dyadicFactorScale, dyadicScale, hj, hn] <;> norm_num
      · have hscale : dyadicFactorScale (.one j) =
            (dyadicLowerNat j.val.val : ℝ) := by
          simp [dyadicFactorScale, dyadicScale, dyadicLowerNat, hj]
        have hupper : (dyadicUpperNat j.val.val : ℝ) =
            2 * dyadicFactorScale (.one j) := by
          have hpred := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hj)
          have hpow : (2 : ℝ) ^ j.val.val =
              2 * (2 : ℝ) ^ j.val.val.pred := by
            calc
              (2 : ℝ) ^ j.val.val = (2 : ℝ) ^ (j.val.val.pred + 1) :=
                congrArg (fun m : ℕ => (2 : ℝ) ^ m) hpred.symm
              _ = (2 : ℝ) ^ j.val.val.pred * 2 := by rw [pow_succ]
              _ = 2 * (2 : ℝ) ^ j.val.val.pred := by ring
          rw [dyadicUpperNat, Nat.cast_pow, Nat.cast_ofNat, hpow]
          simpa [dyadicFactorScale, dyadicScale, hj]
        constructor
        · rw [hscale]
          exact_mod_cast hInt.1
        · rw [← hupper]
          exact_mod_cast hInt.2
  | logarithm j =>
      have hInt : inDyadicInterval j.val.val n := by
        by_contra hInt
        apply hne
        simp [dyadicFactorFunction, dyadicLogFactor_apply, hInt]
      have hbase : dyadicFactorScale (.logarithm j) = dyadicScale j.val.val := rfl
      rw [hbase]
      by_cases hj : j.val.val = 0
      · have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hInt.1
        have hnle : n ≤ 1 := by
          simpa [inDyadicInterval, dyadicUpperNat, hj] using hInt.2
        have hn : n = 1 := by omega
        simp [dyadicScale, hj, hn] <;> norm_num
      · have hscale : dyadicScale j.val.val =
            (dyadicLowerNat j.val.val : ℝ) := by
          simp [dyadicScale, dyadicLowerNat, hj]
        have hupper : (dyadicUpperNat j.val.val : ℝ) =
            2 * dyadicScale j.val.val := by
          have hpred := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hj)
          have hpow : (2 : ℝ) ^ j.val.val =
              2 * (2 : ℝ) ^ j.val.val.pred := by
            calc
              (2 : ℝ) ^ j.val.val = (2 : ℝ) ^ (j.val.val.pred + 1) :=
                congrArg (fun m : ℕ => (2 : ℝ) ^ m) hpred.symm
              _ = (2 : ℝ) ^ j.val.val.pred * 2 := by rw [pow_succ]
              _ = 2 * (2 : ℝ) ^ j.val.val.pred := by ring
          rw [dyadicUpperNat, Nat.cast_pow, Nat.cast_ofNat, hpow]
          simpa [dyadicScale, hj]
        constructor
        · rw [hscale]
          exact_mod_cast hInt.1
        · rw [← hupper]
          exact_mod_cast hInt.2
  | mobius j =>
      have hInt : inDyadicInterval j.val.val n := by
        by_contra hInt
        apply hne
        simp [dyadicFactorFunction, dyadicMobiusFactor_apply, hInt]
      have hbase : dyadicFactorScale (.mobius j) = dyadicScale j.val.val := rfl
      rw [hbase]
      by_cases hj : j.val.val = 0
      · have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hInt.1
        have hnle : n ≤ 1 := by
          simpa [inDyadicInterval, dyadicUpperNat, hj] using hInt.2
        have hn : n = 1 := by omega
        simp [dyadicScale, hj, hn] <;> norm_num
      · have hscale : dyadicScale j.val.val =
            (dyadicLowerNat j.val.val : ℝ) := by
          simp [dyadicScale, dyadicLowerNat, hj]
        have hupper : (dyadicUpperNat j.val.val : ℝ) =
            2 * dyadicScale j.val.val := by
          have hpred := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hj)
          have hpow : (2 : ℝ) ^ j.val.val =
              2 * (2 : ℝ) ^ j.val.val.pred := by
            calc
              (2 : ℝ) ^ j.val.val = (2 : ℝ) ^ (j.val.val.pred + 1) :=
                congrArg (fun m : ℕ => (2 : ℝ) ^ m) hpred.symm
              _ = (2 : ℝ) ^ j.val.val.pred * 2 := by rw [pow_succ]
              _ = 2 * (2 : ℝ) ^ j.val.val.pred := by ring
          rw [dyadicUpperNat, Nat.cast_pow, Nat.cast_ofNat, hpow]
          simpa [dyadicScale, hj]
        constructor
        · rw [hscale]
          exact_mod_cast hInt.1
        · rw [← hupper]
          exact_mod_cast hInt.2

private theorem dyadicFactorScale_pos_local {X : ℝ}
    (f : DyadicArithmeticFactor X) : 0 < dyadicFactorScale f := by
  cases f with
  | one j =>
      by_cases hj : j.val.val = 0 <;>
        simp [dyadicFactorScale, dyadicScale, hj] <;> positivity
  | logarithm j =>
      by_cases hj : j.val.val = 0 <;>
        simp [dyadicFactorScale, dyadicScale, hj] <;> positivity
  | mobius j =>
      by_cases hj : j.val.val = 0 <;>
        simp [dyadicFactorScale, dyadicScale, hj] <;> positivity

private theorem dyadicFactorScaleProduct_pos_local {X : ℝ}
    (fs : List (DyadicArithmeticFactor X)) : 0 < dyadicFactorScaleProduct fs := by
  induction fs with
  | nil => simp [dyadicFactorScaleProduct]
  | cons f fs ih =>
      simp only [dyadicFactorScaleProduct, List.map_cons, List.prod_cons]
      exact mul_pos (dyadicFactorScale_pos_local f) ih

private theorem arithmeticFunction_mul_apply_ne_zero_local
    {f g : ArithmeticFunction ℝ} {n : ℕ} (hne : (f * g) n ≠ 0) :
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

private theorem dyadicConvolutionFactors_support_bounds_local {X z : ℝ}
    (fs : List (DyadicArithmeticFactor X)) (hfs : fs ≠ []) {n : ℕ}
    (hne : dyadicConvolutionFactors z fs n ≠ 0) :
    dyadicFactorScaleProduct fs < (n : ℝ) ∧
      (n : ℝ) ≤ (2 : ℝ) ^ fs.length * dyadicFactorScaleProduct fs := by
  induction fs generalizing n with
  | nil => contradiction
  | cons f fs ih =>
      cases fs with
      | nil =>
          have hfactor : dyadicFactorFunction z f n ≠ 0 := by
            simpa [dyadicConvolutionFactors] using hne
          have hb := dyadicFactorIntervalSupport f hfactor
          simpa [dyadicFactorScaleProduct, dyadicConvolutionFactors] using hb
      | cons g gs =>
          have hmul :
              (dyadicFactorFunction z f * dyadicConvolutionFactors z (g :: gs)) n ≠ 0 := by
            simpa [dyadicConvolutionFactors] using hne
          obtain ⟨x, hx, hfirst, htail⟩ :=
            arithmeticFunction_mul_apply_ne_zero_local hmul
          have hfirstBounds := dyadicFactorIntervalSupport f hfirst
          have htailBounds := ih (by simp) htail
          have hpair := (Nat.mem_divisorsAntidiagonal.mp hx).1
          have hpairReal : (n : ℝ) = (x.1 : ℝ) * (x.2 : ℝ) := by
            exact_mod_cast hpair.symm
          have hx1pos : 0 < (x.1 : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero
              (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx)
          have hscalePos : 0 < dyadicFactorScaleProduct (g :: gs) :=
            dyadicFactorScaleProduct_pos_local (g :: gs)
          have hlow : dyadicFactorScale f * dyadicFactorScaleProduct (g :: gs) <
              (x.1 : ℝ) * (x.2 : ℝ) := by
            calc
              dyadicFactorScale f * dyadicFactorScaleProduct (g :: gs) <
                  (x.1 : ℝ) * dyadicFactorScaleProduct (g :: gs) :=
                mul_lt_mul_of_pos_right hfirstBounds.1 hscalePos
              _ < (x.1 : ℝ) * (x.2 : ℝ) :=
                mul_lt_mul_of_pos_left htailBounds.1 hx1pos
          have hupp : (x.1 : ℝ) * (x.2 : ℝ) ≤
              (2 : ℝ) ^ ((g :: gs).length + 1) *
                (dyadicFactorScale f * dyadicFactorScaleProduct (g :: gs)) := by
            calc
              (x.1 : ℝ) * (x.2 : ℝ) ≤
                  (2 * dyadicFactorScale f) * (x.2 : ℝ) :=
                mul_le_mul_of_nonneg_right hfirstBounds.2 (by positivity)
              _ ≤ (2 * dyadicFactorScale f) *
                    ((2 : ℝ) ^ (g :: gs).length * dyadicFactorScaleProduct (g :: gs)) :=
                mul_le_mul_of_nonneg_left htailBounds.2
                  (mul_nonneg (by norm_num) (dyadicFactorScale_pos_local f).le)
              _ = (2 : ℝ) ^ ((g :: gs).length + 1) *
                    (dyadicFactorScale f * dyadicFactorScaleProduct (g :: gs)) := by
                rw [pow_succ]
                ring
          constructor
          · rw [dyadicFactorScaleProduct, List.map_cons, List.prod_cons]
            exact hlow.trans_eq hpairReal.symm
          · rw [dyadicFactorScaleProduct, List.map_cons, List.prod_cons,
              List.length_cons]
            exact hpairReal ▸ hupp

private theorem complexConvolution_ofRealArithmeticFunctions
    (f g : ArithmeticFunction ℝ) (n : PositiveInteger) :
    complexPositiveDirichletConvolution
        (fun m : PositiveInteger => ((f m.1 : ℝ) : ℂ))
        (fun m : PositiveInteger => ((g m.1 : ℝ) : ℂ)) n =
      (((f * g) n.1 : ℝ) : ℂ) := by
  have hdiv : (f * g) n.1 =
      ∑ d ∈ n.1.divisors, f d * g (n.1 / d) := by
    rw [ArithmeticFunction.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal
      (f := fun a b => f a * g b)]
  rw [complexPositiveDirichletConvolution_eq_divisor_sum, hdiv,
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp [complexDivisorConvolutionSummand, hd]

theorem dyadicConvolutionPositiveComplex_append {X : ℝ} (z : ℝ)
    (fs gs : List (DyadicArithmeticFactor X)) :
    complexPositiveDirichletConvolution
        (dyadicConvolutionPositiveComplex z fs)
        (dyadicConvolutionPositiveComplex z gs) =
      dyadicConvolutionPositiveComplex z (fs ++ gs) := by
  funext n
  change complexPositiveDirichletConvolution
      (fun m : PositiveInteger => ((dyadicConvolutionFactors z fs m.1 : ℝ) : ℂ))
      (fun m : PositiveInteger => ((dyadicConvolutionFactors z gs m.1 : ℝ) : ℂ)) n =
    ((dyadicConvolutionFactors z (fs ++ gs) n.1 : ℝ) : ℂ)
  rw [complexConvolution_ofRealArithmeticFunctions
    (dyadicConvolutionFactors z fs) (dyadicConvolutionFactors z gs) n]
  simp [dyadicConvolutionFactors, List.map_append, List.prod_append]

/-- The factors whose original labels lie in a selected finite set of
positions.  The `Fin` labels retain multiplicity when equal factors occur. -/
def selectedDyadicFactors {X : ℝ} (fs : List (DyadicArithmeticFactor X))
    (s : Finset (Fin fs.length)) : List (DyadicArithmeticFactor X) :=
  s.toList.map fs.get

@[simp]
theorem selectedDyadicFactors_length {X : ℝ}
    (fs : List (DyadicArithmeticFactor X)) (s : Finset (Fin fs.length)) :
    (selectedDyadicFactors fs s).length = s.card := by
  simp [selectedDyadicFactors]

/-- A selected convolution group is the corresponding finite product of
the original labeled factors. -/
theorem dyadicConvolutionFactors_selected {X : ℝ} (z : ℝ)
    (fs : List (DyadicArithmeticFactor X)) (s : Finset (Fin fs.length)) :
    dyadicConvolutionFactors z (selectedDyadicFactors fs s) =
      ∏ i ∈ s, dyadicFactorFunction z (fs.get i) := by
  classical
  simp [dyadicConvolutionFactors, selectedDyadicFactors,
    Finset.prod_map_toList]

private theorem dyadicFactorScaleProduct_selected {X : ℝ}
    (fs : List (DyadicArithmeticFactor X)) (s : Finset (Fin fs.length)) :
    dyadicFactorScaleProduct (selectedDyadicFactors fs s) =
      ∏ i ∈ s, dyadicFactorScale (fs.get i) := by
  simp [dyadicFactorScaleProduct, selectedDyadicFactors,
    Finset.prod_map_toList]

/-- The product of scales in a labeled group has the exact power comparison
needed for grouped support. -/
private theorem selectedDyadicScaleProduct_bounds {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (fs : List (DyadicArithmeticFactor X))
    (s : Finset (Fin fs.length)) (α : Fin fs.length → ℝ)
    (hcount : s.card ≤ 20)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i) :
    ((2 : ℝ) ^ 460)⁻¹ * X ^ (∑ i ∈ s, α i) ≤
        ∏ i ∈ s, dyadicFactorScale (fs.get i) ∧
      ∏ i ∈ s, dyadicFactorScale (fs.get i) ≤
        (2 : ℝ) ^ 460 * X ^ (∑ i ∈ s, α i) := by
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) hX
  have hCpos : 0 < normalizedExponentConstant := by
    norm_num [normalizedExponentConstant]
  have hCle : 1 ≤ normalizedExponentConstant := by
    norm_num [normalizedExponentConstant]
  have hcard : s.card ≤ fs.length := by
    calc
      s.card ≤ (Finset.univ : Finset (Fin fs.length)).card :=
        Finset.card_le_card (Finset.subset_univ s)
      _ = fs.length := by simp
  have hprodLo :
      (∏ i ∈ s, normalizedExponentConstant⁻¹ * X ^ α i) ≤
        ∏ i ∈ s, dyadicFactorScale (fs.get i) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact mul_nonneg (inv_pos.mpr hCpos).le (Real.rpow_nonneg hXpos.le _)
    intro i hi
    exact (hscale i).1
  have hprodHi :
      (∏ i ∈ s, dyadicFactorScale (fs.get i)) ≤
        ∏ i ∈ s, normalizedExponentConstant * X ^ α i := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact (dyadicFactorScale_pos_local (fs.get i)).le
    intro i hi
    exact (hscale i).2
  have hbaseLo :
      (∏ i ∈ s, normalizedExponentConstant⁻¹ * X ^ α i) =
        normalizedExponentConstant⁻¹ ^ s.card * X ^ (∑ i ∈ s, α i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const,
      ← Real.rpow_sum_of_pos hXpos]
  have hbaseHi :
      (∏ i ∈ s, normalizedExponentConstant * X ^ α i) =
        normalizedExponentConstant ^ s.card * X ^ (∑ i ∈ s, α i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const,
      ← Real.rpow_sum_of_pos hXpos]
  have hrecippow : normalizedExponentConstant⁻¹ ^ 20 ≤
      normalizedExponentConstant⁻¹ ^ s.card :=
    pow_le_pow_of_le_one (by positivity)
      (show normalizedExponentConstant⁻¹ ≤ 1 by norm_num [normalizedExponentConstant])
      hcount
  have hrecippow_eq : normalizedExponentConstant⁻¹ ^ 20 =
      ((2 : ℝ) ^ 460)⁻¹ := by
    rw [normalizedExponentConstant, ← inv_pow, ← pow_mul]
    norm_num [one_div_pow]
  have hpow : normalizedExponentConstant ^ s.card ≤
      normalizedExponentConstant ^ 20 :=
    pow_le_pow_right₀ hCle hcount
  have hpow_eq : normalizedExponentConstant ^ 20 = (2 : ℝ) ^ 460 := by
    rw [normalizedExponentConstant, ← pow_mul]
  constructor
  · rw [hbaseLo] at hprodLo
    calc
      ((2 : ℝ) ^ 460)⁻¹ * X ^ (∑ i ∈ s, α i) ≤
          normalizedExponentConstant⁻¹ ^ s.card * X ^ (∑ i ∈ s, α i) :=
        mul_le_mul_of_nonneg_right
          (by rw [← hrecippow_eq]; exact hrecippow)
          (Real.rpow_nonneg hXpos.le _)
      _ ≤ ∏ i ∈ s, dyadicFactorScale (fs.get i) := hprodLo
  · rw [hbaseHi] at hprodHi
    calc
      ∏ i ∈ s, dyadicFactorScale (fs.get i) ≤
          normalizedExponentConstant ^ s.card * X ^ (∑ i ∈ s, α i) := hprodHi
      _ ≤ (2 : ℝ) ^ 460 * X ^ (∑ i ∈ s, α i) := by
        rw [← hpow_eq]
        exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hXpos.le _)

/-- Exact support interval for a nonempty labeled group, with the component
coefficient attached to that group. -/
private theorem groupedDyadicFactor_supported_power_local {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (z : ℝ) (c : ℂ)
    (fs : List (DyadicArithmeticFactor X)) (s : Finset (Fin fs.length))
    (α : Fin fs.length → ℝ) (hs : s.Nonempty) (hcount : s.card ≤ 20)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i)
    (n : PositiveInteger)
    (hne : groupedDyadicFactor z c (selectedDyadicFactors fs s) n ≠ 0) :
    ((2 : ℝ) ^ 460)⁻¹ * X ^ (∑ i ∈ s, α i) ≤ (n.1 : ℝ) ∧
      (n.1 : ℝ) ≤ (2 : ℝ) ^ 480 * X ^ (∑ i ∈ s, α i) := by
  have hlist : selectedDyadicFactors fs s ≠ [] := by
    apply List.length_pos_iff_ne_nil.mp
    rw [selectedDyadicFactors_length]
    exact Finset.card_pos.mpr hs
  have hconv : dyadicConvolutionFactors z (selectedDyadicFactors fs s) n.1 ≠ 0 := by
    intro hzero
    apply hne
    simp [groupedDyadicFactor, hzero]
  have hsupport := dyadicConvolutionFactors_support_bounds_local
    (selectedDyadicFactors fs s) hlist hconv
  have hscales := selectedDyadicScaleProduct_bounds hX fs s α hcount hscale
  rw [dyadicFactorScaleProduct_selected] at hsupport
  have hlen : (selectedDyadicFactors fs s).length ≤ 20 := by
    rw [selectedDyadicFactors_length]
    exact hcount
  have hpow : (2 : ℝ) ^ (selectedDyadicFactors fs s).length ≤
      (2 : ℝ) ^ 20 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen
  have hscaleprodnonneg :
      0 ≤ ∏ i ∈ s, dyadicFactorScale (fs.get i) :=
    Finset.prod_nonneg (fun i hi => (dyadicFactorScale_pos_local (fs.get i)).le)
  constructor
  · exact le_of_lt (hscales.1.trans_lt hsupport.1)
  · calc
      (n.1 : ℝ) ≤ (2 : ℝ) ^ (selectedDyadicFactors fs s).length *
          (∏ i ∈ s, dyadicFactorScale (fs.get i)) := hsupport.2
      _ ≤ (2 : ℝ) ^ 20 *
          (∏ i ∈ s, dyadicFactorScale (fs.get i)) :=
            mul_le_mul_of_nonneg_right hpow hscaleprodnonneg
      _ ≤ (2 : ℝ) ^ 20 *
          ((2 : ℝ) ^ 460 * X ^ (∑ i ∈ s, α i)) :=
            mul_le_mul_of_nonneg_left hscales.2 (by positivity)
      _ = (2 : ℝ) ^ 480 * X ^ (∑ i ∈ s, α i) := by
            calc
              (2 : ℝ) ^ 20 * ((2 : ℝ) ^ 460 * X ^ (∑ i ∈ s, α i)) =
                  ((2 : ℝ) ^ 20 * (2 : ℝ) ^ 460) *
                    X ^ (∑ i ∈ s, α i) := by ring
              _ = (2 : ℝ) ^ 480 * X ^ (∑ i ∈ s, α i) := by
                    rw [← pow_add]

private theorem groupedDyadicFactor_supportedAbove_power_local {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (z : ℝ) (c : ℂ)
    (fs : List (DyadicArithmeticFactor X)) (s : Finset (Fin fs.length))
    (α : Fin fs.length → ℝ) (hcount : s.card ≤ 20)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i)
    (n : PositiveInteger)
    (hne : groupedDyadicFactor z c (selectedDyadicFactors fs s) n ≠ 0) :
    (n.1 : ℝ) ≤ (2 : ℝ) ^ 480 * X ^ (∑ i ∈ s, α i) := by
  by_cases hs : s.Nonempty
  · exact (groupedDyadicFactor_supported_power_local hX z c fs s α hs hcount
      hscale n hne).2
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hsum : (∑ i ∈ s, α i) = 0 := by simp [hs0]
    have hsel : selectedDyadicFactors fs s = [] := by
      simp [selectedDyadicFactors, hs0]
    have hn : n.1 = 1 := by
      by_contra hn
      apply hne
      simp [groupedDyadicFactor, dyadicConvolutionFactors, hsel, hn]
    rw [hsum, hn]
    simp only [Nat.cast_one]
    calc
      (1 : ℝ) ≤ (2 : ℝ) ^ 480 :=
        one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      _ = (2 : ℝ) ^ 480 * X ^ (0 : ℝ) := by simp

/-- The selected convolution factors multiply across disjoint labeled sets. -/
theorem dyadicConvolutionFactors_selected_union {X : ℝ} (z : ℝ)
    (fs : List (DyadicArithmeticFactor X)) (s t : Finset (Fin fs.length))
    (hdis : Disjoint s t) :
    dyadicConvolutionFactors z (selectedDyadicFactors fs (s ∪ t)) =
      dyadicConvolutionFactors z (selectedDyadicFactors fs s) *
        dyadicConvolutionFactors z (selectedDyadicFactors fs t) := by
  rw [dyadicConvolutionFactors_selected, Finset.prod_union hdis,
    ← dyadicConvolutionFactors_selected, ← dyadicConvolutionFactors_selected]

private theorem finRange_univ_perm (k : ℕ) :
    ((Finset.univ : Finset (Fin k)).toList).Perm (List.finRange k) := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact Finset.nodup_toList _
  · exact List.nodup_finRange _
  · ext i
    simp

/-- Taking all position labels recovers the original ordered convolution
product, even when some factor values happen to be equal. -/
private theorem dyadicConvolutionFactors_selected_univ {X : ℝ} (z : ℝ)
    (fs : List (DyadicArithmeticFactor X)) :
    dyadicConvolutionFactors z (selectedDyadicFactors fs Finset.univ) =
      dyadicConvolutionFactors z fs := by
  classical
  have hindex := finRange_univ_perm fs.length
  have hmap : (List.finRange fs.length).map fs.get = fs := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_get fs
  have hfactor : List.Perm
      ((Finset.univ : Finset (Fin fs.length)).toList.map fs.get) fs :=
    (hindex.map fs.get).trans (List.Perm.of_eq hmap)
  change (((Finset.univ : Finset (Fin fs.length)).toList.map fs.get).map
      (dyadicFactorFunction z)).prod = (fs.map (dyadicFactorFunction z)).prod
  exact (hfactor.map (dyadicFactorFunction z)).prod_eq

/-- Complex positive-integer convolution is linear in its left factor. -/
private theorem complexPositiveDirichletConvolution_smul_left
    (c : ℂ) (f g : ComplexPositiveIntegerFunction) :
    complexPositiveDirichletConvolution (fun n => c * f n) g =
      fun n => c * complexPositiveDirichletConvolution f g n := by
  funext n
  rw [complexPositiveDirichletConvolution_eq_divisor_sum,
    complexPositiveDirichletConvolution_eq_divisor_sum]
  calc
    (∑ d ∈ n.1.divisors,
        complexDivisorConvolutionSummand (fun m => c * f m) g n d) =
      ∑ d ∈ n.1.divisors, c * complexDivisorConvolutionSummand f g n d := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [complexDivisorConvolutionSummand_of_mem _ _ _ _ hd,
          complexDivisorConvolutionSummand_of_mem _ _ _ _ hd]
        ring
    _ = c * ∑ d ∈ n.1.divisors, complexDivisorConvolutionSummand f g n d := by
      rw [Finset.mul_sum]

/-- Grouped dyadic convolutions respect disjoint labeled unions over `ℂ`. -/
theorem dyadicConvolutionPositiveComplex_selected_union {X : ℝ} (z : ℝ)
    (fs : List (DyadicArithmeticFactor X)) (s t : Finset (Fin fs.length))
    (hdis : Disjoint s t) :
    complexPositiveDirichletConvolution
        (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs s))
        (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs t)) =
      dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs (s ∪ t)) := by
  funext n
  change complexPositiveDirichletConvolution
      (fun m : PositiveInteger =>
        ((dyadicConvolutionFactors z (selectedDyadicFactors fs s) m.1 : ℝ) : ℂ))
      (fun m : PositiveInteger =>
        ((dyadicConvolutionFactors z (selectedDyadicFactors fs t) m.1 : ℝ) : ℂ)) n =
    ((dyadicConvolutionFactors z (selectedDyadicFactors fs (s ∪ t)) n.1 : ℝ) : ℂ)
  rw [complexConvolution_ofRealArithmeticFunctions]
  rw [dyadicConvolutionFactors_selected_union z fs s t hdis]

/-- A coefficient may be attached to the first selected group without
changing its product factorization. -/
theorem groupedDyadicFactor_selected_union {X : ℝ} (z : ℝ) (c : ℂ)
    (fs : List (DyadicArithmeticFactor X)) (s t : Finset (Fin fs.length))
    (hdis : Disjoint s t) :
    complexPositiveDirichletConvolution
        (groupedDyadicFactor z c (selectedDyadicFactors fs s))
        (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs t)) =
      groupedDyadicFactor z c (selectedDyadicFactors fs (s ∪ t)) := by
  funext n
  change complexPositiveDirichletConvolution
      (fun m => c * dyadicConvolutionPositiveComplex z
        (selectedDyadicFactors fs s) m)
      (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs t)) n =
    c * dyadicConvolutionPositiveComplex z
      (selectedDyadicFactors fs (s ∪ t)) n
  rw [complexPositiveDirichletConvolution_smul_left,
    dyadicConvolutionPositiveComplex_selected_union z fs s t hdis]

/-- A disjoint partition of the factor labels yields the exact component
factorization, with the coefficient on the first group. -/
theorem groupedDyadicFactor_selected_partition {X : ℝ} (z : ℝ) (c : ℂ)
    (fs : List (DyadicArithmeticFactor X)) (s t : Finset (Fin fs.length))
    (hdis : Disjoint s t) (hunion : s ∪ t = Finset.univ) :
    complexPositiveDirichletConvolution
        (groupedDyadicFactor z c (selectedDyadicFactors fs s))
        (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs t)) =
      groupedDyadicFactor z c fs := by
  rw [groupedDyadicFactor_selected_union z c fs s t hdis]
  rw [hunion]
  funext n
  change c * ((dyadicConvolutionFactors z
      (selectedDyadicFactors fs Finset.univ) n.1 : ℝ) : ℂ) =
    c * ((dyadicConvolutionFactors z fs n.1 : ℝ) : ℂ)
  rw [dyadicConvolutionFactors_selected_univ]

private theorem groupedDyadicFactor_momentBounds_exact {X : ℝ}
    (hX : 3 ≤ X) (z : ℝ) (c : ℂ) (hc : ‖c‖ ≤ (2 : ℝ) ^ 10)
    (fs : List (DyadicArithmeticFactor X)) (hlen : fs.length ≤ 20) :
    complexPositiveSecondMomentBound (decompositionDelta X)
        (groupedDyadicFactor z c fs) ∧
      complexPositiveFourthMomentBound (decompositionDelta X)
        (groupedDyadicFactor z c fs) := by
  have hdinv : (decompositionDelta X)⁻¹ = decompositionDType X := by
    rw [decompositionDelta, inv_inv]
  constructor
  · intro Y hY
    have hm := groupedDyadicFactor_momentBounds hX z c hc fs hlen Y hY
    change complexPositiveSecondMoment (groupedDyadicFactor z c fs) Y ≤ _
    rw [hdinv]
    exact hm.1
  · intro Y hY
    have hm := groupedDyadicFactor_momentBounds hX z c hc fs hlen Y hY
    change complexPositiveFourthMoment (groupedDyadicFactor z c fs) Y ≤ _
    rw [hdinv]
    exact hm.2

/-- The exact third-case data in the elementary type decomposition, including
the independent major type-II factorization and its original-factor witness. -/
def largeTypeIIDyadicComponentData {X : ℝ} (z : ℝ) (c δ : ℝ)
    (f : ComplexPositiveIntegerFunction)
    (fs : List (DyadicArithmeticFactor X)) (α : Fin fs.length → ℝ) : Prop :=
  ∃ (Aminus Aplus : ℝ) (v a b1 : ComplexPositiveIntegerFunction)
    (γ η η' : ℝ) (I J J' : Finset (Fin fs.length)) (i : Fin fs.length),
    typeIIFunction δ Aminus Aplus f ∧
    f = complexPositiveDirichletConvolution v
      (complexPositiveDirichletConvolution a b1) ∧
    v = groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I) ∧
    a = dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J) ∧
    b1 = dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J') ∧
    1 ≤ Aminus ∧ Aminus ≤ Aplus ∧
    decompositionC⁻¹ * X ^ (3 / 8 : ℝ) ≤ Aminus ∧
    Aplus ≤ decompositionC * X ^ (5 / 8 : ℝ) ∧
    γ + η + η' = 1 ∧ 1 / 4 ≤ γ ∧ γ ≤ 1 / 2 ∧
    |η - η'| ≤ 1 / 4 ∧
    complexPositiveSupportedOnInterval v
      (decompositionC⁻¹ * X ^ γ) (decompositionC * X ^ γ) ∧
    complexPositiveSupportedOnInterval a
      (decompositionC⁻¹ * X ^ η) (decompositionC * X ^ η) ∧
    complexPositiveSupportedOnInterval b1
      (decompositionC⁻¹ * X ^ η') (decompositionC * X ^ η') ∧
    i ∈ I ∧ 1 / 80 ≤ α i

/-- The exact per-component data required by the elementary type
decomposition, including the independent major type-II factorization. -/
def largeDyadicComponentPackage {X : ℝ} (z : ℝ) (c δ : ℝ)
    (f : ComplexPositiveIntegerFunction)
    (fs : List (DyadicArithmeticFactor X)) (α : Fin fs.length → ℝ) : Prop :=
  typeIFunction δ (decompositionC * X ^ (5 / 8 : ℝ)) f ∨
    typeI2Function δ (decompositionC * X ^ (7 / 16 : ℝ)) f ∨
      largeTypeIIDyadicComponentData z c δ f fs α

/-- Branch provenance retained from the actual large-component grouping
construction. In the type-II branch the failed type-I selection gives
the strict upper bound on every original factor exponent. -/
def largeDyadicComponentTaggedPackage {X : ℝ} (z : ℝ) (c δ : ℝ)
    (f : ComplexPositiveIntegerFunction)
    (fs : List (DyadicArithmeticFactor X)) (α : Fin fs.length → ℝ) : Prop :=
  typeIFunction δ (decompositionC * X ^ (5 / 8 : ℝ)) f ∨
    typeI2Function δ (decompositionC * X ^ (7 / 16 : ℝ)) f ∨
      (largeTypeIIDyadicComponentData z c δ f fs α ∧
        ∀ i, α i < (3 / 8 : ℝ))

/-- Forgetting branch provenance recovers the approved elementary
three-case component data without changing its definition. -/
theorem largeDyadicComponentTaggedPackage.forget
    {X : ℝ} {z c δ : ℝ} {f : ComplexPositiveIntegerFunction}
    {fs : List (DyadicArithmeticFactor X)} {α : Fin fs.length → ℝ}
    (h : largeDyadicComponentTaggedPackage z c δ f fs α) :
    largeDyadicComponentPackage z c δ f fs α := by
  rcases h with hI | hI2 | ⟨hII, _⟩
  · exact Or.inl hI
  · exact Or.inr (Or.inl hI2)
  · exact Or.inr (Or.inr hII)

private theorem decompositionC_ge_two480 :
    (2 : ℝ) ^ 480 ≤ decompositionC := by
  have hexp : 200 + 280 = 480 := by omega
  have hpowLarge : (2 : ℝ) ^ 280 ≤ (2 : ℝ) ^ 160000 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hpowBase : (2 : ℝ) ^ 160000 ≤ (81 : ℝ) ^ 160000 := by
    gcongr <;> norm_num
  calc
    (2 : ℝ) ^ 480 = (2 : ℝ) ^ (200 + 280) := by rw [hexp]
    _ = (2 : ℝ) ^ 200 * (2 : ℝ) ^ 280 := by rw [pow_add]
    _ ≤ (2 : ℝ) ^ 200 * (2 : ℝ) ^ 160000 :=
      mul_le_mul_of_nonneg_left hpowLarge (by positivity)
    _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
      mul_le_mul_of_nonneg_left hpowBase (by positivity)
    _ = decompositionC := rfl

private theorem sum_complement_singleton {k : ℕ} (α : Fin k → ℝ)
    (i : Fin k) :
    (∑ j ∈ (Finset.univ : Finset (Fin k)) \ {i}, α j) =
      (∑ j ∈ (Finset.univ : Finset (Fin k)), α j) - α i := by
  have hsdiff :
      (Finset.univ : Finset (Fin k)) \ {i} =
        (Finset.univ : Finset (Fin k)).erase i := by
    ext j
    simp
  rw [hsdiff, Finset.sum_erase_eq_sub (Finset.mem_univ i)]

private theorem decompositionDelta_data {X : ℝ} (hX : 3 ≤ X) :
    0 < decompositionDelta X ∧ decompositionDelta X < 1 ∧
      1 < decompositionDType X ∧
      (decompositionDelta X)⁻¹ = decompositionDType X := by
  have hconst := decompositionConstants hX
  have hDpos : 0 < decompositionDType X := by
    have h : 0 < (decompositionDType X)⁻¹ := by
      simpa [decompositionDelta] using hconst.1
    exact inv_pos.mp h
  have hDgt : 1 < decompositionDType X := by
    apply (inv_lt_one₀ hDpos).mp
    simpa [decompositionDelta] using hconst.2
  refine ⟨hconst.1, hconst.2, hDgt, ?_⟩
  rw [decompositionDelta, inv_inv]

private theorem groupedDyadicFactor_supported_C_local {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (z : ℝ) (c : ℂ)
    (fs : List (DyadicArithmeticFactor X)) (s : Finset (Fin fs.length))
    (α : Fin fs.length → ℝ) (hcount : s.card ≤ 20)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i) :
    complexPositiveSupportedOnInterval
      (groupedDyadicFactor z c (selectedDyadicFactors fs s))
      (decompositionC⁻¹ * X ^ (∑ i ∈ s, α i))
      (decompositionC * X ^ (∑ i ∈ s, α i)) := by
  have hC480 := decompositionC_ge_two480
  have hC460 : (2 : ℝ) ^ 460 ≤ decompositionC := by
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)).trans hC480
  have hbasepos : 0 < (2 : ℝ) ^ 460 := by positivity
  have hCpos : 0 < decompositionC := lt_of_lt_of_le hbasepos hC460
  have hinv : decompositionC⁻¹ ≤ ((2 : ℝ) ^ 460)⁻¹ :=
    (inv_le_inv₀ hCpos hbasepos).2 hC460
  have hXpos : 0 ≤ X := by
    have : (0 : ℝ) < (2 : ℝ) ^ 120 := by positivity
    linarith
  intro n hn
  by_cases hs : s.Nonempty
  · have hgroup := groupedDyadicFactor_supported_power_local hX z c fs s α
      hs hcount hscale n hn
    constructor
    · calc
        decompositionC⁻¹ * X ^ (∑ i ∈ s, α i) ≤
            ((2 : ℝ) ^ 460)⁻¹ * X ^ (∑ i ∈ s, α i) :=
          mul_le_mul_of_nonneg_right hinv
            (Real.rpow_nonneg hXpos _)
        _ ≤ (n.1 : ℝ) := hgroup.1
    · calc
        (n.1 : ℝ) ≤ (2 : ℝ) ^ 480 * X ^ (∑ i ∈ s, α i) := hgroup.2
        _ ≤ decompositionC * X ^ (∑ i ∈ s, α i) :=
          mul_le_mul_of_nonneg_right hC480 (Real.rpow_nonneg hXpos _)
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hsum : (∑ i ∈ s, α i) = 0 := by simp [hs0]
    have hsel : selectedDyadicFactors fs s = [] := by
      simp [selectedDyadicFactors, hs0]
    have hn1 : n.1 = 1 := by
      by_contra hn1
      apply hn
      simp [groupedDyadicFactor, hsel, dyadicConvolutionFactors, hn1]
    rw [hsum, hn1]
    simp only [Real.rpow_zero, Nat.cast_one, mul_one]
    constructor
    · have hCge1 : 1 ≤ decompositionC :=
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hC480
      have hCpos : 0 < decompositionC := lt_of_lt_of_le (by norm_num) hCge1
      exact (inv_le_one₀ hCpos).2 hCge1
    · exact (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hC480

private theorem dyadicConvolutionPositiveComplex_singleton {X : ℝ} (z : ℝ)
    (f : DyadicArithmeticFactor X) :
    dyadicConvolutionPositiveComplex z [f] =
      fun n : PositiveInteger => dyadicFactorComplexFunction z f n.1 := by
  funext n
  simp [dyadicConvolutionPositiveComplex, dyadicConvolutionFactors,
    dyadicFactorComplexFunction, dyadicFactorFunction]

private theorem largeGroupedTypeI {X : ℝ} (hX : (2 : ℝ) ^ 120 ≤ X)
    (z c : ℝ) (fs : List (DyadicArithmeticFactor X))
    (hlen : 1 ≤ fs.length ∧ fs.length ≤ 20) (hc : |c| ≤ (2 : ℝ) ^ 10)
    (α : Fin fs.length → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hsum : ∑ i : Fin fs.length, α i = 1)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i)
    (hmob : ∀ i j, fs.get i = .mobius j → α i ≤ (1 / 8 : ℝ))
    (i : Fin fs.length) (hi : 3 / 8 ≤ α i) :
    typeIFunction (decompositionDelta X)
      (decompositionC * X ^ (5 / 8 : ℝ))
      (groupedDyadicFactor z (c : ℂ) fs) := by
  have hX3 : 3 ≤ X := by nlinarith [hX]
  have hconst := decompositionDelta_data hX3
  have hC := decompositionC_ge_two480
  have hCge1 : 1 ≤ decompositionC := by
    exact (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hC
  have hXge1 : 1 ≤ X := by nlinarith [hX]
  have hIpow : 1 ≤ X ^ (5 / 8 : ℝ) :=
    Real.one_le_rpow hXge1 (by norm_num)
  have hAI : 1 ≤ decompositionC * X ^ (5 / 8 : ℝ) := by
    exact one_le_mul_of_one_le_of_one_le hCge1 hIpow
  let R : Finset (Fin fs.length) := Finset.univ \ {i}
  have hdis : Disjoint R {i} := by
    apply Finset.disjoint_left.mpr
    intro j hjR hjI
    simp only [Finset.mem_singleton] at hjI
    subst j
    simp [R] at hjR
  have hunion : R ∪ {i} = Finset.univ := by
    dsimp [R]
    exact Finset.sdiff_union_of_subset (Finset.subset_univ _)
  have hsumR : (∑ j ∈ R, α j) = 1 - α i := by
    rw [sum_complement_singleton, hsum]
  have hsumRle : (∑ j ∈ R, α j) ≤ 5 / 8 := by linarith
  have hRcard : R.card ≤ fs.length := by
    calc
      R.card ≤ (Finset.univ : Finset (Fin fs.length)).card :=
        Finset.card_le_card (Finset.subset_univ R)
      _ = fs.length := by simp
  have hRcard20 : R.card ≤ 20 := hRcard.trans hlen.2
  have hRlen : (selectedDyadicFactors fs R).length ≤ 20 := by
    rw [selectedDyadicFactors_length]
    exact hRcard20
  have hcComplex : ‖(c : ℂ)‖ ≤ (2 : ℝ) ^ 10 := by simpa using hc
  have hMom := groupedDyadicFactor_momentBounds_exact hX3 z (c : ℂ)
    hcComplex (selectedDyadicFactors fs R) hRlen
  have hAupper (n : PositiveInteger)
      (hn : groupedDyadicFactor z (c : ℂ)
        (selectedDyadicFactors fs R) n ≠ 0) :
      (n.1 : ℝ) ≤ decompositionC * X ^ (5 / 8 : ℝ) := by
    have hgroup := groupedDyadicFactor_supportedAbove_power_local hX z
      (c : ℂ) fs R α hRcard20 hscale n hn
    have hXpow := Real.rpow_le_rpow_of_exponent_le hXge1 hsumRle
    calc
      (n.1 : ℝ) ≤ (2 : ℝ) ^ 480 * X ^ (∑ j ∈ R, α j) := hgroup
      _ ≤ (2 : ℝ) ^ 480 * X ^ (5 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left hXpow (by positivity)
      _ ≤ decompositionC * X ^ (5 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hC
          (Real.rpow_nonneg (by linarith : 0 ≤ X) _)
  have hnotmob : ∀ j, fs.get i ≠ .mobius j := by
    intro j hEq
    have hbound := hmob i j hEq
    linarith
  have hvariation := nonMobiusDyadicFactor_residueVariation_bound hX3 z
    (fs.get i) hnotmob
  have hdeltaInv : (decompositionDelta X)⁻¹ = decompositionDType X :=
    hconst.2.2.2
  have hvariation' :
      complexPositiveIntegerResidueVariation
        (dyadicConvolutionPositiveComplex z [fs.get i]) 1 (by decide) ≤
          ENNReal.ofReal ((decompositionDelta X)⁻¹) := by
    rw [dyadicConvolutionPositiveComplex_singleton, hdeltaInv]
    exact hvariation
  have hq : (1 : ℝ) ≤ (decompositionDelta X)⁻¹ :=
    le_of_lt (by rw [hdeltaInv]; exact hconst.2.2.1)
  let A := groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs R)
  let B := dyadicConvolutionPositiveComplex z [fs.get i]
  have hsingle : selectedDyadicFactors fs {i} = [fs.get i] := by
    simp [selectedDyadicFactors]
  have hfactor :
      groupedDyadicFactor z (c : ℂ) fs =
        complexPositiveDirichletConvolution A B := by
    have hpart := groupedDyadicFactor_selected_partition z (c : ℂ)
      fs R {i} hdis hunion
    rw [hsingle] at hpart
    exact hpart.symm
  have hAsupp :
      complexPositiveSupportedOnInterval A 1
        (decompositionC * X ^ (5 / 8 : ℝ)) := by
    intro n hn
    exact ⟨by exact_mod_cast n.2, hAupper n hn⟩
  refine ⟨hconst.1, hconst.2.1, hAI,
      ⟨A, B, 1, by decide, hfactor, hAsupp, hMom.1, by norm_num,
        (by simpa using hq),
      hvariation'⟩⟩

private theorem largeGroupedTypeI2 {X : ℝ} (hX : (2 : ℝ) ^ 120 ≤ X)
    (z c : ℝ) (fs : List (DyadicArithmeticFactor X))
    (hlen : 1 ≤ fs.length ∧ fs.length ≤ 20) (hc : |c| ≤ (2 : ℝ) ^ 10)
    (α : Fin fs.length → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hsum : ∑ i : Fin fs.length, α i = 1)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i)
    (hmob : ∀ i j, fs.get i = .mobius j → α i ≤ (1 / 8 : ℝ))
    (hNoI : ∀ i, α i < 3 / 8)
    (i j : Fin fs.length) (hij : i ≠ j)
    (hpair : 9 / 16 ≤ α i + α j) :
    typeI2Function (decompositionDelta X)
      (decompositionC * X ^ (7 / 16 : ℝ))
      (groupedDyadicFactor z (c : ℂ) fs) := by
  have hX3 : 3 ≤ X := by nlinarith [hX]
  have hconst := decompositionDelta_data hX3
  have hC := decompositionC_ge_two480
  have hCge1 : 1 ≤ decompositionC := by
    exact (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hC
  have hXge1 : 1 ≤ X := by nlinarith [hX]
  have hI2pow : 1 ≤ X ^ (7 / 16 : ℝ) :=
    Real.one_le_rpow hXge1 (by norm_num)
  have hAI2 : 1 ≤ decompositionC * X ^ (7 / 16 : ℝ) :=
    one_le_mul_of_one_le_of_one_le hCge1 hI2pow
  have hiLarge : 3 / 16 < α i := by
    have hjSmall := hNoI j
    linarith
  have hjLarge : 3 / 16 < α j := by
    have hiSmall := hNoI i
    linarith
  have hnotmobI : ∀ k, fs.get i ≠ .mobius k := by
    intro k hEq
    have hbound := hmob i k hEq
    linarith
  have hnotmobJ : ∀ k, fs.get j ≠ .mobius k := by
    intro k hEq
    have hbound := hmob j k hEq
    linarith
  let R : Finset (Fin fs.length) := Finset.univ \ {i, j}
  let T : Finset (Fin fs.length) := Finset.univ \ {j}
  have hReq : R = T \ {i} := by
    ext k
    simp [R, T] <;> tauto
  have hTdiff : T = (Finset.univ : Finset (Fin fs.length)).erase j := by
    ext k
    simp [T]
  have hMemI : i ∈ T := by
    simp [T, hij]
  have hRsum : (∑ k ∈ R, α k) = 1 - α i - α j := by
    calc
      (∑ k ∈ R, α k) = ∑ k ∈ T \ {i}, α k := by rw [hReq]
      _ = (∑ k ∈ T, α k) - α i := by
        have hdiff : T \ {i} = T.erase i := by
          ext k
          simp [and_comm]
        rw [hdiff, Finset.sum_erase_eq_sub hMemI]
      _ = ((∑ k ∈ (Finset.univ : Finset (Fin fs.length)), α k) - α j) - α i := by
        rw [hTdiff, Finset.sum_erase_eq_sub (Finset.mem_univ j)]
      _ = 1 - α i - α j := by rw [hsum]; ring
  have hRsumle : (∑ k ∈ R, α k) ≤ 7 / 16 := by linarith
  have hdisRI : Disjoint R {i} := by
    apply Finset.disjoint_left.mpr
    intro k hkR hkI
    simp only [Finset.mem_singleton] at hkI
    subst k
    simp [R] at hkR
  have hsubsetI : {i} ⊆ T := by
    apply Finset.singleton_subset_iff.mpr
    simp [T, hij]
  have hunionRI : R ∪ {i} = T := by
    rw [hReq]
    exact Finset.sdiff_union_of_subset hsubsetI
  have hdisTJ : Disjoint T {j} := by
    apply Finset.disjoint_left.mpr
    intro k hkT hkJ
    simp only [Finset.mem_singleton] at hkJ
    subst k
    simp [T] at hkT
  have hunionTJ : T ∪ {j} = Finset.univ := by
    dsimp [T]
    exact Finset.sdiff_union_of_subset (Finset.subset_univ _)
  have hRcard : R.card ≤ fs.length := by
    calc
      R.card ≤ (Finset.univ : Finset (Fin fs.length)).card :=
        Finset.card_le_card (Finset.subset_univ R)
      _ = fs.length := by simp
  have hRcard20 : R.card ≤ 20 := hRcard.trans hlen.2
  have hRlen : (selectedDyadicFactors fs R).length ≤ 20 := by
    rw [selectedDyadicFactors_length]
    exact hRcard20
  have hcComplex : ‖(c : ℂ)‖ ≤ (2 : ℝ) ^ 10 := by simpa using hc
  have hMom := groupedDyadicFactor_momentBounds_exact hX3 z (c : ℂ)
    hcComplex (selectedDyadicFactors fs R) hRlen
  have hAupper (n : PositiveInteger)
      (hn : groupedDyadicFactor z (c : ℂ)
        (selectedDyadicFactors fs R) n ≠ 0) :
      (n.1 : ℝ) ≤ decompositionC * X ^ (7 / 16 : ℝ) := by
    have hgroup := groupedDyadicFactor_supportedAbove_power_local hX z
      (c : ℂ) fs R α hRcard20 hscale n hn
    have hXpow := Real.rpow_le_rpow_of_exponent_le hXge1 hRsumle
    calc
      (n.1 : ℝ) ≤ (2 : ℝ) ^ 480 * X ^ (∑ k ∈ R, α k) := hgroup
      _ ≤ (2 : ℝ) ^ 480 * X ^ (7 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_left hXpow (by positivity)
      _ ≤ decompositionC * X ^ (7 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_right hC
          (Real.rpow_nonneg (by linarith : 0 ≤ X) _)
  have hdeltaInv : (decompositionDelta X)⁻¹ = decompositionDType X :=
    hconst.2.2.2
  have hq : (1 : ℝ) ≤ (decompositionDelta X)⁻¹ :=
    le_of_lt (by rw [hdeltaInv]; exact hconst.2.2.1)
  have hvarI := nonMobiusDyadicFactor_residueVariation_bound hX3 z
    (fs.get i) hnotmobI
  have hvarJ := nonMobiusDyadicFactor_residueVariation_bound hX3 z
    (fs.get j) hnotmobJ
  have hvarI' :
      complexPositiveIntegerResidueVariation
        (dyadicConvolutionPositiveComplex z [fs.get i]) 1 (by decide) ≤
          ENNReal.ofReal ((decompositionDelta X)⁻¹) := by
    rw [dyadicConvolutionPositiveComplex_singleton, hdeltaInv]
    exact hvarI
  have hvarJ' :
      complexPositiveIntegerResidueVariation
        (dyadicConvolutionPositiveComplex z [fs.get j]) 1 (by decide) ≤
          ENNReal.ofReal ((decompositionDelta X)⁻¹) := by
    rw [dyadicConvolutionPositiveComplex_singleton, hdeltaInv]
    exact hvarJ
  have hsingleI : selectedDyadicFactors fs {i} = [fs.get i] := by
    simp [selectedDyadicFactors]
  have hsingleJ : selectedDyadicFactors fs {j} = [fs.get j] := by
    simp [selectedDyadicFactors]
  let A := groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs R)
  let B₁ := dyadicConvolutionPositiveComplex z [fs.get i]
  let B₂ := dyadicConvolutionPositiveComplex z [fs.get j]
  have hfactor : groupedDyadicFactor z (c : ℂ) fs =
      complexPositiveDirichletConvolution
        (complexPositiveDirichletConvolution A B₁) B₂ := by
    have hpart1 := groupedDyadicFactor_selected_union z (c : ℂ)
      fs R {i} hdisRI
    rw [hsingleI] at hpart1
    rw [hunionRI] at hpart1
    have hpart2 := groupedDyadicFactor_selected_partition z (c : ℂ)
      fs T {j} hdisTJ hunionTJ
    rw [hsingleJ] at hpart2
    calc
      groupedDyadicFactor z (c : ℂ) fs =
          complexPositiveDirichletConvolution
            (groupedDyadicFactor z (c : ℂ)
              (selectedDyadicFactors fs T)) B₂ := hpart2.symm
      _ = complexPositiveDirichletConvolution
            (complexPositiveDirichletConvolution A B₁) B₂ := by
              rw [← hpart1]
  have hAsupp :
      complexPositiveSupportedOnInterval A 1
        (decompositionC * X ^ (7 / 16 : ℝ)) := by
    intro n hn
    exact ⟨by exact_mod_cast n.2, hAupper n hn⟩
  refine ⟨hconst.1, hconst.2.1, hAI2,
    ⟨A, B₁, B₂, 1, by decide, hfactor, hAsupp, hMom.1, by norm_num,
      (by simpa using hq),
      hvarI', hvarJ'⟩⟩

private theorem largeGroupedTypeIIofMinor {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (z c : ℝ)
    (fs : List (DyadicArithmeticFactor X))
    (hlen : 1 ≤ fs.length ∧ fs.length ≤ 20)
    (hc : |c| ≤ (2 : ℝ) ^ 10)
    (α : Fin fs.length → ℝ)
    (hα : ∀ i, 0 ≤ α i)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i)
    (J J' : Finset (Fin fs.length))
    (hdis : Disjoint J J') (hunion : J ∪ J' = Finset.univ)
    (hJlo : 3 / 8 ≤ ∑ i ∈ J, α i) (hJhi : (∑ i ∈ J, α i) ≤ 5 / 8)
    (hJ'lo : 3 / 8 ≤ ∑ i ∈ J', α i) (hJ'hi : (∑ i ∈ J', α i) ≤ 5 / 8) :
    ∃ Aminus Aplus : ℝ,
      typeIIFunction (decompositionDelta X) Aminus Aplus
        (groupedDyadicFactor z (c : ℂ) fs) ∧
      1 ≤ Aminus ∧ Aminus ≤ Aplus ∧
      decompositionC⁻¹ * X ^ (3 / 8 : ℝ) ≤ Aminus ∧
      Aplus ≤ decompositionC * X ^ (5 / 8 : ℝ) := by
  have hX3 : 3 ≤ X := by nlinarith [hX]
  have hconst := decompositionDelta_data hX3
  have hC480 := decompositionC_ge_two480
  have hC460 : (2 : ℝ) ^ 460 ≤ decompositionC := by
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)).trans hC480
  have hbasepos : 0 < (2 : ℝ) ^ 460 := by positivity
  have hCpos : 0 < decompositionC := lt_of_lt_of_le hbasepos hC460
  have hinv : decompositionC⁻¹ ≤ ((2 : ℝ) ^ 460)⁻¹ :=
    (inv_le_inv₀ hCpos hbasepos).2 hC460
  have hXge1 : 1 ≤ X := by nlinarith [hX]
  have hJnonneg : 0 ≤ ∑ i ∈ J, α i :=
    Finset.sum_nonneg (fun i hi => hα i)
  have hJ'nonneg : 0 ≤ ∑ i ∈ J', α i :=
    Finset.sum_nonneg (fun i hi => hα i)
  let Aminus : ℝ := max 1 (((2 : ℝ) ^ 460)⁻¹ * X ^ (∑ i ∈ J, α i))
  let Aplus : ℝ := (2 : ℝ) ^ 480 * X ^ (∑ i ∈ J, α i)
  have hAminusOne : 1 ≤ Aminus := le_max_left _ _
  have hAplusOne : 1 ≤ Aplus := by
    dsimp [Aplus]
    have hpow : 1 ≤ X ^ (∑ i ∈ J, α i) :=
      Real.one_le_rpow hXge1 hJnonneg
    exact one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hpow
  have hbaseLE : ((2 : ℝ) ^ 460)⁻¹ * X ^ (∑ i ∈ J, α i) ≤ Aplus := by
    dsimp [Aplus]
    have hconstLE : ((2 : ℝ) ^ 460)⁻¹ ≤ (2 : ℝ) ^ 480 := by
      calc
        ((2 : ℝ) ^ 460)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        _ ≤ (2 : ℝ) ^ 480 := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact mul_le_mul_of_nonneg_right hconstLE
      (Real.rpow_nonneg (by linarith [hX]) _)
  have hAminusLE : Aminus ≤ Aplus := by
    dsimp [Aminus]
    exact max_le_iff.mpr ⟨hAplusOne, hbaseLE⟩
  have hAminusLow :
      decompositionC⁻¹ * X ^ (3 / 8 : ℝ) ≤ Aminus := by
    apply le_trans _ (le_max_right _ _)
    calc
      decompositionC⁻¹ * X ^ (3 / 8 : ℝ) ≤
          ((2 : ℝ) ^ 460)⁻¹ * X ^ (3 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hinv
          (Real.rpow_nonneg (by linarith [hX]) _)
      _ ≤ ((2 : ℝ) ^ 460)⁻¹ * X ^ (∑ i ∈ J, α i) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hXge1 hJlo)
          (by positivity)
  have hAplusHigh :
      Aplus ≤ decompositionC * X ^ (5 / 8 : ℝ) := by
    dsimp [Aplus]
    calc
      (2 : ℝ) ^ 480 * X ^ (∑ i ∈ J, α i) ≤
          (2 : ℝ) ^ 480 * X ^ (5 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hXge1 hJhi) (by positivity)
      _ ≤ decompositionC * X ^ (5 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hC480
          (Real.rpow_nonneg (by linarith [hX]) _)
  have hJcard : J.card ≤ 20 := by
    calc
      J.card ≤ (Finset.univ : Finset (Fin fs.length)).card :=
        Finset.card_le_card (Finset.subset_univ J)
      _ = fs.length := by simp
      _ ≤ 20 := hlen.2
  have hJ'card : J'.card ≤ 20 := by
    calc
      J'.card ≤ (Finset.univ : Finset (Fin fs.length)).card :=
        Finset.card_le_card (Finset.subset_univ J')
      _ = fs.length := by simp
      _ ≤ 20 := hlen.2
  have hJlen : (selectedDyadicFactors fs J).length ≤ 20 := by
    rw [selectedDyadicFactors_length]
    exact hJcard
  have hJ'len : (selectedDyadicFactors fs J').length ≤ 20 := by
    rw [selectedDyadicFactors_length]
    exact hJ'card
  have hcComplex : ‖(c : ℂ)‖ ≤ (2 : ℝ) ^ 10 := by simpa using hc
  have hMomA := groupedDyadicFactor_momentBounds_exact hX3 z (c : ℂ)
    hcComplex (selectedDyadicFactors fs J) hJlen
  have hMomB := groupedDyadicFactor_momentBounds_exact hX3 z (1 : ℂ)
    (by norm_num) (selectedDyadicFactors fs J') hJ'len
  let A := groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs J)
  let B := groupedDyadicFactor z (1 : ℂ) (selectedDyadicFactors fs J')
  have hBgroup :
      dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J') = B := by
    funext n
    simp [B, dyadicConvolutionPositiveComplex, groupedDyadicFactor]
  have hAupperlo : J.Nonempty := by
    by_contra hempty
    have hzero : (∑ i ∈ J, α i) = 0 := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
    linarith
  have hAsupp :
      complexPositiveSupportedOnInterval A Aminus Aplus := by
    intro n hn
    have hgroup := groupedDyadicFactor_supported_power_local hX z (c : ℂ)
      fs J α hAupperlo hJcard hscale n hn
    have hnlo : 1 ≤ (n.1 : ℝ) := by exact_mod_cast n.2
    constructor
    · dsimp [Aminus]
      exact max_le_iff.mpr ⟨hnlo, hgroup.1⟩
    · exact hgroup.2
  have hfactor :
      groupedDyadicFactor z (c : ℂ) fs =
        complexPositiveDirichletConvolution A B := by
    have hpart := groupedDyadicFactor_selected_partition z (c : ℂ)
      fs J J' hdis hunion
    rw [hBgroup] at hpart
    dsimp [A, B]
    exact hpart.symm
  have hTypeII : typeIIFunction (decompositionDelta X) Aminus Aplus
      (groupedDyadicFactor z (c : ℂ) fs) := by
    refine ⟨hconst.1, hconst.2.1, hAminusOne, hAplusOne,
      A, B, hfactor, hAsupp, ?_, hMomA.1, hMomB.1, hMomB.2⟩
    intro hbad
    exact (False.elim (not_le_of_gt hbad hAminusLE))
  exact ⟨Aminus, Aplus, hTypeII, hAminusOne, hAminusLE,
    hAminusLow, hAplusHigh⟩

private theorem largeGroupedMajorData {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (z c : ℝ)
    (fs : List (DyadicArithmeticFactor X))
    (hlen : 1 ≤ fs.length ∧ fs.length ≤ 20)
    (α : Fin fs.length → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i : Fin fs.length, α i = 1)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i)
    (I J J' : Finset (Fin fs.length))
    (hdisIJ : Disjoint I J) (hdisIJ' : Disjoint I J')
    (hdisJJ' : Disjoint J J') (hunion : I ∪ J ∪ J' = Finset.univ)
    (hIlo : 1 / 4 ≤ ∑ i ∈ I, α i)
    (hIhi : (∑ i ∈ I, α i) ≤ 1 / 2)
    (hgap : |(∑ i ∈ J, α i) - (∑ i ∈ J', α i)| ≤ 1 / 4) :
    ∃ i : Fin fs.length,
      i ∈ I ∧ (1 / 80 : ℝ) ≤ α i ∧
      (∑ i ∈ I, α i) + (∑ i ∈ J, α i) + (∑ i ∈ J', α i) = 1 ∧
      1 / 4 ≤ ∑ i ∈ I, α i ∧
      (∑ i ∈ I, α i) ≤ 1 / 2 ∧
      |(∑ i ∈ J, α i) - (∑ i ∈ J', α i)| ≤ 1 / 4 ∧
      complexPositiveSupportedOnInterval
        (groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I))
        (decompositionC⁻¹ * X ^ (∑ i ∈ I, α i))
        (decompositionC * X ^ (∑ i ∈ I, α i)) ∧
      complexPositiveSupportedOnInterval
        (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J))
        (decompositionC⁻¹ * X ^ (∑ i ∈ J, α i))
        (decompositionC * X ^ (∑ i ∈ J, α i)) ∧
      complexPositiveSupportedOnInterval
        (dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J'))
        (decompositionC⁻¹ * X ^ (∑ i ∈ J', α i))
        (decompositionC * X ^ (∑ i ∈ J', α i)) := by
  have hIcard : I.card ≤ 20 := by
    calc
      I.card ≤ (Finset.univ : Finset (Fin fs.length)).card :=
        Finset.card_le_card (Finset.subset_univ I)
      _ = fs.length := by simp
      _ ≤ 20 := hlen.2
  have hJcard : J.card ≤ 20 := by
    calc
      J.card ≤ (Finset.univ : Finset (Fin fs.length)).card :=
        Finset.card_le_card (Finset.subset_univ J)
      _ = fs.length := by simp
      _ ≤ 20 := hlen.2
  have hJ'card : J'.card ≤ 20 := by
    calc
      J'.card ≤ (Finset.univ : Finset (Fin fs.length)).card :=
        Finset.card_le_card (Finset.subset_univ J')
      _ = fs.length := by simp
      _ ≤ 20 := hlen.2
  have hIlen : (selectedDyadicFactors fs I).length ≤ 20 := by
    rw [selectedDyadicFactors_length]
    exact hIcard
  have hJlen : (selectedDyadicFactors fs J).length ≤ 20 := by
    rw [selectedDyadicFactors_length]
    exact hJcard
  have hJ'len : (selectedDyadicFactors fs J').length ≤ 20 := by
    rw [selectedDyadicFactors_length]
    exact hJ'card
  let v := groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I)
  let a := dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J)
  let b1 := dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J')
  have hVsupport :
      complexPositiveSupportedOnInterval v
        (decompositionC⁻¹ * X ^ (∑ i ∈ I, α i))
        (decompositionC * X ^ (∑ i ∈ I, α i)) := by
    dsimp [v]
    exact groupedDyadicFactor_supported_C_local hX z (c : ℂ)
      fs I α hIcard hscale
  have hAsupport :
      complexPositiveSupportedOnInterval a
        (decompositionC⁻¹ * X ^ (∑ i ∈ J, α i))
        (decompositionC * X ^ (∑ i ∈ J, α i)) := by
    dsimp [a]
    have hgroup :
        dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J) =
          groupedDyadicFactor z (1 : ℂ) (selectedDyadicFactors fs J) := by
      funext n
      simp [dyadicConvolutionPositiveComplex, groupedDyadicFactor]
    rw [hgroup]
    exact groupedDyadicFactor_supported_C_local hX z (1 : ℂ)
      fs J α hJcard hscale
  have hBsupport :
      complexPositiveSupportedOnInterval b1
        (decompositionC⁻¹ * X ^ (∑ i ∈ J', α i))
        (decompositionC * X ^ (∑ i ∈ J', α i)) := by
    dsimp [b1]
    have hgroup :
        dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs J') =
          groupedDyadicFactor z (1 : ℂ) (selectedDyadicFactors fs J') := by
      funext n
      simp [dyadicConvolutionPositiveComplex, groupedDyadicFactor]
    rw [hgroup]
    exact groupedDyadicFactor_supported_C_local hX z (1 : ℂ)
      fs J' α hJ'card hscale
  have hIunion : I ∪ (J ∪ J') = Finset.univ := by
    simpa [Finset.union_assoc] using hunion
  have hdisIUnion : Disjoint I (J ∪ J') :=
    Finset.disjoint_union_right.mpr ⟨hdisIJ, hdisIJ'⟩
  have hdisUnion : Disjoint (I ∪ J) J' :=
    Finset.disjoint_union_left.mpr ⟨hdisIJ', hdisJJ'⟩
  have hsumUnion :
      (∑ i ∈ Finset.univ, α i) =
        (∑ i ∈ I, α i) + (∑ i ∈ J, α i) + (∑ i ∈ J', α i) := by
    calc
      (∑ i ∈ Finset.univ, α i) = ∑ i ∈ I ∪ (J ∪ J'), α i := by rw [← hIunion]
      _ = (∑ i ∈ I, α i) + (∑ i ∈ J ∪ J', α i) :=
        Finset.sum_union hdisIUnion
      _ = (∑ i ∈ I, α i) +
          ((∑ i ∈ J, α i) + (∑ i ∈ J', α i)) := by
        rw [Finset.sum_union hdisJJ']
      _ = (∑ i ∈ I, α i) + (∑ i ∈ J, α i) + (∑ i ∈ J', α i) := by ring
  have hsumGroups :
      (∑ i ∈ I, α i) + (∑ i ∈ J, α i) + (∑ i ∈ J', α i) = 1 := by
    rw [← hsumUnion, hsum]
  have hInonempty : I.Nonempty := by
    by_contra hempty
    have hzero : (∑ i ∈ I, α i) = 0 := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
    linarith
  obtain ⟨i₀, hi₀⟩ := hInonempty
  have hexists : ∃ i, i ∈ I ∧ (1 / 80 : ℝ) ≤ α i := by
    by_contra hno
    have hsmall : ∀ i ∈ I, α i < (1 / 80 : ℝ) := by
      intro i hi
      by_contra hnot
      have hge : (1 / 80 : ℝ) ≤ α i := le_of_not_gt hnot
      exact hno ⟨i, hi, hge⟩
    have hstrict :
        (∑ i ∈ I, α i) < ∑ i ∈ I, (1 / 80 : ℝ) := by
      apply Finset.sum_lt_sum (fun i hi => (hsmall i hi).le)
      exact ⟨i₀, hi₀, hsmall i₀ hi₀⟩
    have hsumConst :
        (∑ i ∈ I, (1 / 80 : ℝ)) = (I.card : ℝ) / 80 := by
      simp
      ring
    have hcardReal : (I.card : ℝ) ≤ 20 := by exact_mod_cast hIcard
    rw [hsumConst] at hstrict
    have hbound : (I.card : ℝ) / 80 ≤ (1 / 4 : ℝ) := by nlinarith
    linarith
  rcases hexists with ⟨i, hiI, hiAlpha⟩
  exact ⟨i, hiI, hiAlpha, hsumGroups, hIlo, hIhi, hgap,
    hVsupport, hAsupport, hBsupport⟩

private theorem largeGroupedDyadicComponentTaggedPackage {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (z c : ℝ)
    (fs : List (DyadicArithmeticFactor X))
    (hlen : 1 ≤ fs.length ∧ fs.length ≤ 20)
    (hc : |c| ≤ (2 : ℝ) ^ 10)
    (α : Fin fs.length → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i : Fin fs.length, α i = 1)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i)
    (hmob : ∀ i j, fs.get i = .mobius j → α i ≤ (1 / 8 : ℝ)) :
    largeDyadicComponentTaggedPackage z c (decompositionDelta X)
      (groupedDyadicFactor z (c : ℂ) fs) fs α := by
  let w : GroupingPredicates fs.length :=
    ⟨α, by omega, hα, hsum⟩
  by_cases hI : w.I (5 / 8)
  · dsimp [GroupingPredicates.I, w] at hI
    rcases hI with ⟨i, hi⟩
    have hiLarge : (3 / 8 : ℝ) ≤ α i := by norm_num at hi ⊢; linarith
    exact Or.inl (largeGroupedTypeI hX z c fs hlen hc α hα hsum
      hscale hmob i hiLarge)
  · by_cases hI2 : w.I2 (5 / 8)
    · have hNoI : ∀ i, α i < (3 / 8 : ℝ) := by
        intro i
        by_contra hnot
        have hiLarge : (3 / 8 : ℝ) ≤ α i := le_of_not_gt hnot
        apply hI
        refine ⟨i, ?_⟩
        norm_num at hiLarge ⊢
        exact hiLarge
      dsimp [GroupingPredicates.I2, w] at hI2
      rcases hI2 with ⟨i, j, hij, hpair⟩
      have hpair' : (9 / 16 : ℝ) ≤ α i + α j := by
        norm_num at hpair ⊢
        exact hpair
      exact Or.inr (Or.inl
        (largeGroupedTypeI2 hX z c fs hlen hc α hα hsum hscale hmob
          hNoI i j hij hpair'))
    · have hNoI : ∀ i, α i < (3 / 8 : ℝ) := by
        intro i
        by_contra hnot
        have hiLarge : (3 / 8 : ℝ) ≤ α i := le_of_not_gt hnot
        apply hI
        refine ⟨i, ?_⟩
        norm_num at hiLarge ⊢
        exact hiLarge
      have hcombined := combinedGroupingFiveEighths w
      rcases hcombined with hI' | hI2' | hthird
      · exact False.elim (hI hI')
      · exact False.elim (hI2 hI2')
      · rcases hthird with ⟨hminor, hmajor⟩
        rcases hminor with ⟨J, J', hdisJJ', hunionJJ',
          hJlo, hJhi, hJ'lo, hJ'hi⟩
        have hJlo' : (3 / 8 : ℝ) ≤ ∑ i ∈ J, α i := by
          change 1 - (5 / 8 : ℝ) ≤ ∑ i ∈ J, α i at hJlo
          norm_num at hJlo
          exact hJlo
        have hJhi' : (∑ i ∈ J, α i) ≤ (5 / 8 : ℝ) := by
          change (∑ i ∈ J, α i) ≤ (5 / 8 : ℝ) at hJhi
          exact hJhi
        have hJ'lo' : (3 / 8 : ℝ) ≤ ∑ i ∈ J', α i := by
          change 1 - (5 / 8 : ℝ) ≤ ∑ i ∈ J', α i at hJ'lo
          norm_num at hJ'lo
          exact hJ'lo
        have hJ'hi' : (∑ i ∈ J', α i) ≤ (5 / 8 : ℝ) := by
          change (∑ i ∈ J', α i) ≤ (5 / 8 : ℝ) at hJ'hi
          exact hJ'hi
        rcases hmajor with ⟨I, K, K', hdisIK, hdisIK', hdisKK',
          hunionIKK', hIlo, hIhi, hgap⟩
        have hIlo' : (1 / 4 : ℝ) ≤ ∑ i ∈ I, α i := by
          change 2 * (5 / 8 : ℝ) - 1 ≤ ∑ i ∈ I, α i at hIlo
          norm_num at hIlo
          exact hIlo
        have hIhi' : (∑ i ∈ I, α i) ≤ (1 / 2 : ℝ) := by
          change (∑ i ∈ I, α i) ≤ 4 * (5 / 8 : ℝ) - 2 at hIhi
          norm_num at hIhi
          exact hIhi
        have hgap' :
            |(∑ i ∈ K, α i) - (∑ i ∈ K', α i)| ≤ (1 / 4 : ℝ) := by
          change |(∑ i ∈ K, α i) - (∑ i ∈ K', α i)| ≤
            2 * (5 / 8 : ℝ) - 1 at hgap
          norm_num at hgap
          exact hgap
        obtain ⟨Aminus, Aplus, htypeII, hAminusOne, hAminusAplus,
          hAminusLow, hAplusHigh⟩ :=
          largeGroupedTypeIIofMinor hX z c fs hlen hc α hα hscale
            J J' hdisJJ' hunionJJ' hJlo' hJhi' hJ'lo' hJ'hi'
        have hunionIKK : I ∪ (K ∪ K') = Finset.univ := by
          simpa [Finset.union_assoc] using hunionIKK'
        have hdisIUnion : Disjoint I (K ∪ K') :=
          Finset.disjoint_union_right.mpr ⟨hdisIK, hdisIK'⟩
        have hsumMajor :
            (∑ i ∈ I, α i) + (∑ i ∈ K, α i) + (∑ i ∈ K', α i) = 1 := by
          have hdisUnion : Disjoint (I ∪ K) K' :=
            Finset.disjoint_union_left.mpr ⟨hdisIK', hdisKK'⟩
          have hsumUnion :
              (∑ i ∈ Finset.univ, α i) =
                (∑ i ∈ I, α i) + (∑ i ∈ K, α i) + (∑ i ∈ K', α i) := by
            calc
              (∑ i ∈ Finset.univ, α i) =
                  ∑ i ∈ I ∪ (K ∪ K'), α i := by rw [← hunionIKK]
              _ = (∑ i ∈ I, α i) + (∑ i ∈ K ∪ K', α i) :=
                Finset.sum_union hdisIUnion
              _ = (∑ i ∈ I, α i) +
                  ((∑ i ∈ K, α i) + (∑ i ∈ K', α i)) := by
                rw [Finset.sum_union hdisKK']
              _ = (∑ i ∈ I, α i) + (∑ i ∈ K, α i) +
                  (∑ i ∈ K', α i) := by ring
          rw [← hsumUnion, hsum]
        obtain ⟨i, hiI, hiAlpha, hgammasum, hgammaLo, hgammaHi,
          hmajorGap, hvsupp, hasupp, hb1supp⟩ :=
          largeGroupedMajorData hX z c fs hlen α hα hsum hscale
            I K K' hdisIK hdisIK' hdisKK' hunionIKK'
            hIlo' hIhi' hgap'
        let v := groupedDyadicFactor z (c : ℂ) (selectedDyadicFactors fs I)
        let a := dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs K)
        let b1 := dyadicConvolutionPositiveComplex z (selectedDyadicFactors fs K')
        have hfactor :
            groupedDyadicFactor z (c : ℂ) fs =
              complexPositiveDirichletConvolution v
                (complexPositiveDirichletConvolution a b1) := by
          have houter := groupedDyadicFactor_selected_partition z (c : ℂ)
            fs I (K ∪ K') hdisIUnion hunionIKK
          have hinner := dyadicConvolutionPositiveComplex_selected_union
            z fs K K' hdisKK'
          dsimp [v, a, b1]
          calc
            groupedDyadicFactor z (c : ℂ) fs =
                complexPositiveDirichletConvolution
                  (groupedDyadicFactor z (c : ℂ)
                    (selectedDyadicFactors fs I))
                  (dyadicConvolutionPositiveComplex z
                    (selectedDyadicFactors fs (K ∪ K'))) := houter.symm
            _ = complexPositiveDirichletConvolution
                  (groupedDyadicFactor z (c : ℂ)
                    (selectedDyadicFactors fs I))
                  (complexPositiveDirichletConvolution
                    (dyadicConvolutionPositiveComplex z
                      (selectedDyadicFactors fs K))
                    (dyadicConvolutionPositiveComplex z
                      (selectedDyadicFactors fs K'))) := by rw [← hinner]
        exact Or.inr (Or.inr
          ⟨⟨Aminus, Aplus, v, a, b1,
            (∑ i ∈ I, α i), (∑ i ∈ K, α i), (∑ i ∈ K', α i),
            I, K, K', i, htypeII, hfactor, rfl, rfl, rfl,
            hAminusOne, hAminusAplus, hAminusLow, hAplusHigh,
            hgammasum, hgammaLo, hgammaHi, hmajorGap,
            hvsupp, hasupp, hb1supp, hiI, hiAlpha⟩, hNoI⟩)

/-- The tag-preserving form of the already checked grouped dyadic
component trichotomy. This exposes the source's failed type-I exponent
inequality before the untagged projection discards it. -/
theorem largeGroupedDyadicComponentTaggedPackage_public {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (z c : ℝ)
    (fs : List (DyadicArithmeticFactor X))
    (hlen : 1 ≤ fs.length ∧ fs.length ≤ 20)
    (hc : |c| ≤ (2 : ℝ) ^ 10)
    (α : Fin fs.length → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i : Fin fs.length, α i = 1)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i)
    (hmob : ∀ i j, fs.get i = .mobius j → α i ≤ (1 / 8 : ℝ)) :
    largeDyadicComponentTaggedPackage z c (decompositionDelta X)
      (groupedDyadicFactor z (c : ℂ) fs) fs α :=
  largeGroupedDyadicComponentTaggedPackage hX z c fs hlen hc α
    hα hsum hscale hmob

#print axioms largeGroupedDyadicComponentTaggedPackage_public

private theorem largeGroupedDyadicComponentPackage {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (z c : ℝ)
    (fs : List (DyadicArithmeticFactor X))
    (hlen : 1 ≤ fs.length ∧ fs.length ≤ 20)
    (hc : |c| ≤ (2 : ℝ) ^ 10)
    (α : Fin fs.length → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i : Fin fs.length, α i = 1)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i)
    (hmob : ∀ i j, fs.get i = .mobius j → α i ≤ (1 / 8 : ℝ)) :
    largeDyadicComponentPackage z c (decompositionDelta X)
      (groupedDyadicFactor z (c : ℂ) fs) fs α := by
  exact (largeGroupedDyadicComponentTaggedPackage hX z c fs hlen hc α
    hα hsum hscale hmob).forget

/-- Every retained Möbius dyadic component at the large scale has one of the
three exact arithmetic types in the elementary type decomposition. -/
theorem largeMobiusDyadicComponentTypes {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (ν : MobiusDyadicLabel X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X)) :
    ∃ α : Fin (mobiusLabelFactors ν).length → ℝ,
      (∀ i, 0 ≤ α i) ∧
      (∑ i, α i = 1) ∧
      (∀ i,
        normalizedExponentConstant⁻¹ * X ^ α i ≤
            dyadicFactorScale ((mobiusLabelFactors ν)[i]) ∧
          dyadicFactorScale ((mobiusLabelFactors ν)[i]) ≤
            normalizedExponentConstant * X ^ α i) ∧
      (∀ i j, (mobiusLabelFactors ν)[i] = .mobius j →
        α i ≤ (1 / 8 : ℝ)) ∧
      largeDyadicComponentPackage (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        (fun n : PositiveInteger =>
          ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ))
        (mobiusLabelFactors ν) α := by
  obtain ⟨α, hα, hsum, hscale, hmob⟩ :=
    mobiusComponentNormalizedExponents hX hν
  have hlen := mobiusLabelFactorCount ν
  have hc := dyadicBinomialCoefficient_abs_le ν.1
  have hscaleGet :
      ∀ i,
        normalizedExponentConstant⁻¹ * X ^ α i ≤
            dyadicFactorScale ((mobiusLabelFactors ν).get i) ∧
          dyadicFactorScale ((mobiusLabelFactors ν).get i) ≤
            normalizedExponentConstant * X ^ α i := by
    intro i
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hscale i
  have hmobGet :
      ∀ i j, (mobiusLabelFactors ν).get i = .mobius j →
        α i ≤ (1 / 8 : ℝ) := by
    intro i j hij
    apply hmob i j
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hij
  have hcomponent :
      (fun n : PositiveInteger =>
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)) =
      groupedDyadicFactor (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1 : ℂ) (mobiusLabelFactors ν) := by
    funext n
    simp [groupedDyadicFactor, mobiusDyadicComponent_apply]
  have hpackage := largeGroupedDyadicComponentPackage hX
    (dyadicMobiusCutoff X) (dyadicBinomialCoefficient ν.1)
    (mobiusLabelFactors ν) hlen hc α hα hsum hscaleGet hmobGet
  refine ⟨α, hα, hsum, hscale, hmob, ?_⟩
  rw [hcomponent]
  exact hpackage

/-- The actual Möbius grouping construction retains the failed type-I
branch inequality when it designates a component as major type II.
The approved untagged package is its projection. -/
theorem largeMobiusDyadicComponentTypesTagged {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (ν : MobiusDyadicLabel X)
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X)) :
    ∃ α : Fin (mobiusLabelFactors ν).length → ℝ,
      (∀ i, 0 ≤ α i) ∧
      (∑ i, α i = 1) ∧
      (∀ i,
        normalizedExponentConstant⁻¹ * X ^ α i ≤
            dyadicFactorScale ((mobiusLabelFactors ν)[i]) ∧
          dyadicFactorScale ((mobiusLabelFactors ν)[i]) ≤
            normalizedExponentConstant * X ^ α i) ∧
      (∀ i j, (mobiusLabelFactors ν)[i] = .mobius j →
        α i ≤ (1 / 8 : ℝ)) ∧
      largeDyadicComponentTaggedPackage (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        (fun n : PositiveInteger =>
          ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ))
        (mobiusLabelFactors ν) α := by
  obtain ⟨α, hα, hsum, hscale, hmob⟩ :=
    mobiusComponentNormalizedExponents hX hν
  have hlen := mobiusLabelFactorCount ν
  have hc := dyadicBinomialCoefficient_abs_le ν.1
  have hscaleGet :
      ∀ i,
        normalizedExponentConstant⁻¹ * X ^ α i ≤
            dyadicFactorScale ((mobiusLabelFactors ν).get i) ∧
          dyadicFactorScale ((mobiusLabelFactors ν).get i) ≤
            normalizedExponentConstant * X ^ α i := by
    intro i
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hscale i
  have hmobGet :
      ∀ i j, (mobiusLabelFactors ν).get i = .mobius j →
        α i ≤ (1 / 8 : ℝ) := by
    intro i j hij
    apply hmob i j
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hij
  have hcomponent :
      (fun n : PositiveInteger =>
        ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)) =
      groupedDyadicFactor (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1 : ℂ) (mobiusLabelFactors ν) := by
    funext n
    simp [groupedDyadicFactor, mobiusDyadicComponent_apply]
  have hpackage := largeGroupedDyadicComponentTaggedPackage hX
    (dyadicMobiusCutoff X) (dyadicBinomialCoefficient ν.1)
    (mobiusLabelFactors ν) hlen hc α hα hsum hscaleGet hmobGet
  refine ⟨α, hα, hsum, hscale, hmob, ?_⟩
  rw [hcomponent]
  exact hpackage

#print axioms largeMobiusDyadicComponentTypesTagged

/-- Every retained von Mangoldt dyadic component at the large scale has one
of the three exact arithmetic types in the elementary type decomposition. -/
theorem largeVonMangoldtDyadicComponentTypes {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (ν : VonMangoldtDyadicLabel X)
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)) :
    ∃ α : Fin (vonMangoldtLabelFactors ν).length → ℝ,
      (∀ i, 0 ≤ α i) ∧
      (∑ i, α i = 1) ∧
      (∀ i,
        normalizedExponentConstant⁻¹ * X ^ α i ≤
            dyadicFactorScale ((vonMangoldtLabelFactors ν)[i]) ∧
          dyadicFactorScale ((vonMangoldtLabelFactors ν)[i]) ≤
            normalizedExponentConstant * X ^ α i) ∧
      (∀ i j, (vonMangoldtLabelFactors ν)[i] = .mobius j →
        α i ≤ (1 / 8 : ℝ)) ∧
      largeDyadicComponentPackage (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        (fun n : PositiveInteger =>
          ((vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ))
        (vonMangoldtLabelFactors ν) α := by
  obtain ⟨α, hα, hsum, hscale, hmob⟩ :=
    vonMangoldtComponentNormalizedExponents hX hν
  have hlen := vonMangoldtLabelFactorCount ν
  have hc := dyadicBinomialCoefficient_abs_le ν.1
  have hscaleGet :
      ∀ i,
        normalizedExponentConstant⁻¹ * X ^ α i ≤
            dyadicFactorScale ((vonMangoldtLabelFactors ν).get i) ∧
          dyadicFactorScale ((vonMangoldtLabelFactors ν).get i) ≤
            normalizedExponentConstant * X ^ α i := by
    intro i
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hscale i
  have hmobGet :
      ∀ i j, (vonMangoldtLabelFactors ν).get i = .mobius j →
        α i ≤ (1 / 8 : ℝ) := by
    intro i j hij
    apply hmob i j
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hij
  have hcomponent :
      (fun n : PositiveInteger =>
        ((vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)) =
      groupedDyadicFactor (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1 : ℂ) (vonMangoldtLabelFactors ν) := by
    funext n
    simp [groupedDyadicFactor, vonMangoldtDyadicComponent_apply]
  have hpackage := largeGroupedDyadicComponentPackage hX
    (dyadicMobiusCutoff X) (dyadicBinomialCoefficient ν.1)
    (vonMangoldtLabelFactors ν) hlen hc α hα hsum hscaleGet hmobGet
  refine ⟨α, hα, hsum, hscale, hmob, ?_⟩
  rw [hcomponent]
  exact hpackage

private theorem dyadicPartitionCount_le_eightLog {X : ℝ} (hX : 3 ≤ X) :
    (dyadicPartitionCount X : ℝ) ≤ 8 * Real.log X := by
  have hlogX : 1 < Real.log X := by
    linarith [Real.log_three_gt_d9,
      Real.log_le_log (by norm_num : (0 : ℝ) < 3) hX]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lower : (2 / 3 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2inv : (Real.log 2)⁻¹ ≤ (3 / 2 : ℝ) := by
    have hthird : 0 < (2 / 3 : ℝ) := by norm_num
    have h := (inv_le_inv₀ hlog2 hthird).2 hlog2lower
    norm_num at h ⊢
    exact h
  have h8X : 0 < 8 * X := by positivity
  have h8Xone : 1 ≤ 8 * X := by nlinarith [hX]
  have hlog8Xnonneg : 0 ≤ Real.log (8 * X) :=
    Real.log_nonneg h8Xone
  have hlogbnonneg : 0 ≤ Real.logb 2 (8 * X) := by
    rw [Real.logb]
    exact div_nonneg hlog8Xnonneg hlog2.le
  have hceil :
      (Nat.ceil (Real.logb 2 (8 * X)) : ℝ) <
        Real.logb 2 (8 * X) + 1 :=
    Nat.ceil_lt_add_one hlogbnonneg
  have hlog8X :
      Real.log (8 * X) = 3 * Real.log 2 + Real.log X := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ 3 ≠ 0)
        (by
          have hXpos : 0 < X := by linarith
          exact ne_of_gt hXpos),
      Real.log_pow]
    ring
  have hlogb :
      Real.logb 2 (8 * X) = 3 + Real.log X / Real.log 2 := by
    rw [Real.logb, hlog8X]
    field_simp
  have hD :
      (dyadicPartitionCount X : ℝ) <
        6 + Real.log X / Real.log 2 := by
    have hceil' :
        (Nat.ceil (Real.logb 2 (8 * X)) : ℝ) <
          1 + Real.logb 2 (8 * X) := by linarith [hceil]
    dsimp [dyadicPartitionCount]
    push_cast
    calc
      2 + (Nat.ceil (Real.logb 2 (8 * X)) : ℝ) <
          2 + (1 + Real.logb 2 (8 * X)) :=
        by linarith [hceil']
      _ = 6 + Real.log X / Real.log 2 := by rw [hlogb]; ring
  have hratio :
      Real.log X / Real.log 2 ≤ (3 / 2 : ℝ) * Real.log X := by
    rw [div_eq_mul_inv]
    calc
      Real.log X * (Real.log 2)⁻¹ ≤ Real.log X * (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2inv
          (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlogX.le)
      _ = (3 / 2 : ℝ) * Real.log X := by ring
  have hDle : 6 + Real.log X / Real.log 2 ≤ 8 * Real.log X := by
    have hratio' := hratio
    nlinarith [hlogX]
  exact hD.le.trans hDle

theorem mobiusDyadicLabels_typeCount {X : ℝ} (hX : 3 ≤ X) :
    (mobiusDyadicLabels X (dyadicMobiusCutoff X)).card ≤
      decompositionDType X := by
  have hD := mobiusDyadicLabels_card_le X (dyadicMobiusCutoff X)
  have hlog : 1 < Real.log X := by
    linarith [Real.log_three_gt_d9,
      Real.log_le_log (by norm_num : (0 : ℝ) < 3) hX]
  have hDpower :
      (dyadicPartitionCount X : ℝ) ^ 20 ≤
        (8 * Real.log X) ^ 20 :=
    pow_le_pow_left₀ (by positivity) (dyadicPartitionCount_le_eightLog hX) 20
  have hlogPower :
      (Real.log X) ^ 20 ≤ (Real.log X) ^ decompositionB := by
    exact pow_le_pow_right₀ (le_of_lt hlog) (by norm_num [decompositionB])
  have hconstant :
      10 * (8 : ℝ) ^ 20 ≤ decompositionC := by
    calc
      10 * (8 : ℝ) ^ 20 ≤ (2 : ℝ) ^ 200 := by norm_num
      _ ≤ decompositionC := by
        have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 :=
          one_le_pow₀ (by norm_num)
        dsimp [decompositionC]
        calc
          (2 : ℝ) ^ 200 = (2 : ℝ) ^ 200 * 1 := by ring
          _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
            mul_le_mul_of_nonneg_left h81 (by positivity)
  have hcount :
      10 * (dyadicPartitionCount X : ℝ) ^ 20 ≤ decompositionDType X := by
    calc
      10 * (dyadicPartitionCount X : ℝ) ^ 20 ≤
          10 * (8 * Real.log X) ^ 20 :=
        mul_le_mul_of_nonneg_left hDpower (by norm_num)
      _ = (10 * (8 : ℝ) ^ 20) * (Real.log X) ^ 20 := by ring
      _ ≤ decompositionC * (Real.log X) ^ 20 :=
        mul_le_mul_of_nonneg_right hconstant
          (pow_nonneg
            (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog.le) 20)
      _ ≤ decompositionC * (Real.log X) ^ decompositionB :=
        mul_le_mul_of_nonneg_left hlogPower (by
          unfold decompositionC
          positivity)
      _ = decompositionDType X := by rfl
  have hDreal :
      ((mobiusDyadicLabels X (dyadicMobiusCutoff X)).card : ℝ) ≤
        10 * (dyadicPartitionCount X : ℝ) ^ 20 := by exact_mod_cast hD
  exact le_trans hDreal hcount

theorem vonMangoldtDyadicLabels_typeCount {X : ℝ} (hX : 3 ≤ X) :
    (vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)).card ≤
      decompositionDType X := by
  have hD := vonMangoldtDyadicLabels_card_le X (dyadicMobiusCutoff X)
  have hlog : 1 < Real.log X := by
    linarith [Real.log_three_gt_d9,
      Real.log_le_log (by norm_num : (0 : ℝ) < 3) hX]
  have hDpower :
      (dyadicPartitionCount X : ℝ) ^ 20 ≤
        (8 * Real.log X) ^ 20 :=
    pow_le_pow_left₀ (by positivity) (dyadicPartitionCount_le_eightLog hX) 20
  have hlogPower :
      (Real.log X) ^ 20 ≤ (Real.log X) ^ decompositionB := by
    exact pow_le_pow_right₀ (le_of_lt hlog) (by norm_num [decompositionB])
  have hconstant :
      10 * (8 : ℝ) ^ 20 ≤ decompositionC := by
    calc
      10 * (8 : ℝ) ^ 20 ≤ (2 : ℝ) ^ 200 := by norm_num
      _ ≤ decompositionC := by
        have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 :=
          one_le_pow₀ (by norm_num)
        dsimp [decompositionC]
        calc
          (2 : ℝ) ^ 200 = (2 : ℝ) ^ 200 * 1 := by ring
          _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
            mul_le_mul_of_nonneg_left h81 (by positivity)
  have hcount :
      10 * (dyadicPartitionCount X : ℝ) ^ 20 ≤ decompositionDType X := by
    calc
      10 * (dyadicPartitionCount X : ℝ) ^ 20 ≤
          10 * (8 * Real.log X) ^ 20 :=
        mul_le_mul_of_nonneg_left hDpower (by norm_num)
      _ = (10 * (8 : ℝ) ^ 20) * (Real.log X) ^ 20 := by ring
      _ ≤ decompositionC * (Real.log X) ^ 20 :=
        mul_le_mul_of_nonneg_right hconstant
          (pow_nonneg
            (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog.le) 20)
      _ ≤ decompositionC * (Real.log X) ^ decompositionB :=
        mul_le_mul_of_nonneg_left hlogPower (by
          unfold decompositionC
          positivity)
      _ = decompositionDType X := by rfl
  have hDreal :
      ((vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)).card : ℝ) ≤
        10 * (dyadicPartitionCount X : ℝ) ^ 20 := by exact_mod_cast hD
  exact le_trans hDreal hcount

/-- The unit for Dirichlet convolution, restricted to positive integers. -/
private def positiveDeltaOne : ComplexPositiveIntegerFunction :=
  fun n => if n.1 = 1 then 1 else 0

private theorem complexPositiveDirichletConvolution_deltaOne_right
    (f : ComplexPositiveIntegerFunction) :
    complexPositiveDirichletConvolution f positiveDeltaOne = f := by
  have hdelta : toComplexArithmeticFunction positiveDeltaOne = 1 := by
    ext n
    by_cases hn : n = 1
    · subst n
      simp [toComplexArithmeticFunction, positiveDeltaOne]
    · simp [toComplexArithmeticFunction, positiveDeltaOne, hn,
        ArithmeticFunction.one_apply]
  funext n
  change (toComplexArithmeticFunction f *
    toComplexArithmeticFunction positiveDeltaOne) n.1 = f n
  rw [hdelta, mul_one, toComplexArithmeticFunction_apply]

private def deltaOneEntry (n : ℤ) : ℝ := if 0 < n then 1 else 0

private def deltaOneExit (n : ℤ) : ℝ := if 1 < n then 1 else 0

private def deltaOneIncrementSum (h : ℤ → ℝ) (a : ℤ) : List ℤ → ℝ
  | [] => 0
  | b :: bs => (h b - h a) + deltaOneIncrementSum h b bs

private theorem deltaOneIncrementSum_bounds (h : ℤ → ℝ) (L : ℝ)
    (hmono : ∀ a b, a ≤ b → h a ≤ h b)
    (hhi : ∀ a, h a ≤ L) :
    ∀ {a : ℤ} (bs : List ℤ), List.Pairwise (· ≤ ·) (a :: bs) →
      0 ≤ deltaOneIncrementSum h a bs ∧
        h a + deltaOneIncrementSum h a bs ≤ L := by
  intro a bs
  induction bs generalizing a with
  | nil =>
      intro _
      constructor
      · simp [deltaOneIncrementSum]
      · simpa [deltaOneIncrementSum] using hhi a
  | cons b bs ih =>
      intro hs
      have hparts := List.pairwise_cons.mp hs
      have hab : a ≤ b := hparts.1 b (by simp)
      have htailBound := ih (a := b) hparts.2
      have hdiff : 0 ≤ h b - h a := sub_nonneg.mpr (hmono a b hab)
      constructor
      · exact add_nonneg hdiff htailBound.1
      · change h a + ((h b - h a) + deltaOneIncrementSum h b bs) ≤ L
        calc
          h a + ((h b - h a) + deltaOneIncrementSum h b bs) =
              h b + deltaOneIncrementSum h b bs := by ring
          _ ≤ L := htailBound.2

private theorem deltaOneAdjacentVariation_cons_cons (g : ℤ → ℂ)
    (a b : ℤ) (bs : List ℤ) :
    listAdjacentVariation g (a :: b :: bs) =
      ‖g b - g a‖ + listAdjacentVariation g (b :: bs) := by
  simp [listAdjacentVariation, List.consecutivePairs, List.zip, List.tail]

private theorem deltaOneAdjacentVariation_sub_monotone_le
    (A B : ℤ → ℝ) (a : ℤ) (bs : List ℤ)
    (hmonoA : ∀ x y, x ≤ y → A x ≤ A y)
    (hmonoB : ∀ x y, x ≤ y → B x ≤ B y)
    (hsorted : List.Pairwise (· ≤ ·) (a :: bs)) :
    listAdjacentVariation (fun n => ((A n - B n : ℝ) : ℂ)) (a :: bs) ≤
      deltaOneIncrementSum A a bs + deltaOneIncrementSum B a bs := by
  induction bs generalizing a with
  | nil => simp [listAdjacentVariation, deltaOneIncrementSum,
      List.consecutivePairs]
  | cons b bs ih =>
      have hparts := List.pairwise_cons.mp hsorted
      have hab : a ≤ b := hparts.1 b (by simp)
      have htail := ih (a := b) hparts.2
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
        rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      rw [deltaOneAdjacentVariation_cons_cons]
      simp only [deltaOneIncrementSum] at htail ⊢
      calc
        ‖((A b - B b : ℝ) : ℂ) - ((A a - B a : ℝ) : ℂ)‖ +
            listAdjacentVariation (fun n => ((A n - B n : ℝ) : ℂ))
              (b :: bs) ≤
          (A b - A a) + (B b - B a) +
            (deltaOneIncrementSum A b bs + deltaOneIncrementSum B b bs) :=
          add_le_add hstep htail
        _ = (A b - A a + deltaOneIncrementSum A b bs) +
            (B b - B a + deltaOneIncrementSum B b bs) := by ring

private theorem deltaOneListSupNorm_le (g : ℤ → ℂ) (ns : List ℤ)
    (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ n ∈ ns, ‖g n‖ ≤ L) : listSupNorm g ns ≤ L := by
  have hfold : ∀ (l : List ℤ) (b : ℝ), b ≤ L →
      (∀ n ∈ l, ‖g n‖ ≤ L) → (l.map fun n => ‖g n‖).foldl max b ≤ L := by
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

private theorem deltaOneVariation_sub_monotone_le
    (P : Set ℤ) (g : ℤ → ℂ) (A B : ℤ → ℝ)
    (hmonoA : ∀ x y, x ≤ y → A x ≤ A y)
    (hmonoB : ∀ x y, x ≤ y → B x ≤ B y)
    (hloA : ∀ x, 0 ≤ A x) (hloB : ∀ x, 0 ≤ B x)
    (hhiA : ∀ x, A x ≤ 1) (hhiB : ∀ x, B x ≤ 1)
    (hAB : ∀ x ∈ P, B x ≤ A x)
    (hg : ∀ x ∈ P, g x = ((A x - B x : ℝ) : ℂ)) :
    orderedTotalVariation P g ≤ ENNReal.ofReal 3 := by
  unfold orderedTotalVariation
  apply iSup_le
  intro F
  let ns := F.1.sort (· ≤ ·)
  have hsorted : List.Pairwise (· ≤ ·) ns := Finset.pairwise_sort F.1 (· ≤ ·)
  have hmem : ∀ n ∈ ns, n ∈ P := by
    intro n hn
    exact F.2 n ((Finset.mem_sort (s := F.1) (r := (· ≤ ·))).1 hn)
  let g' : ℤ → ℂ := fun n => ((A n - B n : ℝ) : ℂ)
  have hsup : listSupNorm g' ns ≤ 1 := by
    apply deltaOneListSupNorm_le g' ns 1 (by norm_num)
    intro n hn
    simp only [g', Complex.norm_real, Real.norm_eq_abs]
    have hnonneg : 0 ≤ A n - B n := sub_nonneg.mpr (hAB n (hmem n hn))
    rw [abs_of_nonneg hnonneg]
    linarith [hhiA n, hloB n]
  have hadj : listAdjacentVariation g' ns ≤ 2 := by
    cases hs : ns with
    | nil => simp [listAdjacentVariation]
    | cons a tail =>
        have hsorted' : List.Pairwise (· ≤ ·) (a :: tail) := by
          simpa [hs] using hsorted
        have hvar := deltaOneAdjacentVariation_sub_monotone_le A B a tail
          hmonoA hmonoB hsorted'
        have hApath := deltaOneIncrementSum_bounds A 1 hmonoA hhiA tail hsorted'
        have hBpath := deltaOneIncrementSum_bounds B 1 hmonoB hhiB tail hsorted'
        have hAupper : deltaOneIncrementSum A a tail ≤ 1 := by
          linarith [hApath.2, hloA a]
        have hBupper : deltaOneIncrementSum B a tail ≤ 1 := by
          linarith [hBpath.2, hloB a]
        have htarget : listAdjacentVariation g' (a :: tail) ≤ 2 := by
          change listAdjacentVariation (fun n => ((A n - B n : ℝ) : ℂ))
            (a :: tail) ≤ 2
          calc
            listAdjacentVariation (fun n => ((A n - B n : ℝ) : ℂ))
                (a :: tail) ≤ deltaOneIncrementSum A a tail +
                  deltaOneIncrementSum B a tail := hvar
            _ ≤ 1 + 1 := add_le_add hAupper hBupper
            _ = 2 := by norm_num
        simpa [hs] using htarget
  have hfinite : finiteOrderedTotalVariation F.1 g ≤ 3 := by
    rw [finiteOrderedTotalVariation_congr_on_logPhase F.1 g g'
      (fun n hn => hg n (F.2 n hn))]
    unfold finiteOrderedTotalVariation
    change listSupNorm g' ns + listAdjacentVariation g' ns ≤ 3
    linarith
  exact ENNReal.ofReal_le_ofReal hfinite

/-- The unit Dirichlet factor has positive-integer residue variation at most
three, matching the bounded-range type-I argument. -/
private theorem positiveDeltaOne_residueVariation :
    complexPositiveIntegerResidueVariation positiveDeltaOne 1 (by decide) ≤
      ENNReal.ofReal 3 := by
  let A : ℤ → ℝ := deltaOneEntry
  let B : ℤ → ℝ := deltaOneExit
  have hmonoA : ∀ x y, x ≤ y → A x ≤ A y := by
    intro x y hxy
    by_cases hx : 0 < x <;> by_cases hy : 0 < y <;>
      simp [A, deltaOneEntry, hx, hy] <;> linarith
  have hmonoB : ∀ x y, x ≤ y → B x ≤ B y := by
    intro x y hxy
    by_cases hx : 1 < x <;> by_cases hy : 1 < y <;>
      simp [B, deltaOneExit, hx, hy] <;> linarith
  have hloA : ∀ x, 0 ≤ A x := by
    intro x
    by_cases hx : 0 < x <;> simp [A, deltaOneEntry, hx]
  have hloB : ∀ x, 0 ≤ B x := by
    intro x
    by_cases hx : 1 < x <;> simp [B, deltaOneExit, hx]
  have hhiA : ∀ x, A x ≤ 1 := by
    intro x
    by_cases hx : 0 < x <;> simp [A, deltaOneEntry, hx]
  have hhiB : ∀ x, B x ≤ 1 := by
    intro x
    by_cases hx : 1 < x <;> simp [B, deltaOneExit, hx]
  have hAB : ∀ x ∈ {n : ℤ | 0 < n}, B x ≤ A x := by
    intro x hx
    have hxpos : 0 < x := by simpa using hx
    by_cases hgt : 1 < x
    · simp [A, B, deltaOneEntry, deltaOneExit, hxpos, hgt]
    · simp [A, B, deltaOneEntry, deltaOneExit, hxpos, hgt]
  have hg : ∀ x ∈ {n : ℤ | 0 < n},
      complexPositiveIntegerZeroExtension positiveDeltaOne x =
        ((A x - B x : ℝ) : ℂ) := by
    intro x hx
    have hxpos : 0 < x := by simpa using hx
    have hcast : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hxpos.le
    by_cases hxone : x = 1
    · subst x
      simp [complexPositiveIntegerZeroExtension, positiveDeltaOne,
        A, B, deltaOneEntry, deltaOneExit]
    · have hgt : 1 < x := by omega
      have hnatNe : x.toNat ≠ 1 := by
        intro hnat
        apply hxone
        calc
          x = (x.toNat : ℤ) := hcast.symm
          _ = 1 := by exact_mod_cast hnat
      simp [complexPositiveIntegerZeroExtension, positiveDeltaOne,
        hnatNe, A, B, deltaOneEntry, deltaOneExit, hxpos, hgt]
  have htv := deltaOneVariation_sub_monotone_le
    {n : ℤ | 0 < n} (complexPositiveIntegerZeroExtension positiveDeltaOne)
    A B hmonoA hmonoB hloA hloB hhiA hhiB hAB hg
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
  simp only [Set.inter_univ]
  exact htv

/-- Truncate an arithmetic component at a real support endpoint. -/
def truncatePositiveComponent (N : ℝ)
    (f : ComplexPositiveIntegerFunction) : ComplexPositiveIntegerFunction :=
  fun n => if (n.1 : ℝ) ≤ N then f n else 0

private theorem truncatePositiveComponent_norm_le (N : ℝ)
    (f : ComplexPositiveIntegerFunction) (n : PositiveInteger) :
    ‖truncatePositiveComponent N f n‖ ≤ ‖f n‖ := by
  by_cases hn : (n.1 : ℝ) ≤ N
  · simp [truncatePositiveComponent, hn]
  · simp [truncatePositiveComponent, hn]

private theorem complexPositiveSecondMoment_truncate_le (N : ℝ)
    (f : ComplexPositiveIntegerFunction) (Y : ℝ) :
    complexPositiveSecondMoment (truncatePositiveComponent N f) Y ≤
      complexPositiveSecondMoment f Y := by
  unfold complexPositiveSecondMoment
  apply Finset.sum_le_sum
  intro n hn
  by_cases hpos : 0 < n
  · simp only [complexPositiveSecondMomentSummand, hpos, dite_true]
    have hnorm := truncatePositiveComponent_norm_le N f ⟨n, hpos⟩
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
  · simp [complexPositiveSecondMomentSummand, hpos]

private theorem truncatePositiveComponent_momentBound {X : ℝ}
    (N : ℝ) (f : ComplexPositiveIntegerFunction)
    (hf : complexPositiveSecondMomentBound (decompositionDelta X) f) :
    complexPositiveSecondMomentBound (decompositionDelta X)
      (truncatePositiveComponent N f) := by
  intro Y hY
  exact (complexPositiveSecondMoment_truncate_le N f Y).trans (hf Y hY)

private theorem decompositionC_ge_two200 :
    (2 : ℝ) ^ 200 ≤ decompositionC := by
  have h81 : (1 : ℝ) ≤ (81 : ℝ) ^ 160000 :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 81)
  dsimp [decompositionC]
  calc
    (2 : ℝ) ^ 200 = (2 : ℝ) ^ 200 * 1 := by ring
    _ ≤ (2 : ℝ) ^ 200 * (81 : ℝ) ^ 160000 :=
      mul_le_mul_of_nonneg_left h81 (by positivity)

private theorem decompositionDType_ge_three {X : ℝ} (hX : 3 ≤ X) :
    3 ≤ decompositionDType X := by
  have hlog : 1 ≤ Real.log X := by
    linarith [Real.log_three_gt_d9,
      Real.log_le_log (by norm_num : (0 : ℝ) < 3) hX]
  have hpow : 1 ≤ (Real.log X) ^ decompositionB := one_le_pow₀ hlog
  have hC : 3 ≤ decompositionC := by
    calc
      3 ≤ (2 : ℝ) ^ 200 := by norm_num
      _ ≤ decompositionC := decompositionC_ge_two200
  have hCnonneg : 0 ≤ decompositionC := le_trans (by norm_num) hC
  unfold decompositionDType
  calc
    3 ≤ decompositionC * 1 := by nlinarith [hC]
    _ ≤ decompositionC * (Real.log X) ^ decompositionB :=
      mul_le_mul_of_nonneg_left hpow hCnonneg

def elementaryTypeComponent (X : ℝ)
    (f : ComplexPositiveIntegerFunction) : Prop :=
  typeIFunction (decompositionDelta X)
      (decompositionC * X ^ (5 / 8 : ℝ)) f ∨
    typeI2Function (decompositionDelta X)
      (decompositionC * X ^ (7 / 16 : ℝ)) f ∨
    ∃ (z c : ℝ) (fs : List (DyadicArithmeticFactor X))
      (α : Fin fs.length → ℝ),
      (∀ i, 0 ≤ α i) ∧
      (∑ i, α i = 1) ∧
      (∀ i,
        normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
          dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i) ∧
      (∀ i j, fs.get i = .mobius j → α i ≤ (1 / 8 : ℝ)) ∧
      largeTypeIIDyadicComponentData z c (decompositionDelta X) f fs α

private theorem largePackage_to_elementaryTypeComponent {X : ℝ}
    (z c : ℝ) (f : ComplexPositiveIntegerFunction)
    (fs : List (DyadicArithmeticFactor X)) (α : Fin fs.length → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1)
    (hscale : ∀ i,
      normalizedExponentConstant⁻¹ * X ^ α i ≤ dyadicFactorScale (fs.get i) ∧
        dyadicFactorScale (fs.get i) ≤ normalizedExponentConstant * X ^ α i)
    (hmob : ∀ i j, fs.get i = .mobius j → α i ≤ (1 / 8 : ℝ))
    (h : largeDyadicComponentPackage z c (decompositionDelta X) f fs α) :
    elementaryTypeComponent X f := by
  rcases h with hI | hI2 | hII
  · exact Or.inl hI
  · exact Or.inr (Or.inl hI2)
  · exact Or.inr (Or.inr ⟨z, c, fs, α, hα, hsum, hscale, hmob, hII⟩)

/-- The small-X construction is specifically type I, retaining the branch
rather than only the overlapping arithmetic-type disjunction. -/
theorem truncatedRawDyadicComponent_typeI_explicit {X : ℝ}
    (hX : 3 ≤ X) (hXsmall : X ≤ (2 : ℝ) ^ 120)
    (z : ℝ) (c : ℝ)
    (fs : List (DyadicArithmeticFactor X))
    (hlen : 1 ≤ fs.length ∧ fs.length ≤ 20)
    (hc : |c| ≤ (2 : ℝ) ^ 10) :
    typeIFunction (decompositionDelta X)
      (decompositionC * X ^ (5 / 8 : ℝ))
      (truncatePositiveComponent (4 * X)
        (groupedDyadicFactor z (c : ℂ) fs)) := by
  have hconst := decompositionDelta_data hX
  have hDinv : (decompositionDelta X)⁻¹ = decompositionDType X :=
    hconst.2.2.2
  have hD3 := decompositionDType_ge_three hX
  have hC200 := decompositionC_ge_two200
  have hXone : 1 ≤ X := by linarith
  have hXpow : 1 ≤ X ^ (5 / 8 : ℝ) :=
    Real.one_le_rpow hXone (by norm_num)
  have hCnonneg : 0 ≤ decompositionC :=
    le_trans (by norm_num : 0 ≤ (2 : ℝ) ^ 200) hC200
  have hAupper : 4 * X ≤ decompositionC * X ^ (5 / 8 : ℝ) := by
    have h4X : 4 * X ≤ (2 : ℝ) ^ 122 := by
      calc
        4 * X ≤ 4 * (2 : ℝ) ^ 120 := by nlinarith [hXsmall]
        _ = (2 : ℝ) ^ 122 := by norm_num
    calc
      4 * X ≤ (2 : ℝ) ^ 122 := h4X
      _ ≤ (2 : ℝ) ^ 200 := by norm_num
      _ ≤ decompositionC := hC200
      _ = decompositionC * 1 := by ring
      _ ≤ decompositionC * X ^ (5 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left hXpow hCnonneg
  have hc' : ‖(c : ℂ)‖ ≤ (2 : ℝ) ^ 10 := by simpa using hc
  have hmomRaw := groupedDyadicFactor_momentBounds_exact hX z (c : ℂ)
    hc' fs hlen.2
  have hmom : complexPositiveSecondMomentBound (decompositionDelta X)
      (truncatePositiveComponent (4 * X)
        (groupedDyadicFactor z (c : ℂ) fs)) :=
    truncatePositiveComponent_momentBound (4 * X)
      (groupedDyadicFactor z (c : ℂ) fs) hmomRaw.1
  have hAone : 1 ≤ decompositionC * X ^ (5 / 8 : ℝ) := by
    exact one_le_mul_of_one_le_of_one_le
      (le_trans (by norm_num : (1 : ℝ) ≤ (2 : ℝ) ^ 200) hC200) hXpow
  have hvariation :
      complexPositiveIntegerResidueVariation positiveDeltaOne 1 (by decide) ≤
        ENNReal.ofReal ((decompositionDelta X)⁻¹) := by
    rw [hDinv]
    exact (positiveDeltaOne_residueVariation).trans
      (ENNReal.ofReal_le_ofReal hD3)
  have hfactor :
      truncatePositiveComponent (4 * X)
          (groupedDyadicFactor z (c : ℂ) fs) =
        complexPositiveDirichletConvolution
          (truncatePositiveComponent (4 * X)
            (groupedDyadicFactor z (c : ℂ) fs)) positiveDeltaOne := by
    exact (complexPositiveDirichletConvolution_deltaOne_right _).symm
  have hsupport :
      complexPositiveSupportedOnInterval
        (truncatePositiveComponent (4 * X)
          (groupedDyadicFactor z (c : ℂ) fs))
        1 (decompositionC * X ^ (5 / 8 : ℝ)) := by
    intro n hn
    have hcut : (n.1 : ℝ) ≤ 4 * X := by
      by_contra hnot
      have hgt : 4 * X < (n.1 : ℝ) := not_le.mp hnot
      have hfalse : ¬ (n.1 : ℝ) ≤ 4 * X := not_le.mpr hgt
      simp [truncatePositiveComponent, hfalse] at hn
    exact ⟨by exact_mod_cast n.2, le_trans hcut hAupper⟩
  refine ⟨hconst.1, hconst.2.1, hAone,
    ⟨truncatePositiveComponent (4 * X)
        (groupedDyadicFactor z (c : ℂ) fs), positiveDeltaOne,
      1, by decide, hfactor, hsupport, hmom, by norm_num,
      (by rw [hDinv]; exact le_trans (by norm_num) hD3), hvariation⟩⟩

private theorem truncatedRawDyadicComponent_typeI {X : ℝ}
    (hX : 3 ≤ X) (hXsmall : X ≤ (2 : ℝ) ^ 120)
    (z : ℝ) (c : ℝ)
    (fs : List (DyadicArithmeticFactor X))
    (hlen : 1 ≤ fs.length ∧ fs.length ≤ 20)
    (hc : |c| ≤ (2 : ℝ) ^ 10) :
    elementaryTypeComponent X
      (truncatePositiveComponent (4 * X)
        (groupedDyadicFactor z (c : ℂ) fs)) := by
  exact Or.inl (truncatedRawDyadicComponent_typeI_explicit hX hXsmall z c fs hlen hc)

/-- An exact finite decomposition into the arithmetic types of `lu:types`.
The component predicate retains the separate major-grouping and
large-original-factor data required in the type-II alternative. -/
structure ElementaryArithmeticTypeDecomposition (X : ℝ)
    (g : ComplexPositiveIntegerFunction) where
  Index : Type
  indices : Finset Index
  component : Index → ComplexPositiveIntegerFunction
  decomposition : ∀ n : PositiveInteger,
    X / 2 ≤ (n.1 : ℝ) → (n.1 : ℝ) ≤ 4 * X →
      g n = ∑ i ∈ indices, component i n
  componentType : ∀ i ∈ indices, elementaryTypeComponent X (component i)
  count : (indices.card : ℝ) ≤ decompositionDType X

private theorem assembleDyadicTypeDecomposition {X : ℝ}
    (hX : 3 ≤ X) (z : ℝ) {Index : Type}
    (indices : Finset Index) (g : ComplexPositiveIntegerFunction)
    (raw : Index → ComplexPositiveIntegerFunction)
    (factors : Index → List (DyadicArithmeticFactor X))
    (coefficient : Index → ℝ)
    (raw_eq_grouped : ∀ i,
      raw i = groupedDyadicFactor z (coefficient i : ℂ) (factors i))
    (hlen : ∀ i, 1 ≤ (factors i).length ∧ (factors i).length ≤ 20)
    (hcoeff : ∀ i, |coefficient i| ≤ (2 : ℝ) ^ 10)
    (hdecomposition : ∀ n : PositiveInteger,
      X / 2 ≤ (n.1 : ℝ) → (n.1 : ℝ) ≤ 4 * X →
        g n = ∑ i ∈ indices, raw i n)
    (hlarge : ∀ i ∈ indices, (2 : ℝ) ^ 120 ≤ X →
      ∃ α : Fin (factors i).length → ℝ,
        (∀ j, 0 ≤ α j) ∧
        (∑ j, α j = 1) ∧
        (∀ j,
          normalizedExponentConstant⁻¹ * X ^ α j ≤
              dyadicFactorScale ((factors i).get j) ∧
            dyadicFactorScale ((factors i).get j) ≤
              normalizedExponentConstant * X ^ α j) ∧
        (∀ j k, (factors i).get j = .mobius k → α j ≤ (1 / 8 : ℝ)) ∧
        largeDyadicComponentPackage z (coefficient i)
          (decompositionDelta X) (raw i) (factors i) α)
    (hcount : (indices.card : ℝ) ≤ decompositionDType X) :
    Nonempty (ElementaryArithmeticTypeDecomposition X g) := by
  classical
  let component : Index → ComplexPositiveIntegerFunction := fun i =>
    if (2 : ℝ) ^ 120 ≤ X then raw i
    else truncatePositiveComponent (4 * X) (raw i)
  refine ⟨⟨Index, indices, component, ?_, ?_, hcount⟩⟩
  · intro n hnlo hnhi
    by_cases hlargeX : (2 : ℝ) ^ 120 ≤ X
    · simpa [component, hlargeX] using hdecomposition n hnlo hnhi
    · have hcut : ∀ i, component i n = raw i n := by
        intro i
        simp [component, hlargeX, truncatePositiveComponent, hnhi]
      calc
        g n = ∑ i ∈ indices, raw i n := hdecomposition n hnlo hnhi
        _ = ∑ i ∈ indices, component i n := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcut]
  · intro i hi
    by_cases hlargeX : (2 : ℝ) ^ 120 ≤ X
    · obtain ⟨α, hα, hsum, hscale, hmob, hpackage⟩ :=
        hlarge i hi hlargeX
      simpa [component, hlargeX] using
        largePackage_to_elementaryTypeComponent z (coefficient i)
          (raw i) (factors i) α hα hsum hscale hmob hpackage
    · have hXsmall : X ≤ (2 : ℝ) ^ 120 := by
        exact le_of_lt (lt_of_not_ge hlargeX)
      have hsmall := truncatedRawDyadicComponent_typeI hX hXsmall z
        (coefficient i) (factors i) (hlen i) (hcoeff i)
      rw [← raw_eq_grouped i] at hsmall
      simpa [component, hlargeX] using hsmall

def mobiusComplexPositiveFunction : ComplexPositiveIntegerFunction :=
  fun n => ((ArithmeticFunction.moebius n.1 : ℝ) : ℂ)

def vonMangoldtComplexPositiveFunction : ComplexPositiveIntegerFunction :=
  fun n => ((ArithmeticFunction.vonMangoldt n.1 : ℝ) : ℂ)

private def mobiusRawDyadicComponent {X : ℝ}
    (ν : MobiusDyadicLabel X) : ComplexPositiveIntegerFunction :=
  fun n => ((mobiusDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)

private def vonMangoldtRawDyadicComponent {X : ℝ}
    (ν : VonMangoldtDyadicLabel X) : ComplexPositiveIntegerFunction :=
  fun n => ((vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n.1 : ℝ) : ℂ)

/-- The exact indexed decomposition in blueprint item `lucomb:type-decomposition`
for the Möbius function. -/
theorem mobiusElementaryTypeDecomposition {X : ℝ} (hX : 3 ≤ X) :
    Nonempty (ElementaryArithmeticTypeDecomposition X
      mobiusComplexPositiveFunction) := by
  classical
  let indices := mobiusDyadicLabels X (dyadicMobiusCutoff X)
  let raw : MobiusDyadicLabel X → ComplexPositiveIntegerFunction :=
    mobiusRawDyadicComponent
  let factors : MobiusDyadicLabel X → List (DyadicArithmeticFactor X) :=
    mobiusLabelFactors
  let coefficient : MobiusDyadicLabel X → ℝ :=
    fun ν => dyadicBinomialCoefficient ν.1
  have hraw : ∀ ν,
      raw ν = groupedDyadicFactor (dyadicMobiusCutoff X)
        (coefficient ν : ℂ) (factors ν) := by
    intro ν
    funext n
    simp [raw, mobiusRawDyadicComponent, groupedDyadicFactor,
      factors, coefficient, mobiusDyadicComponent_apply]
  have hlen : ∀ ν, 1 ≤ (factors ν).length ∧ (factors ν).length ≤ 20 := by
    intro ν
    exact mobiusLabelFactorCount ν
  have hcoeff : ∀ ν, |coefficient ν| ≤ (2 : ℝ) ^ 10 := by
    intro ν
    exact dyadicBinomialCoefficient_abs_le ν.1
  have hdecomposition : ∀ n : PositiveInteger,
      X / 2 ≤ (n.1 : ℝ) → (n.1 : ℝ) ≤ 4 * X →
        mobiusComplexPositiveFunction n = ∑ ν ∈ indices, raw ν n := by
    intro n hnlo hnhi
    have h := mobiusDyadicDecomposition hX n.2 hnlo hnhi
    have hcast := congrArg (fun r : ℝ => (r : ℂ)) h
    simpa [mobiusComplexPositiveFunction, indices, raw,
      mobiusRawDyadicComponent, Complex.ofReal_sum] using hcast
  have hlarge : ∀ ν ∈ indices, (2 : ℝ) ^ 120 ≤ X →
      ∃ α : Fin (factors ν).length → ℝ,
        (∀ j, 0 ≤ α j) ∧
        (∑ j, α j = 1) ∧
        (∀ j,
          normalizedExponentConstant⁻¹ * X ^ α j ≤
              dyadicFactorScale ((factors ν).get j) ∧
            dyadicFactorScale ((factors ν).get j) ≤
              normalizedExponentConstant * X ^ α j) ∧
        (∀ j k, (factors ν).get j = .mobius k → α j ≤ (1 / 8 : ℝ)) ∧
        largeDyadicComponentPackage (dyadicMobiusCutoff X) (coefficient ν)
          (decompositionDelta X) (raw ν) (factors ν) α := by
    intro ν hν hXlarge
    obtain ⟨α, hα, hsum, hscale, hmob, hpackage⟩ :=
      largeMobiusDyadicComponentTypes hXlarge ν hν
    have hscale' : ∀ j,
        normalizedExponentConstant⁻¹ * X ^ α j ≤
            dyadicFactorScale ((factors ν).get j) ∧
          dyadicFactorScale ((factors ν).get j) ≤
            normalizedExponentConstant * X ^ α j := by
      intro j
      simpa only [List.get_eq_getElem, Fin.getElem_fin, factors] using hscale j
    have hmob' : ∀ j k, (factors ν).get j = .mobius k →
        α j ≤ (1 / 8 : ℝ) := by
      intro j k hj
      apply hmob j k
      simpa only [List.get_eq_getElem, Fin.getElem_fin, factors] using hj
    refine ⟨α, hα, hsum, hscale', hmob', ?_⟩
    change largeDyadicComponentPackage (dyadicMobiusCutoff X)
      (coefficient ν) (decompositionDelta X) (raw ν) (factors ν) α at hpackage
    exact hpackage
  have hcount : (indices.card : ℝ) ≤ decompositionDType X := by
    exact_mod_cast mobiusDyadicLabels_typeCount hX
  exact assembleDyadicTypeDecomposition hX (dyadicMobiusCutoff X)
    indices mobiusComplexPositiveFunction raw factors coefficient hraw hlen
    hcoeff hdecomposition hlarge hcount

/-- The exact indexed decomposition in blueprint item `lucomb:type-decomposition`
for the von Mangoldt function. -/
theorem vonMangoldtElementaryTypeDecomposition {X : ℝ} (hX : 3 ≤ X) :
    Nonempty (ElementaryArithmeticTypeDecomposition X
      vonMangoldtComplexPositiveFunction) := by
  classical
  let indices := vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)
  let raw : VonMangoldtDyadicLabel X → ComplexPositiveIntegerFunction :=
    vonMangoldtRawDyadicComponent
  let factors : VonMangoldtDyadicLabel X → List (DyadicArithmeticFactor X) :=
    vonMangoldtLabelFactors
  let coefficient : VonMangoldtDyadicLabel X → ℝ :=
    fun ν => dyadicBinomialCoefficient ν.1
  have hraw : ∀ ν,
      raw ν = groupedDyadicFactor (dyadicMobiusCutoff X)
        (coefficient ν : ℂ) (factors ν) := by
    intro ν
    funext n
    simp [raw, vonMangoldtRawDyadicComponent, groupedDyadicFactor,
      factors, coefficient, vonMangoldtDyadicComponent_apply]
  have hlen : ∀ ν, 1 ≤ (factors ν).length ∧ (factors ν).length ≤ 20 := by
    intro ν
    exact vonMangoldtLabelFactorCount ν
  have hcoeff : ∀ ν, |coefficient ν| ≤ (2 : ℝ) ^ 10 := by
    intro ν
    exact dyadicBinomialCoefficient_abs_le ν.1
  have hdecomposition : ∀ n : PositiveInteger,
      X / 2 ≤ (n.1 : ℝ) → (n.1 : ℝ) ≤ 4 * X →
        vonMangoldtComplexPositiveFunction n = ∑ ν ∈ indices, raw ν n := by
    intro n hnlo hnhi
    have h := vonMangoldtDyadicDecomposition hX n.2 hnlo hnhi
    have hcast := congrArg (fun r : ℝ => (r : ℂ)) h
    simpa [vonMangoldtComplexPositiveFunction, indices, raw,
      vonMangoldtRawDyadicComponent, Complex.ofReal_sum] using hcast
  have hlarge : ∀ ν ∈ indices, (2 : ℝ) ^ 120 ≤ X →
      ∃ α : Fin (factors ν).length → ℝ,
        (∀ j, 0 ≤ α j) ∧
        (∑ j, α j = 1) ∧
        (∀ j,
          normalizedExponentConstant⁻¹ * X ^ α j ≤
              dyadicFactorScale ((factors ν).get j) ∧
            dyadicFactorScale ((factors ν).get j) ≤
              normalizedExponentConstant * X ^ α j) ∧
        (∀ j k, (factors ν).get j = .mobius k → α j ≤ (1 / 8 : ℝ)) ∧
        largeDyadicComponentPackage (dyadicMobiusCutoff X) (coefficient ν)
          (decompositionDelta X) (raw ν) (factors ν) α := by
    intro ν hν hXlarge
    obtain ⟨α, hα, hsum, hscale, hmob, hpackage⟩ :=
      largeVonMangoldtDyadicComponentTypes hXlarge ν hν
    have hscale' : ∀ j,
        normalizedExponentConstant⁻¹ * X ^ α j ≤
            dyadicFactorScale ((factors ν).get j) ∧
          dyadicFactorScale ((factors ν).get j) ≤
            normalizedExponentConstant * X ^ α j := by
      intro j
      simpa only [List.get_eq_getElem, Fin.getElem_fin, factors] using hscale j
    have hmob' : ∀ j k, (factors ν).get j = .mobius k →
        α j ≤ (1 / 8 : ℝ) := by
      intro j k hj
      apply hmob j k
      simpa only [List.get_eq_getElem, Fin.getElem_fin, factors] using hj
    refine ⟨α, hα, hsum, hscale', hmob', ?_⟩
    change largeDyadicComponentPackage (dyadicMobiusCutoff X)
      (coefficient ν) (decompositionDelta X) (raw ν) (factors ν) α at hpackage
    exact hpackage
  have hcount : (indices.card : ℝ) ≤ decompositionDType X := by
    exact_mod_cast vonMangoldtDyadicLabels_typeCount hX
  exact assembleDyadicTypeDecomposition hX (dyadicMobiusCutoff X)
    indices vonMangoldtComplexPositiveFunction raw factors coefficient hraw hlen
    hcoeff hdecomposition hlarge hcount

/-- The manifest-facing form of `lucomb:type-decomposition`, for either
of the two arithmetic functions in its statement. -/
theorem elementaryTypeDecomposition {X : ℝ} (hX : 3 ≤ X)
    (g : ComplexPositiveIntegerFunction)
    (hg : g = mobiusComplexPositiveFunction ∨
      g = vonMangoldtComplexPositiveFunction) :
    Nonempty (ElementaryArithmeticTypeDecomposition X g) := by
  rcases hg with hμ | hΛ
  · rw [hμ]
    exact mobiusElementaryTypeDecomposition hX
  · rw [hΛ]
    exact vonMangoldtElementaryTypeDecomposition hX

end

end FractionalPrimes.Literature.Uniformity.Combinatorics

end

#print axioms FractionalPrimes.Literature.Uniformity.Combinatorics.mobiusElementaryTypeDecomposition
#print axioms FractionalPrimes.Literature.Uniformity.Combinatorics.vonMangoldtElementaryTypeDecomposition
#print axioms FractionalPrimes.Literature.Uniformity.Combinatorics.elementaryTypeDecomposition
