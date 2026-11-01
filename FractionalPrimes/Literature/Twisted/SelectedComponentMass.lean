module

public import FractionalPrimes.Literature.Twisted.LocalDivisorMoment
public import FractionalPrimes.Literature.Twisted.DivisorTwentyBound
public import FractionalPrimes.Literature.Uniformity.ArithmeticGroupedFactorBounds
public import FractionalPrimes.Literature.Uniformity.ArchimedeanTwist

/-!
# Local mass of selected arithmetic components

This module implements `ltw:component-mass`. The first prerequisite
tracks the unique logarithmic factor of a von Mangoldt component
without assigning a logarithmic loss to its Möbius and one factors.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

noncomputable section

/-- Pointwise majorant for one dyadic factor. -/
def dyadicFactorMassWeight {X : ℝ} (f : DyadicArithmeticFactor X) : ℝ :=
  match f with
  | .logarithm _ => Real.log (8 * X)
  | .one _ => 1
  | .mobius _ => 1

theorem dyadicFactorMassWeight_nonneg {X : ℝ} (hX : 3 ≤ X)
    (f : DyadicArithmeticFactor X) : 0 ≤ dyadicFactorMassWeight f := by
  cases f with
  | one j => simp [dyadicFactorMassWeight]
  | mobius j => simp [dyadicFactorMassWeight]
  | logarithm j =>
      dsimp [dyadicFactorMassWeight]
      linarith [log_eightX_gt_one hX]

theorem dyadicFactorFunction_abs_le_massWeight {X : ℝ} (hX : 3 ≤ X)
    (z : ℝ) (f : DyadicArithmeticFactor X) (n : ℕ) :
    |dyadicFactorFunction z f n| ≤ dyadicFactorMassWeight f := by
  cases f with
  | one j =>
      by_cases hI : inDyadicInterval j.val.val n
      · simp [dyadicFactorFunction, dyadicOneFactor_apply,
          dyadicFactorMassWeight, hI]
      · simp [dyadicFactorFunction, dyadicOneFactor_apply,
          dyadicFactorMassWeight, hI]
  | mobius j =>
      by_cases hI : inDyadicInterval j.val.val n ∧ (n : ℝ) ≤ z
      · simpa [dyadicFactorFunction, dyadicMobiusFactor_apply,
          dyadicFactorMassWeight, hI] using
          (show |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 by
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n))
      · simp [dyadicFactorFunction, dyadicMobiusFactor_apply,
          dyadicFactorMassWeight, hI]
  | logarithm j =>
      by_cases hI : inDyadicInterval j.val.val n
      · have hnpos : 0 < n := by
          have := hI.1
          omega
        have hupper : (n : ℝ) ≤ 8 * X := by
          have hn' : n ≤ dyadicUpperNat j.val.val := hI.2
          exact (by exact_mod_cast hn' : (n : ℝ) ≤ dyadicUpperNat j.val.val).trans
            (dyadicUpperNat_le_eightX hX j)
        have hlog : Real.log (n : ℝ) ≤ Real.log (8 * X) :=
          Real.log_le_log (by exact_mod_cast hnpos) hupper
        have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
          Real.log_natCast_nonneg n
        simpa [dyadicFactorFunction, dyadicLogFactor_apply,
          dyadicFactorMassWeight, hI, ArithmeticFunction.log_apply,
          abs_of_nonneg hlognonneg] using hlog
      · have hL : 0 ≤ Real.log (8 * X) := by
          linarith [log_eightX_gt_one hX]
        simpa [dyadicFactorFunction, dyadicLogFactor_apply,
          dyadicFactorMassWeight, hI] using hL

/-- The product of the individual factor majorants. -/
def dyadicFactorsMassWeight {X : ℝ}
    (fs : List (DyadicArithmeticFactor X)) : ℝ :=
  (fs.map dyadicFactorMassWeight).prod

theorem dyadicFactorsMassWeight_nonneg {X : ℝ} (hX : 3 ≤ X)
    (fs : List (DyadicArithmeticFactor X)) :
    0 ≤ dyadicFactorsMassWeight fs := by
  dsimp [dyadicFactorsMassWeight]
  apply List.prod_nonneg
  intro a ha
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
  exact dyadicFactorMassWeight_nonneg hX f

/-- Convolution of the selected dyadic factors is bounded by the
factor-weight product times the ordered divisor coefficient. -/
theorem dyadicConvolutionFactors_abs_le_massWeight {X : ℝ} (hX : 3 ≤ X)
    (z : ℝ) (fs : List (DyadicArithmeticFactor X))
    (n : PositiveInteger) :
    |dyadicConvolutionFactors z fs n.1| ≤
      dyadicFactorsMassWeight fs * (divisorCoefficient fs.length n.1 : ℝ) := by
  revert n
  induction fs with
  | nil =>
      intro n
      by_cases hn1 : n.1 = 1
      · simp [dyadicConvolutionFactors, dyadicFactorsMassWeight,
          divisorCoefficient, ArithmeticFunction.one_apply, hn1]
      · simp [dyadicConvolutionFactors, dyadicFactorsMassWeight,
          divisorCoefficient, ArithmeticFunction.one_apply, hn1]
  | cons f fs ih =>
      intro n
      have hfactor := dyadicFactorFunction_abs_le_massWeight hX z f
      have hweight0 := dyadicFactorMassWeight_nonneg hX f
      have htail0 := dyadicFactorsMassWeight_nonneg hX fs
      rw [dyadicConvolutionFactors, List.map_cons, List.prod_cons]
      have hsum :
          |∑ d ∈ n.1.divisors,
            dyadicConvolutionFactors z fs d * dyadicFactorFunction z f (n.1 / d)| ≤
            ∑ d ∈ n.1.divisors,
              dyadicFactorsMassWeight fs *
                (divisorCoefficient fs.length d : ℝ) *
                  dyadicFactorMassWeight f := by
        calc
          _ ≤ ∑ d ∈ n.1.divisors,
                |dyadicConvolutionFactors z fs d * dyadicFactorFunction z f (n.1 / d)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro d hd
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
            have htail := ih ⟨d, hdpos⟩
            have hhead := hfactor (n.1 / d)
            have hupper0 :
                0 ≤ dyadicFactorsMassWeight fs *
                  (divisorCoefficient fs.length d : ℝ) :=
              mul_nonneg htail0 (Nat.cast_nonneg _)
            rw [abs_mul]
            exact mul_le_mul htail hhead (abs_nonneg _) hupper0
      have hrec := divisorCoefficient_succ_divisor_sum fs.length n.1
      have hsum' :
          ∑ d ∈ n.1.divisors,
            dyadicFactorsMassWeight fs *
              (divisorCoefficient fs.length d : ℝ) *
                dyadicFactorMassWeight f =
            dyadicFactorsMassWeight (f :: fs) *
              (divisorCoefficient (fs.length + 1) n.1 : ℝ) := by
        simp only [dyadicFactorsMassWeight, List.map_cons, List.prod_cons]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        rw [← Nat.cast_sum, hrec]
        ring
      rw [List.length_cons]
      change |(dyadicFactorFunction z f * dyadicConvolutionFactors z fs) n.1| ≤ _
      rw [mul_comm, ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal
          (f := fun a b => dyadicConvolutionFactors z fs a *
            dyadicFactorFunction z f b)]
      exact hsum.trans hsum'.le

theorem mobiusLabelFactors_massWeight {X : ℝ}
    (ν : MobiusDyadicLabel X) :
    dyadicFactorsMassWeight (mobiusLabelFactors ν) = 1 := by
  simp [dyadicFactorsMassWeight, mobiusLabelFactors,
    dyadicFactorMassWeight, List.map_append, List.prod_append,
    List.prod_ofFn, Function.comp_def]

theorem vonMangoldtLabelFactors_massWeight {X : ℝ}
    (ν : VonMangoldtDyadicLabel X) :
    dyadicFactorsMassWeight (vonMangoldtLabelFactors ν) =
      Real.log (8 * X) := by
  simp [dyadicFactorsMassWeight, vonMangoldtLabelFactors,
    dyadicFactorMassWeight, List.map_append, List.prod_append,
    List.prod_ofFn, Function.comp_def]

/-- Both permitted dyadic component families obey the blueprint's
single-logarithm coefficient estimate. -/
theorem mobiusDyadicComponent_abs_le_divisorTwenty
    {X : ℝ} (hX : 3 ≤ X) (ν : MobiusDyadicLabel X)
    (n : ℕ) (hn : 0 < n) :
    |mobiusDyadicComponent (dyadicMobiusCutoff X) ν n| ≤
      2 ^ 10 * Real.log (8 * X) *
        (divisorCoefficient 2 n : ℝ) ^ 20 := by
  have hL : 1 ≤ Real.log (8 * X) := (log_eightX_gt_one hX).le
  have hC := dyadicBinomialCoefficient_abs_le ν.1
  have hlen := (mobiusLabelFactorCount ν).2
  have hconv := dyadicConvolutionFactors_abs_le_massWeight hX
    (dyadicMobiusCutoff X) (mobiusLabelFactors ν) ⟨n, hn⟩
  rw [mobiusLabelFactors_massWeight, one_mul] at hconv
  have hdiv := divisorCoefficient_mono hn hlen
  have htwenty := divisorCoefficient_twenty_le_two_pow n hn
  rw [mobiusDyadicComponent_apply, abs_mul]
  have hcoeff0 : 0 ≤ (divisorCoefficient 20 n : ℝ) := Nat.cast_nonneg _
  have htwo0 : 0 ≤ (divisorCoefficient 2 n : ℝ) ^ 20 := by positivity
  have hdivReal :
      (divisorCoefficient (mobiusLabelFactors ν).length n : ℝ) ≤
        divisorCoefficient 20 n := by exact_mod_cast hdiv
  have htwentyReal :
      (divisorCoefficient 20 n : ℝ) ≤
        (divisorCoefficient 2 n : ℝ) ^ 20 := by exact_mod_cast htwenty
  calc
    |dyadicBinomialCoefficient ν.1| *
        |dyadicConvolutionFactors (dyadicMobiusCutoff X)
          (mobiusLabelFactors ν) n| ≤
        (2 ^ 10 : ℝ) *
          (divisorCoefficient (mobiusLabelFactors ν).length n : ℝ) := by
            exact mul_le_mul hC hconv (abs_nonneg _) (by norm_num)
    _ ≤ (2 ^ 10 : ℝ) * Real.log (8 * X) *
        (divisorCoefficient 2 n : ℝ) ^ 20 := by
          have hchain := hdivReal.trans htwentyReal
          nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 ^ 10)
            htwo0]

theorem vonMangoldtDyadicComponent_abs_le_divisorTwenty
    {X : ℝ} (hX : 3 ≤ X) (ν : VonMangoldtDyadicLabel X)
    (n : ℕ) (hn : 0 < n) :
    |vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n| ≤
      2 ^ 10 * Real.log (8 * X) *
        (divisorCoefficient 2 n : ℝ) ^ 20 := by
  have hL : 0 ≤ Real.log (8 * X) := (log_eightX_gt_one hX).le.trans' (by norm_num)
  have hC := dyadicBinomialCoefficient_abs_le ν.1
  have hlen := (vonMangoldtLabelFactorCount ν).2
  have hconv := dyadicConvolutionFactors_abs_le_massWeight hX
    (dyadicMobiusCutoff X) (vonMangoldtLabelFactors ν) ⟨n, hn⟩
  rw [vonMangoldtLabelFactors_massWeight] at hconv
  have hdiv := divisorCoefficient_mono hn hlen
  have htwenty := divisorCoefficient_twenty_le_two_pow n hn
  rw [vonMangoldtDyadicComponent_apply, abs_mul]
  have hdivReal :
      (divisorCoefficient (vonMangoldtLabelFactors ν).length n : ℝ) ≤
        divisorCoefficient 20 n := by exact_mod_cast hdiv
  have htwentyReal :
      (divisorCoefficient 20 n : ℝ) ≤
        (divisorCoefficient 2 n : ℝ) ^ 20 := by exact_mod_cast htwenty
  calc
    |dyadicBinomialCoefficient ν.1| *
        |dyadicConvolutionFactors (dyadicMobiusCutoff X)
          (vonMangoldtLabelFactors ν) n| ≤
        (2 ^ 10 : ℝ) *
          (Real.log (8 * X) *
            (divisorCoefficient (vonMangoldtLabelFactors ν).length n : ℝ)) := by
              exact mul_le_mul hC hconv (abs_nonneg _) (by positivity)
    _ ≤ (2 ^ 10 : ℝ) * Real.log (8 * X) *
        (divisorCoefficient 2 n : ℝ) ^ 20 := by
          nlinarith

/-- A retained factor list of length at most twenty has the exact
support window used by the selected-component mass lemma. -/
theorem selectedFactorList_support_bounds
    {X z : ℝ} {fs : List (DyadicArithmeticFactor X)}
    (hret : dyadicFactorsRetained (X := X) (z := z) fs)
    (hlenlo : 1 ≤ fs.length) (hlenhi : fs.length ≤ 20)
    {n : ℕ} (hne : dyadicConvolutionFactors z fs n ≠ 0) :
    X / (2 : ℝ) ^ 21 < (n : ℝ) ∧
      (n : ℝ) ≤ (2 : ℝ) ^ 22 * X := by
  have hfs : fs ≠ [] := by
    intro he
    simp [he] at hlenlo
  obtain ⟨hlow, hupp⟩ :=
    dyadicConvolutionFactors_support_bounds fs hfs hne
  obtain ⟨hprodlo, hprodhi⟩ :=
    dyadicFactorsRetained_product_bounds hret hlenhi
  have hprodpos : 0 < dyadicFactorScaleProduct fs :=
    dyadicFactorScaleProduct_pos fs
  have hpow : (2 : ℝ) ^ fs.length ≤ (2 : ℝ) ^ 20 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlenhi
  constructor
  · exact hprodlo.trans_lt hlow
  · calc
      (n : ℝ) ≤ (2 : ℝ) ^ fs.length * dyadicFactorScaleProduct fs := hupp
      _ ≤ (2 : ℝ) ^ 20 * dyadicFactorScaleProduct fs :=
        mul_le_mul_of_nonneg_right hpow hprodpos.le
      _ ≤ (2 : ℝ) ^ 20 * (4 * X) :=
        mul_le_mul_of_nonneg_left hprodhi (by positivity)
      _ = (2 : ℝ) ^ 22 * X := by norm_num; ring

theorem mobiusDyadicComponent_support_bounds
    {X : ℝ} {ν : MobiusDyadicLabel X}
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X))
    {n : ℕ} (hne : mobiusDyadicComponent (dyadicMobiusCutoff X) ν n ≠ 0) :
    X / (2 : ℝ) ^ 21 < (n : ℝ) ∧
      (n : ℝ) ≤ (2 : ℝ) ^ 22 * X := by
  have hconv : dyadicConvolutionFactors (dyadicMobiusCutoff X)
      (mobiusLabelFactors ν) n ≠ 0 := by
    intro hz
    apply hne
    simp [mobiusDyadicComponent_apply, hz]
  exact selectedFactorList_support_bounds
    (mobiusDyadicLabels_mem hν)
    (mobiusLabelFactorCount ν).1 (mobiusLabelFactorCount ν).2 hconv

theorem vonMangoldtDyadicComponent_support_bounds
    {X : ℝ} {ν : VonMangoldtDyadicLabel X}
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X))
    {n : ℕ} (hne : vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n ≠ 0) :
    X / (2 : ℝ) ^ 21 < (n : ℝ) ∧
      (n : ℝ) ≤ (2 : ℝ) ^ 22 * X := by
  have hconv : dyadicConvolutionFactors (dyadicMobiusCutoff X)
      (vonMangoldtLabelFactors ν) n ≠ 0 := by
    intro hz
    apply hne
    simp [vonMangoldtDyadicComponent_apply, hz]
  exact selectedFactorList_support_bounds
    (vonMangoldtDyadicLabels_mem hν)
    (vonMangoldtLabelFactorCount ν).1 (vonMangoldtLabelFactorCount ν).2 hconv

/-- The exact scale and constant in `ltw:component-mass`. -/
def selectedComponentH0 (X : ℝ) : ℝ :=
  ((2 : ℝ) ^ 22 * X) ^ (1 / 4 : ℝ)

def selectedComponentK (X : ℝ) : ℝ :=
  (2 : ℝ) ^ 90 *
    (1 + Real.log ((2 : ℝ) ^ 22 * X)) ^ (2 ^ 180 + 1)

theorem selectedComponentH0_le_sqrt {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) :
    selectedComponentH0 X ≤ Real.sqrt X := by
  have hXpos : 0 < X := by positivity
  have hX22 : (2 : ℝ) ^ 22 ≤ X := by
    norm_num at hX ⊢
    linarith
  have hZle : (2 : ℝ) ^ 22 * X ≤ X ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hX22) hXpos.le]
  calc
    selectedComponentH0 X ≤ (X ^ 2) ^ (1 / 4 : ℝ) := by
      exact Real.rpow_le_rpow (by positivity) hZle (by norm_num)
    _ = X ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast_mul hXpos.le 2 (1 / 4 : ℝ)]
      norm_num
    _ = Real.sqrt X := (Real.sqrt_eq_rpow X).symm

theorem selectedComponent_prefactor_le_K {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) :
    (2 : ℝ) ^ 10 * Real.log (8 * X) * (2 : ℝ) ^ 80 *
      (1 + Real.log (selectedComponentH0 X)) ^ (2 ^ 180) ≤
        selectedComponentK X := by
  let Z : ℝ := (2 : ℝ) ^ 22 * X
  let D : ℝ := selectedComponentH0 X
  let HZ : ℝ := 1 + Real.log Z
  let HD : ℝ := 1 + Real.log D
  let E : ℕ := 2 ^ 180
  have hXpos : 0 < X := by positivity
  have hZ1 : 1 ≤ Z := by
    dsimp [Z]
    nlinarith [hX]
  have hD1 : 1 ≤ D := by
    dsimp [D, selectedComponentH0]
    exact Real.one_le_rpow hZ1 (by norm_num)
  have hDle : D ≤ Z := by
    have htmp : Z ^ (1 / 4 : ℝ) ≤ Z ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
    simpa only [D, selectedComponentH0, Z, Real.rpow_one] using htmp
  have hHDle : HD ≤ HZ := by
    dsimp [HD, HZ]
    linarith [Real.log_le_log (by linarith : 0 < D) hDle]
  have hHZ1 : 1 ≤ HZ := by
    dsimp [HZ]
    linarith [Real.log_nonneg hZ1]
  have hlogle : Real.log (8 * X) ≤ HZ := by
    have h8Z : 8 * X ≤ Z := by
      dsimp [Z]
      nlinarith [hXpos.le]
    have hlog := Real.log_le_log (by positivity : 0 < 8 * X) h8Z
    dsimp [HZ]
    linarith
  have hlog0 : 0 ≤ Real.log (8 * X) := by
    have h8 : 1 ≤ 8 * X := by nlinarith [hX]
    exact Real.log_nonneg h8
  have hHD0 : 0 ≤ HD := by
    dsimp [HD]
    linarith [Real.log_nonneg hD1]
  have hpow : HD ^ E ≤ HZ ^ E := pow_le_pow_left₀ hHD0 hHDle E
  have hcoeff :
      Real.log (8 * X) * HD ^ E ≤ HZ * HZ ^ E :=
    mul_le_mul hlogle hpow (pow_nonneg hHD0 E)
      ((zero_le_one).trans hHZ1)
  have hpowSucc : HZ * HZ ^ E = HZ ^ (E + 1) := by
    rw [pow_succ]
    exact mul_comm _ _
  have hconst : (2 : ℝ) ^ 10 * (2 : ℝ) ^ 80 = (2 : ℝ) ^ 90 := by
    rw [← pow_add]
  have hfinal :
      (2 : ℝ) ^ 10 * Real.log (8 * X) * (2 : ℝ) ^ 80 * HD ^ E ≤
        (2 : ℝ) ^ 90 * HZ ^ (E + 1) := by
    calc
      _ = ((2 : ℝ) ^ 10 * (2 : ℝ) ^ 80) *
            (Real.log (8 * X) * HD ^ E) := by ac_rfl
      _ ≤ (2 : ℝ) ^ 90 * (HZ * HZ ^ E) := by
        rw [hconst]
        exact mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = (2 : ℝ) ^ 90 * HZ ^ (E + 1) :=
        congrArg (fun v : ℝ => (2 : ℝ) ^ 90 * v) hpowSucc
  simpa only [selectedComponentK, Z, D, HZ, HD, E] using hfinal

/-- Generic local mass conclusion from the exact pointwise component
majorant, under the support cutoff `n≤2^22 X`. -/
theorem selectedComponentLocalMass_of_pointwise
    {X : ℝ} (hX : (2 : ℝ) ^ 120 ≤ X)
    (f : ℕ → ℝ)
    (hpoint : ∀ n : ℕ, 0 < n →
      |f n| ≤ (2 : ℝ) ^ 10 * Real.log (8 * X) *
        (divisorCoefficient 2 n : ℝ) ^ 20)
    (x h : ℝ) (hh : 0 ≤ h) :
    (∑ n ∈ (Finset.Icc 1 (Nat.floor ((2 : ℝ) ^ 22 * X))).filter
        (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h), |f n|) ≤
      selectedComponentK X * (h + selectedComponentH0 X) := by
  let Z : ℝ := (2 : ℝ) ^ 22 * X
  let A : ℝ := (2 : ℝ) ^ 10 * Real.log (8 * X)
  let D : ℝ := selectedComponentH0 X
  let H : ℝ := 1 + Real.log D
  let E : ℕ := 2 ^ 180
  let s := (Finset.Icc 1 (Nat.floor Z)).filter
    (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h)
  have hXpos : 0 < X := by positivity
  have hZ1 : 1 ≤ Z := by
    dsimp [Z]
    nlinarith [hX]
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have hlog : 0 ≤ Real.log (8 * X) :=
      Real.log_nonneg (by nlinarith [hX])
    positivity
  have hD0 : 0 ≤ D := by
    dsimp [D, selectedComponentH0]
    positivity
  have hlocal := localDivisorMoment 4 20 (by norm_num) (by norm_num)
    Z x h hZ1 hh
  have hroot : Z ^ (1 / (4 : ℝ) : ℝ) = D := rfl
  have hR : (2 * 4 + 1) * 20 = 180 := by norm_num
  have hsum :
      (∑ n ∈ s, (divisorCoefficient 2 n : ℝ) ^ 20) ≤
        (2 : ℝ) ^ 80 * (h + D) * H ^ E := by
    simpa [s, Z, D, selectedComponentH0, H, E] using hlocal
  have hpref : A * (2 : ℝ) ^ 80 * H ^ E ≤
      selectedComponentK X := by
    simpa only [A, H, D, E] using selectedComponent_prefactor_le_K hX
  have hlen0 : 0 ≤ h + D := add_nonneg hh hD0
  calc
    (∑ n ∈ s, |f n|) ≤
        ∑ n ∈ s, A * (divisorCoefficient 2 n : ℝ) ^ 20 := by
          apply Finset.sum_le_sum
          intro n hn
          exact hpoint n (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    _ = A * ∑ n ∈ s, (divisorCoefficient 2 n : ℝ) ^ 20 := by
      rw [Finset.mul_sum]
    _ ≤ A * ((2 : ℝ) ^ 80 * (h + D) * H ^ E) :=
      mul_le_mul_of_nonneg_left hsum hA0
    _ ≤ selectedComponentK X * (h + D) := by
      calc
        _ = (A * (2 : ℝ) ^ 80 * H ^ E) * (h + D) := by ac_rfl
        _ ≤ selectedComponentK X * (h + D) :=
          mul_le_mul_of_nonneg_right hpref hlen0

/-- Positive integers in the paper's real half-open interval. The
natural-floor bound makes this a finite sum without an artificial
support cutoff. -/
def selectedPositiveInterval (x h : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor (max 0 (x + h)))).filter
    (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h)

theorem selectedPositiveInterval_mem_iff
    (x h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    n ∈ selectedPositiveInterval x h ↔
      0 < n ∧ x < (n : ℝ) ∧ (n : ℝ) ≤ x + h := by
  constructor
  · intro hn
    have hn' := Finset.mem_filter.mp hn
    exact ⟨(Finset.mem_Icc.mp hn'.1).1, hn'.2.1, hn'.2.2⟩
  · rintro ⟨hn, hxlo, hxhi⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · exact hn
      · apply Nat.le_floor
        have hmax : (n : ℝ) ≤ max 0 (x + h) :=
          hxhi.trans (le_max_right _ _)
        exact hmax
    · exact ⟨hxlo, hxhi⟩

/-- A function supported below `Z` has the same sum over the full
half-open interval as over the interval truncated at `Z`. -/
theorem selectedPositiveInterval_sum_eq_cutoff
    (f : ℕ → ℝ) (Z x h : ℝ) (hh : 0 ≤ h)
    (hsupport : ∀ n : ℕ, f n ≠ 0 → (n : ℝ) ≤ Z) :
    (∑ n ∈ selectedPositiveInterval x h, |f n|) =
      ∑ n ∈ (Finset.Icc 1 (Nat.floor Z)).filter
        (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h), |f n| := by
  let s := (Finset.Icc 1 (Nat.floor Z)).filter
    (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h)
  have hsubset : s ⊆ selectedPositiveInterval x h := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    exact (selectedPositiveInterval_mem_iff x h hh n).mpr
      ⟨(Finset.mem_Icc.mp hn'.1).1, hn'.2.1, hn'.2.2⟩
  apply (Finset.sum_subset hsubset ?_).symm
  intro n hnfull hnnot
  have hnpos : 0 < n :=
    ((selectedPositiveInterval_mem_iff x h hh n).mp hnfull).1
  by_cases hf : f n = 0
  · simp [hf]
  · exfalso
    have hnZ : (n : ℝ) ≤ Z := hsupport n hf
    have hfloor : n ≤ Nat.floor Z := Nat.le_floor hnZ
    have hx := (selectedPositiveInterval_mem_iff x h hh n).mp hnfull
    apply hnnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnpos, hfloor⟩,
      hx.2.1, hx.2.2⟩

/-- The selected Möbius components have the blueprint support and
local absolute mass bound. -/
theorem mobiusSelectedComponentLocalMass
    {X : ℝ} (hX : (2 : ℝ) ^ 120 ≤ X)
    {ν : MobiusDyadicLabel X}
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X)) :
    (∀ n : ℕ, mobiusDyadicComponent (dyadicMobiusCutoff X) ν n ≠ 0 →
      X / (2 : ℝ) ^ 21 < (n : ℝ) ∧ (n : ℝ) ≤ (2 : ℝ) ^ 22 * X) ∧
    selectedComponentH0 X ≤ Real.sqrt X ∧
    ∀ x h : ℝ, 0 ≤ h →
      (∑ n ∈ selectedPositiveInterval x h,
        |mobiusDyadicComponent (dyadicMobiusCutoff X) ν n|) ≤
          selectedComponentK X * (h + selectedComponentH0 X) := by
  have hX3 : 3 ≤ X := by
    norm_num at hX ⊢
    linarith
  have hsupport (n : ℕ)
      (hn : mobiusDyadicComponent (dyadicMobiusCutoff X) ν n ≠ 0) :=
    mobiusDyadicComponent_support_bounds hν hn
  refine ⟨hsupport, selectedComponentH0_le_sqrt hX, ?_⟩
  intro x h hh
  let f : ℕ → ℝ := fun n => mobiusDyadicComponent (dyadicMobiusCutoff X) ν n
  have hcut : ∀ n : ℕ, f n ≠ 0 → (n : ℝ) ≤ (2 : ℝ) ^ 22 * X := by
    intro n hn
    exact (hsupport n hn).2
  rw [selectedPositiveInterval_sum_eq_cutoff f ((2 : ℝ) ^ 22 * X) x h hh hcut]
  exact selectedComponentLocalMass_of_pointwise hX f
    (fun n hn => mobiusDyadicComponent_abs_le_divisorTwenty hX3 ν n hn)
    x h hh

/-- The selected von Mangoldt components have the same bound, with
their unique logarithmic factor included in `K_X`. -/
theorem vonMangoldtSelectedComponentLocalMass
    {X : ℝ} (hX : (2 : ℝ) ^ 120 ≤ X)
    {ν : VonMangoldtDyadicLabel X}
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)) :
    (∀ n : ℕ, vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n ≠ 0 →
      X / (2 : ℝ) ^ 21 < (n : ℝ) ∧ (n : ℝ) ≤ (2 : ℝ) ^ 22 * X) ∧
    selectedComponentH0 X ≤ Real.sqrt X ∧
    ∀ x h : ℝ, 0 ≤ h →
      (∑ n ∈ selectedPositiveInterval x h,
        |vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n|) ≤
          selectedComponentK X * (h + selectedComponentH0 X) := by
  have hX3 : 3 ≤ X := by
    norm_num at hX ⊢
    linarith
  have hsupport (n : ℕ)
      (hn : vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n ≠ 0) :=
    vonMangoldtDyadicComponent_support_bounds hν hn
  refine ⟨hsupport, selectedComponentH0_le_sqrt hX, ?_⟩
  intro x h hh
  let f : ℕ → ℝ := fun n => vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n
  have hcut : ∀ n : ℕ, f n ≠ 0 → (n : ℝ) ≤ (2 : ℝ) ^ 22 * X := by
    intro n hn
    exact (hsupport n hn).2
  rw [selectedPositiveInterval_sum_eq_cutoff f ((2 : ℝ) ^ 22 * X) x h hh hcut]
  exact selectedComponentLocalMass_of_pointwise hX f
    (fun n hn => vonMangoldtDyadicComponent_abs_le_divisorTwenty hX3 ν n hn)
    x h hh

/-- `ltw:component-mass` for every selected dyadic component in both
arithmetic families, with the exact blueprint constants. -/
theorem selectedComponentLocalMass
    (X : ℝ) (hX : (2 : ℝ) ^ 120 ≤ X) :
    (∀ ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X),
      (∀ n : ℕ, mobiusDyadicComponent (dyadicMobiusCutoff X) ν n ≠ 0 →
        X / (2 : ℝ) ^ 21 < (n : ℝ) ∧ (n : ℝ) ≤ (2 : ℝ) ^ 22 * X) ∧
      selectedComponentH0 X ≤ Real.sqrt X ∧
      ∀ x h : ℝ, 0 ≤ h →
        (∑ n ∈ selectedPositiveInterval x h,
          |mobiusDyadicComponent (dyadicMobiusCutoff X) ν n|) ≤
            selectedComponentK X * (h + selectedComponentH0 X)) ∧
    (∀ ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X),
      (∀ n : ℕ, vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n ≠ 0 →
        X / (2 : ℝ) ^ 21 < (n : ℝ) ∧ (n : ℝ) ≤ (2 : ℝ) ^ 22 * X) ∧
      selectedComponentH0 X ≤ Real.sqrt X ∧
      ∀ x h : ℝ, 0 ≤ h →
        (∑ n ∈ selectedPositiveInterval x h,
          |vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n|) ≤
            selectedComponentK X * (h + selectedComponentH0 X)) := by
  constructor
  · intro ν hν
    exact mobiusSelectedComponentLocalMass hX hν
  · intro ν hν
    exact vonMangoldtSelectedComponentLocalMass hX hν

/-- Multiplication by any complex weight of modulus at most one
preserves the real-component local mass estimate. This includes the
phase `n^{iT}` and residue-class indicators in the blueprint. -/
theorem selectedPositiveInterval_weighted_mass_le
    (f : ℕ → ℝ) (w : ℕ → ℂ)
    (hw : ∀ n, ‖w n‖ ≤ 1) (x h : ℝ) :
    (∑ n ∈ selectedPositiveInterval x h, ‖(f n : ℂ) * w n‖) ≤
      ∑ n ∈ selectedPositiveInterval x h, |f n| := by
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simpa using mul_le_mul_of_nonneg_left (hw n) (abs_nonneg (f n))

theorem selectedComponentLocalMass_weighted
    (X : ℝ) (hX : (2 : ℝ) ^ 120 ≤ X) :
    (∀ ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X),
      ∀ w : ℕ → ℂ, (∀ n, ‖w n‖ ≤ 1) →
        ∀ x h : ℝ, 0 ≤ h →
          (∑ n ∈ selectedPositiveInterval x h,
            ‖(mobiusDyadicComponent (dyadicMobiusCutoff X) ν n : ℂ) * w n‖) ≤
              selectedComponentK X * (h + selectedComponentH0 X)) ∧
    (∀ ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X),
      ∀ w : ℕ → ℂ, (∀ n, ‖w n‖ ≤ 1) →
        ∀ x h : ℝ, 0 ≤ h →
          (∑ n ∈ selectedPositiveInterval x h,
            ‖(vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n : ℂ) * w n‖) ≤
              selectedComponentK X * (h + selectedComponentH0 X)) := by
  obtain ⟨hm, hv⟩ := selectedComponentLocalMass X hX
  constructor
  · intro ν hν w hw x h hh
    exact (selectedPositiveInterval_weighted_mass_le
      (fun n => mobiusDyadicComponent (dyadicMobiusCutoff X) ν n)
      w hw x h).trans ((hm ν hν).2.2 x h hh)
  · intro ν hν w hw x h hh
    exact (selectedPositiveInterval_weighted_mass_le
      (fun n => vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n)
      w hw x h).trans ((hv ν hν).2.2 x h hh)

/-- The precise combined Mellin phase, residue restriction, and
additional modulus-at-most-one multiplier from the source. -/
def selectedComponentModulatedWeight
    (T : ℝ) (q a : ℕ) (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  archimedeanTwist T n * (if n % q = a then 1 else 0) * u n

theorem selectedComponentModulatedWeight_norm_le_one
    (T : ℝ) (q a : ℕ) (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (n : ℕ) :
    ‖selectedComponentModulatedWeight T q a u n‖ ≤ 1 := by
  by_cases hres : n % q = a
  · simp [selectedComponentModulatedWeight, hres,
      norm_archimedeanTwist_eq_one]
    exact hu n
  · simp [selectedComponentModulatedWeight, hres]

theorem selectedComponentLocalMass_modulated
    (X : ℝ) (hX : (2 : ℝ) ^ 120 ≤ X)
    (T : ℝ) (q a : ℕ) (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) :
    (∀ ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X),
      ∀ x h : ℝ, 0 ≤ h →
        (∑ n ∈ selectedPositiveInterval x h,
          ‖(mobiusDyadicComponent (dyadicMobiusCutoff X) ν n : ℂ) *
            selectedComponentModulatedWeight T q a u n‖) ≤
              selectedComponentK X * (h + selectedComponentH0 X)) ∧
    (∀ ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X),
      ∀ x h : ℝ, 0 ≤ h →
        (∑ n ∈ selectedPositiveInterval x h,
          ‖(vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n : ℂ) *
            selectedComponentModulatedWeight T q a u n‖) ≤
              selectedComponentK X * (h + selectedComponentH0 X)) := by
  obtain ⟨hm, hv⟩ := selectedComponentLocalMass_weighted X hX
  exact ⟨fun ν hν => hm ν hν _
    (selectedComponentModulatedWeight_norm_le_one T q a u hu),
    fun ν hν => hv ν hν _
      (selectedComponentModulatedWeight_norm_le_one T q a u hu)⟩

#print axioms dyadicFactorFunction_abs_le_massWeight
#print axioms dyadicConvolutionFactors_abs_le_massWeight
#print axioms mobiusLabelFactors_massWeight
#print axioms vonMangoldtLabelFactors_massWeight
#print axioms mobiusDyadicComponent_abs_le_divisorTwenty
#print axioms vonMangoldtDyadicComponent_abs_le_divisorTwenty
#print axioms selectedFactorList_support_bounds
#print axioms mobiusDyadicComponent_support_bounds
#print axioms vonMangoldtDyadicComponent_support_bounds
#print axioms selectedComponentH0_le_sqrt
#print axioms selectedComponent_prefactor_le_K
#print axioms selectedComponentLocalMass_of_pointwise
#print axioms selectedPositiveInterval_sum_eq_cutoff
#print axioms mobiusSelectedComponentLocalMass
#print axioms vonMangoldtSelectedComponentLocalMass
#print axioms selectedComponentLocalMass
#print axioms selectedComponentLocalMass_weighted
#print axioms selectedComponentLocalMass_modulated

end
end FractionalPrimes.Literature.Twisted
end
