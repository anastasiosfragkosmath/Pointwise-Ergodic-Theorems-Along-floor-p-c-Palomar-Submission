module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic
public import FractionalPrimes.Literature.Uniformity.HeathBrownIdentity

/-!
# Exact dyadic components of the Möbius and von Mangoldt functions

This file formalizes blueprint item `lucomb:dyadic-components`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity.Combinatorics

open Finset

noncomputable section

/-- The dyadic partition count from `lucomb:dyadic-components`. -/
def dyadicPartitionCount (X : ℝ) : ℕ :=
  2 + Nat.ceil (Real.logb 2 (8 * X))

/-- The exact cutoff `z=(4X)^(1/10)` used in the truncated identity. -/
def dyadicMobiusCutoff (X : ℝ) : ℝ := (4 * X) ^ (1 / 10 : ℝ)

theorem dyadicMobiusCutoff_pow {X : ℝ} (hX : 0 ≤ X) :
    dyadicMobiusCutoff X ^ 10 = 4 * X := by
  dsimp [dyadicMobiusCutoff]
  have hbase : 0 ≤ 4 * X := mul_nonneg (by norm_num) hX
  convert Real.rpow_inv_natCast_pow (x := 4 * X) hbase
      (n := 10) (by norm_num) using 1 <;> norm_num [one_div]

theorem dyadicMobiusCutoff_ge_one {X : ℝ} (hX : 3 ≤ X) :
    1 ≤ dyadicMobiusCutoff X := by
  by_contra h
  have hzlt : dyadicMobiusCutoff X < 1 := lt_of_not_ge h
  have hX0 : 0 ≤ X := by linarith
  have hznonneg : 0 ≤ dyadicMobiusCutoff X :=
    Real.rpow_nonneg (mul_nonneg (by norm_num) hX0) _
  have hpowle : dyadicMobiusCutoff X ^ 10 ≤ 1 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_one hznonneg hzlt.le (by norm_num)
  rw [dyadicMobiusCutoff_pow hX0] at hpowle
  have hlarge : 1 < 4 * X := by linarith
  linarith

/-- The upper endpoint of dyadic interval `j`, namely `2^j`. -/
def dyadicUpperNat (j : ℕ) : ℕ := 2 ^ j

/-- The positive-integer lower endpoint of dyadic interval `j`. -/
def dyadicLowerNat (j : ℕ) : ℕ := if j = 0 then 0 else 2 ^ j.pred

/-- The real scale `N_j` for the interval `(N_j, 2 N_j]`. -/
def dyadicScale (j : ℕ) : ℝ :=
  if j = 0 then (1 / 2 : ℝ) else (2 : ℝ) ^ j.pred

/-- The finite set of dyadic interval indices whose lower endpoint is below `4X`. -/
abbrev DyadicIndex (X : ℝ) :=
  {j : Fin (dyadicPartitionCount X) // dyadicScale j.val < 4 * X}

/-- Membership in the integer version of `(N_j, 2 N_j]`. -/
def inDyadicInterval (j n : ℕ) : Prop :=
  dyadicLowerNat j < n ∧ n ≤ dyadicUpperNat j

instance (j n : ℕ) : Decidable (inDyadicInterval j n) := by
  unfold inDyadicInterval
  infer_instance

/-- The constant-one arithmetic function restricted to a dyadic interval. -/
noncomputable def dyadicOneFactor (j : ℕ) : ArithmeticFunction ℝ := by
  classical
  exact ⟨fun n => if inDyadicInterval j n then 1 else 0, by
    simp [inDyadicInterval, dyadicLowerNat]
  ⟩

/-- The logarithm restricted to a dyadic interval. -/
noncomputable def dyadicLogFactor (j : ℕ) : ArithmeticFunction ℝ := by
  classical
  exact ⟨fun n => if inDyadicInterval j n then ArithmeticFunction.log n else 0, by
    simp [inDyadicInterval, dyadicLowerNat]
  ⟩

/-- The Möbius function restricted to a dyadic interval and the cutoff `z`. -/
noncomputable def dyadicMobiusFactor (z : ℝ) (j : ℕ) : ArithmeticFunction ℝ := by
  classical
  exact ⟨fun n => if inDyadicInterval j n ∧ (n : ℝ) ≤ z then
      (ArithmeticFunction.moebius n : ℝ) else 0, by
    simp [inDyadicInterval, dyadicLowerNat]
  ⟩

@[simp]
theorem dyadicOneFactor_apply (j n : ℕ) :
    dyadicOneFactor j n = if inDyadicInterval j n then 1 else 0 := by
  classical
  rfl

@[simp]
theorem dyadicLogFactor_apply (j n : ℕ) :
    dyadicLogFactor j n = if inDyadicInterval j n then ArithmeticFunction.log n else 0 := by
  classical
  rfl

@[simp]
theorem dyadicMobiusFactor_apply (z : ℝ) (j n : ℕ) :
    dyadicMobiusFactor z j n =
      if inDyadicInterval j n ∧ (n : ℝ) ≤ z then
        (ArithmeticFunction.moebius n : ℝ) else 0 := by
  classical
  rfl

/-- The scalar indicator of a dyadic interval. -/
noncomputable def dyadicIntervalIndicator (j n : ℕ) : ℝ :=
  if inDyadicInterval j n then 1 else 0

/-- For positive integers the dyadic intervals are exactly the level sets of
`Nat.clog 2`. -/
theorem inDyadicInterval_iff_clog {j n : ℕ} (hn : 0 < n) :
    inDyadicInterval j n ↔ Nat.clog 2 n = j := by
  constructor
  · intro h
    have hjUpper : Nat.clog 2 n ≤ j :=
      Nat.clog_le_of_le_pow (by simpa [dyadicUpperNat] using h.2)
    by_cases hj : j = 0
    · have hnle : n ≤ 1 := by simpa [dyadicUpperNat, hj] using h.2
      have hn1 : n = 1 := by omega
      simp [hj, hn1]
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
      have hjLower : 2 ^ j.pred < n := by
        simpa [dyadicLowerNat, hj] using h.1
      have hpred : j.pred < Nat.clog 2 n :=
        (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 hjLower
      have hjsucc : j.pred + 1 = j := Nat.succ_pred_eq_of_pos hjpos
      omega
  · intro h
    subst j
    have hnUpper : n ≤ 2 ^ Nat.clog 2 n :=
      Nat.le_pow_clog (by decide : 1 < 2) n
    by_cases hnOne : n = 1
    · subst n
      simp [inDyadicInterval, dyadicLowerNat, dyadicUpperNat]
    · have hnBig : 1 < n := by omega
      have hnLower : 2 ^ (Nat.clog 2 n).pred < n :=
        Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hnBig
      have hclogPos : 0 < Nat.clog 2 n :=
        Nat.clog_pos (by decide : 1 < 2) hnBig
      exact ⟨by simpa [dyadicLowerNat, hclogPos.ne'] using hnLower,
        by simpa [dyadicUpperNat] using hnUpper⟩

/-- Convert a finite sum of arithmetic functions to its pointwise form. -/
private theorem arithmeticFunction_sum_apply {α : Type*} (s : Finset α)
    (f : α → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [Finset.sum_insert ha, ArithmeticFunction.add_apply, ih]

/-- The finite dyadic partition of the constant-one function. -/
noncomputable def dyadicOnePartition (X : ℝ) : ArithmeticFunction ℝ :=
  ∑ j : DyadicIndex X, dyadicOneFactor j.val.val

/-- The finite dyadic partition of the logarithm. -/
noncomputable def dyadicLogPartition (X : ℝ) : ArithmeticFunction ℝ :=
  ∑ j : DyadicIndex X, dyadicLogFactor j.val.val

/-- The finite dyadic partition of the truncated Möbius function. -/
noncomputable def dyadicMobiusPartition (X z : ℝ) : ArithmeticFunction ℝ :=
  ∑ j : DyadicIndex X, dyadicMobiusFactor z j.val.val

/-- Every positive integer in `[1,4X]` belongs to one of the retained dyadic
intervals. -/
theorem dyadic_interval_cover {X : ℝ} (hX : 3 ≤ X) {n : ℕ}
    (hn : 0 < n) (hnX : (n : ℝ) ≤ 4 * X) :
    ∃ j : DyadicIndex X, inDyadicInterval j.val.val n := by
  let j : ℕ := Nat.clog 2 n
  have hnUpper : n ≤ 2 ^ j := by
    exact Nat.le_pow_clog (by decide : 1 < 2) n
  have hnLower : dyadicLowerNat j < n := by
    by_cases hnOne : n = 1
    · subst n
      simp [dyadicLowerNat, j]
    · have hnBig : 1 < n := by omega
      have hpow : 2 ^ (Nat.clog 2 n).pred < n :=
        Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hnBig
      have hjpos : 0 < j := Nat.clog_pos (by decide : 1 < 2) hnBig
      simpa [dyadicLowerNat, j, hjpos.ne'] using hpow
  have hscale : dyadicScale j < 4 * X := by
    have hscaleN : dyadicScale j < (n : ℝ) := by
      by_cases hj : j = 0
      · rw [dyadicScale, if_pos hj]
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
        exact (by norm_num : (1 / 2 : ℝ) < 1).trans_le hn1
      · have hEq : dyadicScale j = (dyadicLowerNat j : ℝ) := by
          simp [dyadicScale, dyadicLowerNat, hj]
        rw [hEq]
        exact_mod_cast hnLower
    exact hscaleN.trans_le hnX
  let c : ℕ := Nat.ceil (Real.logb 2 (8 * X))
  have hlog : Real.logb 2 (8 * X) ≤ (c : ℝ) := by
    exact Nat.le_ceil _
  have hpowReal : 8 * X ≤ (2 : ℝ) ^ (c : ℝ) := by
    exact (Real.logb_le_iff_le_rpow (by norm_num : 1 < (2 : ℝ))
      (by positivity : 0 < 8 * X)).mp hlog
  have hceilBound : Nat.ceil (8 * X) ≤ 2 ^ c := by
    apply Nat.ceil_le.2
    exact_mod_cast hpowReal
  have hnCeil : n ≤ Nat.ceil (8 * X) := by
    have hnX' : (n : ℝ) ≤ 8 * X := by linarith
    have hceil : 8 * X ≤ (Nat.ceil (8 * X) : ℝ) := Nat.le_ceil _
    exact_mod_cast hnX'.trans hceil
  have hjBound : j ≤ c := by
    dsimp [j]
    exact (Nat.clog_mono_right 2 hnCeil).trans
      (Nat.clog_le_of_le_pow hceilBound)
  have hjFin : j < dyadicPartitionCount X := by
    dsimp [dyadicPartitionCount]
    omega
  exact ⟨⟨⟨j, hjFin⟩, hscale⟩, hnLower, hnUpper⟩

/-- The interval indicators sum to one throughout the target range. -/
theorem dyadicIntervalIndicator_sum {X : ℝ} (hX : 3 ≤ X) {n : ℕ}
    (hn : 0 < n) (hnX : (n : ℝ) ≤ 4 * X) :
    (∑ j : DyadicIndex X, dyadicIntervalIndicator j.val.val n) = 1 := by
  classical
  obtain ⟨j, hj⟩ := dyadic_interval_cover hX hn hnX
  have hsum :
      (∑ i : DyadicIndex X,
        if i = j then (1 : ℝ) else 0) = 1 := by simp
  rw [← hsum]
  apply Fintype.sum_congr
  intro i
  by_cases hij : i = j
  · simp [dyadicIntervalIndicator, hij, hj]
  · have hnot : ¬ inDyadicInterval i.val.val n := by
      intro hi
      have hclogI := (inDyadicInterval_iff_clog hn).mp hi
      have hclogJ := (inDyadicInterval_iff_clog hn).mp hj
      apply hij
      apply Subtype.ext
      apply Fin.ext
      exact hclogI.symm.trans hclogJ
    simp [dyadicIntervalIndicator, hij, hnot]

private theorem dyadic_indicator_weighted_sum {X : ℝ} (n : ℕ) (a : ℝ) :
    (∑ j : DyadicIndex X,
      if inDyadicInterval j.val.val n then a else 0) =
      (∑ j : DyadicIndex X, dyadicIntervalIndicator j.val.val n) * a := by
  classical
  rw [Finset.sum_mul]
  apply Fintype.sum_congr
  intro j
  by_cases h : inDyadicInterval j.val.val n <;>
    simp [dyadicIntervalIndicator, h]

/-- On the target range, the truncated dyadic sum of the constant-one
factor is exactly Mathlib's `zeta` arithmetic function. -/
theorem dyadicOnePartition_apply {X : ℝ} (hX : 3 ≤ X) {n : ℕ}
    (hn : 0 < n) (hnX : (n : ℝ) ≤ 4 * X) :
    dyadicOnePartition X n = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by
  classical
  rw [dyadicOnePartition, arithmeticFunction_sum_apply]
  calc
    (∑ j : DyadicIndex X, dyadicOneFactor j.val.val n) =
        ∑ j : DyadicIndex X,
          if inDyadicInterval j.val.val n then (1 : ℝ) else 0 := by
            apply Fintype.sum_congr
            intro j
            rw [dyadicOneFactor_apply]
    _ = ∑ j : DyadicIndex X, dyadicIntervalIndicator j.val.val n := by
          apply Fintype.sum_congr
          intro j
          rfl
    _ = 1 := dyadicIntervalIndicator_sum hX hn hnX
    _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by simp [hn.ne']

/-- The logarithmic dyadic partition agrees locally with the full logarithm. -/
theorem dyadicLogPartition_apply {X : ℝ} (hX : 3 ≤ X) {n : ℕ}
    (hn : 0 < n) (hnX : (n : ℝ) ≤ 4 * X) :
    dyadicLogPartition X n = (ArithmeticFunction.log : ArithmeticFunction ℝ) n := by
  classical
  rw [dyadicLogPartition, arithmeticFunction_sum_apply]
  calc
    (∑ j : DyadicIndex X, dyadicLogFactor j.val.val n) =
        ∑ j : DyadicIndex X,
          if inDyadicInterval j.val.val n then
            (ArithmeticFunction.log : ArithmeticFunction ℝ) n else 0 := by
              apply Fintype.sum_congr
              intro j
              rw [dyadicLogFactor_apply]
    _ = (∑ j : DyadicIndex X,
          dyadicIntervalIndicator j.val.val n) *
          (ArithmeticFunction.log : ArithmeticFunction ℝ) n := by
            apply dyadic_indicator_weighted_sum
    _ = (ArithmeticFunction.log : ArithmeticFunction ℝ) n := by
          rw [dyadicIntervalIndicator_sum hX hn hnX]
          ring

/-- The truncated Möbius dyadic partition agrees locally with `μ_z`. -/
theorem dyadicMobiusPartition_apply {X z : ℝ} (hX : 3 ≤ X) {n : ℕ}
    (hn : 0 < n) (hnX : (n : ℝ) ≤ 4 * X) :
    dyadicMobiusPartition X z n = truncatedMobius z n := by
  classical
  rw [dyadicMobiusPartition, arithmeticFunction_sum_apply]
  by_cases hnz : (n : ℝ) ≤ z
  · calc
      (∑ j : DyadicIndex X, dyadicMobiusFactor z j.val.val n) =
          ∑ j : DyadicIndex X,
            if inDyadicInterval j.val.val n then
              (ArithmeticFunction.moebius n : ℝ) else 0 := by
                apply Fintype.sum_congr
                intro j
                rw [dyadicMobiusFactor_apply]
                simp [hnz]
      _ = (∑ j : DyadicIndex X,
            dyadicIntervalIndicator j.val.val n) *
            (ArithmeticFunction.moebius n : ℝ) := by
              apply dyadic_indicator_weighted_sum
      _ = (ArithmeticFunction.moebius n : ℝ) := by
            rw [dyadicIntervalIndicator_sum hX hn hnX]
            ring
      _ = truncatedMobius z n := by simp [hnz]
  · calc
      (∑ j : DyadicIndex X, dyadicMobiusFactor z j.val.val n) = 0 := by
        apply Fintype.sum_eq_zero
        intro j
        simp [dyadicMobiusFactor_apply, hnz]
      _ = truncatedMobius z n := by simp [truncatedMobius, hnz]

/-- One of the three allowed dyadic factor types. The index fixes its exact
interval `(N_j,2N_j]`; the Möbius constructor also retains the cutoff `n≤z`. -/
inductive DyadicArithmeticFactor (X : ℝ) where
  | one (j : DyadicIndex X)
  | logarithm (j : DyadicIndex X)
  | mobius (j : DyadicIndex X)

/-- The arithmetic function represented by a tagged dyadic factor. -/
noncomputable def dyadicFactorFunction {X : ℝ} (z : ℝ) :
    DyadicArithmeticFactor X → ArithmeticFunction ℝ
  | .one j => dyadicOneFactor j.val.val
  | .logarithm j => dyadicLogFactor j.val.val
  | .mobius j => dyadicMobiusFactor z j.val.val

/-- The support scale attached to a dyadic factor. -/
def dyadicFactorScale {X : ℝ} : DyadicArithmeticFactor X → ℝ
  | .one j => dyadicScale j.val.val
  | .logarithm j => dyadicScale j.val.val
  | .mobius j => dyadicScale j.val.val

private theorem dyadicScale_ge_half (j : ℕ) :
    (1 / 2 : ℝ) ≤ dyadicScale j := by
  by_cases hj : j = 0
  · simp [dyadicScale, hj]
  · have hp : (1 : ℝ) ≤ (2 : ℝ) ^ j.pred :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    simpa [dyadicScale, hj] using
      (le_trans (by norm_num : (1 / 2 : ℝ) ≤ 1) hp)

theorem dyadicFactorScale_ge_half {X : ℝ} (f : DyadicArithmeticFactor X) :
    (1 / 2 : ℝ) ≤ dyadicFactorScale f := by
  cases f with
  | one j => exact dyadicScale_ge_half j.val.val
  | logarithm j => exact dyadicScale_ge_half j.val.val
  | mobius j => exact dyadicScale_ge_half j.val.val

theorem dyadicFactorScale_lt_fourX {X : ℝ} (f : DyadicArithmeticFactor X) :
    dyadicFactorScale f < 4 * X := by
  cases f with
  | one j => exact j.property
  | logarithm j => exact j.property
  | mobius j => exact j.property

/-- The ordered convolution of a finite list of dyadic factors. -/
noncomputable def dyadicConvolutionFactors {X : ℝ} (z : ℝ) :
    List (DyadicArithmeticFactor X) → ArithmeticFunction ℝ
  | fs => (fs.map (dyadicFactorFunction z)).prod

private theorem dyadicMobiusPowerExpansion {X z : ℝ} (r : ℕ) :
    dyadicMobiusPartition X z ^ r =
      ∑ φ : Fin r → DyadicIndex X,
        dyadicConvolutionFactors z
          (List.ofFn fun i : Fin r => DyadicArithmeticFactor.mobius (φ i)) := by
  rw [dyadicMobiusPartition, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro φ
  simp [dyadicConvolutionFactors, List.map_ofFn, List.prod_ofFn,
    dyadicFactorFunction]

private theorem dyadicOnePowerExpansion {X z : ℝ} (r : ℕ) :
    dyadicOnePartition X ^ r =
      ∑ φ : Fin r → DyadicIndex X,
        dyadicConvolutionFactors z
          (List.ofFn fun i : Fin r => DyadicArithmeticFactor.one (φ i)) := by
  rw [dyadicOnePartition, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro φ
  simp [dyadicConvolutionFactors, List.map_ofFn, List.prod_ofFn,
    dyadicFactorFunction]

private theorem dyadicMobiusOneProductExpansion {X z : ℝ} (r s : ℕ) :
    dyadicMobiusPartition X z ^ r * dyadicOnePartition X ^ s =
      ∑ p : (Fin r → DyadicIndex X) × (Fin s → DyadicIndex X),
        dyadicConvolutionFactors z
          (List.ofFn (fun i : Fin r => DyadicArithmeticFactor.mobius (p.1 i)) ++
            List.ofFn (fun i : Fin s => DyadicArithmeticFactor.one (p.2 i))) := by
  rw [dyadicMobiusPowerExpansion (X := X) (z := z) r,
    dyadicOnePowerExpansion (X := X) (z := z) s,
    Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_congr
  intro p
  rcases p with ⟨φ, ψ⟩
  simp [dyadicConvolutionFactors, List.map_append, List.prod_append,
    List.map_ofFn, List.prod_ofFn, dyadicFactorFunction]

private theorem dyadicMobiusOneLogProductExpansion {X z : ℝ} (r s : ℕ) :
    (dyadicMobiusPartition X z ^ r * dyadicOnePartition X ^ s) *
        dyadicLogPartition X =
      ∑ p : ((Fin r → DyadicIndex X) × (Fin s → DyadicIndex X)) ×
          DyadicIndex X,
        dyadicConvolutionFactors z
          ((List.ofFn (fun i : Fin r => DyadicArithmeticFactor.mobius (p.1.1 i)) ++
              List.ofFn (fun i : Fin s => DyadicArithmeticFactor.one (p.1.2 i))) ++
            [DyadicArithmeticFactor.logarithm p.2]) := by
  rw [dyadicMobiusOneProductExpansion, dyadicLogPartition,
    Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_congr
  intro p
  rcases p with ⟨⟨φ, ψ⟩, j⟩
  simp [dyadicConvolutionFactors, List.map_append, List.prod_append,
    List.map_ofFn, List.prod_ofFn, dyadicFactorFunction]
  exact mul_assoc _ _ _

/-- The ten indices in the Heath--Brown sum `1 ≤ r ≤ 10`. -/
abbrev HeathBrownIndex := {r : ℕ // r ∈ Finset.Icc 1 10}

/-- Labels for all dyadic expansions of the Möbius identity. Repeated choices
remain distinct indices. -/
abbrev MobiusDyadicLabel (X : ℝ) :=
  Σ r : HeathBrownIndex,
    ((Fin r.val → DyadicIndex X) × (Fin (r.val - 1) → DyadicIndex X))

/-- Labels for all dyadic expansions of the von Mangoldt identity, including
the separately indexed logarithmic factor. -/
abbrev VonMangoldtDyadicLabel (X : ℝ) :=
  Σ r : HeathBrownIndex,
    (((Fin r.val → DyadicIndex X) × (Fin (r.val - 1) → DyadicIndex X)) ×
      DyadicIndex X)

/-- The factor list associated to a Möbius label: `r` cutoff Möbius factors
followed by `r-1` constant-one factors. -/
def mobiusLabelFactors {X : ℝ} (ν : MobiusDyadicLabel X) :
    List (DyadicArithmeticFactor X) :=
  List.ofFn (fun i : Fin ν.1.val => .mobius (ν.2.1 i)) ++
    List.ofFn (fun i : Fin (ν.1.val - 1) => .one (ν.2.2 i))

/-- The factor list associated to a von Mangoldt label, with its one
logarithmic factor last. -/
def vonMangoldtLabelFactors {X : ℝ} (ν : VonMangoldtDyadicLabel X) :
    List (DyadicArithmeticFactor X) :=
  List.ofFn (fun i : Fin ν.1.val => .mobius (ν.2.1.1 i)) ++
    List.ofFn (fun i : Fin (ν.1.val - 1) => .one (ν.2.1.2 i)) ++
      [.logarithm ν.2.2]

/-- The coefficient `(-1)^(r-1) * choose(10,r)` attached to either identity. -/
def dyadicBinomialCoefficient (r : HeathBrownIndex) : ℝ :=
  (-1 : ℝ) ^ (r.val - 1) * (Nat.choose 10 r.val : ℝ)

theorem dyadicBinomialCoefficient_abs_le (r : HeathBrownIndex) :
    |dyadicBinomialCoefficient r| ≤ 2 ^ 10 := by
  have hchoose : (Nat.choose 10 r.val : ℝ) ≤ (2 : ℝ) ^ 10 := by
    exact_mod_cast Nat.choose_le_two_pow 10 r.val
  have hchoose_nonneg : 0 ≤ (Nat.choose 10 r.val : ℝ) := Nat.cast_nonneg _
  calc
    |dyadicBinomialCoefficient r| =
        |(-1 : ℝ) ^ (r.val - 1)| * |(Nat.choose 10 r.val : ℝ)| := by
          simp [dyadicBinomialCoefficient, abs_mul]
    _ = (Nat.choose 10 r.val : ℝ) := by
          rw [abs_of_nonneg hchoose_nonneg]
          simp
    _ ≤ 2 ^ 10 := hchoose

/-- The arithmetic component assigned to a Möbius label. -/
noncomputable def mobiusDyadicComponent {X : ℝ} (z : ℝ)
    (ν : MobiusDyadicLabel X) : ArithmeticFunction ℝ :=
  algebraMap ℝ (ArithmeticFunction ℝ) (dyadicBinomialCoefficient ν.1) *
    dyadicConvolutionFactors z (mobiusLabelFactors ν)

/-- The arithmetic component assigned to a von Mangoldt label. -/
noncomputable def vonMangoldtDyadicComponent {X : ℝ} (z : ℝ)
    (ν : VonMangoldtDyadicLabel X) : ArithmeticFunction ℝ :=
  algebraMap ℝ (ArithmeticFunction ℝ) (dyadicBinomialCoefficient ν.1) *
    dyadicConvolutionFactors z (vonMangoldtLabelFactors ν)

@[simp]
theorem mobiusDyadicComponent_apply {X : ℝ} (z : ℝ)
    (ν : MobiusDyadicLabel X) (n : ℕ) :
    mobiusDyadicComponent z ν n =
      dyadicBinomialCoefficient ν.1 *
        dyadicConvolutionFactors z (mobiusLabelFactors ν) n := by
  rw [mobiusDyadicComponent, ← Algebra.smul_def]
  simp [ArithmeticFunction.smul_map]

@[simp]
theorem vonMangoldtDyadicComponent_apply {X : ℝ} (z : ℝ)
    (ν : VonMangoldtDyadicLabel X) (n : ℕ) :
    vonMangoldtDyadicComponent z ν n =
      dyadicBinomialCoefficient ν.1 *
        dyadicConvolutionFactors z (vonMangoldtLabelFactors ν) n := by
  rw [vonMangoldtDyadicComponent, ← Algebra.smul_def]
  simp [ArithmeticFunction.smul_map]

/-- The product of the dyadic lower scales for an ordered list of factors. -/
def dyadicFactorScaleProduct {X : ℝ} (fs : List (DyadicArithmeticFactor X)) : ℝ :=
  (fs.map dyadicFactorScale).prod

/-- A component is retained when its factors are nonzero and its possible
product interval `(P,2^k P]` intersects `[X/2,4X]`. -/
def dyadicFactorsRetained {X z : ℝ} (fs : List (DyadicArithmeticFactor X)) : Prop :=
  (∀ f ∈ fs, dyadicFactorFunction z f ≠ 0) ∧
    dyadicFactorScaleProduct fs < 4 * X ∧
    X / 2 ≤ (2 : ℝ) ^ fs.length * dyadicFactorScaleProduct fs

/-- The retained dyadic components for the Möbius identity. -/
noncomputable def mobiusDyadicLabels (X z : ℝ) : Finset (MobiusDyadicLabel X) := by
  classical
  exact Finset.univ.filter
    (fun ν => dyadicFactorsRetained (X := X) (z := z) (mobiusLabelFactors ν))

/-- The retained dyadic components for the von Mangoldt identity. -/
noncomputable def vonMangoldtDyadicLabels (X z : ℝ) :
    Finset (VonMangoldtDyadicLabel X) := by
  classical
  exact Finset.univ.filter
    (fun ν => dyadicFactorsRetained (X := X) (z := z) (vonMangoldtLabelFactors ν))

@[simp]
theorem mobiusLabelFactors_length {X : ℝ} (ν : MobiusDyadicLabel X) :
    (mobiusLabelFactors ν).length = 2 * ν.1.val - 1 := by
  have hr : 1 ≤ ν.1.val := (Finset.mem_Icc.mp ν.1.property).1
  simp [mobiusLabelFactors]
  omega

@[simp]
theorem vonMangoldtLabelFactors_length {X : ℝ} (ν : VonMangoldtDyadicLabel X) :
    (vonMangoldtLabelFactors ν).length = 2 * ν.1.val := by
  have hr : 1 ≤ ν.1.val := (Finset.mem_Icc.mp ν.1.property).1
  simp [vonMangoldtLabelFactors]
  omega

theorem mobiusDyadicLabels_mem {X z : ℝ} {ν : MobiusDyadicLabel X}
    (hν : ν ∈ mobiusDyadicLabels X z) :
    dyadicFactorsRetained (X := X) (z := z) (mobiusLabelFactors ν) :=
  by
    classical
    unfold mobiusDyadicLabels at hν
    exact (Finset.mem_filter.mp hν).2

theorem vonMangoldtDyadicLabels_mem {X z : ℝ} {ν : VonMangoldtDyadicLabel X}
    (hν : ν ∈ vonMangoldtDyadicLabels X z) :
    dyadicFactorsRetained (X := X) (z := z) (vonMangoldtLabelFactors ν) :=
  by
    classical
    unfold vonMangoldtDyadicLabels at hν
    exact (Finset.mem_filter.mp hν).2

theorem mobiusLabelFactorCount {X : ℝ} (ν : MobiusDyadicLabel X) :
    1 ≤ (mobiusLabelFactors ν).length ∧ (mobiusLabelFactors ν).length ≤ 20 := by
  rcases Finset.mem_Icc.mp ν.1.property with ⟨hrlo, hrhi⟩
  rw [mobiusLabelFactors_length]
  constructor <;> omega

theorem vonMangoldtLabelFactorCount {X : ℝ} (ν : VonMangoldtDyadicLabel X) :
    1 ≤ (vonMangoldtLabelFactors ν).length ∧
      (vonMangoldtLabelFactors ν).length ≤ 20 := by
  rcases Finset.mem_Icc.mp ν.1.property with ⟨hrlo, hrhi⟩
  rw [vonMangoldtLabelFactors_length]
  constructor <;> omega

private def heathBrownIndexEquiv : HeathBrownIndex ≃ Fin 10 where
  toFun r := ⟨r.val - 1, by
    rcases Finset.mem_Icc.mp r.property with ⟨hrlo, hrhi⟩
    omega⟩
  invFun r := ⟨r.val + 1, by
    have hrlt := r.isLt
    simp only [Finset.mem_Icc]
    constructor <;> omega⟩
  left_inv r := by
    apply Subtype.ext
    exact Nat.sub_add_cancel (Finset.mem_Icc.mp r.property).1
  right_inv r := by
    apply Fin.ext
    change (r.val + 1) - 1 = r.val
    exact Nat.add_sub_cancel_right _ _

private theorem heathBrownIndex_card : Fintype.card HeathBrownIndex = 10 := by
  calc
    Fintype.card HeathBrownIndex = Fintype.card (Fin 10) :=
      Fintype.card_congr heathBrownIndexEquiv
    _ = 10 := Fintype.card_fin 10

private theorem dyadicIndex_card_le (X : ℝ) :
    Fintype.card (DyadicIndex X) ≤ dyadicPartitionCount X := by
  classical
  let f : DyadicIndex X → Fin (dyadicPartitionCount X) := fun j => j.val
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext hab
  simpa using Fintype.card_le_of_injective f hf

private theorem mobiusDyadicLabel_card_le (X : ℝ) :
    Fintype.card (MobiusDyadicLabel X) ≤
      10 * dyadicPartitionCount X ^ 20 := by
  classical
  let d := Fintype.card (DyadicIndex X)
  let D := dyadicPartitionCount X
  have hd : d ≤ D := dyadicIndex_card_le X
  have hD : 1 ≤ D := by dsimp [D, dyadicPartitionCount]; omega
  have hcard : Fintype.card (MobiusDyadicLabel X) =
      ∑ r : HeathBrownIndex, d ^ r.val * d ^ (r.val - 1) := by
    simp [MobiusDyadicLabel, d, Fintype.card_sigma, Fintype.card_prod,
      Fintype.card_fun, Fintype.card_pi_const]
  rw [hcard]
  calc
    (∑ r : HeathBrownIndex, d ^ r.val * d ^ (r.val - 1)) ≤
        ∑ _r : HeathBrownIndex, D ^ 20 := by
          change (∑ r ∈ (Finset.univ : Finset HeathBrownIndex),
            d ^ r.val * d ^ (r.val - 1)) ≤
              ∑ r ∈ (Finset.univ : Finset HeathBrownIndex), D ^ 20
          apply Finset.sum_le_sum
          intro r hrmem
          rcases Finset.mem_Icc.mp r.property with ⟨hrlo, hrhi⟩
          have hexp : r.val + (r.val - 1) ≤ 20 := by omega
          calc
            d ^ r.val * d ^ (r.val - 1) = d ^ (r.val + (r.val - 1)) := by
              rw [← pow_add]
            _ ≤ D ^ (r.val + (r.val - 1)) :=
              pow_le_pow_left' hd _
            _ ≤ D ^ 20 := pow_le_pow_right' hD hexp
    _ = 10 * D ^ 20 := by
      rw [Finset.sum_const, Finset.card_univ, heathBrownIndex_card]
      simp

private theorem vonMangoldtDyadicLabel_card_le (X : ℝ) :
    Fintype.card (VonMangoldtDyadicLabel X) ≤
      10 * dyadicPartitionCount X ^ 20 := by
  classical
  let d := Fintype.card (DyadicIndex X)
  let D := dyadicPartitionCount X
  have hd : d ≤ D := dyadicIndex_card_le X
  have hD : 1 ≤ D := by dsimp [D, dyadicPartitionCount]; omega
  have hcard : Fintype.card (VonMangoldtDyadicLabel X) =
      ∑ r : HeathBrownIndex, d ^ r.val * d ^ (r.val - 1) * d := by
    simp [VonMangoldtDyadicLabel, d, Fintype.card_sigma, Fintype.card_prod,
      Fintype.card_fun]
  rw [hcard]
  calc
    (∑ r : HeathBrownIndex, d ^ r.val * d ^ (r.val - 1) * d) ≤
        ∑ _r : HeathBrownIndex, D ^ 20 := by
          change (∑ r ∈ (Finset.univ : Finset HeathBrownIndex),
            d ^ r.val * d ^ (r.val - 1) * d) ≤
              ∑ r ∈ (Finset.univ : Finset HeathBrownIndex), D ^ 20
          apply Finset.sum_le_sum
          intro r hrmem
          rcases Finset.mem_Icc.mp r.property with ⟨hrlo, hrhi⟩
          have hexp : r.val + (r.val - 1) + 1 ≤ 20 := by omega
          have hfactor : d ^ r.val * d ^ (r.val - 1) * d =
              d ^ (r.val + (r.val - 1) + 1) := by
            calc
              d ^ r.val * d ^ (r.val - 1) * d =
                  d ^ (r.val + (r.val - 1)) * d := by rw [← pow_add]
              _ = d ^ (r.val + (r.val - 1)) * d ^ 1 := by simp
              _ = d ^ (r.val + (r.val - 1) + 1) := by rw [← pow_add]
          calc
            d ^ r.val * d ^ (r.val - 1) * d =
                d ^ (r.val + (r.val - 1) + 1) := hfactor
            _ ≤ D ^ (r.val + (r.val - 1) + 1) :=
              pow_le_pow_left' hd _
            _ ≤ D ^ 20 := pow_le_pow_right' hD hexp
    _ = 10 * D ^ 20 := by
      rw [Finset.sum_const, Finset.card_univ, heathBrownIndex_card]
      simp

theorem mobiusDyadicLabels_card_le (X z : ℝ) :
    (mobiusDyadicLabels X z).card ≤ 10 * dyadicPartitionCount X ^ 20 := by
  classical
  calc
    (mobiusDyadicLabels X z).card ≤ Fintype.card (MobiusDyadicLabel X) := by
      rw [← Finset.card_univ (α := MobiusDyadicLabel X)]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ 10 * dyadicPartitionCount X ^ 20 := mobiusDyadicLabel_card_le X

theorem vonMangoldtDyadicLabels_card_le (X z : ℝ) :
    (vonMangoldtDyadicLabels X z).card ≤ 10 * dyadicPartitionCount X ^ 20 := by
  classical
  calc
    (vonMangoldtDyadicLabels X z).card ≤ Fintype.card (VonMangoldtDyadicLabel X) := by
      rw [← Finset.card_univ (α := VonMangoldtDyadicLabel X)]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ 10 * dyadicPartitionCount X ^ 20 := vonMangoldtDyadicLabel_card_le X

private theorem dyadicInterval_real_bounds {j n : ℕ}
    (h : inDyadicInterval j n) :
    dyadicScale j < (n : ℝ) ∧ (n : ℝ) ≤ 2 * dyadicScale j := by
  by_cases hj : j = 0
  · have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h.1
    have hnle : n ≤ 1 := by simpa [inDyadicInterval, dyadicUpperNat, hj] using h.2
    have hn : n = 1 := by omega
    simp [dyadicScale, hj, hn]
    norm_num
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hscale : dyadicScale j = (dyadicLowerNat j : ℝ) := by
      simp [dyadicScale, dyadicLowerNat, hj]
    have hjEq : j.pred + 1 = j := by
      simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hjpos
    have hpow : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ j.pred := by
      calc
        (2 : ℝ) ^ j = (2 : ℝ) ^ (j.pred + 1) :=
          congrArg (fun k : ℕ => (2 : ℝ) ^ k) hjEq.symm
        _ = (2 : ℝ) ^ j.pred * 2 := by rw [pow_succ]
        _ = 2 * (2 : ℝ) ^ j.pred := by ring
    have hupper : (dyadicUpperNat j : ℝ) = 2 * dyadicScale j := by
      simp only [dyadicUpperNat, Nat.cast_pow, Nat.cast_ofNat]
      rw [hpow, dyadicScale, if_neg hj]
    constructor
    · rw [hscale]
      exact_mod_cast h.1
    · rw [← hupper]
      exact_mod_cast h.2

private theorem dyadicFactorFunction_support_bounds {X z : ℝ}
    (f : DyadicArithmeticFactor X) {n : ℕ}
    (hne : dyadicFactorFunction z f n ≠ 0) :
    dyadicFactorScale f < (n : ℝ) ∧ (n : ℝ) ≤ 2 * dyadicFactorScale f := by
  cases f with
  | one j =>
      have hInt : inDyadicInterval j.val.val n := by
        by_contra hInt
        apply hne
        simp [dyadicFactorFunction, dyadicOneFactor_apply, hInt]
      exact dyadicInterval_real_bounds hInt
  | logarithm j =>
      have hInt : inDyadicInterval j.val.val n := by
        by_contra hInt
        apply hne
        simp [dyadicFactorFunction, dyadicLogFactor_apply, hInt]
      exact dyadicInterval_real_bounds hInt
  | mobius j =>
      have hInt : inDyadicInterval j.val.val n := by
        by_contra hInt
        apply hne
        simp [dyadicFactorFunction, dyadicMobiusFactor_apply, hInt]
      exact dyadicInterval_real_bounds hInt

private theorem dyadicFactorScale_pos {X : ℝ} (f : DyadicArithmeticFactor X) :
    0 < dyadicFactorScale f := by
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

theorem dyadicFactorScaleProduct_pos {X : ℝ}
    (fs : List (DyadicArithmeticFactor X)) :
    0 < dyadicFactorScaleProduct fs := by
  induction fs with
  | nil => simp [dyadicFactorScaleProduct]
  | cons f fs ih =>
      simp only [dyadicFactorScaleProduct, List.map_cons, List.prod_cons]
      exact mul_pos (dyadicFactorScale_pos f) ih

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
  have hsum :
      (∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rcases hterms x hx with hf | hg
    · simp [hf]
    · simp [hg]
  exact hne hsum

theorem dyadicConvolutionFactors_support_bounds {X z : ℝ}
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
          have hb := dyadicFactorFunction_support_bounds f hfactor
          simpa [dyadicFactorScaleProduct, dyadicConvolutionFactors] using hb
      | cons g gs =>
          have hmul :
              (dyadicFactorFunction z f * dyadicConvolutionFactors z (g :: gs)) n ≠ 0 := by
            simpa [dyadicConvolutionFactors] using hne
          obtain ⟨x, hx, hfirst, htail⟩ :=
            arithmeticFunction_mul_apply_ne_zero hmul
          have hfirstBounds := dyadicFactorFunction_support_bounds f hfirst
          have htailBounds := ih (by simp) htail
          have hpair := (Nat.mem_divisorsAntidiagonal.mp hx).1
          have hpairReal : (n : ℝ) = (x.1 : ℝ) * (x.2 : ℝ) := by
            exact_mod_cast hpair.symm
          have hx1pos : 0 < (x.1 : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero
              (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx)
          have hscalePos : 0 < dyadicFactorScaleProduct (g :: gs) :=
            dyadicFactorScaleProduct_pos (g :: gs)
          have hlow :
              dyadicFactorScale f * dyadicFactorScaleProduct (g :: gs) <
                (x.1 : ℝ) * (x.2 : ℝ) := by
            calc
              dyadicFactorScale f * dyadicFactorScaleProduct (g :: gs) <
                  (x.1 : ℝ) * dyadicFactorScaleProduct (g :: gs) :=
                mul_lt_mul_of_pos_right hfirstBounds.1 hscalePos
              _ < (x.1 : ℝ) * (x.2 : ℝ) :=
                mul_lt_mul_of_pos_left htailBounds.1 hx1pos
          have hupp :
              (x.1 : ℝ) * (x.2 : ℝ) ≤
                (2 : ℝ) ^ ((g :: gs).length + 1) *
                  (dyadicFactorScale f * dyadicFactorScaleProduct (g :: gs)) := by
            calc
              (x.1 : ℝ) * (x.2 : ℝ) ≤
                  (2 * dyadicFactorScale f) * (x.2 : ℝ) :=
                mul_le_mul_of_nonneg_right hfirstBounds.2 (by positivity)
              _ ≤ (2 * dyadicFactorScale f) *
                    ((2 : ℝ) ^ (g :: gs).length *
                      dyadicFactorScaleProduct (g :: gs)) :=
                mul_le_mul_of_nonneg_left htailBounds.2
                  (mul_nonneg (by norm_num) (dyadicFactorScale_pos f).le)
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

private theorem dyadicConvolutionFactors_eq_zero_of_zero_factor {X z : ℝ}
    (fs : List (DyadicArithmeticFactor X))
    (hzero : ∃ f ∈ fs, dyadicFactorFunction z f = 0) :
    dyadicConvolutionFactors z fs = 0 := by
  induction fs with
  | nil => rcases hzero with ⟨f, hf, _⟩; simp at hf
  | cons f fs ih =>
      rcases hzero with ⟨g, hg, hgz⟩
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · simp [dyadicConvolutionFactors, hgz]
      · have htail := ih ⟨g, hg, hgz⟩
        have htail' : (List.map (dyadicFactorFunction z) fs).prod = 0 := by
          simpa [dyadicConvolutionFactors] using htail
        simp [dyadicConvolutionFactors, htail']

private theorem dyadicConvolutionFactors_eq_zero_of_not_retained
    {X z : ℝ} (fs : List (DyadicArithmeticFactor X))
    (hfs : fs ≠ [])
    (hnot : ¬ dyadicFactorsRetained (X := X) (z := z) fs)
    {n : ℕ} (hn : 0 < n) (hnlo : X / 2 ≤ (n : ℝ))
    (hnhi : (n : ℝ) ≤ 4 * X) : dyadicConvolutionFactors z fs n = 0 := by
  classical
  by_cases hfac : ∀ f ∈ fs, dyadicFactorFunction z f ≠ 0
  · by_contra hne
    have hb := dyadicConvolutionFactors_support_bounds fs hfs hne
    have hrange :
        dyadicFactorScaleProduct fs < 4 * X ∧
          X / 2 ≤ (2 : ℝ) ^ fs.length * dyadicFactorScaleProduct fs := by
      constructor
      · exact lt_of_lt_of_le hb.1 hnhi
      · exact le_trans hnlo hb.2
    exact hnot ⟨hfac, hrange.1, hrange.2⟩
  · push_neg at hfac
    obtain ⟨f, hf, hzero⟩ := hfac
    exact congrArg (fun F : ArithmeticFunction ℝ => F n)
      (dyadicConvolutionFactors_eq_zero_of_zero_factor fs ⟨f, hf, hzero⟩)

private theorem arithmeticFunction_pow_apply_eq_of_divisors
    {f g : ArithmeticFunction ℝ} (k n : ℕ)
    (hfg : ∀ d, d ∣ n → f d = g d) :
    (f ^ k) n = (g ^ k) n := by
  induction k generalizing n hfg with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ArithmeticFunction.mul_apply,
        pow_succ, ArithmeticFunction.mul_apply]
      apply Finset.sum_congr rfl
      intro x hx
      have hpair := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have hdvd1 : x.1 ∣ n := ⟨x.2, hpair.symm⟩
      have hdvd2 : x.2 ∣ n := ⟨x.1, by simpa [Nat.mul_comm] using hpair.symm⟩
      have hleft : (f ^ k) x.1 = (g ^ k) x.1 :=
        ih x.1 (fun d hd => hfg d (dvd_trans hd hdvd1))
      rw [hleft, hfg x.2 hdvd2]

private theorem arithmeticFunction_mul_apply_eq_of_divisors
    {f f' g g' : ArithmeticFunction ℝ} {n : ℕ}
    (hff : ∀ d, d ∣ n → f d = f' d)
    (hgg : ∀ d, d ∣ n → g d = g' d) :
    (f * g) n = (f' * g') n := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  have hpair := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hdvd1 : x.1 ∣ n := ⟨x.2, hpair.symm⟩
  have hdvd2 : x.2 ∣ n := ⟨x.1, by simpa [Nat.mul_comm] using hpair.symm⟩
  rw [hff x.1 hdvd1, hgg x.2 hdvd2]

private theorem mobiusDyadicUnfilteredExpansion {X : ℝ} (hX : 3 ≤ X)
    {n : ℕ} (hn : 0 < n) (hnlo : X / 2 ≤ (n : ℝ))
    (hnhi : (n : ℝ) ≤ 4 * X) :
    (ArithmeticFunction.moebius n : ℝ) =
      ∑ ν : MobiusDyadicLabel X,
        mobiusDyadicComponent (dyadicMobiusCutoff X) ν n := by
  classical
  let z : ℝ := dyadicMobiusCutoff X
  have hX0 : 0 ≤ X := by linarith
  have hz1 : 1 ≤ z := by
    dsimp [z]
    exact dyadicMobiusCutoff_ge_one hX
  have hnz : (n : ℝ) ≤ z ^ 10 := by
    dsimp [z]
    rw [dyadicMobiusCutoff_pow hX0]
    exact hnhi
  have hHB := heathBrownMobiusIdentity (L := 10) (by norm_num) (z := z)
    hz1 hn hnz
  have hHBattach : (ArithmeticFunction.moebius n : ℝ) =
      ∑ r ∈ (Finset.Icc 1 10).attach,
        ((-1 : ℝ) ^ (r.val - 1) * (Nat.choose 10 r.val : ℝ)) *
          ((truncatedMobius z ^ r.val *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) n) := by
    rw [← Finset.sum_attach]
    exact hHB
  have hHB' : (ArithmeticFunction.moebius n : ℝ) =
      ∑ r : HeathBrownIndex,
        dyadicBinomialCoefficient r *
          ((truncatedMobius z ^ r.val *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) n) := by
    simpa [HeathBrownIndex, dyadicBinomialCoefficient,
      Finset.sum_coe_sort_eq_attach] using hHBattach
  have hlocalMu (d : ℕ) (hdn : d ∣ n) :
      truncatedMobius z d = dyadicMobiusPartition X z d := by
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hdle : d ≤ n := Nat.le_of_dvd hn hdn
    have hdreal : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdle
    exact (dyadicMobiusPartition_apply hX hdpos (hdreal.trans hnhi)).symm
  have hlocalOne (d : ℕ) (hdn : d ∣ n) :
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) d = dyadicOnePartition X d := by
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hdle : d ≤ n := Nat.le_of_dvd hn hdn
    have hdreal : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdle
    exact (dyadicOnePartition_apply hX hdpos (hdreal.trans hnhi)).symm
  have hterm (r : HeathBrownIndex) :
      dyadicBinomialCoefficient r *
          ((truncatedMobius z ^ r.val *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) n) =
        ∑ p : (Fin r.val → DyadicIndex X) × (Fin (r.val - 1) → DyadicIndex X),
          mobiusDyadicComponent z ⟨r, p⟩ n := by
    have hpowMu (m : ℕ) (hmn : m ∣ n) :
        (truncatedMobius z ^ r.val) m =
          (dyadicMobiusPartition X z ^ r.val) m := by
      apply arithmeticFunction_pow_apply_eq_of_divisors
      intro d hdm
      exact hlocalMu d (dvd_trans hdm hmn)
    have hpowOne (m : ℕ) (hmn : m ∣ n) :
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) m =
          (dyadicOnePartition X ^ (r.val - 1)) m := by
      apply arithmeticFunction_pow_apply_eq_of_divisors
      intro d hdm
      exact hlocalOne d (dvd_trans hdm hmn)
    have hprod := arithmeticFunction_mul_apply_eq_of_divisors hpowMu hpowOne
    have hexp := dyadicMobiusOneProductExpansion (X := X) (z := z)
      r.val (r.val - 1)
    have hexpN :
        (dyadicMobiusPartition X z ^ r.val *
          dyadicOnePartition X ^ (r.val - 1)) n =
        ∑ p : (Fin r.val → DyadicIndex X) × (Fin (r.val - 1) → DyadicIndex X),
          dyadicConvolutionFactors z
            (List.ofFn (fun i : Fin r.val => DyadicArithmeticFactor.mobius (p.1 i)) ++
              List.ofFn (fun i : Fin (r.val - 1) => DyadicArithmeticFactor.one (p.2 i))) n := by
      calc
        _ = (∑ p : (Fin r.val → DyadicIndex X) ×
              (Fin (r.val - 1) → DyadicIndex X),
              dyadicConvolutionFactors z
                (List.ofFn (fun i : Fin r.val => DyadicArithmeticFactor.mobius (p.1 i)) ++
                  List.ofFn (fun i : Fin (r.val - 1) =>
                    DyadicArithmeticFactor.one (p.2 i)))) n :=
              congrArg (fun F : ArithmeticFunction ℝ => F n) hexp
        _ = _ := arithmeticFunction_sum_apply _ _ _
    calc
      _ = dyadicBinomialCoefficient r *
            ((dyadicMobiusPartition X z ^ r.val *
              dyadicOnePartition X ^ (r.val - 1)) n) := by rw [hprod]
      _ = ∑ p : (Fin r.val → DyadicIndex X) ×
            (Fin (r.val - 1) → DyadicIndex X),
            dyadicBinomialCoefficient r *
              dyadicConvolutionFactors z
                (List.ofFn (fun i : Fin r.val => DyadicArithmeticFactor.mobius (p.1 i)) ++
                  List.ofFn (fun i : Fin (r.val - 1) =>
                    DyadicArithmeticFactor.one (p.2 i))) n := by
              rw [hexpN, Finset.mul_sum]
      _ = _ := by
            apply Fintype.sum_congr
            intro p
            simp [mobiusDyadicComponent_apply, mobiusLabelFactors,
              dyadicBinomialCoefficient]
  calc
    (ArithmeticFunction.moebius n : ℝ) =
        ∑ r : HeathBrownIndex,
          dyadicBinomialCoefficient r *
            ((truncatedMobius z ^ r.val *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) n) := hHB'
    _ = ∑ r : HeathBrownIndex,
          ∑ p : (Fin r.val → DyadicIndex X) ×
            (Fin (r.val - 1) → DyadicIndex X),
            mobiusDyadicComponent z ⟨r, p⟩ n := by
          apply Fintype.sum_congr
          intro r
          exact hterm r
    _ = ∑ ν : MobiusDyadicLabel X, mobiusDyadicComponent z ν n := by
          simpa only [MobiusDyadicLabel, Fintype.sum_sigma]

private theorem vonMangoldtDyadicUnfilteredExpansion {X : ℝ} (hX : 3 ≤ X)
    {n : ℕ} (hn : 0 < n) (hnlo : X / 2 ≤ (n : ℝ))
    (hnhi : (n : ℝ) ≤ 4 * X) :
    ArithmeticFunction.vonMangoldt n =
      ∑ ν : VonMangoldtDyadicLabel X,
        vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n := by
  classical
  let z : ℝ := dyadicMobiusCutoff X
  have hX0 : 0 ≤ X := by linarith
  have hz1 : 1 ≤ z := by
    dsimp [z]
    exact dyadicMobiusCutoff_ge_one hX
  have hnz : (n : ℝ) ≤ z ^ 10 := by
    dsimp [z]
    rw [dyadicMobiusCutoff_pow hX0]
    exact hnhi
  have hHB := heathBrownVonMangoldtIdentity (L := 10) (by norm_num) (z := z)
    hz1 hn hnz
  have hHBattach : ArithmeticFunction.vonMangoldt n =
      ∑ r ∈ (Finset.Icc 1 10).attach,
        ((-1 : ℝ) ^ (r.val - 1) * (Nat.choose 10 r.val : ℝ)) *
          (((truncatedMobius z ^ r.val *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) *
              (ArithmeticFunction.log : ArithmeticFunction ℝ)) n) := by
    rw [← Finset.sum_attach]
    exact hHB
  have hHB' : ArithmeticFunction.vonMangoldt n =
      ∑ r : HeathBrownIndex,
        dyadicBinomialCoefficient r *
          (((truncatedMobius z ^ r.val *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) *
              (ArithmeticFunction.log : ArithmeticFunction ℝ)) n) := by
    simpa [HeathBrownIndex, dyadicBinomialCoefficient,
      Finset.sum_coe_sort_eq_attach] using hHBattach
  have hlocalMu (d : ℕ) (hdn : d ∣ n) :
      truncatedMobius z d = dyadicMobiusPartition X z d := by
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hdle : d ≤ n := Nat.le_of_dvd hn hdn
    have hdreal : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdle
    exact (dyadicMobiusPartition_apply hX hdpos (hdreal.trans hnhi)).symm
  have hlocalOne (d : ℕ) (hdn : d ∣ n) :
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) d = dyadicOnePartition X d := by
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hdle : d ≤ n := Nat.le_of_dvd hn hdn
    have hdreal : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdle
    exact (dyadicOnePartition_apply hX hdpos (hdreal.trans hnhi)).symm
  have hlocalLog (d : ℕ) (hdn : d ∣ n) :
      (ArithmeticFunction.log : ArithmeticFunction ℝ) d = dyadicLogPartition X d := by
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hdle : d ≤ n := Nat.le_of_dvd hn hdn
    have hdreal : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdle
    exact (dyadicLogPartition_apply hX hdpos (hdreal.trans hnhi)).symm
  have hterm (r : HeathBrownIndex) :
      dyadicBinomialCoefficient r *
          (((truncatedMobius z ^ r.val *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) *
              (ArithmeticFunction.log : ArithmeticFunction ℝ)) n) =
        ∑ p : ((Fin r.val → DyadicIndex X) ×
            (Fin (r.val - 1) → DyadicIndex X)) × DyadicIndex X,
          vonMangoldtDyadicComponent z ⟨r, p⟩ n := by
    have hpowMu (m : ℕ) (hmn : m ∣ n) :
        (truncatedMobius z ^ r.val) m =
          (dyadicMobiusPartition X z ^ r.val) m := by
      apply arithmeticFunction_pow_apply_eq_of_divisors
      intro d hdm
      exact hlocalMu d (dvd_trans hdm hmn)
    have hpowOne (m : ℕ) (hmn : m ∣ n) :
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) m =
          (dyadicOnePartition X ^ (r.val - 1)) m := by
      apply arithmeticFunction_pow_apply_eq_of_divisors
      intro d hdm
      exact hlocalOne d (dvd_trans hdm hmn)
    have hpowProduct (m : ℕ) (hmn : m ∣ n) :
        (truncatedMobius z ^ r.val *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) m =
        (dyadicMobiusPartition X z ^ r.val *
          dyadicOnePartition X ^ (r.val - 1)) m := by
      exact arithmeticFunction_mul_apply_eq_of_divisors
        (fun d hdm => hpowMu d (dvd_trans hdm hmn))
        (fun d hdm => hpowOne d (dvd_trans hdm hmn))
    have hprod := arithmeticFunction_mul_apply_eq_of_divisors
      hpowProduct hlocalLog
    have hexp := dyadicMobiusOneLogProductExpansion (X := X) (z := z)
      r.val (r.val - 1)
    have hexpN :
        ((dyadicMobiusPartition X z ^ r.val *
            dyadicOnePartition X ^ (r.val - 1)) *
              dyadicLogPartition X) n =
        ∑ p : ((Fin r.val → DyadicIndex X) ×
            (Fin (r.val - 1) → DyadicIndex X)) × DyadicIndex X,
          dyadicConvolutionFactors z
            ((List.ofFn (fun i : Fin r.val =>
                DyadicArithmeticFactor.mobius (p.1.1 i)) ++
              List.ofFn (fun i : Fin (r.val - 1) =>
                DyadicArithmeticFactor.one (p.1.2 i))) ++
            [DyadicArithmeticFactor.logarithm p.2]) n := by
      calc
        _ = (∑ p : ((Fin r.val → DyadicIndex X) ×
              (Fin (r.val - 1) → DyadicIndex X)) × DyadicIndex X,
              dyadicConvolutionFactors z
                ((List.ofFn (fun i : Fin r.val =>
                    DyadicArithmeticFactor.mobius (p.1.1 i)) ++
                  List.ofFn (fun i : Fin (r.val - 1) =>
                    DyadicArithmeticFactor.one (p.1.2 i))) ++
                  [DyadicArithmeticFactor.logarithm p.2])) n :=
              congrArg (fun F : ArithmeticFunction ℝ => F n) hexp
        _ = _ := arithmeticFunction_sum_apply _ _ _
    calc
      _ = dyadicBinomialCoefficient r *
            (((dyadicMobiusPartition X z ^ r.val *
              dyadicOnePartition X ^ (r.val - 1)) *
                dyadicLogPartition X) n) := by rw [hprod]
      _ = ∑ p : ((Fin r.val → DyadicIndex X) ×
              (Fin (r.val - 1) → DyadicIndex X)) × DyadicIndex X,
            dyadicBinomialCoefficient r *
              dyadicConvolutionFactors z
                ((List.ofFn (fun i : Fin r.val =>
                    DyadicArithmeticFactor.mobius (p.1.1 i)) ++
                  List.ofFn (fun i : Fin (r.val - 1) =>
                    DyadicArithmeticFactor.one (p.1.2 i))) ++
                  [DyadicArithmeticFactor.logarithm p.2]) n := by
              rw [hexpN, Finset.mul_sum]
      _ = _ := by
            apply Fintype.sum_congr
            intro p
            simp [vonMangoldtDyadicComponent_apply,
              vonMangoldtLabelFactors, dyadicBinomialCoefficient]
  calc
    ArithmeticFunction.vonMangoldt n =
        ∑ r : HeathBrownIndex,
          dyadicBinomialCoefficient r *
            (((truncatedMobius z ^ r.val *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (r.val - 1)) *
                (ArithmeticFunction.log : ArithmeticFunction ℝ)) n) := hHB'
    _ = ∑ r : HeathBrownIndex,
          ∑ p : ((Fin r.val → DyadicIndex X) ×
            (Fin (r.val - 1) → DyadicIndex X)) × DyadicIndex X,
            vonMangoldtDyadicComponent z ⟨r, p⟩ n := by
          apply Fintype.sum_congr
          intro r
          exact hterm r
    _ = ∑ ν : VonMangoldtDyadicLabel X,
          vonMangoldtDyadicComponent z ν n := by
          simpa only [VonMangoldtDyadicLabel, Fintype.sum_sigma]

private theorem mobiusDyadicFilteredSum_eq_univ {X z : ℝ} {n : ℕ}
    (hn : 0 < n) (hnlo : X / 2 ≤ (n : ℝ)) (hnhi : (n : ℝ) ≤ 4 * X) :
    (∑ ν ∈ mobiusDyadicLabels X z, mobiusDyadicComponent z ν n) =
      ∑ ν : MobiusDyadicLabel X, mobiusDyadicComponent z ν n := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro ν hνall hνnot
  have hnot :
      ¬ dyadicFactorsRetained (X := X) (z := z) (mobiusLabelFactors ν) := by
    intro hret
    apply hνnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hret⟩
  have hlen := mobiusLabelFactorCount ν
  have hfs : mobiusLabelFactors ν ≠ [] := by
    intro hnil
    simp [hnil] at hlen
  have hconv := dyadicConvolutionFactors_eq_zero_of_not_retained
    (mobiusLabelFactors ν) hfs hnot hn hnlo hnhi
  rw [mobiusDyadicComponent_apply]
  simp [hconv]

private theorem vonMangoldtDyadicFilteredSum_eq_univ {X z : ℝ} {n : ℕ}
    (hn : 0 < n) (hnlo : X / 2 ≤ (n : ℝ)) (hnhi : (n : ℝ) ≤ 4 * X) :
    (∑ ν ∈ vonMangoldtDyadicLabels X z,
      vonMangoldtDyadicComponent z ν n) =
      ∑ ν : VonMangoldtDyadicLabel X, vonMangoldtDyadicComponent z ν n := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro ν hνall hνnot
  have hnot :
      ¬ dyadicFactorsRetained (X := X) (z := z) (vonMangoldtLabelFactors ν) := by
    intro hret
    apply hνnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hret⟩
  have hlen := vonMangoldtLabelFactorCount ν
  have hfs : vonMangoldtLabelFactors ν ≠ [] := by
    intro hnil
    simp [hnil] at hlen
  have hconv := dyadicConvolutionFactors_eq_zero_of_not_retained
    (vonMangoldtLabelFactors ν) hfs hnot hn hnlo hnhi
  rw [vonMangoldtDyadicComponent_apply]
  simp [hconv]

/-- The exact finite dyadic decomposition of the Möbius function on the
specified interval. -/
theorem mobiusDyadicDecomposition {X : ℝ} (hX : 3 ≤ X)
    {n : ℕ} (hn : 0 < n) (hnlo : X / 2 ≤ (n : ℝ))
    (hnhi : (n : ℝ) ≤ 4 * X) :
    (ArithmeticFunction.moebius n : ℝ) =
      ∑ ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X),
        mobiusDyadicComponent (dyadicMobiusCutoff X) ν n := by
  calc
    (ArithmeticFunction.moebius n : ℝ) =
        ∑ ν : MobiusDyadicLabel X,
          mobiusDyadicComponent (dyadicMobiusCutoff X) ν n :=
            mobiusDyadicUnfilteredExpansion hX hn hnlo hnhi
    _ = ∑ ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X),
          mobiusDyadicComponent (dyadicMobiusCutoff X) ν n :=
            (mobiusDyadicFilteredSum_eq_univ hn hnlo hnhi).symm

/-- The exact finite dyadic decomposition of the von Mangoldt function on the
specified interval. -/
theorem vonMangoldtDyadicDecomposition {X : ℝ} (hX : 3 ≤ X)
    {n : ℕ} (hn : 0 < n) (hnlo : X / 2 ≤ (n : ℝ))
    (hnhi : (n : ℝ) ≤ 4 * X) :
    ArithmeticFunction.vonMangoldt n =
      ∑ ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X),
        vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n := by
  calc
    ArithmeticFunction.vonMangoldt n =
        ∑ ν : VonMangoldtDyadicLabel X,
          vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n :=
            vonMangoldtDyadicUnfilteredExpansion hX hn hnlo hnhi
    _ = ∑ ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X),
          vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n :=
            (vonMangoldtDyadicFilteredSum_eq_univ hn hnlo hnhi).symm

/-- The pair of exact dyadic decompositions in blueprint item
`lucomb:dyadic-components`. -/
theorem dyadicComponents (X : ℝ) (hX : 3 ≤ X) :
    (∀ n : ℕ, 0 < n → X / 2 ≤ (n : ℝ) → (n : ℝ) ≤ 4 * X →
      (ArithmeticFunction.moebius n : ℝ) =
        ∑ ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X),
          mobiusDyadicComponent (dyadicMobiusCutoff X) ν n) ∧
    (∀ n : ℕ, 0 < n → X / 2 ≤ (n : ℝ) → (n : ℝ) ≤ 4 * X →
      ArithmeticFunction.vonMangoldt n =
        ∑ ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X),
          vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n) := by
  constructor
  · intro n hn hnlo hnhi
    exact mobiusDyadicDecomposition hX hn hnlo hnhi
  · intro n hn hnlo hnhi
    exact vonMangoldtDyadicDecomposition hX hn hnlo hnhi

theorem dyadicFactorsRetained_product_bounds {X z : ℝ}
    {fs : List (DyadicArithmeticFactor X)}
    (hret : dyadicFactorsRetained (X := X) (z := z) fs)
    (hlen : fs.length ≤ 20) :
    X / (2 : ℝ) ^ 21 ≤ dyadicFactorScaleProduct fs ∧
      dyadicFactorScaleProduct fs ≤ 4 * X := by
  rcases hret with ⟨_, hupper, hlower⟩
  have hpow : (2 : ℝ) ^ fs.length ≤ (2 : ℝ) ^ 20 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen
  have hXle : X ≤ (2 : ℝ) ^ 21 * dyadicFactorScaleProduct fs := by
    calc
      X ≤ 2 * ((2 : ℝ) ^ fs.length * dyadicFactorScaleProduct fs) := by
        linarith [hlower]
      _ ≤ 2 * ((2 : ℝ) ^ 20 * dyadicFactorScaleProduct fs) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right hpow
            (dyadicFactorScaleProduct_pos fs).le
        · norm_num
      _ = (2 : ℝ) ^ 21 * dyadicFactorScaleProduct fs := by
        rw [pow_succ]
        ring
  constructor
  · apply (div_le_iff₀ (by positivity)).2
    nlinarith [hXle]
  · exact le_of_lt hupper

theorem mobiusDyadicComponent_spec {X : ℝ} {ν : MobiusDyadicLabel X}
    (hν : ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X)) :
    let fs := mobiusLabelFactors ν
    1 ≤ fs.length ∧ fs.length ≤ 20 ∧
      (∀ f ∈ fs,
        dyadicFactorFunction (dyadicMobiusCutoff X) f ≠ 0 ∧
          (1 / 2 : ℝ) ≤ dyadicFactorScale f ∧ dyadicFactorScale f < 4 * X) ∧
      |dyadicBinomialCoefficient ν.1| ≤ 2 ^ 10 ∧
      dyadicFactorScaleProduct fs < 4 * X ∧
      X / 2 ≤ (2 : ℝ) ^ fs.length * dyadicFactorScaleProduct fs ∧
      X / (2 : ℝ) ^ 21 ≤ dyadicFactorScaleProduct fs ∧
      dyadicFactorScaleProduct fs ≤ 4 * X := by
  dsimp
  have hret := mobiusDyadicLabels_mem hν
  have hlen := mobiusLabelFactorCount ν
  have hprod := dyadicFactorsRetained_product_bounds hret hlen.2
  refine ⟨hlen.1, hlen.2, ?_, dyadicBinomialCoefficient_abs_le ν.1,
    hret.2.1, hret.2.2, hprod.1, hprod.2⟩
  intro f hf
  exact ⟨hret.1 f hf, dyadicFactorScale_ge_half f,
    dyadicFactorScale_lt_fourX f⟩

theorem vonMangoldtDyadicComponent_spec {X : ℝ}
    {ν : VonMangoldtDyadicLabel X}
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X)) :
    let fs := vonMangoldtLabelFactors ν
    1 ≤ fs.length ∧ fs.length ≤ 20 ∧
      (∀ f ∈ fs,
        dyadicFactorFunction (dyadicMobiusCutoff X) f ≠ 0 ∧
          (1 / 2 : ℝ) ≤ dyadicFactorScale f ∧ dyadicFactorScale f < 4 * X) ∧
      |dyadicBinomialCoefficient ν.1| ≤ 2 ^ 10 ∧
      dyadicFactorScaleProduct fs < 4 * X ∧
      X / 2 ≤ (2 : ℝ) ^ fs.length * dyadicFactorScaleProduct fs ∧
      X / (2 : ℝ) ^ 21 ≤ dyadicFactorScaleProduct fs ∧
      dyadicFactorScaleProduct fs ≤ 4 * X := by
  dsimp
  have hret := vonMangoldtDyadicLabels_mem hν
  have hlen := vonMangoldtLabelFactorCount ν
  have hprod := dyadicFactorsRetained_product_bounds hret hlen.2
  refine ⟨hlen.1, hlen.2, ?_, dyadicBinomialCoefficient_abs_le ν.1,
    hret.2.1, hret.2.2, hprod.1, hprod.2⟩
  intro f hf
  exact ⟨hret.1 f hf, dyadicFactorScale_ge_half f,
    dyadicFactorScale_lt_fourX f⟩

#print axioms dyadicComponents
#print axioms mobiusDyadicDecomposition
#print axioms vonMangoldtDyadicDecomposition

end

end FractionalPrimes.Literature.Uniformity.Combinatorics

end
