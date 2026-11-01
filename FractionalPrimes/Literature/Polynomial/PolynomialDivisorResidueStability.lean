module

public import FractionalPrimes.Literature.Uniformity.CramerShortDivisor
public import FractionalPrimes.Literature.LongArithmetic.CramerResidueIntervalCount
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# Stability of short divisor averages on residue classes

This is the finite `lup:divisor-stability` layer. The exact arbitrary-gcd
CRT interval count is imported from the checked long-arithmetic development.
-/

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open scoped BigOperators

private theorem rosserPositiveDivisorsBelow_eq_Icc_filter
    (Y : ℝ) (n : ℕ) :
    rosserPositiveDivisorsBelow Y n =
      (Finset.Icc 1 (Nat.floor Y)).filter (fun d => d ∣ n) := by
  ext d
  simp [rosserPositiveDivisorsBelow, Finset.mem_filter,
    Finset.mem_range, Finset.mem_Icc]
  omega

private theorem shortDivisorSumNat_eq_Icc_sum
    (Y : ℝ) (b : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    shortDivisorSumNat Y b n =
      ∑ d ∈ Finset.Icc 1 (Nat.floor Y), if d ∣ n then b d else 0 := by
  rw [shortDivisorSumNat_eq_rosserSum Y b n hn,
    rosserPositiveDivisorsBelow_eq_Icc_filter]
  rw [Finset.sum_filter]

/-- A short divisor polynomial has almost the same normalized residue average
on two interval lengths: its interval main term is independent of length, and
each supported divisor contributes at most the two endpoint errors. -/
theorem shortDivisorResidueAverage_stability
    (X H₁ H₂ q : ℕ) (a : ℤ) (Y B : ℝ) (b : ℕ → ℝ)
    (hH₁ : 0 < H₁) (hH₂ : 0 < H₂) (hq : 0 < q)
    (hY : 1 ≤ Y)
    (hb : ∀ d, |b d| ≤ B) :
    |((H₁ : ℝ)⁻¹ * ∑ n ∈ (Finset.Ioc X (X + H₁)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          shortDivisorSumNat Y b n) -
      (H₂ : ℝ)⁻¹ * ∑ n ∈ (Finset.Ioc X (X + H₂)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          shortDivisorSumNat Y b n| ≤
      B * (Nat.floor Y : ℝ) * ((H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹) := by
  classical
  let S : Finset ℕ := Finset.Icc 1 (Nat.floor Y)
  let count : ℕ → ℕ → ℕ := fun H d =>
    ((Finset.Ioc X (X + H)).filter
      (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)] ∧ d ∣ n)).card
  let main : ℕ → ℝ := fun H =>
    ∑ d ∈ S, b d * (if (Nat.gcd d q : ℤ) ∣ a then
      (Nat.lcm d q : ℝ)⁻¹ else 0)
  have hS_card : (S.card : ℝ) = Nat.floor Y := by
    dsimp [S]
    have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
    have hfloor : 1 ≤ Nat.floor Y := Nat.le_floor (by exact_mod_cast hY')
    simp [Nat.card_Icc]
  have hcount_eq (H d : ℕ) :
      count H d =
        ((Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ)).filter
          (fun n : ℤ => (d : ℤ) ∣ n ∧ n ≡ a [ZMOD (q : ℤ)])).card := by
    let Pn : ℕ → Prop := fun n =>
      (n : ℤ) ≡ a [ZMOD (q : ℤ)] ∧ d ∣ n
    let Pi : ℤ → Prop := fun n =>
      (d : ℤ) ∣ n ∧ n ≡ a [ZMOD (q : ℤ)]
    let Fn : ℕ → ℝ := fun n => if Pn n then 1 else 0
    let Fi : ℤ → ℝ := fun n => if Pi n then 1 else 0
    have hsum := cramerShortInterval_sum_nat_eq_int X H Fi
    have hnat : (∑ n ∈ (Finset.Ioc X (X + H)).filter Pn, (1 : ℝ)) =
        (∑ n ∈ Finset.Ioc X (X + H), Fn n) := by
      rw [← Finset.sum_filter]
    have hint : (∑ n ∈ (Finset.Ioc (X : ℤ)
        ((X + H : ℕ) : ℤ)).filter Pi, (1 : ℝ)) =
        (∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ), Fi n) := by
      rw [← Finset.sum_filter]
    have hcast : ∀ n : ℕ, Fn n = Fi (n : ℤ) := by
      intro n
      by_cases hd : d ∣ n <;> by_cases hr : (n : ℤ) ≡ a [ZMOD (q : ℤ)] <;>
        simp [Fn, Fi, Pn, Pi, hd, hr, Int.natCast_dvd_natCast, and_comm]
    have hsum' : (∑ n ∈ Finset.Ioc X (X + H), Fn n) =
        ∑ n ∈ Finset.Ioc X (X + H), Fi (n : ℤ) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hcast n
    have hnatCard : ((count H d : ℕ) : ℝ) =
        ∑ n ∈ (Finset.Ioc X (X + H)).filter Pn, (1 : ℝ) := by
      simp [count, Pn]
    have hintCard : (((Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ)).filter Pi).card : ℝ) =
        ∑ n ∈ (Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ)).filter Pi, (1 : ℝ) := by
      simp
    have hReal : (count H d : ℝ) =
        (((Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ)).filter Pi).card : ℝ) := by
      calc
        (count H d : ℝ) =
            ∑ n ∈ (Finset.Ioc X (X + H)).filter Pn, (1 : ℝ) := hnatCard
        _ = ∑ n ∈ Finset.Ioc X (X + H), Fn n := hnat
        _ = ∑ n ∈ Finset.Ioc X (X + H), Fi (n : ℤ) := hsum'
        _ = ∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ), Fi n := hsum
        _ = ∑ n ∈ (Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ)).filter Pi, (1 : ℝ) := hint.symm
        _ = (((Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ)).filter Pi).card : ℝ) := hintCard.symm
    exact_mod_cast hReal
  have hcountError (H d : ℕ) (hH : 0 < H) (hd : 0 < d) :
      |(count H d : ℝ) -
        (if (Nat.gcd d q : ℤ) ∣ a then
          (H : ℝ) / (Nat.lcm d q : ℝ) else 0)| ≤ 1 := by
    have h := FractionalPrimes.Literature.LongArithmetic.crtIntervalCount
      (X : ℝ) (H : ℝ) d q a (by exact_mod_cast hH) hd hq
    have hcast : (Int.floor (X : ℝ) : ℤ) = X := Int.floor_natCast X
    have hcast' : (Int.floor ((X : ℝ) + (H : ℝ)) : ℤ) = X + H := by
      have hsumcast : (X : ℝ) + (H : ℝ) = ((X + H : ℕ) : ℝ) := by norm_cast
      rw [hsumcast, Int.floor_natCast]
      norm_num [Nat.cast_add]
    have h' := h
    rw [hcast, hcast'] at h'
    rw [hcount_eq H d]
    by_cases hg : (Nat.gcd d q : ℤ) ∣ a
    · simpa [hg] using h'
    · simp only [if_neg hg] at h'
      simp [hg, h']
  have hsumExpand (H : ℕ) (hH : 0 < H) :
      (∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          shortDivisorSumNat Y b n) =
        ∑ d ∈ S, b d * (count H d : ℝ) := by
    have hpos (n : ℕ) (hn : n ∈ (Finset.Ioc X (X + H)).filter
        (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)])) : 0 < n := by
      have hn' := (Finset.mem_filter.mp hn).1
      simp only [Finset.mem_Ioc] at hn'
      omega
    calc
      _ = ∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          ∑ d ∈ S, if d ∣ n then b d else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            exact shortDivisorSumNat_eq_Icc_sum Y b n (hpos n hn)
      _ = ∑ d ∈ S, ∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          if d ∣ n then b d else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ d ∈ S, b d * (count H d : ℝ) := by
            apply Finset.sum_congr rfl
            intro d hd
            calc
              (∑ n ∈ (Finset.Ioc X (X + H)).filter
                  (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
                  if d ∣ n then b d else 0) =
                ∑ n ∈ ((Finset.Ioc X (X + H)).filter
                    (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)])).filter
                    (fun n : ℕ => d ∣ n), b d := by
                  rw [← Finset.sum_filter]
              _ =
                  (((Finset.Ioc X (X + H)).filter
                    (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)])).filter
                    (fun n : ℕ => d ∣ n)).card * b d := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ = b d * (count H d : ℝ) := by
                  simp [count, Finset.filter_filter, mul_comm, and_comm]
  have hdev (H : ℕ) (hH : 0 < H) :
      |(H : ℝ)⁻¹ *
          ∑ n ∈ (Finset.Ioc X (X + H)).filter
            (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
            shortDivisorSumNat Y b n - main H| ≤
        B * (Nat.floor Y : ℝ) * (H : ℝ)⁻¹ := by
    have hsum := hsumExpand H hH
    let T : ℝ := ∑ d ∈ S, b d * (count H d : ℝ)
    have hmainScale : main H = (H : ℝ)⁻¹ *
        ∑ d ∈ S, b d * (if (Nat.gcd d q : ℤ) ∣ a then
          (H : ℝ) / (Nat.lcm d q : ℝ) else 0) := by
      dsimp [main]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hg : (Nat.gcd d q : ℤ) ∣ a
      · rw [if_pos hg, if_pos hg]
        have hHposR : 0 < (H : ℝ) := by exact_mod_cast hH
        field_simp [hHposR.ne']
      · rw [if_neg hg, if_neg hg]
        simp
    have hdiff : (H : ℝ)⁻¹ * T - main H =
        ∑ d ∈ S, (H : ℝ)⁻¹ *
          (b d * ((count H d : ℝ) -
            (if (Nat.gcd d q : ℤ) ∣ a then
              (H : ℝ) / (Nat.lcm d q : ℝ) else 0))) := by
      rw [hmainScale]
      calc
        (H : ℝ)⁻¹ * T - (H : ℝ)⁻¹ *
            ∑ d ∈ S, b d * (if (Nat.gcd d q : ℤ) ∣ a then
              (H : ℝ) / (Nat.lcm d q : ℝ) else 0) =
          (H : ℝ)⁻¹ *
            (T - ∑ d ∈ S, b d * (if (Nat.gcd d q : ℤ) ∣ a then
              (H : ℝ) / (Nat.lcm d q : ℝ) else 0)) := by ring
        _ = (H : ℝ)⁻¹ *
            (∑ d ∈ S, b d * (count H d : ℝ) -
              ∑ d ∈ S, b d * (if (Nat.gcd d q : ℤ) ∣ a then
                (H : ℝ) / (Nat.lcm d q : ℝ) else 0)) := by
              simp [T]
        _ = (H : ℝ)⁻¹ * ∑ d ∈ S,
              (b d * (count H d : ℝ) -
                b d * (if (Nat.gcd d q : ℤ) ∣ a then
                  (H : ℝ) / (Nat.lcm d q : ℝ) else 0)) := by
              rw [← Finset.sum_sub_distrib]
        _ = ∑ d ∈ S, (H : ℝ)⁻¹ *
              (b d * (count H d : ℝ) -
                b d * (if (Nat.gcd d q : ℤ) ∣ a then
                  (H : ℝ) / (Nat.lcm d q : ℝ) else 0)) := by
              rw [Finset.mul_sum]
        _ = ∑ d ∈ S, (H : ℝ)⁻¹ *
              (b d * ((count H d : ℝ) -
                (if (Nat.gcd d q : ℤ) ∣ a then
                  (H : ℝ) / (Nat.lcm d q : ℝ) else 0))) := by
              apply Finset.sum_congr rfl
              intro d hd
              ring
    rw [hsum, hdiff]
    calc
      |∑ d ∈ S, (H : ℝ)⁻¹ *
          (b d * ((count H d : ℝ) -
            (if (Nat.gcd d q : ℤ) ∣ a then
              (H : ℝ) / (Nat.lcm d q : ℝ) else 0)))| ≤
        ∑ d ∈ S, |(H : ℝ)⁻¹ *
          (b d * ((count H d : ℝ) -
            (if (Nat.gcd d q : ℤ) ∣ a then
              (H : ℝ) / (Nat.lcm d q : ℝ) else 0)))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ S, B * (H : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro d hd
        have hcnt : |(count H d : ℝ) -
            (if (Nat.gcd d q : ℤ) ∣ a then
              (H : ℝ) / (Nat.lcm d q : ℝ) else 0)| ≤ 1 := by
          have hdpos : 0 < d := by
            change d ∈ Finset.Icc 1 (Nat.floor Y) at hd
            have := Finset.mem_Icc.mp hd
            omega
          exact hcountError H d hH hdpos
        have hHposR : 0 < (H : ℝ) := by exact_mod_cast hH
        rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hHposR.le)]
        have hmul := mul_le_mul_of_nonneg_right hcnt (abs_nonneg (b d))
        have hb' := hb d
        have hbound : |b d| *
            |(count H d : ℝ) -
              (if (Nat.gcd d q : ℤ) ∣ a then
                (H : ℝ) / (Nat.lcm d q : ℝ) else 0)| ≤ B := by
          calc
            _ ≤ |b d| * 1 := mul_le_mul_of_nonneg_left hcnt (abs_nonneg _)
            _ ≤ B := by simpa using hb'
        calc
          (H : ℝ)⁻¹ * (|b d| *
              |(count H d : ℝ) -
                (if (Nat.gcd d q : ℤ) ∣ a then
                  (H : ℝ) / (Nat.lcm d q : ℝ) else 0)|) ≤
              (H : ℝ)⁻¹ * B := mul_le_mul_of_nonneg_left hbound
                (inv_nonneg.mpr hHposR.le)
          _ = B * (H : ℝ)⁻¹ := by ring
      _ = B * (Nat.floor Y : ℝ) * (H : ℝ)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul, hS_card]
        ring
  have hmain_eq : main H₁ = main H₂ := by
    dsimp [main]
  have h₁ := hdev H₁ hH₁
  have h₂ := hdev H₂ hH₂
  have htriangle :
      |((H₁ : ℝ)⁻¹ *
          ∑ n ∈ (Finset.Ioc X (X + H₁)).filter
            (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
            shortDivisorSumNat Y b n) -
        ((H₂ : ℝ)⁻¹ *
          ∑ n ∈ (Finset.Ioc X (X + H₂)).filter
            (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
            shortDivisorSumNat Y b n)| ≤
      B * (Nat.floor Y : ℝ) * (H₁ : ℝ)⁻¹ +
        B * (Nat.floor Y : ℝ) * (H₂ : ℝ)⁻¹ := by
    calc
      _ = |(((H₁ : ℝ)⁻¹ *
          ∑ n ∈ (Finset.Ioc X (X + H₁)).filter
            (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
            shortDivisorSumNat Y b n) - main H₁) +
        (main H₂ - ((H₂ : ℝ)⁻¹ *
          ∑ n ∈ (Finset.Ioc X (X + H₂)).filter
            (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
            shortDivisorSumNat Y b n))| := by rw [hmain_eq]; ring_nf
      _ ≤ |((H₁ : ℝ)⁻¹ *
          ∑ n ∈ (Finset.Ioc X (X + H₁)).filter
            (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
            shortDivisorSumNat Y b n) - main H₁| +
          |main H₂ - ((H₂ : ℝ)⁻¹ *
          ∑ n ∈ (Finset.Ioc X (X + H₂)).filter
            (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
            shortDivisorSumNat Y b n)| := by
        calc
          |(((H₁ : ℝ)⁻¹ *
              ∑ n ∈ (Finset.Ioc X (X + H₁)).filter
                (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
                shortDivisorSumNat Y b n) - main H₁) +
            (main H₂ - ((H₂ : ℝ)⁻¹ *
              ∑ n ∈ (Finset.Ioc X (X + H₂)).filter
                (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
                shortDivisorSumNat Y b n))| =
              ‖(((H₁ : ℝ)⁻¹ *
                ∑ n ∈ (Finset.Ioc X (X + H₁)).filter
                  (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
                  shortDivisorSumNat Y b n) - main H₁) +
                (main H₂ - ((H₂ : ℝ)⁻¹ *
                  ∑ n ∈ (Finset.Ioc X (X + H₂)).filter
                    (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
                    shortDivisorSumNat Y b n))‖ := by rw [Real.norm_eq_abs]
          _ ≤ ‖((H₁ : ℝ)⁻¹ *
                ∑ n ∈ (Finset.Ioc X (X + H₁)).filter
                  (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
                  shortDivisorSumNat Y b n) - main H₁‖ +
              ‖main H₂ - ((H₂ : ℝ)⁻¹ *
                ∑ n ∈ (Finset.Ioc X (X + H₂)).filter
                  (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
                  shortDivisorSumNat Y b n)‖ := norm_add_le _ _
          _ = _ := by simp [Real.norm_eq_abs]
      _ ≤ _ := add_le_add h₁ (by simpa [abs_sub_comm] using h₂)
  calc
    _ ≤ B * (Nat.floor Y : ℝ) * (H₁ : ℝ)⁻¹ +
        B * (Nat.floor Y : ℝ) * (H₂ : ℝ)⁻¹ := htriangle
    _ = B * (Nat.floor Y : ℝ) *
        ((H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹) := by ring

private theorem cramerShortDivisorApproximationNatFixed
    (A : ℝ) (X H : ℕ) (hA : 0 < A) (hX : 3 ≤ X)
    (hH : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H : ℝ)) :
    (∑ n ∈ Finset.Ioc X (X + H),
      |paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
        shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ))
          (cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)) n|) ≤
      cramerApproximationConstant A (1 / 16 : ℝ) * (H : ℝ) *
        (Real.log (X : ℝ)) ^ (-A : ℝ) := by
  let δ : ℝ := 1 / 16
  let Y : ℝ := (X : ℝ) ^ δ
  let b : ℕ → ℝ := cramerShortDivisorCoefficient (X : ℝ) δ
  have hpoint (n : ℕ) (hn : n ∈ Finset.Ioc X (X + H)) :
      shortDivisorSumNat Y b n =
        ∑ d ∈ rosserPositiveDivisorsBelow Y n, b d := by
    have hnpos : 0 < n := by
      have hn' := Finset.mem_Ioc.mp hn
      omega
    exact shortDivisorSumNat_eq_rosserSum Y b n hnpos
  have hcastSum := cramerShortInterval_sum_nat_eq_int X H
    (fun n : ℤ => |paperShortBlockCramerWeight (X : ℝ) n -
      ∑ d ∈ rosserPositiveDivisorsBelow
        ((X : ℝ) ^ (1 / 16 : ℝ)) n.natAbs,
          cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ) d|)
  have hnatRosser :
      (∑ n ∈ Finset.Ioc X (X + H),
        |paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
          ∑ d ∈ rosserPositiveDivisorsBelow ((X : ℝ) ^ (1 / 16 : ℝ)) n,
            cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ) d|) =
        ∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ),
          |paperShortBlockCramerWeight (X : ℝ) n -
            ∑ d ∈ rosserPositiveDivisorsBelow
              ((X : ℝ) ^ (1 / 16 : ℝ)) n.natAbs,
                cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ) d| := by
    simpa only [Int.natAbs_natCast] using hcastSum
  have herror := cramerApproximationIntervalBound A (1 / 16 : ℝ) X H
    hA hX (by norm_num) (by norm_num) hH
  calc
    _ = ∑ n ∈ Finset.Ioc X (X + H),
        |paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
          ∑ d ∈ rosserPositiveDivisorsBelow ((X : ℝ) ^ (1 / 16 : ℝ)) n,
            cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ) d| := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hpoint n hn]
    _ = ∑ n ∈ Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ),
        |paperShortBlockCramerWeight (X : ℝ) n -
          ∑ d ∈ rosserPositiveDivisorsBelow
            ((X : ℝ) ^ (1 / 16 : ℝ)) n.natAbs,
              cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ) d| := hnatRosser
    _ ≤ cramerApproximationConstant A (1 / 16 : ℝ) * (H : ℝ) *
        (Real.log (X : ℝ)) ^ (-A : ℝ) := herror

private theorem paperCramerResidueApproximationError
    (A : ℝ) (X H q : ℕ) (a : ℤ)
    (hA : 0 < A) (hX : 3 ≤ X)
    (hH : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H : ℝ)) (hHpos : 0 < H) :
    |(H : ℝ)⁻¹ *
        ∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
      (H : ℝ)⁻¹ *
        ∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ))
            (cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)) n| ≤
      cramerApproximationConstant A (1 / 16 : ℝ) *
        (Real.log (X : ℝ)) ^ (-A : ℝ) := by
  have hXerr := cramerShortDivisorApproximationNatFixed A X H hA hX hH
  have hsubset :
      (∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          |paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
            shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ))
              (cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)) n|) ≤
        ∑ n ∈ Finset.Ioc X (X + H),
          |paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
            shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ))
              (cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)) n| := by
    calc
      _ = ∑ n ∈ Finset.Ioc X (X + H),
          if (n : ℤ) ≡ a [ZMOD (q : ℤ)] then
            |paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
              shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ))
                (cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)) n|
          else 0 := by rw [Finset.sum_filter]
      _ ≤ ∑ n ∈ Finset.Ioc X (X + H),
          |paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
            shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ))
              (cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)) n| := by
          apply Finset.sum_le_sum
          intro n hn
          by_cases hres : (n : ℤ) ≡ a [ZMOD (q : ℤ)]
          · simp [hres]
          · simpa [hres] using
              (abs_nonneg (paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
                shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ))
                  (cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)) n))
  have hsumSub :
      (∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          paperShortBlockCramerWeight (X : ℝ) (n : ℤ)) -
        ∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ))
            (cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)) n =
      ∑ n ∈ (Finset.Ioc X (X + H)).filter
        (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
        (paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
          shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ))
            (cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)) n) := by
    rw [Finset.sum_sub_distrib]
  have hInv : 0 ≤ (H : ℝ)⁻¹ := inv_nonneg.mpr (by exact_mod_cast hHpos.le)
  have hHposR : 0 < (H : ℝ) := by exact_mod_cast hHpos
  calc
    _ = (H : ℝ)⁻¹ * |(∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          paperShortBlockCramerWeight (X : ℝ) (n : ℤ)) -
        ∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ))
            (cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)) n| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hInv]
    _ ≤ (H : ℝ)⁻¹ *
        ∑ n ∈ (Finset.Ioc X (X + H)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          |paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
            shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ))
              (cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)) n| := by
          apply mul_le_mul_of_nonneg_left _ hInv
          rw [hsumSub]
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (H : ℝ)⁻¹ *
        (∑ n ∈ Finset.Ioc X (X + H),
          |paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
            shortDivisorSumNat ((X : ℝ) ^ (1 / 16 : ℝ))
              (cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)) n|) :=
          mul_le_mul_of_nonneg_left hsubset hInv
    _ ≤ (H : ℝ)⁻¹ * (cramerApproximationConstant A (1 / 16 : ℝ) *
          (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ)) :=
          mul_le_mul_of_nonneg_left hXerr hInv
    _ = cramerApproximationConstant A (1 / 16 : ℝ) *
          (Real.log (X : ℝ)) ^ (-A : ℝ) := by
          field_simp [hHposR.ne']

/-- The literal short-to-long stability constant from blueprint
`lup:cramer-stability`. -/
noncomputable def cramerShortLongStabilityConstant (A : ℝ) : ℝ :=
  2 * cramerApproximationConstant A (1 / 16 : ℝ) +
    2 * Real.exp 13 *
      (16 * (A + 2 / 5) / (9 * Real.exp 1)) ^ (A + 2 / 5)

/-- The exact Cramér model has stable normalized averages on residue classes
between any two source short lengths. The divisor coefficients are fixed at
the common center `X`, as in the approved source theorem. -/
theorem cramerShortLongStability
    (A : ℝ) (X H₁ H₂ q : ℕ) (a : ℤ)
    (hA : 0 < A) (hX : 3 ≤ X)
    (hH₁ : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H₁ : ℝ))
    (hH₁₂ : H₁ ≤ H₂) (hH₂X : H₂ ≤ X) (hq : 0 < q) :
    |(H₁ : ℝ)⁻¹ *
        ∑ n ∈ (Finset.Ioc X (X + H₁)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          paperShortBlockCramerWeight (X : ℝ) (n : ℤ) -
      (H₂ : ℝ)⁻¹ *
        ∑ n ∈ (Finset.Ioc X (X + H₂)).filter
          (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          paperShortBlockCramerWeight (X : ℝ) (n : ℤ)| ≤
      cramerShortLongStabilityConstant A *
        (Real.log (X : ℝ)) ^ (-A : ℝ) := by
  classical
  let Y : ℝ := (X : ℝ) ^ (1 / 16 : ℝ)
  let b : ℕ → ℝ := cramerShortDivisorCoefficient (X : ℝ) (1 / 16 : ℝ)
  let B : ℝ := Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ)
  let modelAverage : ℕ → ℝ := fun H =>
    (H : ℝ)⁻¹ *
      ∑ n ∈ (Finset.Ioc X (X + H)).filter
        (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
        paperShortBlockCramerWeight (X : ℝ) (n : ℤ)
  let divisorAverage : ℕ → ℝ := fun H =>
    (H : ℝ)⁻¹ *
      ∑ n ∈ (Finset.Ioc X (X + H)).filter
        (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
        shortDivisorSumNat Y b n
  have hXreal : 3 ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : 0 < (X : ℝ) := by positivity
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hpowpos : 0 < (X : ℝ) ^ (5 / 8 : ℝ) :=
    Real.rpow_pos_of_pos hXpos _
  have hH₁posR : 0 < (H₁ : ℝ) := lt_of_lt_of_le hpowpos hH₁
  have hH₁pos : 0 < H₁ := by exact_mod_cast hH₁posR
  have hH₂lower : (X : ℝ) ^ (5 / 8 : ℝ) ≤ (H₂ : ℝ) :=
    hH₁.trans (by exact_mod_cast hH₁₂)
  have hH₂posR : 0 < (H₂ : ℝ) := lt_of_lt_of_le hpowpos hH₂lower
  have hH₂pos : 0 < H₂ := by exact_mod_cast hH₂posR
  have happrox₁ := paperCramerResidueApproximationError A X H₁ q a
    hA hX hH₁ hH₁pos
  have happrox₂ := paperCramerResidueApproximationError A X H₂ q a
    hA hX hH₂lower hH₂pos
  have hYge : 1 ≤ Y := by
    dsimp [Y]
    exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ X by omega)) (by norm_num)
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (Real.exp_pos 13).le (Real.rpow_nonneg hlog.le _)
  have hb : ∀ d, |b d| ≤ B := by
    intro d
    dsimp [b, B]
    exact cramerShortDivisorCoefficient_abs_le (X : ℝ) (1 / 16 : ℝ)
      hXreal d
  have hdiv := shortDivisorResidueAverage_stability X H₁ H₂ q a Y B b
    hH₁pos hH₂pos hq hYge hb
  have hfloor : (Nat.floor Y : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hinv₁ : (H₁ : ℝ)⁻¹ ≤ (X : ℝ) ^ (-(5 / 8 : ℝ)) := by
    have h := one_div_le_one_div_of_le hpowpos hH₁
    have h' : (H₁ : ℝ)⁻¹ ≤ ((X : ℝ) ^ (5 / 8 : ℝ))⁻¹ := by
      simpa only [one_div] using h
    rw [Real.rpow_neg hXpos.le]
    exact h'
  have hinv₂ : (H₂ : ℝ)⁻¹ ≤ (X : ℝ) ^ (-(5 / 8 : ℝ)) := by
    have h := one_div_le_one_div_of_le hpowpos hH₂lower
    have h' : (H₂ : ℝ)⁻¹ ≤ ((X : ℝ) ^ (5 / 8 : ℝ))⁻¹ := by
      simpa only [one_div] using h
    rw [Real.rpow_neg hXpos.le]
    exact h'
  have hinvSum : (H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹ ≤
      2 * (X : ℝ) ^ (-(5 / 8 : ℝ)) := by
    calc
      _ ≤ (X : ℝ) ^ (-(5 / 8 : ℝ)) + (X : ℝ) ^ (-(5 / 8 : ℝ)) :=
        add_le_add hinv₁ hinv₂
      _ = 2 * (X : ℝ) ^ (-(5 / 8 : ℝ)) := by ring
  have hpowerGap : Y * (X : ℝ) ^ (-(5 / 8 : ℝ)) =
      Real.exp (-((9 / 16 : ℝ) * Real.log (X : ℝ))) := by
    dsimp [Y]
    calc
      (X : ℝ) ^ (1 / 16 : ℝ) * (X : ℝ) ^ (-(5 / 8 : ℝ)) =
          (X : ℝ) ^ ((1 / 16 : ℝ) + (-(5 / 8 : ℝ))) :=
        (Real.rpow_add hXpos _ _).symm
      _ = (X : ℝ) ^ (-(9 / 16 : ℝ)) := by congr 1 <;> norm_num
      _ = Real.exp (-((9 / 16 : ℝ) * Real.log (X : ℝ))) := by
        rw [Real.rpow_def_of_pos hXpos]
        congr 1
        ring
  have hdivGap : B * (Nat.floor Y : ℝ) *
        ((H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹) ≤
      2 * Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) *
        Real.exp (-((9 / 16 : ℝ) * Real.log (X : ℝ))) := by
    have hsumNonneg : 0 ≤ (H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹ :=
      add_nonneg (inv_nonneg.mpr (by exact_mod_cast hH₁pos.le))
        (inv_nonneg.mpr (by exact_mod_cast hH₂pos.le))
    have hprod : (Nat.floor Y : ℝ) *
        ((H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹) ≤
        Y * (2 * (X : ℝ) ^ (-(5 / 8 : ℝ))) := by
      calc
        _ ≤ Y * ((H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right hfloor hsumNonneg
        _ ≤ Y * (2 * (X : ℝ) ^ (-(5 / 8 : ℝ))) :=
          mul_le_mul_of_nonneg_left hinvSum (Real.rpow_nonneg hXpos.le _)
    calc
      _ = B * ((Nat.floor Y : ℝ) *
          ((H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹)) := by ring
      _ ≤ B * (Y * (2 * (X : ℝ) ^ (-(5 / 8 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hprod hBnonneg
      _ = 2 * Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) *
          Real.exp (-((9 / 16 : ℝ) * Real.log (X : ℝ))) := by
        dsimp [B]
        rw [show Y * (2 * (X : ℝ) ^ (-(5 / 8 : ℝ))) =
          2 * (Y * (X : ℝ) ^ (-(5 / 8 : ℝ))) by ring, hpowerGap]
        ring
  let β : ℝ := A + 2 / 5
  have hβ : 0 < β := by dsimp [β]; linarith
  have hmax := rpow_mul_exp_neg_le_exact_max β (9 / 16 : ℝ)
    (Real.log (X : ℝ)) hβ (by norm_num) hlog
  have hpowCancel : (Real.log (X : ℝ)) ^ β *
      (Real.log (X : ℝ)) ^ (-A : ℝ) =
        (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) := by
    dsimp [β]
    rw [Real.rpow_add hlog A (2 / 5 : ℝ), Real.rpow_neg hlog.le]
    have hne : (Real.log (X : ℝ)) ^ A ≠ 0 :=
      (Real.rpow_pos_of_pos hlog A).ne'
    field_simp [hne]
  have hbase : β / (Real.exp 1 * (9 / 16 : ℝ)) =
      16 * β / (9 * Real.exp 1) := by
    field_simp
  have habsorbed :
      (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) *
        Real.exp (-((9 / 16 : ℝ) * Real.log (X : ℝ))) ≤
      (16 * β / (9 * Real.exp 1)) ^ β *
        (Real.log (X : ℝ)) ^ (-A : ℝ) := by
    calc
      _ = ((Real.log (X : ℝ)) ^ β *
          Real.exp (-((9 / 16 : ℝ) * Real.log (X : ℝ)))) *
          (Real.log (X : ℝ)) ^ (-A : ℝ) := by
            rw [← hpowCancel]
            ring
      _ ≤ (β / (Real.exp 1 * (9 / 16 : ℝ))) ^ β *
          (Real.log (X : ℝ)) ^ (-A : ℝ) :=
        mul_le_mul_of_nonneg_right hmax (Real.rpow_nonneg hlog.le _)
      _ = _ := by rw [hbase]
  have hdivGapAbsorbed : B * (Nat.floor Y : ℝ) *
      ((H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹) ≤
      2 * Real.exp 13 * (16 * β / (9 * Real.exp 1)) ^ β *
        (Real.log (X : ℝ)) ^ (-A : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left habsorbed
      (show 0 ≤ 2 * Real.exp 13 by positivity)
    calc
      _ ≤ 2 * Real.exp 13 * (Real.log (X : ℝ)) ^ (2 / 5 : ℝ) *
          Real.exp (-((9 / 16 : ℝ) * Real.log (X : ℝ))) := hdivGap
      _ = 2 * Real.exp 13 * ((Real.log (X : ℝ)) ^ (2 / 5 : ℝ) *
          Real.exp (-((9 / 16 : ℝ) * Real.log (X : ℝ)))) := by ring
      _ ≤ 2 * Real.exp 13 * ((16 * β / (9 * Real.exp 1)) ^ β *
          (Real.log (X : ℝ)) ^ (-A : ℝ)) := hmul
      _ = _ := by ring
  have happrox₁' : |modelAverage H₁ - divisorAverage H₁| ≤
      cramerApproximationConstant A (1 / 16 : ℝ) *
        (Real.log (X : ℝ)) ^ (-A : ℝ) := by
    simpa [modelAverage, divisorAverage, Y, b] using happrox₁
  have happrox₂' : |modelAverage H₂ - divisorAverage H₂| ≤
      cramerApproximationConstant A (1 / 16 : ℝ) *
        (Real.log (X : ℝ)) ^ (-A : ℝ) := by
    simpa [modelAverage, divisorAverage, Y, b] using happrox₂
  have hdiv' : |divisorAverage H₁ - divisorAverage H₂| ≤
      B * (Nat.floor Y : ℝ) * ((H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹) := by
    simpa [divisorAverage] using hdiv
  have htriangle : |modelAverage H₁ - modelAverage H₂| ≤
      2 * cramerApproximationConstant A (1 / 16 : ℝ) *
          (Real.log (X : ℝ)) ^ (-A : ℝ) +
        B * (Nat.floor Y : ℝ) * ((H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹) := by
    calc
      _ = |(modelAverage H₁ - divisorAverage H₁) +
          (divisorAverage H₁ - divisorAverage H₂) +
          (divisorAverage H₂ - modelAverage H₂)| := by
            congr 1
            ring
      _ ≤ |modelAverage H₁ - divisorAverage H₁| +
          |divisorAverage H₁ - divisorAverage H₂| +
          |divisorAverage H₂ - modelAverage H₂| := by
            calc
              _ ≤ |(modelAverage H₁ - divisorAverage H₁) +
                  (divisorAverage H₁ - divisorAverage H₂)| +
                  |divisorAverage H₂ - modelAverage H₂| := abs_add_le _ _
              _ ≤ (|modelAverage H₁ - divisorAverage H₁| +
                  |divisorAverage H₁ - divisorAverage H₂|) +
                  |divisorAverage H₂ - modelAverage H₂| :=
                    add_le_add_left (abs_add_le _ _) _
              _ = _ := by ring
      _ ≤ _ := by
        have hlast : |divisorAverage H₂ - modelAverage H₂| =
            |modelAverage H₂ - divisorAverage H₂| := abs_sub_comm _ _
        rw [hlast]
        calc
          _ = |modelAverage H₁ - divisorAverage H₁| +
              (|divisorAverage H₁ - divisorAverage H₂| +
                |modelAverage H₂ - divisorAverage H₂|) := by ring
          _ ≤ cramerApproximationConstant A (1 / 16 : ℝ) *
                (Real.log (X : ℝ)) ^ (-A : ℝ) +
              (B * (Nat.floor Y : ℝ) *
                ((H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹) +
                cramerApproximationConstant A (1 / 16 : ℝ) *
                  (Real.log (X : ℝ)) ^ (-A : ℝ)) := by
            exact add_le_add happrox₁' (add_le_add hdiv' happrox₂')
          _ = _ := by ring
  calc
    _ = |modelAverage H₁ - modelAverage H₂| := rfl
    _ ≤ _ := by
      calc
        _ ≤ 2 * cramerApproximationConstant A (1 / 16 : ℝ) *
            (Real.log (X : ℝ)) ^ (-A : ℝ) +
          B * (Nat.floor Y : ℝ) * ((H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹) := htriangle
        _ ≤ (2 * cramerApproximationConstant A (1 / 16 : ℝ) +
            2 * Real.exp 13 * (16 * β / (9 * Real.exp 1)) ^ β) *
            (Real.log (X : ℝ)) ^ (-A : ℝ) := by
          have h := add_le_add
            (le_refl (2 * cramerApproximationConstant A (1 / 16 : ℝ) *
              (Real.log (X : ℝ)) ^ (-A : ℝ)))
            hdivGapAbsorbed
          calc
            _ = 2 * cramerApproximationConstant A (1 / 16 : ℝ) *
                (Real.log (X : ℝ)) ^ (-A : ℝ) +
                  B * (Nat.floor Y : ℝ) *
                    ((H₁ : ℝ)⁻¹ + (H₂ : ℝ)⁻¹) := by rfl
            _ ≤ 2 * cramerApproximationConstant A (1 / 16 : ℝ) *
                (Real.log (X : ℝ)) ^ (-A : ℝ) +
                  2 * Real.exp 13 * (16 * β / (9 * Real.exp 1)) ^ β *
                    (Real.log (X : ℝ)) ^ (-A : ℝ) := h
            _ = (2 * cramerApproximationConstant A (1 / 16 : ℝ) +
                2 * Real.exp 13 * (16 * β / (9 * Real.exp 1)) ^ β) *
                (Real.log (X : ℝ)) ^ (-A : ℝ) := by ring
        _ = cramerShortLongStabilityConstant A *
            (Real.log (X : ℝ)) ^ (-A : ℝ) := by
          simp [cramerShortLongStabilityConstant, β]

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.shortDivisorResidueAverage_stability
#print axioms FractionalPrimes.Literature.Polynomial.cramerShortLongStability
