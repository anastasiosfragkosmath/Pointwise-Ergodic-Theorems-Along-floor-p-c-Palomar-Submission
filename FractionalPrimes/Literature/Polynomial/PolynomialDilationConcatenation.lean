module

public import FractionalPrimes.Literature.Polynomial.PolynomialRecurrence
public import FractionalPrimes.Literature.Polynomial.PolynomialInverseBudgets
public import FractionalPrimes.Literature.Polynomial.AffineRecurrence
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Combinatorics.Pigeonhole

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

private theorem intFloor_div_natCast_eq_floorFloor_div_natCast
    (x : ℝ) (a : ℕ) :
    Int.floor (x / (a : ℝ)) =
      Int.floor (((Int.floor x : ℤ) : ℝ) / (a : ℝ)) := by
  rw [Int.floor_div_natCast, Int.floor_div_natCast, Int.floor_intCast]

private theorem dilationCenter_offset_abs_lt
    (x : ℝ) {a : ℕ} (ha : 1 ≤ a) :
    |(((a : ℤ) * Int.floor (x / (a : ℝ)) - Int.floor x : ℤ) : ℝ)| <
      (a : ℝ) := by
  let y : ℤ := Int.floor x
  let q : ℤ := Int.floor ((y : ℝ) / (a : ℝ))
  have haR : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hqeq : Int.floor (x / (a : ℝ)) = q := by
    dsimp [q, y]
    exact intFloor_div_natCast_eq_floorFloor_div_natCast x a
  have hqle : (q : ℝ) ≤ (y : ℝ) / (a : ℝ) := by
    dsimp [q]
    exact Int.floor_le _
  have hqright : (y : ℝ) / (a : ℝ) < (q : ℝ) + 1 := by
    dsimp [q]
    exact Int.lt_floor_add_one _
  have hleft : (a : ℝ) * (q : ℝ) ≤ (y : ℝ) := by
    rw [le_div_iff₀ haR] at hqle
    nlinarith
  have hright : (y : ℝ) < (a : ℝ) * ((q : ℝ) + 1) := by
    rw [div_lt_iff₀ haR] at hqright
    nlinarith
  have hcast :
      (((a : ℤ) * Int.floor (x / (a : ℝ)) - Int.floor x : ℤ) : ℝ) =
        (a : ℝ) * (q : ℝ) - (y : ℝ) := by
    rw [hqeq]
    simp [y]
  rw [hcast]
  have habs : -(a : ℝ) < (a : ℝ) * (q : ℝ) - (y : ℝ) ∧
      (a : ℝ) * (q : ℝ) - (y : ℝ) < (a : ℝ) := by
    constructor <;> nlinarith
  exact abs_lt.mpr habs

private theorem coeff_affine_pow
    {a b : ℝ} (ha : a ≠ 0) (n j : ℕ) :
    ((Polynomial.C b + Polynomial.C a * Polynomial.X) ^ n).coeff j =
      (n.choose j : ℝ) * a ^ j * b ^ (n - j) := by
  have hfactor :
      Polynomial.C b + Polynomial.C a * Polynomial.X =
        Polynomial.C a * (Polynomial.X + Polynomial.C (b / a)) := by
    rw [mul_add, ← Polynomial.C_mul]
    field_simp [ha]
    ring
  rw [hfactor, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  by_cases hj : j ≤ n
  · have hpow : a ^ n = a ^ j * a ^ (n - j) := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    rw [hpow, div_pow]
    field_simp [ha]
  · have hlt : n < j := Nat.lt_of_not_ge hj
    simp [Nat.choose_eq_zero_of_lt hlt]

private theorem coeff_comp_affine
    (p : Polynomial ℝ) (d j : ℕ) (hp : p.natDegree ≤ d)
    {a b : ℝ} (ha : a ≠ 0) :
    (p.comp (Polynomial.C b + Polynomial.C a * Polynomial.X)).coeff j =
      ∑ i ∈ Finset.Icc j d,
        p.coeff i * (i.choose j : ℝ) * a ^ j * b ^ (i - j) := by
  have hsum :
      p.comp (Polynomial.C b + Polynomial.C a * Polynomial.X) =
        ∑ i ∈ Finset.range (d + 1),
          Polynomial.C (p.coeff i) *
            (Polynomial.C b + Polynomial.C a * Polynomial.X) ^ i := by
    rw [Polynomial.comp, Polynomial.eval₂_eq_sum_range'
      (f := Polynomial.C) (Nat.lt_succ_of_le hp)]
  have hrange : Finset.range (d + 1) = Finset.Icc 0 d := by
    ext i
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hsum, Polynomial.finsetSum_coeff, hrange]
  calc
    (∑ i ∈ Finset.Icc 0 d,
        (Polynomial.C (p.coeff i) *
          (Polynomial.C b + Polynomial.C a * Polynomial.X) ^ i).coeff j) =
      ∑ i ∈ Finset.Icc 0 d,
        p.coeff i * (i.choose j : ℝ) * a ^ j * b ^ (i - j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Polynomial.coeff_C_mul, coeff_affine_pow ha]
          ring
    _ = ∑ i ∈ Finset.Icc j d,
        p.coeff i * (i.choose j : ℝ) * a ^ j * b ^ (i - j) := by
          symm
          apply Finset.sum_subset
          · intro i hi
            simp only [Finset.mem_Icc] at hi ⊢
            exact ⟨Nat.zero_le _, hi.2⟩
          · intro i hi hni
            have hij : i < j := by
              simp only [Finset.mem_Icc] at hi hni
              omega
            simp [Nat.choose_eq_zero_of_lt hij]

private theorem affineInverseCoeff
    (p : Polynomial ℝ) (d j : ℕ) (hp : p.natDegree ≤ d)
    (a c : ℝ) (ha : a ≠ 0) :
    a ^ d * p.coeff j =
      ∑ i ∈ Finset.Icc j d,
        (i.choose j : ℝ) * a ^ (d - i) * (-c) ^ (i - j) *
          (p.comp (Polynomial.C c + Polynomial.C a * Polynomial.X)).coeff i := by
  let affine : Polynomial ℝ := Polynomial.C c + Polynomial.C a * Polynomial.X
  let inverse : Polynomial ℝ :=
    Polynomial.C (-c / a) + Polynomial.C (a⁻¹) * Polynomial.X
  have haInv : a⁻¹ ≠ 0 := inv_ne_zero ha
  have hdegAffine : affine.natDegree = 1 := by
    dsimp [affine]
    rw [add_comm, Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul_X]
    exact ha
  have hqdeg :
      (p.comp affine).natDegree ≤ d := by
    calc
      (p.comp affine).natDegree ≤ p.natDegree * affine.natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ d * 1 := Nat.mul_le_mul hp (le_of_eq hdegAffine)
      _ = d := by simp
  have hlin : affine.comp inverse = Polynomial.X := by
    dsimp [affine, inverse]
    simp only [Polynomial.comp, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    rw [mul_add, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul,
      ← add_assoc, ← Polynomial.C_add]
    have hc : c + a * (-c / a) = 0 := by field_simp [ha]; ring
    have ha' : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
    simp [hc, ha']
  have hcomp :
      (p.comp affine).comp inverse = p := by
    calc
      (p.comp affine).comp inverse = p.comp (affine.comp inverse) :=
        Polynomial.comp_assoc p affine inverse
      _ = p.comp Polynomial.X := by rw [hlin]
      _ = p := Polynomial.comp_X
  have hcoeff :
      p.coeff j =
        ∑ i ∈ Finset.Icc j d,
          (p.comp affine).coeff i * (i.choose j : ℝ) *
            (a⁻¹) ^ j * (-c / a) ^ (i - j) := by
    calc
      p.coeff j = ((p.comp affine).comp inverse).coeff j := by rw [hcomp]
      _ = ∑ i ∈ Finset.Icc j d,
          (p.comp affine).coeff i * (i.choose j : ℝ) *
            (a⁻¹) ^ j * (-c / a) ^ (i - j) := by
              simpa [inverse] using
                (coeff_comp_affine (p.comp affine) d j hqdeg
                  (a := a⁻¹) (b := -c / a) haInv)
  rw [hcoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : j ≤ i := (Finset.mem_Icc.mp hi).1
  have hid : i ≤ d := (Finset.mem_Icc.mp hi).2
  have hpow : a ^ d = a ^ (d - i) * a ^ j * a ^ (i - j) := by
    calc
      a ^ d = a ^ ((d - i) + i) := by rw [Nat.sub_add_cancel hid]
      _ = a ^ (d - i) * a ^ i := by rw [pow_add]
      _ = a ^ (d - i) * a ^ (j + (i - j)) := by
        rw [Nat.add_sub_of_le hij]
      _ = a ^ (d - i) * a ^ j * a ^ (i - j) := by
        rw [pow_add]
        ring
  have hterm :
      a ^ d * (a⁻¹) ^ j * (-c / a) ^ (i - j) =
        a ^ (d - i) * (-c) ^ (i - j) := by
    rw [hpow, inv_pow, div_pow]
    field_simp [ha]
  calc
    a ^ d * ((p.comp affine).coeff i * (i.choose j : ℝ) *
        (a⁻¹) ^ j * (-c / a) ^ (i - j)) =
      ((p.comp affine).coeff i * (i.choose j : ℝ)) *
        (a ^ d * (a⁻¹) ^ j * (-c / a) ^ (i - j)) := by ring
    _ = ((p.comp affine).coeff i * (i.choose j : ℝ)) *
        (a ^ (d - i) * (-c) ^ (i - j)) := by rw [hterm]
    _ = (i.choose j : ℝ) * a ^ (d - i) * (-c) ^ (i - j) *
        (p.comp affine).coeff i := by ring

private theorem affineInverseDistanceBound
    (p : Polynomial ℝ) (d j : ℕ) (hp : p.natDegree ≤ d)
    (a : ℕ) (ha : 1 ≤ a) (c r : ℤ) (H B : ℝ)
    (hH : 0 < H) (hB : 0 ≤ B) (haH : (a : ℝ) < H / 2)
    (hc : |(c : ℝ)| < (a : ℝ))
    (hj : 1 ≤ j) (hjd : j ≤ d)
    (hlocal : ∀ i ∈ Finset.Icc j d,
      (H / (a : ℝ)) ^ i * realDistanceToIntegers
        ((r : ℝ) * (p.comp (Polynomial.C (c : ℝ) +
          Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) ≤ B) :
    H ^ j * realDistanceToIntegers
      ((r : ℝ) * (a : ℝ) ^ d * p.coeff j) ≤
        (2 : ℝ) ^ (d + 1) * B * (a : ℝ) ^ d := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  let w : ℕ → ℤ := fun i =>
    (i.choose j : ℤ) * (a : ℤ) ^ (d - i) * (-c) ^ (i - j)
  have hsum :
      (r : ℝ) * (a : ℝ) ^ d * p.coeff j =
        ∑ i ∈ Finset.Icc j d,
          (w i : ℝ) * ((r : ℝ) *
            (p.comp (Polynomial.C (c : ℝ) +
              Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) := by
    calc
      (r : ℝ) * (a : ℝ) ^ d * p.coeff j =
          (r : ℝ) * ((a : ℝ) ^ d * p.coeff j) := by ring
      _ = (r : ℝ) * ∑ i ∈ Finset.Icc j d,
          (i.choose j : ℝ) * (a : ℝ) ^ (d - i) *
            (-(c : ℝ)) ^ (i - j) *
              (p.comp (Polynomial.C (c : ℝ) +
                Polynomial.C (a : ℝ) * Polynomial.X)).coeff i := by
          rw [affineInverseCoeff p d j hp (a : ℝ) (c : ℝ) (ne_of_gt haR)]
      _ = ∑ i ∈ Finset.Icc j d,
          (r : ℝ) * ((i.choose j : ℝ) * (a : ℝ) ^ (d - i) *
            (-(c : ℝ)) ^ (i - j) *
              (p.comp (Polynomial.C (c : ℝ) +
                Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) := by
          rw [Finset.mul_sum]
      _ = ∑ i ∈ Finset.Icc j d,
          (w i : ℝ) * ((r : ℝ) *
            (p.comp (Polynomial.C (c : ℝ) +
              Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [w, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
            Int.cast_neg, Int.cast_ofNat]
          push_cast
          ring
  have hratio : 0 < H / (a : ℝ) := div_pos hH haR
  have hratioPow (i : ℕ) : 0 < (H / (a : ℝ)) ^ i := pow_pos hratio _
  have hlocal' (i : ℕ) (hi : i ∈ Finset.Icc j d) :
      realDistanceToIntegers
        ((r : ℝ) * (p.comp (Polynomial.C (c : ℝ) +
          Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) ≤
        B * ((a : ℝ) / H) ^ i := by
    have hmul := hlocal i hi
    have hmul' :
        realDistanceToIntegers
            ((r : ℝ) * (p.comp (Polynomial.C (c : ℝ) +
              Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) *
          (H / (a : ℝ)) ^ i ≤ B := by
      calc
        _ = (H / (a : ℝ)) ^ i * realDistanceToIntegers
            ((r : ℝ) * (p.comp (Polynomial.C (c : ℝ) +
              Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) := by ring
        _ ≤ B := hmul
    have hdiv := (le_div_iff₀ (hratioPow i)).2 hmul'
    have hratioInv : (H / (a : ℝ))⁻¹ = (a : ℝ) / H := by
      field_simp [ne_of_gt hH, ne_of_gt haR]
    calc
      realDistanceToIntegers
          ((r : ℝ) * (p.comp (Polynomial.C (c : ℝ) +
            Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) ≤
        B / (H / (a : ℝ)) ^ i := hdiv
      _ = B * ((a : ℝ) / H) ^ i := by
        rw [div_eq_mul_inv, ← inv_pow, hratioInv]
  have hdist := realDistanceToIntegers_intWeightedSum_le
    (Finset.Icc j d) w
    (fun i => (r : ℝ) * (p.comp (Polynomial.C (c : ℝ) +
      Polynomial.C (a : ℝ) * Polynomial.X)).coeff i)
    (fun i => B * ((a : ℝ) / H) ^ i) hlocal'
  rw [← hsum] at hdist
  have hterm (i : ℕ) (hi : i ∈ Finset.Icc j d) :
      H ^ j * |(w i : ℝ)| * (B * ((a : ℝ) / H) ^ i) ≤
        B * (a : ℝ) ^ d * (i.choose j : ℝ) := by
    have hij : j ≤ i := (Finset.mem_Icc.mp hi).1
    have hid : i ≤ d := (Finset.mem_Icc.mp hi).2
    have hcH : |(c : ℝ)| / H ≤ 1 := by
      apply (div_le_one hH).2
      exact le_trans (le_of_lt hc) (le_trans (le_of_lt haH) (by nlinarith))
    have hpow : H ^ j * (a : ℝ) ^ (d - i) *
        |(c : ℝ)| ^ (i - j) * ((a : ℝ) / H) ^ i =
        (a : ℝ) ^ d * ((|(c : ℝ)| / H) ^ (i - j)) := by
      have hiEq : i = j + (i - j) := (Nat.add_sub_of_le hij).symm
      have hsub : d - (j + (i - j)) = d - i := by omega
      rw [hiEq, Nat.add_sub_cancel_left, hsub, pow_add, div_pow]
      have hcancel : H ^ j * ((a : ℝ) ^ j / H ^ j) = (a : ℝ) ^ j := by
        field_simp [ne_of_gt hH]
      have hratioPower : |(c : ℝ)| ^ (i - j) *
          ((a : ℝ) / H) ^ (i - j) =
            (a : ℝ) ^ (i - j) * ((|(c : ℝ)| / H) ^ (i - j)) := by
        rw [← mul_pow]
        have hratioEq : |(c : ℝ)| * ((a : ℝ) / H) =
            (a : ℝ) * (|(c : ℝ)| / H) := by
          field_simp [ne_of_gt hH]
        rw [hratioEq, mul_pow]
      have hpowA : (a : ℝ) ^ (d - i) * (a : ℝ) ^ j *
          (a : ℝ) ^ (i - j) = (a : ℝ) ^ d := by
        rw [← pow_add, ← pow_add]
        congr 1 <;> omega
      calc
        H ^ j * (a : ℝ) ^ (d - i) * |(c : ℝ)| ^ (i - j) *
            ((a : ℝ) ^ j / H ^ j * ((a : ℝ) / H) ^ (i - j)) =
          (H ^ j * ((a : ℝ) ^ j / H ^ j)) *
            ((a : ℝ) ^ (d - i) *
              (|(c : ℝ)| ^ (i - j) * ((a : ℝ) / H) ^ (i - j))) := by ring
        _ = (a : ℝ) ^ j * ((a : ℝ) ^ (d - i) *
              (|(c : ℝ)| ^ (i - j) * ((a : ℝ) / H) ^ (i - j))) := by
                rw [hcancel]
        _ = (a : ℝ) ^ d * ((|(c : ℝ)| / H) ^ (i - j)) := by
              rw [hratioPower]
              calc
                (a : ℝ) ^ j * ((a : ℝ) ^ (d - i) *
                    ((a : ℝ) ^ (i - j) *
                      ((|(c : ℝ)| / H) ^ (i - j)))) =
                  ((a : ℝ) ^ (d - i) * (a : ℝ) ^ j *
                    (a : ℝ) ^ (i - j)) *
                    ((|(c : ℝ)| / H) ^ (i - j)) := by ring
                _ = (a : ℝ) ^ d * ((|(c : ℝ)| / H) ^ (i - j)) := by
                  rw [hpowA]
    have hweight : |(w i : ℝ)| =
        (i.choose j : ℝ) * (a : ℝ) ^ (d - i) * |(c : ℝ)| ^ (i - j) := by
      simp [w, abs_mul, abs_pow]
    rw [hweight]
    have hchoose : 0 ≤ (i.choose j : ℝ) := by positivity
    have hpowle : ((|(c : ℝ)| / H) ^ (i - j)) ≤ 1 :=
      pow_le_one₀ (div_nonneg (abs_nonneg _) (le_of_lt hH)) hcH
    have hEq :
        H ^ j * ((i.choose j : ℝ) * (a : ℝ) ^ (d - i) *
          |(c : ℝ)| ^ (i - j)) * (B * ((a : ℝ) / H) ^ i) =
        B * (i.choose j : ℝ) * (a : ℝ) ^ d *
          ((|(c : ℝ)| / H) ^ (i - j)) := by
      calc
        H ^ j * ((i.choose j : ℝ) * (a : ℝ) ^ (d - i) *
            |(c : ℝ)| ^ (i - j)) * (B * ((a : ℝ) / H) ^ i) =
          B * (i.choose j : ℝ) *
            (H ^ j * (a : ℝ) ^ (d - i) * |(c : ℝ)| ^ (i - j) *
              ((a : ℝ) / H) ^ i) := by ring
        _ = B * (i.choose j : ℝ) *
            ((a : ℝ) ^ d * ((|(c : ℝ)| / H) ^ (i - j))) := by rw [hpow]
        _ = B * (i.choose j : ℝ) * (a : ℝ) ^ d *
            ((|(c : ℝ)| / H) ^ (i - j)) := by ring
    rw [hEq]
    calc
      B * (i.choose j : ℝ) * (a : ℝ) ^ d *
          ((|(c : ℝ)| / H) ^ (i - j)) ≤
        B * (i.choose j : ℝ) * (a : ℝ) ^ d :=
          by
            have hcoef : 0 ≤ B * (i.choose j : ℝ) * (a : ℝ) ^ d := by positivity
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowle hcoef
      _ = B * (a : ℝ) ^ d * (i.choose j : ℝ) := by ring
  have hsumBound :
      H ^ j * (∑ i ∈ Finset.Icc j d,
          |(w i : ℝ)| * (B * ((a : ℝ) / H) ^ i)) ≤
        B * (a : ℝ) ^ d * ((d + 1 : ℕ).choose (j + 1) : ℝ) := by
    rw [Finset.mul_sum]
    calc
      ∑ i ∈ Finset.Icc j d,
          H ^ j * (|(w i : ℝ)| * (B * ((a : ℝ) / H) ^ i)) ≤
        ∑ i ∈ Finset.Icc j d,
          B * (a : ℝ) ^ d * (i.choose j : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            simpa [mul_assoc] using hterm i hi
      _ = B * (a : ℝ) ^ d *
          ((d + 1 : ℕ).choose (j + 1) : ℝ) := by
            rw [← Finset.mul_sum]
            norm_cast
            rw [Nat.sum_Icc_choose]
  have hchooseBound : ((d + 1 : ℕ).choose (j + 1) : ℝ) ≤
      (2 : ℝ) ^ (d + 1) := by
    exact_mod_cast Nat.choose_le_two_pow (d + 1) (j + 1)
  have hfactor : 0 ≤ H ^ j := by positivity
  calc
    H ^ j * realDistanceToIntegers
        ((r : ℝ) * (a : ℝ) ^ d * p.coeff j) ≤
      H ^ j * (∑ i ∈ Finset.Icc j d,
        |(w i : ℝ)| * (B * ((a : ℝ) / H) ^ i)) := by
          exact mul_le_mul_of_nonneg_left hdist hfactor
    _ ≤ B * (a : ℝ) ^ d * ((d + 1 : ℕ).choose (j + 1) : ℝ) := hsumBound
    _ ≤ (2 : ℝ) ^ (d + 1) * B * (a : ℝ) ^ d := by
      calc
        B * (a : ℝ) ^ d * ((d + 1 : ℕ).choose (j + 1) : ℝ) ≤
            B * (a : ℝ) ^ d * (2 : ℝ) ^ (d + 1) :=
          mul_le_mul_of_nonneg_left hchooseBound
            (by positivity : 0 ≤ B * (a : ℝ) ^ d)
        _ = (2 : ℝ) ^ (d + 1) * B * (a : ℝ) ^ d := by ring

/-- The polynomial in centered monomial coordinates for `P(Y+t)`. -/
noncomputable def phaseCenteredAt (P : Polynomial ℝ) (Y : ℤ) : Polynomial ℝ :=
  P.comp (Polynomial.C (Y : ℝ) + Polynomial.X)

/-- The polynomial phase `P(a(q+t))` in monomial coordinates. -/
noncomputable def phaseDilatedAt (P : Polynomial ℝ) (a : ℕ) (q : ℤ) :
    Polynomial ℝ :=
  P.comp (Polynomial.C ((a : ℝ) * (q : ℝ)) +
    Polynomial.C (a : ℝ) * Polynomial.X)

private theorem centered_dilation_comp_eq
    (P : Polynomial ℝ) (Y : ℤ) (a : ℕ) (c q : ℤ)
    (hc : (Y : ℝ) + (c : ℝ) = (a : ℝ) * (q : ℝ)) :
    (phaseCenteredAt P Y).comp
        (Polynomial.C (c : ℝ) + Polynomial.C (a : ℝ) * Polynomial.X) =
      phaseDilatedAt P a q := by
  have hlinear :
      (Polynomial.C (Y : ℝ) + Polynomial.X).comp
          (Polynomial.C (c : ℝ) + Polynomial.C (a : ℝ) * Polynomial.X) =
        Polynomial.C ((a : ℝ) * (q : ℝ)) +
          Polynomial.C (a : ℝ) * Polynomial.X := by
    simp only [Polynomial.comp, Polynomial.eval₂_add,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    calc
      Polynomial.C (Y : ℝ) +
          (Polynomial.C (c : ℝ) + Polynomial.C (a : ℝ) * Polynomial.X) =
        (Polynomial.C (Y : ℝ) + Polynomial.C (c : ℝ)) +
          Polynomial.C (a : ℝ) * Polynomial.X := by rw [add_assoc]
      _ = Polynomial.C ((Y : ℝ) + (c : ℝ)) +
          Polynomial.C (a : ℝ) * Polynomial.X := by rw [← Polynomial.C_add]
      _ = Polynomial.C ((a : ℝ) * (q : ℝ)) +
          Polynomial.C (a : ℝ) * Polynomial.X := by rw [hc]
  change (P.comp (Polynomial.C (Y : ℝ) + Polynomial.X)).comp
      (Polynomial.C (c : ℝ) + Polynomial.C (a : ℝ) * Polynomial.X) =
    P.comp (Polynomial.C ((a : ℝ) * (q : ℝ)) +
      Polynomial.C (a : ℝ) * Polynomial.X)
  rw [Polynomial.comp_assoc, hlinear]

private theorem dilationCenter_integer_identity (X : ℝ) (a : ℕ) :
    Int.floor X +
        ((a : ℤ) * Int.floor (X / (a : ℝ)) - Int.floor X) =
      (a : ℤ) * Int.floor (X / (a : ℝ)) := by
  ring

private theorem dilation_smallA_conclusion
    {d : ℕ} (hd : 1 ≤ d)
    {A H X B η : ℝ}
    (hA : 1 / 2 ≤ A) (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hA0 : A < inverseBoundAZero d B η⁻¹)
    (hHlarge : inverseBoundV d B η⁻¹ * A < H)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (S : Finset ℕ) (hSnonempty : S.Nonempty)
    (hSbounds : ∀ a ∈ S, A < (a : ℝ) ∧ (a : ℝ) ≤ 2 * A)
    (hdata : ∀ a ∈ S, ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ B ∧
      ∀ j, 1 ≤ j → j ≤ d →
        (H / (a : ℝ)) ^ j * realDistanceToIntegers
          ((r : ℝ) * (phaseDilatedAt P a
            (Int.floor (X / (a : ℝ)))).coeff j) ≤ B) :
    ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ inverseBoundV d B η⁻¹ ∧
      ∀ j, 1 ≤ j → j ≤ d →
        H ^ j * realDistanceToIntegers
          ((r : ℝ) * (phaseCenteredAt P (Int.floor X)).coeff j) ≤
            inverseBoundV d B η⁻¹ := by
  classical
  obtain ⟨a, haS⟩ := hSnonempty
  obtain ⟨ra, hra, hraB, hlocal⟩ := hdata a haS
  have haPosNat : 0 < a := by
    by_contra hn
    have ha0 : a = 0 := by omega
    subst a
    have hA_lt := (hSbounds 0 haS).1
    norm_num at hA_lt
    linarith [hA]
  have haA : 1 ≤ a := Nat.succ_le_of_lt haPosNat
  have haRpos : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have haTop : (a : ℝ) ≤ 2 * A := (hSbounds a haS).2
  have hy : 2 ≤ η⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hη).2
    nlinarith
  have hA0four := inverseBoundAZero_ge_four d B η⁻¹ hB hy
  have hVfour := inverseBoundV_ge_four d hd B η⁻¹ hB hy
  have hVApos : 0 ≤ inverseBoundV d B η⁻¹ * A :=
    mul_nonneg (by linarith [hVfour]) (by linarith [hA])
  have hfourA : 4 * A < H := by
    have hfourle : 4 * A ≤ inverseBoundV d B η⁻¹ * A :=
      mul_le_mul_of_nonneg_right hVfour (by linarith [hA])
    linarith
  have haH : (a : ℝ) < H / 2 := by linarith
  let c : ℤ := (a : ℤ) * Int.floor (X / (a : ℝ)) - Int.floor X
  have hc : |(c : ℝ)| < (a : ℝ) := by
    dsimp [c]
    exact dilationCenter_offset_abs_lt X haA
  have hcenter : (Int.floor X : ℝ) + (c : ℝ) =
      (a : ℝ) * (Int.floor (X / (a : ℝ)) : ℝ) := by
    have hi := dilationCenter_integer_identity X a
    dsimp [c]
    exact_mod_cast hi
  have hcomp := centered_dilation_comp_eq P (Int.floor X) a c
    (Int.floor (X / (a : ℝ))) hcenter
  have hlocal' (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d) :
      (H / (a : ℝ)) ^ j * realDistanceToIntegers
        ((ra : ℝ) * ((phaseCenteredAt P (Int.floor X)).comp
          (Polynomial.C (c : ℝ) + Polynomial.C (a : ℝ) * Polynomial.X)).coeff j) ≤ B := by
    have h := hlocal j hj hjd
    rw [hcomp]
    exact h
  have hcenterDegree : (phaseCenteredAt P (Int.floor X)).natDegree ≤ d := by
    have hlinearDegree :
        (Polynomial.C (Int.floor X : ℝ) + Polynomial.X).natDegree ≤ 1 := by
      rw [add_comm, Polynomial.natDegree_X_add_C]
    calc
      (phaseCenteredAt P (Int.floor X)).natDegree ≤
          P.natDegree * (Polynomial.C (Int.floor X : ℝ) +
            Polynomial.X).natDegree := Polynomial.natDegree_comp_le
      _ ≤ d * 1 := Nat.mul_le_mul hP hlinearDegree
      _ = d := by simp
  have hbound (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d) :
      H ^ j * realDistanceToIntegers
        ((ra : ℝ) * (a : ℝ) ^ d * (phaseCenteredAt P (Int.floor X)).coeff j) ≤
          (2 : ℝ) ^ (d + 1) * B * (a : ℝ) ^ d :=
    affineInverseDistanceBound
    (phaseCenteredAt P (Int.floor X)) d j hcenterDegree a haA c ra H B
    (by linarith [hH]) (by linarith [hB]) haH hc hj hjd
    (by
      intro i hi
      apply hlocal' i
      · have hji : j ≤ i := (Finset.mem_Icc.mp hi).1
        omega
      · exact (Finset.mem_Icc.mp hi).2)
  have hA2A0 : 2 * A < 2 * inverseBoundAZero d B η⁻¹ := by linarith [hA0]
  have haA0 : (a : ℝ) < 2 * inverseBoundAZero d B η⁻¹ := lt_of_le_of_lt haTop hA2A0
  have haPow : (a : ℝ) ^ d ≤
      (2 * inverseBoundAZero d B η⁻¹) ^ d := by
    exact pow_le_pow_left₀ (by positivity) (le_of_lt haA0) d
  have hErrBudget :
      (2 : ℝ) ^ (d + 1) * B * (a : ℝ) ^ d ≤ inverseBoundV d B η⁻¹ := by
    rw [inverseBoundV_eval]
    have hbaseNonneg : 0 ≤ (2 : ℝ) ^ (d + 1) * B := by positivity
    have hmain :
        (2 : ℝ) ^ (d + 1) * B * (a : ℝ) ^ d ≤
          (2 : ℝ) ^ (d + 1) * B *
            (2 * inverseBoundAZero d B η⁻¹) ^ d :=
      mul_le_mul_of_nonneg_left haPow hbaseNonneg
    have hVterms :
        (2 : ℝ) ^ (d + 1) * B *
            (2 * inverseBoundAZero d B η⁻¹) ^ d ≤
          4 + 1024 * inverseBoundDValue d * B * η⁻¹ *
              inverseBoundU d d B η⁻¹ ^ 2 +
            (2 : ℝ) ^ (d + 1) * B *
              (2 * inverseBoundAZero d B η⁻¹) ^ d +
            inverseBoundU d d B η⁻¹ := by
      have h1 : 0 ≤ 1024 * inverseBoundDValue d * B * η⁻¹ *
          inverseBoundU d d B η⁻¹ ^ 2 := by positivity
      have h2 : 0 ≤ inverseBoundU d d B η⁻¹ := by
        have hU := inverseBoundU_ge_one d hd B η⁻¹ hB hy d
        exact le_trans (by norm_num) hU
      linarith
    exact hmain.trans hVterms
  let rOut : ℤ := ra * (a : ℤ) ^ d
  refine ⟨rOut, ?_, ?_, ?_⟩
  · dsimp [rOut]
    have haZ : 0 < (a : ℤ) := by
      exact_mod_cast (show 0 < a by omega)
    exact mul_pos (by omega) (pow_pos haZ d)
  · dsimp [rOut]
    have hraCast : (ra : ℝ) ≤ B := hraB
    have hpowNonneg : 0 ≤ (a : ℝ) ^ d := by positivity
    have hcoarse :
        (ra : ℝ) * (a : ℝ) ^ d ≤
          (2 : ℝ) ^ (d + 1) * B * (a : ℝ) ^ d := by
      have htwo : 1 ≤ (2 : ℝ) ^ (d + 1) := one_le_pow₀ (by norm_num)
      calc
        (ra : ℝ) * (a : ℝ) ^ d ≤ B * (a : ℝ) ^ d :=
          mul_le_mul_of_nonneg_right hraCast hpowNonneg
        _ = 1 * (B * (a : ℝ) ^ d) := by ring
        _ ≤ (2 : ℝ) ^ (d + 1) * (B * (a : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_right htwo (by positivity)
        _ = (2 : ℝ) ^ (d + 1) * B * (a : ℝ) ^ d := by ring
    have hcast : ((ra * (a : ℤ) ^ d : ℤ) : ℝ) =
        (ra : ℝ) * (a : ℝ) ^ d := by norm_num
    rw [hcast]
    exact hcoarse.trans hErrBudget
  · intro j hj hjd
    have hest := hbound j hj hjd
    have hcast : ((rOut : ℝ) * (phaseCenteredAt P (Int.floor X)).coeff j) =
        (ra : ℝ) * (a : ℝ) ^ d *
          (phaseCenteredAt P (Int.floor X)).coeff j := by
      simp [rOut]
    rw [hcast]
    exact hest.trans hErrBudget

private noncomputable def phasePolynomialTruncation
    (p : Polynomial ℝ) (l : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (l + 1), Polynomial.C (p.coeff i) * Polynomial.X ^ i

private noncomputable def phasePolynomialTail
    (p : Polynomial ℝ) (l d : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.Ico (l + 1) (d + 1),
    Polynomial.C (p.coeff i) * Polynomial.X ^ i

private theorem phasePolynomial_truncation_add_tail
    (p : Polynomial ℝ) {l d : ℕ} (hp : p.natDegree ≤ d)
    (hl : l ≤ d) :
    phasePolynomialTruncation p l + phasePolynomialTail p l d = p := by
  have hsum : p = ∑ i ∈ Finset.range (d + 1),
      Polynomial.C (p.coeff i) * Polynomial.X ^ i := by
    calc
      p = ∑ i ∈ Finset.range (p.natDegree + 1),
          Polynomial.C (p.coeff i) * Polynomial.X ^ i :=
        p.as_sum_range_C_mul_X_pow
      _ = ∑ i ∈ Finset.range (d + 1),
          Polynomial.C (p.coeff i) * Polynomial.X ^ i := by
            apply Finset.sum_subset
            · intro i hi
              exact Finset.mem_range.mpr
                (Nat.lt_succ_of_le (Nat.le_trans
                  (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hp))
            · intro i hi hni
              have hdeg : p.natDegree < i := by
                simp only [Finset.mem_range] at hi hni
                omega
              simp [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg]
  dsimp [phasePolynomialTruncation, phasePolynomialTail]
  calc
    (∑ i ∈ Finset.range (l + 1),
        Polynomial.C (p.coeff i) * Polynomial.X ^ i) +
      ∑ i ∈ Finset.Ico (l + 1) (d + 1),
        Polynomial.C (p.coeff i) * Polynomial.X ^ i =
      ∑ i ∈ Finset.range (d + 1),
        Polynomial.C (p.coeff i) * Polynomial.X ^ i :=
      Finset.sum_range_add_sum_Ico
        (fun i => Polynomial.C (p.coeff i) * Polynomial.X ^ i)
        (Nat.succ_le_succ hl)
    _ = p := hsum.symm

private theorem phasePolynomialTruncation_natDegree_le
    (p : Polynomial ℝ) (l : ℕ) :
    (phasePolynomialTruncation p l).natDegree ≤ l := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have hil : i ≤ l := by
    simp only [Finset.mem_range] at hi
    omega
  calc
    (Polynomial.C (p.coeff i) * Polynomial.X ^ i).natDegree ≤
        (Polynomial.C (p.coeff i)).natDegree +
          (Polynomial.X ^ i).natDegree := Polynomial.natDegree_mul_le
    _ = i := by simp
    _ ≤ l := hil

private theorem phasePolynomialTail_comp_coeff
    (p : Polynomial ℝ) (l d i : ℕ) (a c : ℝ) (ha : a ≠ 0) :
    ((phasePolynomialTail p l d).comp
        (Polynomial.C c + Polynomial.C a * Polynomial.X)).coeff i =
      ∑ j ∈ Finset.Ico (l + 1) (d + 1),
        p.coeff j * (j.choose i : ℝ) * a ^ i * c ^ (j - i) := by
  let affine : Polynomial ℝ := Polynomial.C c + Polynomial.C a * Polynomial.X
  have hcomp :
      (phasePolynomialTail p l d).comp affine =
        ∑ j ∈ Finset.Ico (l + 1) (d + 1),
          Polynomial.C (p.coeff j) * affine ^ j := by
    simp [phasePolynomialTail, affine, Polynomial.comp,
      Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
  rw [hcomp, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.coeff_C_mul, coeff_affine_pow ha]
  ring

private theorem polynomial_comp_C_mul
    (s : ℝ) (p q : Polynomial ℝ) :
    (Polynomial.C s * p).comp q = Polynomial.C s * p.comp q := by
  simp only [Polynomial.comp, Polynomial.eval₂_mul, Polynomial.eval₂_C]

private theorem polynomial_comp_sub
    (p q r : Polynomial ℝ) :
    (p - q).comp r = p.comp r - q.comp r := by
  simp only [Polynomial.comp, Polynomial.eval₂_sub]

private theorem phasePolynomialTruncation_comp_coeff
    (p : Polynomial ℝ) (l d i : ℕ) (hp : p.natDegree ≤ d)
    (hl : l ≤ d) (s : ℤ) (a c : ℝ) (ha : a ≠ 0) :
    ((Polynomial.C (s : ℝ) * phasePolynomialTruncation p l).comp
      (Polynomial.C c + Polynomial.C a * Polynomial.X)).coeff i =
      (s : ℝ) *
          (p.comp (Polynomial.C c + Polynomial.C a * Polynomial.X)).coeff i -
        ∑ j ∈ Finset.Ico (l + 1) (d + 1),
          (s : ℝ) * p.coeff j * (j.choose i : ℝ) * a ^ i * c ^ (j - i) := by
  have hsplit := phasePolynomial_truncation_add_tail p hp hl
  have htrunc : phasePolynomialTruncation p l =
      p - phasePolynomialTail p l d := by
    calc
      phasePolynomialTruncation p l =
          (phasePolynomialTruncation p l +
            phasePolynomialTail p l d) - phasePolynomialTail p l d := by abel
      _ = p - phasePolynomialTail p l d := by rw [hsplit]
  have hpoly :
      Polynomial.C (s : ℝ) * phasePolynomialTruncation p l =
        Polynomial.C (s : ℝ) * p -
          Polynomial.C (s : ℝ) * phasePolynomialTail p l d := by
    rw [htrunc, mul_sub]
  have hcomp :
      (Polynomial.C (s : ℝ) * phasePolynomialTruncation p l).comp
          (Polynomial.C c + Polynomial.C a * Polynomial.X) =
        Polynomial.C (s : ℝ) *
            (p.comp (Polynomial.C c + Polynomial.C a * Polynomial.X)) -
          Polynomial.C (s : ℝ) *
            ((phasePolynomialTail p l d).comp
              (Polynomial.C c + Polynomial.C a * Polynomial.X)) := by
    rw [hpoly]
    rw [polynomial_comp_sub, polynomial_comp_C_mul, polynomial_comp_C_mul]
  rw [hcomp, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, phasePolynomialTail_comp_coeff p l d i a c ha]
  rw [Finset.mul_sum]
  apply congrArg (fun z : ℝ => (s : ℝ) *
    (p.comp (Polynomial.C c + Polynomial.C a * Polynomial.X)).coeff i - z)
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem phasePolynomialTruncation_comp_error_bound
    (p : Polynomial ℝ) (d l i : ℕ) (hp : p.natDegree ≤ d)
    (hl : l ≤ d) (hi1 : 1 ≤ i) (hil : i ≤ l)
    (a : ℕ) (ha : 1 ≤ a) (c r₀ s : ℤ) (k : ℕ)
    (H B U : ℝ) (hH : 0 < H) (hB : 0 ≤ B) (hU : 1 ≤ U)
    (hcH : |(c : ℝ)| / H ≤ 1)
    (hs : s = r₀ * (k : ℤ)) (hkU : (k : ℝ) ≤ U) (hBU : B ≤ U)
    (hlocal : ∀ m, 1 ≤ m → m ≤ d →
      (H / (a : ℝ)) ^ m * realDistanceToIntegers
        ((r₀ : ℝ) *
          (p.comp (Polynomial.C (c : ℝ) +
            Polynomial.C (a : ℝ) * Polynomial.X)).coeff m) ≤ B)
    (hhigh : ∀ j, l < j → j ≤ d →
      H ^ j * realDistanceToIntegers ((s : ℝ) * p.coeff j) ≤ U) :
    (H / (a : ℝ)) ^ i * realDistanceToIntegers
      (((Polynomial.C (s : ℝ) * phasePolynomialTruncation p l).comp
        (Polynomial.C (c : ℝ) + Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) ≤
      ((inverseBoundDValue d : ℕ) : ℝ) * U ^ 2 := by
  classical
  let J : Finset ℕ := Finset.Ico (l + 1) (d + 1)
  let indices : Finset (Option ℕ) := insert none (J.image some)
  let weight : Option ℕ → ℤ := fun z =>
    match z with
    | none => (k : ℤ)
    | some j => -((j.choose i : ℤ) * (a : ℤ) ^ i * c ^ (j - i))
  let value : Option ℕ → ℝ := fun z =>
    match z with
    | none => (r₀ : ℝ) *
        (p.comp (Polynomial.C (c : ℝ) +
          Polynomial.C (a : ℝ) * Polynomial.X)).coeff i
    | some j => (s : ℝ) * p.coeff j
  let error : Option ℕ → ℝ := fun z =>
    match z with
    | none => B * ((a : ℝ) / H) ^ i
    | some j => U / H ^ j
  have haR : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hratio : 0 < H / (a : ℝ) := div_pos hH haR
  have hratioPow (m : ℕ) : 0 < (H / (a : ℝ)) ^ m := pow_pos hratio _
  have hlocal' : realDistanceToIntegers
      ((r₀ : ℝ) * (p.comp (Polynomial.C (c : ℝ) +
        Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) ≤ error none := by
    have hm := hlocal i hi1 (Nat.le_trans hil hl)
    have hm' : realDistanceToIntegers
        ((r₀ : ℝ) * (p.comp (Polynomial.C (c : ℝ) +
          Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) *
          (H / (a : ℝ)) ^ i ≤ B := by
      calc
        _ = (H / (a : ℝ)) ^ i * realDistanceToIntegers
            ((r₀ : ℝ) * (p.comp (Polynomial.C (c : ℝ) +
              Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) := by ring
        _ ≤ B := hm
    have hdiv := (le_div_iff₀ (hratioPow i)).2 hm'
    have hinv : (H / (a : ℝ))⁻¹ = (a : ℝ) / H := by
      field_simp [ne_of_gt hH, ne_of_gt haR]
    dsimp [error]
    calc
      realDistanceToIntegers
          ((r₀ : ℝ) * (p.comp (Polynomial.C (c : ℝ) +
            Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) ≤
        B / (H / (a : ℝ)) ^ i := hdiv
      _ = B * ((a : ℝ) / H) ^ i := by
        rw [div_eq_mul_inv, ← inv_pow, hinv]
  have hhigh' (j : ℕ) (hj : j ∈ J) :
      realDistanceToIntegers ((s : ℝ) * p.coeff j) ≤ error (some j) := by
    have hj' : l < j ∧ j ≤ d := by
      simp only [J, Finset.mem_Ico] at hj
      omega
    have hm := hhigh j hj'.1 hj'.2
    have hm' : realDistanceToIntegers ((s : ℝ) * p.coeff j) * H ^ j ≤ U := by
      calc
        _ = H ^ j * realDistanceToIntegers ((s : ℝ) * p.coeff j) := by ring
        _ ≤ U := hm
    have hpow : 0 < H ^ j := pow_pos hH _
    have hdiv := (le_div_iff₀ hpow).2 hm'
    dsimp [error]
    exact hdiv
  have herror (z : Option ℕ) (hz : z ∈ indices) :
      realDistanceToIntegers (value z) ≤ error z := by
    cases z with
    | none =>
        simpa [value] using hlocal'
    | some j =>
        have hj : j ∈ J := by
          simpa [indices, J] using hz
        simpa [value] using hhigh' j hj
  have hweighted :
      ∑ z ∈ indices, (weight z : ℝ) * value z =
        (((Polynomial.C (s : ℝ) * phasePolynomialTruncation p l).comp
          (Polynomial.C (c : ℝ) + Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) := by
    rw [phasePolynomialTruncation_comp_coeff p l d i hp hl s
      (a := (a : ℝ)) (c := (c : ℝ)) (by positivity)]
    simp only [indices, weight, value, J]
    have hnone : none ∉ (Finset.Ico (l + 1) (d + 1)).image some := by simp
    have hinj : Set.InjOn (some : ℕ → Option ℕ)
        (Finset.Ico (l + 1) (d + 1) : Set ℕ) := by
      intro j hj j' hj' hEq
      exact Option.some.inj hEq
    rw [Finset.sum_insert hnone]
    rw [Finset.sum_image hinj]
    rw [hs]
    push_cast
    have htail :
        (∑ x ∈ Finset.Ico (l + 1) (d + 1),
          -((x.choose i : ℝ) * (a : ℝ) ^ i *
            (c : ℝ) ^ (x - i)) *
              ((r₀ : ℝ) * (k : ℝ) * p.coeff x)) =
          -∑ x ∈ Finset.Ico (l + 1) (d + 1),
            (r₀ : ℝ) * (k : ℝ) * p.coeff x *
              (x.choose i : ℝ) * (a : ℝ) ^ i *
                (c : ℝ) ^ (x - i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [htail]
    ring
  have hdist := realDistanceToIntegers_intWeightedSum_le
    indices weight value error herror
  rw [hweighted] at hdist
  have hratioNonneg : 0 ≤ H / (a : ℝ) := le_of_lt hratio
  have hcoefNone :
      (H / (a : ℝ)) ^ i * |(weight none : ℝ)| * error none ≤ U ^ 2 := by
    have hkNonneg : 0 ≤ (k : ℝ) := by positivity
    have hratioInv : ((H / (a : ℝ)) ^ i) * ((a : ℝ) / H) ^ i = 1 := by
      rw [← mul_pow]
      have hbase : (H / (a : ℝ)) * ((a : ℝ) / H) = 1 := by
        field_simp [ne_of_gt hH, ne_of_gt haR]
      rw [hbase, one_pow]
    dsimp [weight, error]
    rw [Int.cast_natCast, abs_of_nonneg hkNonneg]
    calc
      (H / (a : ℝ)) ^ i * (k : ℝ) *
          (B * ((a : ℝ) / H) ^ i) =
        (k : ℝ) * B *
          (((H / (a : ℝ)) ^ i) * ((a : ℝ) / H) ^ i) := by ring
      _ = (k : ℝ) * B := by rw [hratioInv]; ring
      _ ≤ U ^ 2 := by
        have hkB : (k : ℝ) * B ≤ U * U :=
          mul_le_mul hkU hBU hB (by linarith [hU])
        nlinarith
  have hratioC : |(c : ℝ)| / H ≤ 1 := hcH
  have hcoefSome (j : ℕ) (hj : j ∈ J) :
      (H / (a : ℝ)) ^ i * |(weight (some j) : ℝ)| *
          error (some j) ≤ (2 : ℝ) ^ d * U := by
    have hj' : l < j ∧ j ≤ d := by
      simp only [J, Finset.mem_Ico] at hj
      omega
    have hij : i ≤ j := by omega
    have hchoose : (j.choose i : ℝ) ≤ (2 : ℝ) ^ d := by
      have hchoose' := Nat.choose_le_two_pow j i
      have hpow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ d := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      exact le_trans (by exact_mod_cast hchoose') hpow
    have hpowle : ((|(c : ℝ)| / H) ^ (j - i)) ≤ 1 :=
      pow_le_one₀ (div_nonneg (abs_nonneg _) (le_of_lt hH)) hratioC
    have hcancel :
        (H / (a : ℝ)) ^ i * (a : ℝ) ^ i *
          |(c : ℝ)| ^ (j - i) / H ^ j =
            (|(c : ℝ)| / H) ^ (j - i) := by
      have hjEq : j = i + (j - i) := (Nat.add_sub_of_le hij).symm
      have hbase : (H / (a : ℝ)) ^ i * (a : ℝ) ^ i = H ^ i := by
        rw [div_pow]
        field_simp [ne_of_gt haR]
      rw [hbase, hjEq, pow_add]
      have hsub : i + (j - i) - i = j - i := Nat.add_sub_cancel_left i (j - i)
      rw [hsub]
      rw [div_pow]
      field_simp [ne_of_gt hH, ne_of_gt haR]
    have hweightAbs : |(weight (some j) : ℝ)| =
        (j.choose i : ℝ) * (a : ℝ) ^ i * |(c : ℝ)| ^ (j - i) := by
      simp [weight, abs_mul, abs_pow, abs_neg]
    rw [hweightAbs]
    dsimp [error]
    have hmain :
        (H / (a : ℝ)) ^ i *
            ((j.choose i : ℝ) * (a : ℝ) ^ i * |(c : ℝ)| ^ (j - i)) *
            (U / H ^ j) =
          (j.choose i : ℝ) * U *
            ((H / (a : ℝ)) ^ i * (a : ℝ) ^ i *
              |(c : ℝ)| ^ (j - i) / H ^ j) := by ring
    rw [hmain, hcancel]
    calc
      (j.choose i : ℝ) * U * ((|(c : ℝ)| / H) ^ (j - i)) ≤
          (j.choose i : ℝ) * U :=
        by
          have hcoef : 0 ≤ (j.choose i : ℝ) * U := by positivity
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowle hcoef
      _ ≤ (2 : ℝ) ^ d * U :=
        mul_le_mul_of_nonneg_right hchoose (by linarith [hU])
  have hcardJ : J.card ≤ d := by
    dsimp [J]
    rw [Nat.card_Ico]
    omega
  have hsumBound :
      (H / (a : ℝ)) ^ i *
        (∑ z ∈ indices, |(weight z : ℝ)| * error z) ≤
          (1 + d * 2 ^ d : ℝ) * U ^ 2 := by
    have hsplit :
        ∑ z ∈ indices, (H / (a : ℝ)) ^ i *
            (|(weight z : ℝ)| * error z) =
          (H / (a : ℝ)) ^ i * (|(weight none : ℝ)| * error none) +
            ∑ j ∈ J, (H / (a : ℝ)) ^ i *
              (|(weight (some j) : ℝ)| * error (some j)) := by
      simp [indices, Finset.sum_insert, Finset.sum_image, J,
        Option.some.injEq, Function.Injective]
    rw [Finset.mul_sum, hsplit]
    have hnone' :
        (H / (a : ℝ)) ^ i *
          (|(weight none : ℝ)| * error none) ≤ U ^ 2 := by
      simpa [mul_assoc] using hcoefNone
    have hsumSome :
        (∑ j ∈ J, (H / (a : ℝ)) ^ i *
          (|(weight (some j) : ℝ)| * error (some j))) ≤
            (J.card : ℝ) * ((2 : ℝ) ^ d * U) := by
      calc
        _ ≤ ∑ j ∈ J, (2 : ℝ) ^ d * U :=
          Finset.sum_le_sum fun j hj => by
            simpa [mul_assoc] using hcoefSome j hj
        _ = (J.card : ℝ) * ((2 : ℝ) ^ d * U) := by simp
    have hcardR : (J.card : ℝ) ≤ d := by exact_mod_cast hcardJ
    have hsumSome' :
        (∑ j ∈ J, (H / (a : ℝ)) ^ i *
          (|(weight (some j) : ℝ)| * error (some j))) ≤
            (d : ℝ) * (2 : ℝ) ^ d * U := by
      calc
        _ ≤ (J.card : ℝ) * ((2 : ℝ) ^ d * U) := hsumSome
        _ ≤ (d : ℝ) * ((2 : ℝ) ^ d * U) :=
          mul_le_mul_of_nonneg_right hcardR (by positivity)
        _ = (d : ℝ) * (2 : ℝ) ^ d * U := by ring
    calc
      (H / (a : ℝ)) ^ i * (|(weight none : ℝ)| * error none) +
          ∑ j ∈ J, (H / (a : ℝ)) ^ i *
            (|(weight (some j) : ℝ)| * error (some j)) ≤
        U ^ 2 + (d : ℝ) * (2 : ℝ) ^ d * U :=
          add_le_add hnone' hsumSome'
      _ ≤ (1 + d * 2 ^ d : ℝ) * U ^ 2 := by
          have hU2 : U ≤ U ^ 2 := by nlinarith [hU]
          have hfactor : 0 ≤ (d : ℝ) * (2 : ℝ) ^ d := by positivity
          have hterm := mul_le_mul_of_nonneg_left hU2 hfactor
          nlinarith
  have hfactor : 0 ≤ (H / (a : ℝ)) ^ i := by positivity
  calc
    (H / (a : ℝ)) ^ i * realDistanceToIntegers
        (((Polynomial.C (s : ℝ) * phasePolynomialTruncation p l).comp
          (Polynomial.C (c : ℝ) + Polynomial.C (a : ℝ) * Polynomial.X)).coeff i) ≤
      (H / (a : ℝ)) ^ i *
        ∑ z ∈ indices, |(weight z : ℝ)| * error z :=
          mul_le_mul_of_nonneg_left hdist hfactor
    _ ≤ (1 + d * 2 ^ d : ℝ) * U ^ 2 := hsumBound
    _ = (inverseBoundDValue d : ℝ) * U ^ 2 := by
      simp [inverseBoundDValue]

private theorem phasePolynomialTruncation_comp_top_coeff
    (p : Polynomial ℝ) (l : ℕ) (s a b : ℝ) (ha : a ≠ 0) :
    ((Polynomial.C s * phasePolynomialTruncation p l).comp
      (Polynomial.C b + Polynomial.C a * Polynomial.X)).coeff l =
        s * p.coeff l * a ^ l := by
  rw [polynomial_comp_C_mul, Polynomial.coeff_C_mul]
  have htrunc : (phasePolynomialTruncation p l).natDegree ≤ l :=
    phasePolynomialTruncation_natDegree_le p l
  have hcomp := coeff_comp_affine (phasePolynomialTruncation p l) l l htrunc
    (a := a) (b := b) ha
  rw [hcomp]
  have hcoeff : (phasePolynomialTruncation p l).coeff l = p.coeff l := by
    simp [phasePolynomialTruncation]
  simp [hcoeff, Nat.choose_self]
  ring

private theorem distance_nat_mul_le
    (m : ℕ) (x ε : ℝ)
    (hx : realDistanceToIntegers x ≤ ε) :
    realDistanceToIntegers ((m : ℝ) * x) ≤ (m : ℝ) * ε := by
  classical
  have h := realDistanceToIntegers_intWeightedSum_le
    (S := (Finset.univ : Finset Unit))
    (m := fun _ : Unit => (m : ℤ))
    (x := fun _ : Unit => x) (ε := fun _ : Unit => ε)
    (by intro i hi; exact hx)
  have hAbs : |((m : ℤ) : ℝ)| = (m : ℝ) := by
    rw [abs_of_nonneg (show (0 : ℝ) ≤ ((m : ℤ) : ℝ) by exact_mod_cast Nat.zero_le m)]
    norm_cast
  simpa [hAbs] using h

private theorem recurrenceBudgetT_le_aggregate
    (d l : ℕ) (hl : 1 ≤ l) (hld : l ≤ d)
    (B y : ℝ) (hB : 1 ≤ B) (hy : 2 ≤ y) :
    recurrenceBudgetT l (8 * B * y) ≤ inverseBoundAggregateT d B y := by
  have hx : 2 ≤ 8 * B * y := by nlinarith
  rw [inverseBoundAggregateT_eval]
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 d) :
      0 ≤ recurrenceBudgetT j (8 * B * y) := by
    have hjd : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    exact le_trans (by norm_num) (recurrenceBudgetT_ge_one j hjd _ hx)
  have hsum := Finset.single_le_sum hterm (show l ∈ Finset.Icc 1 d by simp [hl, hld])
  linarith

private theorem recurrenceBudgetR_le_aggregate
    (d l : ℕ) (hl : 1 ≤ l) (hld : l ≤ d)
    (B y : ℝ) (hB : 1 ≤ B) (hy : 2 ≤ y) :
    recurrenceBudgetR l (8 * B * y) ≤ inverseBoundAggregateR d B y := by
  have hx : 2 ≤ 8 * B * y := by nlinarith
  rw [inverseBoundAggregateR_eval]
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 d) :
      0 ≤ recurrenceBudgetR j (8 * B * y) := by
    have hjd : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    exact le_trans (by norm_num) (recurrenceBudgetR_ge_one j hjd _ hx)
  have hsum := Finset.single_le_sum hterm (show l ∈ Finset.Icc 1 d by simp [hl, hld])
  linarith

private theorem inverseBoundU_mono
    (d k n : ℕ) (B y : ℝ) (hd : 1 ≤ d) (hB : 1 ≤ B) (hy : 2 ≤ y)
    (hkn : k ≤ n) :
    inverseBoundU d k B y ≤ inverseBoundU d n B y := by
  have hstep (j : ℕ) :
      inverseBoundU d j B y ≤ inverseBoundU d (j + 1) B y := by
    rw [inverseBoundU_succ_eval]
    have hU : 1 ≤ inverseBoundU d j B y :=
      inverseBoundU_ge_one d hd B y hB hy j
    have hR : 1 ≤ inverseBoundAggregateR d B y :=
      inverseBoundAggregateR_ge_one d B y hB hy
    have hD : 1 ≤ (inverseBoundDValue d : ℝ) := by
      exact_mod_cast inverseBoundD_ge_one d
    have hpow' : 1 ≤ (4 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hpow : 1 ≤ (4 : ℝ) ^ d + 1 := by linarith
    have hfac : 1 ≤ (4 : ℝ) ^ d + 1 := hpow
    have hfacD : 1 ≤ ((4 : ℝ) ^ d + 1) * (inverseBoundDValue d : ℝ) := by
      calc
        1 = 1 * 1 := by ring
        _ ≤ ((4 : ℝ) ^ d + 1) * (inverseBoundDValue d : ℝ) :=
          mul_le_mul hfac hD (by linarith [hfac]) (by linarith [hD])
    have hfacR : 1 ≤ ((4 : ℝ) ^ d + 1) * (inverseBoundDValue d : ℝ) *
        inverseBoundAggregateR d B y := by
      calc
        1 = 1 * 1 := by ring
        _ ≤ ((4 : ℝ) ^ d + 1) * (inverseBoundDValue d : ℝ) *
            inverseBoundAggregateR d B y :=
          mul_le_mul hfacD hR (by linarith [hfacD]) (by linarith [hR])
    have hU2 : inverseBoundU d j B y ≤ (inverseBoundU d j B y) ^ 2 := by
      nlinarith [hU]
    have hmul : inverseBoundU d j B y ≤
        (((4 : ℝ) ^ d + 1) * (inverseBoundDValue d : ℝ) *
          inverseBoundAggregateR d B y) * (inverseBoundU d j B y) ^ 2 := by
      calc
        inverseBoundU d j B y ≤
            (((4 : ℝ) ^ d + 1) * (inverseBoundDValue d : ℝ) *
              inverseBoundAggregateR d B y) * inverseBoundU d j B y :=
          le_mul_of_one_le_left (by positivity) hfacR
        _ ≤ _ := mul_le_mul_of_nonneg_left hU2 (by positivity)
    exact hmul
  induction n with
  | zero => simp at hkn; subst k; exact le_rfl
  | succ n ih =>
      by_cases hkn' : k ≤ n
      · exact le_trans (ih hkn') (hstep n)
      · have hk : k = n + 1 := by omega
        subst k
        exact le_rfl

private theorem floor_interval_bounds (A : ℝ) (hA : 4 ≤ A) :
    1 ≤ Nat.floor A ∧
    1 ≤ Nat.floor (2 * A) - Nat.floor A ∧
    A / 2 ≤ ((Nat.floor (2 * A) - Nat.floor A : ℕ) : ℝ) ∧
    ((Nat.floor (2 * A) - Nat.floor A : ℕ) : ℝ) ≤ A + 1 := by
  let m : ℕ := Nat.floor A
  let q : ℕ := Nat.floor (2 * A)
  have hA0 : 0 ≤ A := by linarith
  have hmle : (m : ℝ) ≤ A := by dsimp [m]; exact Nat.floor_le hA0
  have hmlt : A < (m : ℝ) + 1 := by dsimp [m]; exact Nat.lt_floor_add_one A
  have hqle : (q : ℝ) ≤ 2 * A := by
    dsimp [q]
    exact Nat.floor_le (by positivity)
  have hqlt : 2 * A < (q : ℝ) + 1 := by
    dsimp [q]
    exact Nat.lt_floor_add_one (2 * A)
  have hmq : m ≤ q := by
    apply Nat.le_floor
    nlinarith
  have hNcast : ((q - m : ℕ) : ℝ) = (q : ℝ) - (m : ℝ) := by
    exact Nat.cast_sub hmq
  have hNlower : A / 2 ≤ ((q - m : ℕ) : ℝ) := by
    rw [hNcast]
    nlinarith
  have hNupper : ((q - m : ℕ) : ℝ) ≤ A + 1 := by
    rw [hNcast]
    nlinarith
  refine ⟨?_, ?_, hNlower, hNupper⟩
  · exact Nat.le_floor (by norm_num; linarith [hA])
  · apply Nat.one_le_iff_ne_zero.mpr
    intro hNzero
    have hNzero' : q - m = 0 := by simpa [q, m] using hNzero
    have hNcastzero : ((q - m : ℕ) : ℝ) = 0 := by exact_mod_cast hNzero'
    rw [hNcastzero] at hNlower
    linarith [hA]

private theorem pow_le_self_of_unit_interval
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    x ^ n ≤ x := by
  calc
    x ^ n = x ^ (n - 1 + 1) := by congr 1 <;> omega
    _ = x ^ (n - 1) * x := by rw [pow_succ]
    _ ≤ 1 * x := mul_le_mul_of_nonneg_right (pow_le_one₀ hx0 hx1) hx0
    _ = x := by ring

private theorem inverseBoundU_next_ge_aggregate_mul
    (d k : ℕ) (B y : ℝ) (hd : 1 ≤ d) (hB : 1 ≤ B) (hy : 2 ≤ y) :
    inverseBoundAggregateR d B y * inverseBoundU d k B y ≤
      inverseBoundU d (k + 1) B y := by
  have hU : 1 ≤ inverseBoundU d k B y := inverseBoundU_ge_one d hd B y hB hy k
  have hR : 1 ≤ inverseBoundAggregateR d B y :=
    inverseBoundAggregateR_ge_one d B y hB hy
  have hD : 1 ≤ (inverseBoundDValue d : ℝ) := by
    exact_mod_cast inverseBoundD_ge_one d
  have hpow : 1 ≤ (4 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hfac : 1 ≤ (4 : ℝ) ^ d + 1 := by linarith
  let facD : ℝ := ((4 : ℝ) ^ d + 1) * (inverseBoundDValue d : ℝ)
  have hfacD : 1 ≤ facD := by
    have hmul := mul_le_mul hfac hD (by linarith [hfac]) (by linarith [hD])
    simpa [facD] using hmul
  have hU2 : inverseBoundU d k B y ≤ (inverseBoundU d k B y) ^ 2 := by
    nlinarith [hU]
  have hUkfactor : inverseBoundU d k B y ≤
      facD * (inverseBoundU d k B y) ^ 2 := by
    calc
      inverseBoundU d k B y ≤ (inverseBoundU d k B y) ^ 2 := hU2
      _ = 1 * (inverseBoundU d k B y) ^ 2 := by ring
      _ ≤ facD * (inverseBoundU d k B y) ^ 2 :=
        mul_le_mul_of_nonneg_right hfacD (sq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hUkfactor (by positivity :
    0 ≤ inverseBoundAggregateR d B y)
  have hscaled' : inverseBoundAggregateR d B y * inverseBoundU d k B y ≤
      (4 ^ d + 1) * (inverseBoundDValue d : ℝ) *
        inverseBoundAggregateR d B y * (inverseBoundU d k B y) ^ 2 := by
    calc
      _ ≤ inverseBoundAggregateR d B y *
          (facD * (inverseBoundU d k B y) ^ 2) := hscaled
      _ = _ := by dsimp [facD]; ring
  calc
    inverseBoundAggregateR d B y * inverseBoundU d k B y ≤
        (4 ^ d + 1) * (inverseBoundDValue d : ℝ) *
          inverseBoundAggregateR d B y * (inverseBoundU d k B y) ^ 2 := hscaled'
    _ = inverseBoundU d (k + 1) B y :=
      (inverseBoundU_succ_eval d k B y).symm

set_option maxHeartbeats 800000 in
private theorem largeA_dilation_degree_step
    {d k l N m : ℕ} (hd : 1 ≤ d) (hdk : d - k = l)
    (hl : 1 ≤ l) (hld : l ≤ d)
    {A H X B η : ℝ}
    (hA : 4 ≤ A) (hB : 1 ≤ B) (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hlarge : inverseBoundV d B η⁻¹ * A < H)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (hNpos : 1 ≤ N) (hNlower : A / 2 ≤ (N : ℝ))
    (hNlarge : inverseBoundAggregateT d B η⁻¹ ≤ (N : ℝ))
    (S' : Finset ℕ)
    (hS'dense : (η / (8 * B)) * (N : ℝ) ≤ (S'.card : ℝ))
    (hS'bounds : ∀ a ∈ S', A < (a : ℝ) ∧ (a : ℝ) ≤ 2 * A)
    (hS'interval : ∀ a ∈ S', m < a ∧ a ≤ m + N)
    (r₀ : ℤ) (hr₀pos : 1 ≤ r₀) (hr₀B : (r₀ : ℝ) ≤ B)
    (hlocal₀ : ∀ a ∈ S', ∀ j, 1 ≤ j → j ≤ d →
      (H / (a : ℝ)) ^ j * realDistanceToIntegers
        ((r₀ : ℝ) * (phaseDilatedAt P a
          (Int.floor (X / (a : ℝ)))).coeff j) ≤ B)
    (v : ℕ) (hvpos : 1 ≤ v)
    (hvbound : (r₀ : ℝ) * (v : ℝ) ≤ inverseBoundU d k B η⁻¹)
    (hvhigh : ∀ j, l < j → j ≤ d →
      H ^ j * realDistanceToIntegers
        (((r₀ : ℝ) * (v : ℝ)) * (phaseCenteredAt P (Int.floor X)).coeff j) ≤
          inverseBoundU d k B η⁻¹) :
    ∃ u : ℕ, 1 ≤ u ∧
      (u : ℝ) ≤ inverseBoundAggregateR d B η⁻¹ ∧
      (r₀ : ℝ) * (v * u : ℕ) ≤ inverseBoundU d (k + 1) B η⁻¹ ∧
      ∀ j, d - (k + 1) < j → j ≤ d →
        H ^ j * realDistanceToIntegers
          (((r₀ : ℝ) * (v * u : ℕ)) *
            (phaseCenteredAt P (Int.floor X)).coeff j) ≤
              inverseBoundU d (k + 1) B η⁻¹ := by
  classical
  let y : ℝ := η⁻¹
  let rho : ℝ := η / (8 * B)
  let U : ℝ := inverseBoundU d k B y
  let D : ℝ := inverseBoundDValue d
  let alpha : Polynomial ℝ := phaseCenteredAt P (Int.floor X)
  let s : ℤ := r₀ * (v : ℤ)
  let lpoly : Polynomial ℝ :=
    Polynomial.C ((r₀ : ℝ) * (v : ℝ) * alpha.coeff l) *
      (Polynomial.C (m : ℝ) + Polynomial.X) ^ l
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := by linarith
  have hy2 : 2 ≤ y := by
    dsimp [y]
    rw [← one_div]
    exact (le_div_iff₀ hη).2 (by nlinarith [hηhalf])
  have hrhoPos : 0 < rho := by dsimp [rho]; positivity
  have hrhoHalf : rho < 1 / 2 := by
    dsimp [rho]
    have hden : 8 * B ≥ 8 := by nlinarith [hB]
    have hsmall : η / (8 * B) ≤ η / 8 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * B)
        (by norm_num : (0 : ℝ) < 8)]
      nlinarith [hη, hB]
    linarith [hηhalf]
  have hV4 := inverseBoundV_ge_four d hd B y hB hy2
  have hAZeroNonneg : 0 ≤ inverseBoundAZero d B y := by
    have h := inverseBoundAZero_ge_four d B y hB hy2
    linarith
  have hVterm : 128 * D * (inverseBoundU d d B y) ^ 2 / rho ≤
      inverseBoundV d B y := by
    have htermEq : 128 * D * (inverseBoundU d d B y) ^ 2 / rho =
        1024 * D * B * y * (inverseBoundU d d B y) ^ 2 := by
      dsimp [rho, y]
      field_simp [ne_of_gt hη, ne_of_gt hBpos]
      ring
    calc
      128 * D * (inverseBoundU d d B y) ^ 2 / rho =
          1024 * D * B * y * (inverseBoundU d d B y) ^ 2 := htermEq
      _ ≤ inverseBoundV d B y := by
        rw [inverseBoundV_eval]
        nlinarith [show 0 ≤ 4 * (inverseBoundDValue d : ℝ) * B * y *
          (inverseBoundU d d B y) ^ 2 by positivity,
          show 0 ≤ 2 ^ (d + 1) * B *
            (2 * inverseBoundAZero d B y) ^ d by
              exact mul_nonneg
                (mul_nonneg (by positivity) (by linarith [hB]))
                (pow_nonneg
                  (mul_nonneg (by norm_num) hAZeroNonneg) d),
          show 0 ≤ inverseBoundU d d B y by
            exact le_trans (by norm_num) (inverseBoundU_ge_one d hd B y hB hy2 d)]
  have hlargeD : (128 * D * (inverseBoundU d d B y) ^ 2 / rho) * A < H := by
    calc
      (128 * D * (inverseBoundU d d B y) ^ 2 / rho) * A ≤
          inverseBoundV d B y * A :=
        mul_le_mul_of_nonneg_right hVterm (by linarith [hA])
      _ < H := hlarge
  have hfourA : 4 * A < H := by
    have hmul : 4 * A ≤ inverseBoundV d B y * A :=
      mul_le_mul_of_nonneg_right hV4 (by linarith [hA])
    linarith
  have htwoA : 2 * A < H := by linarith
  have hHpos : 0 < H := by linarith [hfourA, hA]
  have hyInv : y = η⁻¹ := rfl
  have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
  have hDge : 1 ≤ D := by
    dsimp [D]
    exact_mod_cast inverseBoundD_ge_one d
  have hUkge : 1 ≤ U := by dsimp [U, y]; exact inverseBoundU_ge_one d hd B η⁻¹ hB hy2 k
  have hUdge : 1 ≤ inverseBoundU d d B y := by
    exact inverseBoundU_ge_one d hd B y hB hy2 d
  have hUkmono : U ≤ inverseBoundU d d B y := by
    exact inverseBoundU_mono d k d B y hd hB hy2 (by omega)
  have hBU : B ≤ U := by
    have hmono := inverseBoundU_mono d 0 k B y hd hB hy2 (by omega)
    simpa [U, y, inverseBoundU_zero_eval] using hmono
  have hvle : (v : ℝ) ≤ U := by
    have hr₀real : 1 ≤ (r₀ : ℝ) := by exact_mod_cast hr₀pos
    have hmul := mul_le_mul_of_nonneg_right hr₀real (by positivity : 0 ≤ (v : ℝ))
    simpa [U, y] using hmul.trans hvbound
  have halphaDeg : alpha.natDegree ≤ d := by
    dsimp [alpha]
    have hlinearDegree :
        (Polynomial.C (Int.floor X : ℝ) + Polynomial.X).natDegree ≤ 1 := by
      rw [add_comm, Polynomial.natDegree_X_add_C]
    calc
      (phaseCenteredAt P (Int.floor X)).natDegree ≤
          P.natDegree * (Polynomial.C (Int.floor X : ℝ) + Polynomial.X).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ d * 1 := Nat.mul_le_mul hP hlinearDegree
      _ = d := by simp
  have hQdeg : lpoly.natDegree ≤ l := by
    have hlin : (Polynomial.C (m : ℝ) + Polynomial.X).natDegree ≤ 1 := by
      rw [add_comm, Polynomial.natDegree_X_add_C]
    dsimp [lpoly]
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (Polynomial.natDegree_pow_le_of_le l hlin |>.trans (by simp))
  have hQcoeff : lpoly.coeff l = (r₀ : ℝ) * (v : ℝ) * alpha.coeff l := by
    dsimp [lpoly]
    rw [show Polynomial.C (m : ℝ) + Polynomial.X =
      Polynomial.X + Polynomial.C (m : ℝ) by exact add_comm _ _]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
    simp
  have hQeval (n : ℕ) :
      lpoly.eval ((n + 1 : ℕ) : ℝ) =
        ((r₀ : ℝ) * (v : ℝ) * alpha.coeff l) *
          ((m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ l := by
    simp [lpoly, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_pow]
  let eps : ℝ := D * U ^ 2 * (2 * A / H) ^ l
  have hepsNonneg : 0 ≤ eps := by dsimp [eps]; positivity
  have hUmonoSq : U ^ 2 ≤ (inverseBoundU d d B y) ^ 2 := by
    have hU0 : 0 ≤ U := by linarith [hUkge]
    exact (sq_le_sq₀ hU0 (le_trans hU0 hUkmono)).2 hUkmono
  have hratioUnit : 0 ≤ 2 * A / H ∧ 2 * A / H ≤ 1 := by
    constructor
    · exact div_nonneg (by positivity) (le_of_lt hHpos)
    · rw [div_le_one hHpos]
      linarith
  have hpowSmall : (2 * A / H) ^ l ≤ 2 * A / H :=
    pow_le_self_of_unit_interval hratioUnit.1 hratioUnit.2 hl
  have hepsSmall : eps < rho / 64 := by
    have hcoef : D * U ^ 2 ≤ D * (inverseBoundU d d B y) ^ 2 :=
      mul_le_mul_of_nonneg_left hUmonoSq hDnonneg
    have hepsle : eps ≤ D * (inverseBoundU d d B y) ^ 2 * (2 * A / H) := by
      dsimp [eps]
      calc
        D * U ^ 2 * (2 * A / H) ^ l ≤
            D * (inverseBoundU d d B y) ^ 2 * (2 * A / H) ^ l :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ ≤ D * (inverseBoundU d d B y) ^ 2 * (2 * A / H) :=
          mul_le_mul_of_nonneg_left hpowSmall (by positivity)
    have hlargeScaled :
        D * (inverseBoundU d d B y) ^ 2 * (2 * A) < (rho / 64) * H := by
      calc
        D * (inverseBoundU d d B y) ^ 2 * (2 * A) =
            (rho / 64) * ((128 * D * (inverseBoundU d d B y) ^ 2 / rho) * A) := by
              field_simp [ne_of_gt hrhoPos]
              ring
        _ < (rho / 64) * H := mul_lt_mul_of_pos_left hlargeD (by positivity)
    have hquot :
        (D * (inverseBoundU d d B y) ^ 2 * (2 * A)) / H < rho / 64 :=
      (div_lt_iff₀ hHpos).2 hlargeScaled
    have hrewrite :
        D * (inverseBoundU d d B y) ^ 2 * (2 * A / H) =
          (D * (inverseBoundU d d B y) ^ 2 * (2 * A)) / H := by ring
    calc
      eps ≤ D * (inverseBoundU d d B y) ^ 2 * (2 * A / H) := hepsle
      _ = (D * (inverseBoundU d d B y) ^ 2 * (2 * A)) / H := hrewrite
      _ < rho / 64 := hquot
  let G : Finset ℕ := (Finset.range N).filter
    (fun n => realDistanceToIntegers (lpoly.eval ((n + 1 : ℕ) : ℝ)) ≤ eps)
  let Sidx : Finset ℕ := S'.image (fun a => a - (m + 1))
  have hshiftinj : Set.InjOn (fun a : ℕ => a - (m + 1)) S' := by
    intro a ha b hb heq
    have hma := (hS'interval a ha).1
    have hmb := (hS'interval b hb).1
    have hma' : m + 1 ≤ a := Nat.succ_le_of_lt hma
    have hmb' : m + 1 ≤ b := Nat.succ_le_of_lt hmb
    have heq' := congrArg (fun n : ℕ => n + (m + 1)) heq
    simpa [Nat.sub_add_cancel hma', Nat.sub_add_cancel hmb'] using heq'
  have hSidxCard : Sidx.card = S'.card := by
    exact Finset.card_image_of_injOn hshiftinj
  have hSidxSub : Sidx ⊆ G := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    have ham := (hS'interval a ha).1
    have haN := (hS'interval a ha).2
    have hnlt : a - (m + 1) < N := by omega
    have hshift : m + (a - (m + 1) + 1) = a := by omega
    have hshiftCast : (m : ℝ) + ((a - (m + 1) + 1 : ℕ) : ℝ) = (a : ℝ) := by
      exact_mod_cast hshift
    have hval : lpoly.eval ((a - (m + 1) + 1 : ℕ) : ℝ) =
        ((r₀ : ℝ) * (v : ℝ) * alpha.coeff l) * (a : ℝ) ^ l := by
      rw [hQeval, hshiftCast]
    have haPos : 1 ≤ a := by
      have hbound := (hS'bounds a ha).1
      have : 0 < (a : ℝ) := lt_trans (by linarith [hA]) hbound
      exact_mod_cast (show 0 < a by exact_mod_cast this)
    let c : ℤ := (a : ℤ) * Int.floor (X / (a : ℝ)) - Int.floor X
    have hc : |(c : ℝ)| < (a : ℝ) := by
      dsimp [c]
      exact dilationCenter_offset_abs_lt X haPos
    have hcenter : (Int.floor X : ℝ) + (c : ℝ) =
        (a : ℝ) * (Int.floor (X / (a : ℝ)) : ℝ) := by
      have hi := dilationCenter_integer_identity X a
      dsimp [c]
      exact_mod_cast hi
    have hcomp := centered_dilation_comp_eq P (Int.floor X) a c
      (Int.floor (X / (a : ℝ))) hcenter
    have haR : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
    have hcH : |(c : ℝ)| / H ≤ 1 := by
      apply le_of_lt
      apply (div_lt_iff₀ hHpos).2
      have haTop := (hS'bounds a ha).2
      linarith [hc, htwoA]
    have hlocalComp (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d) :
        (H / (a : ℝ)) ^ j * realDistanceToIntegers
          ((r₀ : ℝ) * (alpha.comp
            (Polynomial.C (c : ℝ) + Polynomial.C (a : ℝ) * Polynomial.X)).coeff j) ≤ B := by
      have h := hlocal₀ a ha j hj hjd
      rw [hcomp]
      exact h
    have htrunc := phasePolynomialTruncation_comp_error_bound
      alpha d l l halphaDeg hld hl (Nat.le_refl l) a haPos c r₀ s v H B U
      hHpos (by linarith [hB]) hUkge hcH rfl hvle hBU
      (fun j hj1 hjd => hlocalComp j hj1 hjd)
      (fun j hj hjd => by
        simpa [s, alpha, U, y] using hvhigh j hj hjd)
    have htop := phasePolynomialTruncation_comp_top_coeff alpha l
      (s : ℝ) (a : ℝ) (c : ℝ) (ne_of_gt haR)
    have hsCast : (s : ℝ) = (r₀ : ℝ) * (v : ℝ) := by
      dsimp [s]
      push_cast
      ring
    have hdistLocal :
        (H / (a : ℝ)) ^ l * realDistanceToIntegers
          (((r₀ : ℝ) * (v : ℝ) * alpha.coeff l) * (a : ℝ) ^ l) ≤ D * U ^ 2 := by
      have htrunc' := htrunc
      rw [htop, hsCast] at htrunc'
      simpa [D, U] using htrunc'
    have hratioPos : 0 < H / (a : ℝ) := div_pos hHpos haR
    have hratioPow : 0 < (H / (a : ℝ)) ^ l := pow_pos hratioPos _
    have hdistDiv := (le_div_iff₀ hratioPow).2 (by
      calc
        realDistanceToIntegers
            (((r₀ : ℝ) * (v : ℝ) * alpha.coeff l) * (a : ℝ) ^ l) *
            (H / (a : ℝ)) ^ l =
          (H / (a : ℝ)) ^ l * realDistanceToIntegers
            (((r₀ : ℝ) * (v : ℝ) * alpha.coeff l) * (a : ℝ) ^ l) := by ring
        _ ≤ D * U ^ 2 := hdistLocal)
    have hratioInv : (H / (a : ℝ))⁻¹ = (a : ℝ) / H := by
      field_simp [ne_of_gt hHpos]
    have hdistError :
        realDistanceToIntegers
          (((r₀ : ℝ) * (v : ℝ) * alpha.coeff l) * (a : ℝ) ^ l) ≤ eps := by
      have haOver : (a : ℝ) / H ≤ 2 * A / H := by
        rw [div_le_div_iff_of_pos_right hHpos]
        exact (hS'bounds a ha).2
      have hpow : ((a : ℝ) / H) ^ l ≤ (2 * A / H) ^ l :=
        (pow_le_pow_left₀ (by positivity) haOver l)
      have heq : D * U ^ 2 / (H / (a : ℝ)) ^ l =
          D * U ^ 2 * ((a : ℝ) / H) ^ l := by
        rw [div_eq_mul_inv, ← inv_pow, hratioInv]
      dsimp [eps]
      calc
        realDistanceToIntegers
            (((r₀ : ℝ) * (v : ℝ) * alpha.coeff l) * (a : ℝ) ^ l) ≤
          D * U ^ 2 / (H / (a : ℝ)) ^ l := hdistDiv
        _ = D * U ^ 2 * ((a : ℝ) / H) ^ l := heq
        _ ≤ D * U ^ 2 * (2 * A / H) ^ l :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hnlt, by rw [hval]; exact hdistError⟩
  have hgood : rho * (N : ℝ) ≤ (G.card : ℝ) := by
    have hcard := Finset.card_le_card hSidxSub
    rw [hSidxCard] at hcard
    exact hS'dense.trans (by exact_mod_cast hcard)
  have hQdeg' : lpoly.natDegree ≤ l := hQdeg
  have hrecT : recurrenceBudgetT l rho⁻¹ ≤ (N : ℝ) := by
    have hrhoInv : rho⁻¹ = 8 * B * y := by
      dsimp [rho, y]
      field_simp [ne_of_gt hη, ne_of_gt hBpos]
    rw [hrhoInv]
    calc
      recurrenceBudgetT l (8 * B * y) ≤ inverseBoundAggregateT d B y :=
        recurrenceBudgetT_le_aggregate d l hl hld B y hB hy2
      _ ≤ (N : ℝ) := by simpa [y] using hNlarge
  have hrecDensity : rho * (N : ℝ) ≤ (G.card : ℝ) := hgood
  have hepsRho : eps ≤ rho / 64 := le_of_lt hepsSmall
  obtain ⟨u, huPos, huR, huCoeff⟩ :=
    polynomialRecurrence (d := l) (N := N) hNpos hrhoPos hrhoHalf
      hepsNonneg hepsRho lpoly hQdeg' hrecDensity hrecT
  have hRagg : recurrenceBudgetR l rho⁻¹ ≤ inverseBoundAggregateR d B y := by
    have hrhoInv : rho⁻¹ = 8 * B * y := by
      dsimp [rho, y]
      field_simp [ne_of_gt hη, ne_of_gt hBpos]
    rw [hrhoInv]
    exact recurrenceBudgetR_le_aggregate d l hl hld B y hB hy2
  have hAggRge : 1 ≤ inverseBoundAggregateR d B y :=
    inverseBoundAggregateR_ge_one d B y hB hy2
  have hAggRnonneg : 0 ≤ inverseBoundAggregateR d B y := by linarith
  have huRagg : (u : ℝ) ≤ inverseBoundAggregateR d B y := by
    exact le_trans huR (by simpa [rho, y] using hRagg)
  have hqcoeff := huCoeff l (by omega)
  have hQtop : lpoly.coeff l = (r₀ : ℝ) * (v : ℝ) * alpha.coeff l := hQcoeff
  have huTop : (N : ℝ) ^ l * realDistanceToIntegers
      ((u : ℝ) * ((r₀ : ℝ) * (v : ℝ) * alpha.coeff l)) ≤
        recurrenceBudgetR l rho⁻¹ * eps := by
    rw [← hQtop]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hqcoeff
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hratioN : (H / (N : ℝ)) ^ l * (N : ℝ) ^ l = H ^ l := by
    rw [div_pow]
    field_simp [ne_of_gt hNreal]
  have hscale : (H / (N : ℝ)) ^ l * (2 * A / H) ^ l =
      (2 * A / (N : ℝ)) ^ l := by
    rw [← mul_pow]
    have hbase : (H / (N : ℝ)) * (2 * A / H) = 2 * A / (N : ℝ) := by
      field_simp [ne_of_gt hHpos, ne_of_gt hNreal]
    rw [hbase]
  have hbaseN : 2 * A / (N : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hNreal]
    nlinarith [hNlower]
  have hpowN : (2 * A / (N : ℝ)) ^ l ≤ (4 : ℝ) ^ d := by
    calc
      (2 * A / (N : ℝ)) ^ l ≤ (4 : ℝ) ^ l :=
        (pow_le_pow_left₀ (by positivity) hbaseN l)
      _ ≤ (4 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hld
  have hnewDistance :
      H ^ l * realDistanceToIntegers
        ((u : ℝ) * ((r₀ : ℝ) * (v : ℝ) * alpha.coeff l)) ≤
          inverseBoundU d (k + 1) B y := by
    calc
      H ^ l * realDistanceToIntegers
          ((u : ℝ) * ((r₀ : ℝ) * (v : ℝ) * alpha.coeff l)) =
        (H / (N : ℝ)) ^ l *
          ((N : ℝ) ^ l * realDistanceToIntegers
            ((u : ℝ) * ((r₀ : ℝ) * (v : ℝ) * alpha.coeff l))) := by
              rw [← hratioN]
              ring
      _ ≤ (H / (N : ℝ)) ^ l * (recurrenceBudgetR l rho⁻¹ * eps) :=
        mul_le_mul_of_nonneg_left huTop (by positivity)
      _ = recurrenceBudgetR l rho⁻¹ * D * U ^ 2 *
          (2 * A / (N : ℝ)) ^ l := by
            dsimp [eps]
            calc
              (H / (N : ℝ)) ^ l *
                  (recurrenceBudgetR l rho⁻¹ *
                    (D * U ^ 2 * (2 * A / H) ^ l)) =
                  recurrenceBudgetR l rho⁻¹ * D * U ^ 2 *
                    ((H / (N : ℝ)) ^ l * (2 * A / H) ^ l) := by ring
              _ = recurrenceBudgetR l rho⁻¹ * D * U ^ 2 *
                    (2 * A / (N : ℝ)) ^ l := by rw [hscale]
      _ ≤ inverseBoundAggregateR d B y * D * U ^ 2 *
          (2 * A / (N : ℝ)) ^ l := by
            calc
              recurrenceBudgetR l rho⁻¹ * D * U ^ 2 *
                  (2 * A / (N : ℝ)) ^ l =
                  recurrenceBudgetR l rho⁻¹ *
                    (D * U ^ 2 * (2 * A / (N : ℝ)) ^ l) := by ring
              _ ≤ inverseBoundAggregateR d B y *
                    (D * U ^ 2 * (2 * A / (N : ℝ)) ^ l) :=
                  mul_le_mul_of_nonneg_right hRagg (by positivity)
              _ = inverseBoundAggregateR d B y * D * U ^ 2 *
                    (2 * A / (N : ℝ)) ^ l := by ring
      _ ≤ inverseBoundAggregateR d B y * D * U ^ 2 * (4 : ℝ) ^ d :=
            mul_le_mul_of_nonneg_left hpowN (by
              exact mul_nonneg (mul_nonneg hAggRnonneg hDnonneg) (sq_nonneg U))
      _ ≤ (4 ^ d + 1) * D * inverseBoundAggregateR d B y * U ^ 2 := by
            have hpowPlus : (4 : ℝ) ^ d ≤ (4 : ℝ) ^ d + 1 := by linarith
            have hRDU : 0 ≤ D * inverseBoundAggregateR d B y * U ^ 2 := by
              exact mul_nonneg (mul_nonneg hDnonneg hAggRnonneg) (sq_nonneg U)
            calc
              inverseBoundAggregateR d B y * D * U ^ 2 * (4 : ℝ) ^ d =
                  (4 : ℝ) ^ d *
                    (D * inverseBoundAggregateR d B y * U ^ 2) := by ring
              _ ≤ ((4 : ℝ) ^ d + 1) *
                    (D * inverseBoundAggregateR d B y * U ^ 2) :=
                  mul_le_mul_of_nonneg_right hpowPlus hRDU
              _ = (4 ^ d + 1) * D * inverseBoundAggregateR d B y * U ^ 2 := by ring
      _ = inverseBoundU d (k + 1) B y :=
            (inverseBoundU_succ_eval d k B y).symm
  have hnewDenom : (r₀ : ℝ) * (v * u : ℕ) ≤ inverseBoundU d (k + 1) B y := by
    have hvNonneg : 0 ≤ (r₀ : ℝ) * (v : ℝ) := by positivity
    have huNonneg : 0 ≤ (u : ℝ) := by positivity
    calc
      (r₀ : ℝ) * (v * u : ℕ) = (u : ℝ) * ((r₀ : ℝ) * (v : ℝ)) := by
        push_cast
        ring
      _ ≤ inverseBoundAggregateR d B y * inverseBoundU d k B y :=
        mul_le_mul huRagg hvbound hvNonneg hAggRnonneg
      _ ≤ inverseBoundU d (k + 1) B y :=
        inverseBoundU_next_ge_aggregate_mul d k B y hd hB hy2
  refine ⟨u, ?_, huRagg, hnewDenom, ?_⟩
  · exact huPos
  · intro j hj hjd
    have hnewj : j = l ∨ l < j := by
      have hdl : d - (k + 1) = l - 1 := by omega
      rw [hdl] at hj
      omega
    rcases hnewj with hEq | hgt
    · subst j
      have hnumEq :
          ((r₀ : ℝ) * (v * u : ℕ)) * alpha.coeff l =
            (u : ℝ) * ((r₀ : ℝ) * (v : ℝ) * alpha.coeff l) := by
        push_cast
        ring
      rw [hnumEq]
      exact hnewDistance
    · have hprev := hvhigh j hgt hjd
      have hdistMul := distance_nat_mul_le u
        (((r₀ : ℝ) * (v : ℝ)) * alpha.coeff j)
        (realDistanceToIntegers (((r₀ : ℝ) * (v : ℝ)) * alpha.coeff j)) le_rfl
      have hprevNonneg : 0 ≤ H ^ j *
          realDistanceToIntegers (((r₀ : ℝ) * (v : ℝ)) * alpha.coeff j) :=
        mul_nonneg (pow_nonneg (le_of_lt hHpos) j) Metric.infDist_nonneg
      have hnumEq :
          ((r₀ : ℝ) * (v * u : ℕ)) * alpha.coeff j =
            (u : ℝ) * (((r₀ : ℝ) * (v : ℝ)) * alpha.coeff j) := by
        push_cast
        ring
      rw [hnumEq]
      calc
        H ^ j * realDistanceToIntegers
            ((u : ℝ) * (((r₀ : ℝ) * (v : ℝ)) * alpha.coeff j)) ≤
          H ^ j * ((u : ℝ) *
            realDistanceToIntegers (((r₀ : ℝ) * (v : ℝ)) * alpha.coeff j)) :=
              mul_le_mul_of_nonneg_left hdistMul
                (pow_nonneg (le_of_lt hHpos) j)
        _ = (u : ℝ) * (H ^ j *
            realDistanceToIntegers (((r₀ : ℝ) * (v : ℝ)) * alpha.coeff j)) := by ring
        _ ≤ inverseBoundAggregateR d B y * inverseBoundU d k B y :=
          mul_le_mul huRagg hprev hprevNonneg hAggRnonneg
        _ ≤ inverseBoundU d (k + 1) B y :=
          inverseBoundU_next_ge_aggregate_mul d k B y hd hB hy2

private theorem exists_large_common_dilation
    {S : Finset ℕ}
    (A B η : ℝ) (N : ℕ)
    (hA : 0 < A) (hB : 1 ≤ B) (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hScard : η * A ≤ (S.card : ℝ))
    (hNupper : (N : ℝ) ≤ 3 * A)
    (f : ℕ → ℤ)
    (hf : ∀ a ∈ S, 1 ≤ f a ∧ (f a : ℝ) ≤ B) :
    ∃ r₀ : ℤ, ∃ S' : Finset ℕ,
      S' ⊆ S ∧
      (∀ a ∈ S', f a = r₀) ∧
      1 ≤ r₀ ∧ (r₀ : ℝ) ≤ B ∧
      (η / (8 * B)) * (N : ℝ) ≤ (S'.card : ℝ) := by
  classical
  let K : ℕ := Nat.floor B
  let rho : ℝ := η / (8 * B)
  let n : ℕ := Nat.floor (rho * (N : ℝ))
  let g : ℕ → ℕ := fun a => (f a).toNat - 1
  have hB0 : 0 ≤ B := by linarith
  have hKle : (K : ℝ) ≤ B := by dsimp [K]; exact Nat.floor_le hB0
  have hKpos : 1 ≤ K := by
    change 1 ≤ Nat.floor B
    exact Nat.le_floor (by exact_mod_cast hB)
  have hrhoPos : 0 < rho := by dsimp [rho]; positivity
  have hnle : (n : ℝ) ≤ rho * (N : ℝ) := by
    dsimp [n]
    exact Nat.floor_le (by positivity)
  have hndenseUpper : rho * (N : ℝ) < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one _
  have hmap : ∀ a ∈ S, g a ∈ Finset.range K := by
    intro a ha
    have hfa := hf a ha
    have hfnonneg : 0 ≤ f a := by omega
    have hcast : ((f a).toNat : ℤ) = f a := Int.toNat_of_nonneg hfnonneg
    have hnatpos : 1 ≤ (f a).toNat := by exact_mod_cast hcast.symm ▸ hfa.1
    have hnatcast : ((f a).toNat : ℝ) = (f a : ℝ) := by exact_mod_cast hcast
    have hnatle : (f a).toNat ≤ K := by
      change (f a).toNat ≤ Nat.floor B
      exact Nat.le_floor (by rw [hnatcast]; exact hfa.2)
    dsimp [g]
    simp only [Finset.mem_range]
    omega
  have hprod : K * n < S.card := by
    have hmul : (K : ℝ) * (n : ℝ) ≤ B * (rho * (N : ℝ)) :=
      mul_le_mul hKle hnle (by positivity) (by positivity)
    have hfactor : B * (rho * (N : ℝ)) = η * (N : ℝ) / 8 := by
      dsimp [rho]
      field_simp [ne_of_gt (show 0 < B by linarith)]
    have hNscaled : η * (N : ℝ) / 8 ≤ 3 * η * A / 8 := by
      have := mul_le_mul_of_nonneg_left hNupper (show 0 ≤ η / 8 by positivity)
      nlinarith
    have hstrict : 3 * η * A / 8 < η * A := by nlinarith [mul_pos hη hA]
    have hcardReal : (K : ℝ) * (n : ℝ) < (S.card : ℝ) := by
      calc
        (K : ℝ) * (n : ℝ) ≤ B * (rho * (N : ℝ)) := hmul
        _ = η * (N : ℝ) / 8 := hfactor
        _ ≤ 3 * η * A / 8 := hNscaled
        _ < η * A := hstrict
        _ ≤ (S.card : ℝ) := hScard
    exact_mod_cast hcardReal
  have hprod' : (Finset.range K).card * n < S.card := by simpa using hprod
  obtain ⟨y, hy, hyfiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := S) (t := Finset.range K) (f := g) (n := n) hmap hprod'
  let S' : Finset ℕ := S.filter (fun a => g a = y)
  have hS'sub : S' ⊆ S := Finset.filter_subset _ _
  have hycard : n < S'.card := by
    simpa [S'] using hyfiber
  have hS'dense : rho * (N : ℝ) ≤ (S'.card : ℝ) := by
    have hsucc : (n : ℝ) + 1 ≤ (S'.card : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hycard
    exact (le_of_lt hndenseUpper).trans hsucc
  let r₀ : ℤ := (y + 1 : ℕ)
  have hr₀pos : 1 ≤ r₀ := by dsimp [r₀]; omega
  have hr₀B : (r₀ : ℝ) ≤ B := by
    have hyK : y < K := Finset.mem_range.mp hy
    have hy1 : y + 1 ≤ K := by omega
    dsimp [r₀] at *
    exact (Nat.cast_le.mpr hy1).trans hKle
  have hcommon : ∀ a ∈ S', f a = r₀ := by
    intro a ha
    have haS : a ∈ S := hS'sub ha
    have hga : g a = y := (Finset.mem_filter.mp ha).2
    have hfa := hf a haS
    have hfnonneg : 0 ≤ f a := by omega
    have hcast : ((f a).toNat : ℤ) = f a := Int.toNat_of_nonneg hfnonneg
    have hnatpos : 1 ≤ (f a).toNat := by exact_mod_cast hcast.symm ▸ hfa.1
    have hnatEq : (f a).toNat = y + 1 := by
      dsimp [g] at hga
      omega
    dsimp [r₀]
    rw [← hcast, hnatEq]
    norm_num
  refine ⟨r₀, S', hS'sub, hcommon, hr₀pos, hr₀B, ?_⟩
  simpa [rho] using hS'dense

/-- Concatenate the local scalar denominators on a dense family of dilates. -/
theorem concatenateDilatedPhases
    {d : ℕ} (hd : 1 ≤ d)
    {A H X B η : ℝ}
    (hA : 1 / 2 ≤ A) (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hη : 0 < η) (hηhalf : η < 1 / 2)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (S : Finset ℕ)
    (hSbounds : ∀ a ∈ S, A < (a : ℝ) ∧ (a : ℝ) ≤ 2 * A)
    (hScard : η * A ≤ (S.card : ℝ))
    (hdata : ∀ a ∈ S, ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ B ∧
      ∀ j, 1 ≤ j → j ≤ d →
        (H / (a : ℝ)) ^ j * realDistanceToIntegers
          ((r : ℝ) * (phaseDilatedAt P a
            (Int.floor (X / (a : ℝ)))).coeff j) ≤ B) :
    H ≤ inverseBoundV d B η⁻¹ * A ∨
      ∃ r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ inverseBoundV d B η⁻¹ ∧
        ∀ j, 1 ≤ j → j ≤ d →
          H ^ j * realDistanceToIntegers
            ((r : ℝ) * (phaseCenteredAt P (Int.floor X)).coeff j) ≤
              inverseBoundV d B η⁻¹ := by
  classical
  have hApos : 0 < A := by linarith
  have hSnonempty : S.Nonempty := by
    have hcardpos : 0 < (S.card : ℝ) :=
      lt_of_lt_of_le (mul_pos hη hApos) hScard
    have hcardpos' : 0 < S.card := by exact_mod_cast hcardpos
    exact Finset.card_pos.mp hcardpos'
  by_cases hshort : H ≤ inverseBoundV d B η⁻¹ * A
  · exact Or.inl hshort
  · have hlarge : inverseBoundV d B η⁻¹ * A < H := lt_of_not_ge hshort
    by_cases hAsmall : A < inverseBoundAZero d B η⁻¹
    · exact Or.inr (dilation_smallA_conclusion hd hA hH hB hη hηhalf
        hAsmall hlarge P hP S hSnonempty hSbounds hdata)
    · have hAlarge : inverseBoundAZero d B η⁻¹ ≤ A := le_of_not_gt hAsmall
      have hy2 : 2 ≤ η⁻¹ := by
        rw [← one_div]
        exact (le_div_iff₀ hη).2 (by nlinarith [hηhalf])
      have hA0four : 4 ≤ inverseBoundAZero d B η⁻¹ :=
        inverseBoundAZero_ge_four d B η⁻¹ hB hy2
      have hA4 : 4 ≤ A := le_trans hA0four hAlarge
      let m : ℕ := Nat.floor A
      let N : ℕ := Nat.floor (2 * A) - Nat.floor A
      have hfloor := floor_interval_bounds A hA4
      have hmpos : 1 ≤ m := by simpa [m] using hfloor.1
      have hNpos : 1 ≤ N := by simpa [N, m] using hfloor.2.1
      have hNlower : A / 2 ≤ (N : ℝ) := by
        simpa [N, m] using hfloor.2.2.1
      have hNupper0 : (N : ℝ) ≤ A + 1 := by
        simpa [N, m] using hfloor.2.2.2
      have hNupper : (N : ℝ) ≤ 3 * A := by
        nlinarith [hNupper0, hA]
      have hNlarge : inverseBoundAggregateT d B η⁻¹ ≤ (N : ℝ) := by
        rw [inverseBoundAZero_eval] at hAlarge
        have hTA : inverseBoundAggregateT d B η⁻¹ ≤ A / 2 := by
          nlinarith
        exact hTA.trans hNlower
      let rfun : ℕ → ℤ := fun a =>
        if ha : a ∈ S then Classical.choose (hdata a ha) else 1
      have hrfun : ∀ a ∈ S, 1 ≤ rfun a ∧ (rfun a : ℝ) ≤ B := by
        intro a ha
        have hchoose := Classical.choose_spec (hdata a ha)
        exact ⟨by simpa [rfun, ha] using hchoose.1,
          by simpa [rfun, ha] using hchoose.2.1⟩
      obtain ⟨r₀, S', hS'sub, hcommon, hr₀pos, hr₀B, hS'dense⟩ :=
        exists_large_common_dilation (S := S) A B η N hApos hB hη hηhalf
          hScard hNupper rfun hrfun
      have hS'bounds : ∀ a ∈ S', A < (a : ℝ) ∧ (a : ℝ) ≤ 2 * A := by
        intro a ha
        exact hSbounds a (hS'sub ha)
      have hmle : (m : ℝ) ≤ A := by
        dsimp [m]
        exact Nat.floor_le (by linarith [hA4])
      have hmq : m ≤ Nat.floor (2 * A) := by
        apply Nat.le_floor
        calc
          (m : ℝ) ≤ A := hmle
          _ ≤ 2 * A := by linarith [hA4]
      have hmqeq : m + N = Nat.floor (2 * A) := by
        dsimp [N]
        exact Nat.add_sub_of_le hmq
      have hS'interval : ∀ a ∈ S', m < a ∧ a ≤ m + N := by
        intro a ha
        have haBounds := hS'bounds a ha
        have hamReal : (m : ℝ) < (a : ℝ) := lt_of_le_of_lt hmle haBounds.1
        have ham : m < a := by exact_mod_cast hamReal
        have haq : a ≤ Nat.floor (2 * A) := Nat.le_floor haBounds.2
        constructor
        · exact ham
        · omega
      let alpha : Polynomial ℝ := phaseCenteredAt P (Int.floor X)
      have hlocal₀ : ∀ a ∈ S', ∀ j, 1 ≤ j → j ≤ d →
          (H / (a : ℝ)) ^ j * realDistanceToIntegers
            ((r₀ : ℝ) * (phaseDilatedAt P a
              (Int.floor (X / (a : ℝ)))).coeff j) ≤ B := by
        intro a ha j hj hjd
        have haS : a ∈ S := hS'sub ha
        have hchoose := Classical.choose_spec (hdata a haS)
        have hraEq : Classical.choose (hdata a haS) = r₀ := by
          have h := hcommon a ha
          simpa [rfun, haS] using h
        rw [← hraEq]
        exact hchoose.2.2 j hj hjd
      have hdesc : ∀ k : ℕ, k ≤ d →
          ∃ v : ℕ, 1 ≤ v ∧
            (r₀ : ℝ) * (v : ℝ) ≤ inverseBoundU d k B η⁻¹ ∧
            ∀ j, d - k < j → j ≤ d →
              H ^ j * realDistanceToIntegers
                (((r₀ : ℝ) * (v : ℝ)) * alpha.coeff j) ≤
                  inverseBoundU d k B η⁻¹ := by
        intro k
        induction k with
        | zero =>
            intro hk
            refine ⟨1, by norm_num, ?_, ?_⟩
            · simpa using hr₀B
            · intro j hj hjd
              omega
        | succ k ih =>
            intro hk
            obtain ⟨v, hvpos, hvbound, hvhigh⟩ := ih (by omega)
            let l : ℕ := d - k
            have hdk : d - k = l := rfl
            have hl : 1 ≤ l := by dsimp [l]; omega
            have hld : l ≤ d := by dsimp [l]; omega
            obtain ⟨u, huPos, huR, huDenom, huHigh⟩ :=
              largeA_dilation_degree_step hd hdk hl hld hA4 hB hη hηhalf
                hlarge P hP hNpos hNlower hNlarge S' hS'dense hS'bounds
                hS'interval r₀ hr₀pos hr₀B hlocal₀ v hvpos hvbound
                (fun j hj hjd => hvhigh j (by simpa [l] using hj) hjd)
            have hv0 : 0 < v := by omega
            have hu0 : 0 < u := by omega
            refine ⟨v * u, Nat.succ_le_of_lt (Nat.mul_pos hv0 hu0), ?_, ?_⟩
            · simpa using huDenom
            · simpa [alpha] using huHigh
      obtain ⟨v, hvpos, hvbound, hvhigh⟩ := hdesc d le_rfl
      have hUge : 1 ≤ inverseBoundU d d B η⁻¹ :=
        inverseBoundU_ge_one d hd B η⁻¹ hB hy2 d
      have hA0nonneg : 0 ≤ inverseBoundAZero d B η⁻¹ := by
        have h := inverseBoundAZero_ge_four d B η⁻¹ hB hy2
        linarith
      have hDnonneg : 0 ≤ (inverseBoundDValue d : ℝ) := by positivity
      have hVterm1 : 0 ≤ 1024 * (inverseBoundDValue d : ℝ) * B * η⁻¹ *
          (inverseBoundU d d B η⁻¹) ^ 2 := by positivity
      have hVterm2 : 0 ≤ (2 : ℝ) ^ (d + 1) * B *
          (2 * inverseBoundAZero d B η⁻¹) ^ d := by
        exact mul_nonneg
          (mul_nonneg (by positivity) (by linarith [hB]))
          (pow_nonneg (mul_nonneg (by norm_num) hA0nonneg) d)
      have hUleV : inverseBoundU d d B η⁻¹ ≤ inverseBoundV d B η⁻¹ := by
        rw [inverseBoundV_eval]
        nlinarith [hVterm1, hVterm2]
      let rOut : ℤ := r₀ * (v : ℤ)
      have hrOutCast : (rOut : ℝ) = (r₀ : ℝ) * (v : ℝ) := by
        dsimp [rOut]
        push_cast
        ring
      have hrOutPosReal : 0 < (rOut : ℝ) := by
        rw [hrOutCast]
        exact mul_pos (by exact_mod_cast (show 0 < r₀ by omega))
          (by exact_mod_cast hvpos)
      have hrOutPos : 1 ≤ rOut := by
        have hpos : 0 < rOut := by exact_mod_cast hrOutPosReal
        omega
      refine Or.inr ⟨rOut, hrOutPos, ?_, ?_⟩
      · rw [hrOutCast]
        exact hvbound.trans hUleV
      · intro j hj hjd
        calc
          H ^ j * realDistanceToIntegers
              ((rOut : ℝ) * alpha.coeff j) =
            H ^ j * realDistanceToIntegers
              (((r₀ : ℝ) * (v : ℝ)) * alpha.coeff j) := by rw [hrOutCast]
          _ ≤ inverseBoundU d d B η⁻¹ := hvhigh j (by omega) hjd
          _ ≤ inverseBoundV d B η⁻¹ := hUleV

end FractionalPrimes.Literature.Polynomial
