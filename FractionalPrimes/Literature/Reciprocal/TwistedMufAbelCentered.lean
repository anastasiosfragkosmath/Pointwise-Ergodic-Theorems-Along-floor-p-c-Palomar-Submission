module

public import FractionalPrimes.Literature.Reciprocal.TwistedMufAbelSummation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

noncomputable section

open Finset MeasureTheory Set

namespace FractionalPrimes.Literature.Reciprocal

private theorem sum_cutoff_gt_eq_sub {m n : ℕ} (hmn : m ≤ n) (c : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 0 n, (if m < k then c k else 0)) =
      (∑ k ∈ Finset.Icc 0 n, c k) - ∑ k ∈ Finset.Icc 0 m, c k := by
  have hfilter :
      (∑ k ∈ Finset.Icc 0 n, (if m < k then c k else 0)) =
        ∑ k ∈ Finset.Ioc m n, c k := by
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdecomp : Finset.Icc 0 n = Finset.Icc 0 m ∪ Finset.Ioc m n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 0 m) (Finset.Ioc m n) := by
    apply Finset.disjoint_left.mpr
    intro k hk₁ hk₂
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk₁ hk₂
    omega
  have hsplit :
      (∑ k ∈ Finset.Icc 0 n, c k) =
        (∑ k ∈ Finset.Icc 0 m, c k) + ∑ k ∈ Finset.Ioc m n, c k := by
    rw [hdecomp, Finset.sum_union hdisj]
  rw [hfilter, hsplit]
  abel

private theorem twistedMufPrefix_shifted_eq (a : ℕ → ℂ) {u x : ℝ}
    (hux : u ≤ x) :
    twistedMufPrefix (fun k => if Nat.floor u < k then a k else 0) x =
      twistedMufPrefix a x - twistedMufPrefix a u := by
  let m := Nat.floor u
  let n := Nat.floor x
  let c : ℕ → ℂ := fun k => if k = 0 then 0 else a k
  have hmn : m ≤ n := by
    dsimp [m, n]
    exact Nat.floor_mono hux
  have hpoint (k : ℕ) :
      (if k = 0 then 0 else if m < k then a k else 0) =
        if m < k then c k else 0 := by
    by_cases hk : k = 0
    · subst k
      simp [c]
    · simp [c, hk]
  calc
    twistedMufPrefix (fun k => if Nat.floor u < k then a k else 0) x =
        ∑ k ∈ Finset.Icc 0 n, (if m < k then c k else 0) := by
          simp only [twistedMufPrefix, n]
          apply Finset.sum_congr rfl
          intro k hk
          simpa [m, c] using hpoint k
    _ = (∑ k ∈ Finset.Icc 0 n, c k) - ∑ k ∈ Finset.Icc 0 m, c k :=
          sum_cutoff_gt_eq_sub hmn c
    _ = twistedMufPrefix a x - twistedMufPrefix a u := by
          rfl

private theorem inverseSqrtWeight_hasDerivAt (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt inverseSqrtWeight
      (((-1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) : ℝ) : ℂ) t := by
  convert (Real.hasDerivAt_rpow_const (p := (-1 / 2 : ℝ)) (Or.inl ht)).ofReal_comp
    using 1
  congr 1
  rw [show (-1 / 2 : ℝ) - 1 = -3 / 2 by ring]

private theorem deriv_inverseSqrtWeight (t : ℝ) (ht : t ≠ 0) :
    deriv inverseSqrtWeight t =
      (((-1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) : ℝ) : ℂ) :=
  (inverseSqrtWeight_hasDerivAt t ht).deriv

/-- Exact evaluation of the positive power kernel appearing in endpoint
subtraction for `lrc:muf`. -/
theorem intervalIntegral_rpow_neg_three_halves {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    (∫ z in u..v, z ^ (-3 / 2 : ℝ)) =
      2 * (u ^ (-1 / 2 : ℝ) - v ^ (-1 / 2 : ℝ)) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc u v := by
    rw [Set.uIcc_of_le huv]
    simp only [Set.mem_Icc, not_and]
    intro hu0
    linarith
  rw [integral_rpow (r := (-3 / 2 : ℝ)) (Or.inr ⟨by norm_num, hzero⟩)]
  have hexp : (-3 / 2 : ℝ) + 1 = -1 / 2 := by ring
  rw [hexp]
  ring

/-- Abel summation after subtracting the initial prefix. This is the endpoint-
subtraction form used in the proof of `lrc:muf`. -/
theorem twistedMufAbelSummation_centered (a : ℕ → ℂ) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    (∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
        a n * inverseSqrtWeight (n : ℝ)) =
      inverseSqrtWeight v *
          (twistedMufPrefix a v - twistedMufPrefix a u) -
        ∫ z in Set.Ioc u v,
          deriv inverseSqrtWeight z *
            (twistedMufPrefix a z - twistedMufPrefix a u) := by
  let b : ℕ → ℂ := fun n => if Nat.floor u < n then a n else 0
  have hsum :
      (∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
          a n * inverseSqrtWeight (n : ℝ)) =
        ∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
          b n * inverseSqrtWeight (n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := (Finset.mem_Ioc.mp hn).1
    simp [b, hn']
  have hprefixV :
      twistedMufPrefix b v = twistedMufPrefix a v - twistedMufPrefix a u :=
    twistedMufPrefix_shifted_eq a huv
  have hprefixU : twistedMufPrefix b u = 0 := by
    rw [twistedMufPrefix_shifted_eq a le_rfl]
    ring
  have hintegral :
      (∫ z in Set.Ioc u v, deriv inverseSqrtWeight z * twistedMufPrefix b z) =
        ∫ z in Set.Ioc u v,
          deriv inverseSqrtWeight z *
            (twistedMufPrefix a z - twistedMufPrefix a u) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    change deriv inverseSqrtWeight z *
        twistedMufPrefix (fun k => if Nat.floor u < k then a k else 0) z = _
    rw [twistedMufPrefix_shifted_eq a (le_of_lt hz.1)]
  have habel := twistedMufAbelSummation b hu huv
  rw [← hsum, hprefixV, hprefixU, hintegral] at habel
  simpa only [mul_zero, sub_zero] using habel

/-- The centered Abel identity with the explicit derivative of `x⁻¹ᐟ²`, in
the exact half-open endpoint convention used for `lrc:muf`. -/
theorem twistedMufAbelSummation_explicit (a : ℕ → ℂ) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    (∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v),
        a n * inverseSqrtWeight (n : ℝ)) =
      inverseSqrtWeight v *
          (twistedMufPrefix a v - twistedMufPrefix a u) +
        (1 / 2 : ℂ) *
          ∫ z in Set.Ioc u v,
            (twistedMufPrefix a z - twistedMufPrefix a u) *
              (((z ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) := by
  rw [twistedMufAbelSummation_centered a hu huv]
  have hintegral :
      (∫ z in Set.Ioc u v,
          deriv inverseSqrtWeight z *
            (twistedMufPrefix a z - twistedMufPrefix a u)) =
        (-1 / 2 : ℂ) *
          ∫ z in Set.Ioc u v,
            (twistedMufPrefix a z - twistedMufPrefix a u) *
              (((z ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) := by
    calc
      _ = ∫ z in Set.Ioc u v,
            (-1 / 2 : ℂ) *
              ((twistedMufPrefix a z - twistedMufPrefix a u) *
                (((z ^ (-3 / 2 : ℝ) : ℝ) : ℂ))) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro z hz
          calc
            deriv inverseSqrtWeight z *
                (twistedMufPrefix a z - twistedMufPrefix a u) =
              (((-1 / 2 : ℝ) * z ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
                (twistedMufPrefix a z - twistedMufPrefix a u) := by
                  rw [deriv_inverseSqrtWeight z (ne_of_gt (lt_trans hu hz.1))]
            _ = (-1 / 2 : ℂ) *
                ((twistedMufPrefix a z - twistedMufPrefix a u) *
                  (((z ^ (-3 / 2 : ℝ) : ℝ) : ℂ))) := by
                  push_cast
                  ring
      _ = _ := by
        exact integral_const_mul (-1 / 2 : ℂ) _
  rw [hintegral]
  ring

#print axioms twistedMufAbelSummation_centered
#print axioms twistedMufAbelSummation_explicit
#print axioms intervalIntegral_rpow_neg_three_halves

end FractionalPrimes.Literature.Reciprocal

end
