module

public import FractionalPrimes.Literature.Multiplier.DyadicKernelAbsoluteReconstruction
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The discrete Hörmander kernel estimate

This module follows `lp:hormander` in the approved blueprint and the proof
in `blueprint-sources 2/literature-expansion/sections/multiplier.tex`.
The kernel is reconstructed from its base part and the absolutely summable
dyadic pieces in the preceding checked module.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open MeasureTheory
open scoped FourierTransform

noncomputable section

private theorem summable_prodComm_iff {α β : Type*} (f : α × β → ℝ) :
    Summable (fun z : β × α => f (Equiv.prodComm β α z)) ↔ Summable f := by
  exact (Equiv.prodComm β α).summable_iff (f := f)

private theorem tsum_comm_prod {α β : Type*} (f : α × β → ℝ)
    (hf : Summable f) :
    (∑' a : α, ∑' b : β, f (a, b)) =
      ∑' b : β, ∑' a : α, f (a, b) := by
  simpa [Function.uncurry_def] using
    (hf.tsum_comm (f := fun a b => f (a, b))).symm

/-- The dyadic kernel piece is differentiable on the whole real line. -/
theorem dyadicKernelPiece_differentiable {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    Differentiable ℝ (dyadicKernelPiece h j) := by
  let f : ℝ → ℂ := dyadicSymbolPiece h j
  have hf : Integrable f := by
    simpa [f] using dyadicSymbolPiece_iteratedDeriv_integrable h j 0 (by norm_num)
  have hfweighted : Integrable (fun ξ : ℝ => ξ • f ξ) := by
    have hweight : (fun ξ : ℝ => ξ • f ξ) = dyadicKernelWeightedInput h j := by
      funext ξ
      change ξ • dyadicSymbolPiece h j ξ =
        (ξ : ℂ) * dyadicSymbolPiece h j ξ
      rw [Complex.real_smul]
    rw [hweight]
    exact dyadicKernelWeightedInput_integrable h j
  have hfweightedNorm : Integrable (fun ξ : ℝ => ‖ξ‖ * ‖f ξ‖) := by
    have hnorm := hfweighted.norm
    convert hnorm using 1
    ext ξ
    rw [norm_smul]
  have hFourier : Differentiable ℝ (fun x : ℝ => 𝓕 f x) :=
    Real.differentiable_fourier hf hfweightedNorm
  have hkernel : dyadicKernelPiece h j = fun x : ℝ => 𝓕 f (-x) := by
    funext x
    simpa [f] using dyadicKernelPiece_eq_fourier_neg h j x
  rw [hkernel]
  exact hFourier.comp differentiable_neg

/-- Pointwise derivative-based shift estimate on the strict Hörmander tail.
The real interval between `n-h` and `n` stays outside radius `|n|/2`.
-/
theorem dyadicKernelPiece_shift_difference_pointwise_bound
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (j : ℕ)
    (shift n : ℤ) (htail : 2 * |shift| < |n|) :
    ‖dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
        dyadicKernelPiece h j (n : ℝ)‖ ≤
      A * D * |(shift : ℝ)| * dyadicScale j ^ 2 /
        (1 + dyadicScale j * |(n : ℝ)| / 2) ^ 2 := by
  let x : ℝ := (n : ℝ)
  let y : ℝ := ((n - shift : ℤ) : ℝ)
  let t : ℝ := dyadicScale j
  let u : ℝ := |(shift : ℝ)|
  have ht : 0 < t := by dsimp [t]; exact dyadicScale_pos j
  have hu : 0 ≤ u := abs_nonneg _
  have htailR : 2 * u < |x| := by
    dsimp [u, x]
    exact_mod_cast htail
  have hyx : |y - x| = u := by
    dsimp [y, x, u]
    simp [Int.cast_sub, sub_eq_add_neg, abs_neg]
  have hs : Convex ℝ (Set.uIcc x y) := convex_uIcc x y
  have hderiv (z : ℝ) (hz : z ∈ Set.uIcc x y) :
      ‖deriv (dyadicKernelPiece h j) z‖ ≤
        A * D * t ^ 2 / (1 + t * |x| / 2) ^ 2 := by
    have hzSeg : z ∈ segment ℝ x y := by
      simpa [segment_eq_uIcc] using hz
    have hdist : ‖z - x‖ ≤ ‖y - x‖ := norm_sub_le_of_mem_segment hzSeg
    have hdist' : |z - x| ≤ u := by
      simpa [Real.norm_eq_abs, hyx] using hdist
    have htriangle : |x| ≤ |z| + |z - x| := by
      calc
        |x| = |z + (x - z)| := by congr 1 <;> ring
        _ ≤ |z| + |x - z| := abs_add_le _ _
        _ = |z| + |z - x| := by rw [abs_sub_comm]
    have hzlower : |x| / 2 ≤ |z| := by
      linarith
    have hden : 1 + t * |x| / 2 ≤ 1 + t * |z| := by
      nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hzlower)]
    have hnum : 0 ≤ A * D * t ^ 2 := by
      have hA : 0 ≤ A := by
        rw [A_eq]
        exact mul_nonneg (by positivity) (le_of_lt B_pos)
      exact mul_nonneg (mul_nonneg hA h.D_nonneg) (sq_nonneg t)
    have hdenSq : (1 + t * |x| / 2) ^ 2 ≤ (1 + t * |z|) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hden
    have hbound := dyadicKernelPiece_deriv_pointwise_bound h j z
    change ‖deriv (dyadicKernelPiece h j) z‖ ≤
      A * D * t ^ 2 / (1 + t * |z|) ^ 2 at hbound
    calc
      ‖deriv (dyadicKernelPiece h j) z‖ ≤
          A * D * t ^ 2 / (1 + t * |z|) ^ 2 := hbound
      _ ≤ A * D * t ^ 2 / (1 + t * |x| / 2) ^ 2 := by
        apply div_le_div_of_nonneg_left hnum (by positivity)
        exact hdenSq
  have hmean :
      ‖dyadicKernelPiece h j y - dyadicKernelPiece h j x‖ ≤
        (A * D * t ^ 2 / (1 + t * |x| / 2) ^ 2) * ‖y - x‖ :=
    hs.norm_image_sub_le_of_norm_deriv_le
      (fun z _ => dyadicKernelPiece_differentiable h j z)
      hderiv Set.left_mem_uIcc Set.right_mem_uIcc
  change ‖dyadicKernelPiece h j y - dyadicKernelPiece h j x‖ ≤
    A * D * u * t ^ 2 / (1 + t * |x| / 2) ^ 2
  calc
    ‖dyadicKernelPiece h j y - dyadicKernelPiece h j x‖ ≤
        (A * D * t ^ 2 / (1 + t * |x| / 2) ^ 2) * u := by
          simpa [Real.norm_eq_abs, hyx] using hmean
    _ = A * D * u * t ^ 2 / (1 + t * |x| / 2) ^ 2 := by ring
    _ = A * D * |(shift : ℝ)| * dyadicScale j ^ 2 /
          (1 + dyadicScale j * |(n : ℝ)| / 2) ^ 2 := by
          simp [x, t, u]

/-- A reciprocal-square tail estimate used to sum the dyadic kernel bounds.
This is the shifted form of Mathlib's finite reciprocal-square comparison. -/
private theorem tsum_nat_shifted_inv_sq_le {a : ℕ} (ha : a ≠ 0) :
    (∑' k : ℕ, 1 / ((a + k + 1 : ℝ) ^ 2)) ≤ 1 / (a : ℝ) := by
  have haPos : 0 < (a : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha
  apply Real.tsum_le_of_sum_range_le (c := 1 / (a : ℝ)) (fun _ => by positivity)
  intro N
  have hfinite :
      (∑ k ∈ Finset.range N, 1 / ((a + k + 1 : ℝ) ^ 2)) =
        ∑ k ∈ Finset.Ioc a (a + N), 1 / ((k : ℝ) ^ 2) := by
    apply Finset.sum_bij (fun k _ => a + k + 1)
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ioc]
      omega
    · intro k hk l hl hkl
      omega
    · intro k hk
      simp only [Finset.mem_Ioc] at hk
      refine ⟨k - a - 1, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro k hk
      push_cast
      rfl
  have hIoc := sum_Ioc_inv_sq_le_sub (α := ℝ) ha (Nat.le_add_right a N)
  have hsumle :
      (∑ k ∈ Finset.range N, 1 / ((a + k + 1 : ℝ) ^ 2)) ≤
        1 / (a : ℝ) - 1 / ((a + N : ℕ) : ℝ) := by
    rw [hfinite]
    simpa only [one_div] using hIoc
  have hlast : 0 ≤ 1 / ((a + N : ℕ) : ℝ) := by positivity
  linarith

/-- The scaled shifted reciprocal-square tail estimate used after the dyadic
weight is written with an integer denominator. -/
private theorem tsum_nat_scaled_shifted_inv_sq_le {a c : ℕ} (ha : a ≠ 0) :
    (∑' k : ℕ, (c : ℝ) ^ 2 / ((a + k + 1 : ℝ) ^ 2)) ≤
      (c : ℝ) ^ 2 / (a : ℝ) := by
  have hs : Summable (fun k : ℕ => 1 / ((a + k + 1 : ℝ) ^ 2)) := by
    have hp :=
      (Real.summable_one_div_nat_add_rpow ((a : ℝ) + 1) 2).2 (by norm_num)
    have hnorm (k : ℕ) :
        |(k : ℝ) + ((a : ℝ) + 1)| = (a + k + 1 : ℝ) := by
      rw [abs_of_nonneg]
      · push_cast
        ring
      · positivity
    have htwo : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    simpa only [hnorm, htwo, Real.rpow_natCast] using hp
  have hsum := tsum_nat_shifted_inv_sq_le ha
  calc
    (∑' k : ℕ, (c : ℝ) ^ 2 / ((a + k + 1 : ℝ) ^ 2)) =
        (c : ℝ) ^ 2 * ∑' k : ℕ, 1 / ((a + k + 1 : ℝ) ^ 2) := by
      simpa only [div_eq_mul_inv, one_mul] using
        hs.tsum_mul_left ((c : ℝ) ^ 2)
    _ ≤ (c : ℝ) ^ 2 * (1 / (a : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg (c : ℝ))
    _ = (c : ℝ) ^ 2 / (a : ℝ) := by
      simp only [div_eq_mul_inv, one_mul]

private def dyadicKernelWeight (j : ℕ) (n : ℤ) : ℝ :=
  1 / (1 + dyadicScale j * |(n : ℝ)| / 2) ^ 2

private theorem dyadicScale_mul_two_pow_succ (j : ℕ) :
    dyadicScale j * (2 : ℝ) ^ (j + 1) = 2 := by
  rw [dyadicScale, pow_succ]
  have hpow : (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (1 / 2 : ℝ) ^ j * ((2 : ℝ) ^ j * 2) =
        ((1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j) * 2 := by ring
    _ = 2 := by rw [hpow]; norm_num

/-- The dyadic denominator is an integer-shifted reciprocal-square weight. -/
private theorem dyadicKernelWeight_eq_scaled (j : ℕ) (n : ℤ) :
    dyadicKernelWeight j n =
      ((2 : ℝ) ^ (j + 1)) ^ 2 /
        ((2 : ℝ) ^ (j + 1) + |(n : ℝ)|) ^ 2 := by
  let M : ℝ := (2 : ℝ) ^ (j + 1)
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hMt : M * dyadicScale j = 2 := by
    dsimp [M]
    rw [mul_comm]
    exact dyadicScale_mul_two_pow_succ j
  have hMt' : dyadicScale j * M = 2 := by rw [mul_comm]; exact hMt
  have hratio : dyadicScale j * |(n : ℝ)| / 2 = |(n : ℝ)| / M := by
    field_simp [ne_of_gt hMpos]
    linear_combination |(n : ℝ)| * hMt'
  have hden : 1 + |(n : ℝ)| / M =
      (M + |(n : ℝ)|) / M := by
    field_simp [ne_of_gt hMpos]
  rw [dyadicKernelWeight, hratio, hden]
  dsimp [M]
  field_simp [ne_of_gt hMpos,
    ne_of_gt (add_pos_of_pos_of_nonneg hMpos (abs_nonneg _))]
  <;> ring

/-- The all-integer dyadic weight is summable, with the source's exact `5/t`
bound. -/
private theorem dyadicKernelWeight_summable_and_all_tsum_le (j : ℕ) :
    Summable (fun n : ℤ => dyadicKernelWeight j n) ∧
      (∑' n : ℤ, dyadicKernelWeight j n) ≤ 5 / dyadicScale j := by
  let M : ℕ := 2 ^ (j + 1)
  have hMpos : 0 < (M : ℝ) := by positivity
  have hMcast : (M : ℝ) = (2 : ℝ) ^ (j + 1) := by simp [M]
  have htwo : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  have hbase : Summable
      (fun k : ℕ => 1 / |(k : ℝ) + (M : ℝ)| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow (M : ℝ) 2).2 (by norm_num)
  have hNatEq (k : ℕ) :
      dyadicKernelWeight j (k : ℤ) =
        (M : ℝ) ^ 2 * (1 / |(k : ℝ) + (M : ℝ)| ^ (2 : ℝ)) := by
    rw [dyadicKernelWeight_eq_scaled, hMcast, Int.cast_natCast,
      abs_of_nonneg (Nat.cast_nonneg k)]
    have hnorm : |(k : ℝ) + (2 : ℝ) ^ (j + 1)| =
        (2 : ℝ) ^ (j + 1) + (k : ℝ) := by
      rw [abs_of_nonneg]
      · ring
      · positivity
    rw [hnorm]
    have hrpow2 (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
      rw [htwo, Real.rpow_natCast]
    rw [hrpow2]
    simp only [div_eq_mul_inv, one_mul]
  have hNat : Summable (fun k : ℕ => dyadicKernelWeight j (k : ℤ)) := by
    have hEq : (fun k : ℕ => dyadicKernelWeight j (k : ℤ)) =
        fun k : ℕ => (M : ℝ) ^ 2 * (1 / |(k : ℝ) + (M : ℝ)| ^ (2 : ℝ)) := by
      funext k
      exact hNatEq k
    rw [hEq]
    exact hbase.mul_left ((M : ℝ) ^ 2)
  have hNatNeg : Summable
      (fun k : ℕ => dyadicKernelWeight j (-(k : ℤ))) := by
    have hEq : (fun k : ℕ => dyadicKernelWeight j (-(k : ℤ))) =
        fun k : ℕ => dyadicKernelWeight j (k : ℤ) := by
      funext k
      simp [dyadicKernelWeight]
    rw [hEq]
    exact hNat
  have hInt : Summable (fun n : ℤ => dyadicKernelWeight j n) :=
    Summable.of_nat_of_neg hNat hNatNeg
  have hpositiveTsum :
      (∑' n : ℕ+, dyadicKernelWeight j (n : ℤ)) =
        ∑' k : ℕ, (M : ℝ) ^ 2 / ((M + k + 1 : ℝ) ^ 2) := by
    rw [tsum_pnat_eq_tsum_succ
      (f := fun k : ℕ => dyadicKernelWeight j (k : ℤ))]
    apply tsum_congr
    intro k
    rw [dyadicKernelWeight_eq_scaled]
    have hcast : (((k + 1 : ℕ) : ℤ) : ℝ) = (k : ℝ) + 1 := by
      rw [Int.cast_natCast]
      norm_cast
    rw [hcast, abs_of_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity)]
    push_cast
    rw [hMcast]
    ring
  have hpositive :
      (∑' n : ℕ+, dyadicKernelWeight j (n : ℤ)) ≤ (M : ℝ) := by
    rw [hpositiveTsum]
    calc
      (∑' k : ℕ, (M : ℝ) ^ 2 / ((M + k + 1 : ℝ) ^ 2)) ≤
          (M : ℝ) ^ 2 / (M : ℝ) :=
        tsum_nat_scaled_shifted_inv_sq_le (a := M) (c := M) (by positivity)
      _ = (M : ℝ) := by field_simp [ne_of_gt hMpos]
  have hdecomp :
      (∑' n : ℤ, dyadicKernelWeight j n) =
        dyadicKernelWeight j 0 +
          2 * (∑' n : ℕ+, dyadicKernelWeight j (n : ℤ)) := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat]
    · ring
    · intro n
      simp [dyadicKernelWeight]
    · exact hInt
  have hzero : dyadicKernelWeight j 0 = 1 := by
    simp [dyadicKernelWeight]
  have hrough :
      (∑' n : ℤ, dyadicKernelWeight j n) ≤ 1 + 2 * (M : ℝ) := by
    rw [hdecomp, hzero]
    simpa only [add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_left hpositive (by norm_num : (0 : ℝ) ≤ 2)) 1
  have ht : 0 < dyadicScale j := dyadicScale_pos j
  have htle : dyadicScale j ≤ 1 := dyadicScale_le_one j
  have hMt : (M : ℝ) * dyadicScale j = 2 := by
    rw [hMcast, mul_comm]
    exact dyadicScale_mul_two_pow_succ j
  have hMvalue : (M : ℝ) = 2 / dyadicScale j := by
    field_simp [ne_of_gt ht]
    nlinarith [hMt]
  have hInv : 1 ≤ 1 / dyadicScale j := by
    rw [le_div_iff₀ ht]
    simpa using htle
  refine ⟨hInt, ?_⟩
  calc
    (∑' n : ℤ, dyadicKernelWeight j n) ≤ 1 + 2 * (M : ℝ) := hrough
    _ = 1 + 4 / dyadicScale j := by rw [hMvalue]; ring
    _ ≤ 5 / dyadicScale j := by
      rw [le_div_iff₀ ht]
      field_simp [ne_of_gt ht]
      nlinarith [htle]

/-- The strict integer tail of the dyadic weight, with the source's exact
`4 / (t * (1 + t*u))` bound. -/
private theorem dyadicKernelWeight_strict_tail_summable_and_tsum_le
    (j u : ℕ) :
    Summable (fun n : ℤ =>
      if 2 * (u : ℤ) < |n| then dyadicKernelWeight j n else 0) ∧
    (∑' n : ℤ,
      if 2 * (u : ℤ) < |n| then dyadicKernelWeight j n else 0) ≤
      4 / (dyadicScale j * (1 + dyadicScale j * (u : ℝ))) := by
  let tail : ℤ → ℝ := fun n =>
    if 2 * (u : ℤ) < |n| then dyadicKernelWeight j n else 0
  let N : ℕ := 2 * u
  let M : ℕ := 2 ^ (j + 1)
  have hAll := dyadicKernelWeight_summable_and_all_tsum_le j
  have hweight_nonneg (n : ℤ) : 0 ≤ dyadicKernelWeight j n := by
    unfold dyadicKernelWeight
    exact div_nonneg (by norm_num) (sq_nonneg _)
  have hweight_pos (n : ℤ) : 0 < dyadicKernelWeight j n := by
    unfold dyadicKernelWeight
    apply div_pos (by norm_num)
    exact sq_pos_of_pos (by positivity [dyadicScale_pos j])
  have htailSummable : Summable tail := by
    apply Summable.of_nonneg_of_le
    · intro n
      simp only [tail]
      split_ifs
      · exact hweight_nonneg n
      · norm_num
    · intro n
      dsimp [tail]
      split_ifs
      · exact le_rfl
      · exact le_of_lt (hweight_pos n)
    · exact hAll.1
  have hEven : tail.Even := by
    intro n
    simp [tail, dyadicKernelWeight, abs_neg]
  have hdecomp :
      (∑' n : ℤ, tail n) = tail 0 +
        2 * (∑' n : ℕ+, tail (n : ℤ)) := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat]
    · ring
    · exact hEven
    · exact htailSummable
  have hzero : tail 0 = 0 := by simp [tail]
  have hnatTail : Summable (fun k : ℕ => tail ((Nat.succ k : ℕ) : ℤ)) := by
    have hnat : Summable (fun k : ℕ => tail (k : ℤ)) :=
      htailSummable.comp_injective Nat.cast_injective
    exact hnat.comp_injective Nat.succ_injective
  have hinitial :
      (∑ k ∈ Finset.range N, tail ((Nat.succ k : ℕ) : ℤ)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have hkn : Nat.succ k ≤ N := Nat.succ_le_of_lt hkN
    have hknCast : ((Nat.succ k : ℕ) : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast hkn
    have hNCast : (N : ℤ) = 2 * (u : ℤ) := by simp [N]
    have hnot : ¬ 2 * (u : ℤ) < |((Nat.succ k : ℕ) : ℤ)| := by
      rw [abs_of_nonneg (by positivity : 0 ≤ ((Nat.succ k : ℕ) : ℤ))]
      have hknCast' : ((Nat.succ k : ℕ) : ℤ) ≤ 2 * (u : ℤ) := by
        simpa [hNCast] using hknCast
      omega
    change (if 2 * (u : ℤ) < |((Nat.succ k : ℕ) : ℤ)| then
      dyadicKernelWeight j ((Nat.succ k : ℕ) : ℤ) else 0) = 0
    rw [if_neg hnot]
  have hshift :
      (∑' k : ℕ, tail ((Nat.succ k : ℕ) : ℤ)) =
        ∑' k : ℕ, tail ((Nat.succ (k + N) : ℕ) : ℤ) := by
    have hsplit := hnatTail.sum_add_tsum_nat_add N
    have hsplit' :
        (∑' k : ℕ, tail ((Nat.succ k : ℕ) : ℤ)) =
          (∑ k ∈ Finset.range N, tail ((Nat.succ k : ℕ) : ℤ)) +
            ∑' k : ℕ, tail ((Nat.succ (k + N) : ℕ) : ℤ) := by
      simpa only [Int.natCast_succ] using hsplit.symm
    rw [hinitial] at hsplit'
    simpa using hsplit'
  have hstrict (k : ℕ) :
      2 * (u : ℤ) < |((Nat.succ (k + N) : ℕ) : ℤ)| := by
    rw [abs_of_nonneg (by positivity : 0 ≤ ((Nat.succ (k + N) : ℕ) : ℤ))]
    have hnat : N < Nat.succ (k + N) := by omega
    have hcast : (N : ℤ) < (Nat.succ (k + N) : ℤ) := by exact_mod_cast hnat
    have hNCast : (N : ℤ) = 2 * (u : ℤ) := by simp [N]
    rw [hNCast] at hcast
    exact hcast
  have hpositiveScaled :
      (∑' n : ℕ+, tail (n : ℤ)) =
        ∑' k : ℕ, (M : ℝ) ^ 2 / ((M + N + k + 1 : ℝ) ^ 2) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun k : ℕ => tail (k : ℤ))]
    calc
      (∑' k : ℕ, tail ((k + 1 : ℕ) : ℤ)) =
          ∑' k : ℕ, tail ((Nat.succ k : ℕ) : ℤ) := by rfl
      _ = ∑' k : ℕ, tail ((Nat.succ (k + N) : ℕ) : ℤ) := hshift
      _ = ∑' k : ℕ, (M : ℝ) ^ 2 / ((M + N + k + 1 : ℝ) ^ 2) := by
        apply tsum_congr
        intro k
        change (if 2 * (u : ℤ) < |((Nat.succ (k + N) : ℕ) : ℤ)| then
          dyadicKernelWeight j ((Nat.succ (k + N) : ℕ) : ℤ) else 0) = _
        rw [if_pos (hstrict k), dyadicKernelWeight_eq_scaled]
        have hcast : (((Nat.succ (k + N) : ℕ) : ℤ) : ℝ) =
            (k : ℝ) + (N : ℝ) + 1 := by
          rw [Int.cast_natCast]
          norm_cast
        rw [hcast, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + (N : ℝ) + 1)]
        have hMcast : (M : ℝ) = (2 : ℝ) ^ (j + 1) := by simp [M]
        rw [hMcast]
        <;> ring
  have hpositiveBound :
      (∑' n : ℕ+, tail (n : ℤ)) ≤
        (M : ℝ) ^ 2 / ((M + N : ℕ) : ℝ) := by
    rw [hpositiveScaled]
    have hMpos : 0 < M := by dsimp [M]; positivity
    simpa only [Nat.cast_add] using
      (tsum_nat_scaled_shifted_inv_sq_le (a := M + N) (c := M) (by omega))
  have ht : 0 < dyadicScale j := dyadicScale_pos j
  have hMcast : (M : ℝ) = (2 : ℝ) ^ (j + 1) := by simp [M]
  have hMt : (M : ℝ) * dyadicScale j = 2 := by
    rw [hMcast, mul_comm]
    exact dyadicScale_mul_two_pow_succ j
  have hMvalue : (M : ℝ) = 2 / dyadicScale j := by
    field_simp [ne_of_gt ht]
    nlinarith [hMt]
  have hNcast : (N : ℝ) = 2 * (u : ℝ) := by simp [N]
  have hden : (M : ℝ) + (N : ℝ) =
      2 * (1 + dyadicScale j * (u : ℝ)) / dyadicScale j := by
    rw [hMvalue, hNcast]
    field_simp [ne_of_gt ht]
    <;> ring
  have harith :
      2 * (M : ℝ) ^ 2 / ((M + N : ℕ) : ℝ) =
        4 / (dyadicScale j * (1 + dyadicScale j * (u : ℝ))) := by
    rw [Nat.cast_add, hden, hMvalue]
    field_simp [ne_of_gt ht,
      ne_of_gt (by positivity : 0 < 1 + dyadicScale j * (u : ℝ))]
    <;> ring
  have htotal :
      (∑' n : ℤ, tail n) ≤
        4 / (dyadicScale j * (1 + dyadicScale j * (u : ℝ))) := by
    calc
      (∑' n : ℤ, tail n) =
          2 * (∑' n : ℕ+, tail (n : ℤ)) := by rw [hdecomp, hzero]; ring
      _ ≤ 2 * ((M : ℝ) ^ 2 / ((M + N : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hpositiveBound (by norm_num)
      _ = 4 / (dyadicScale j * (1 + dyadicScale j * (u : ℝ))) := by
        simpa only [mul_div_assoc] using harith
  refine ⟨?_, ?_⟩
  · simpa [tail] using htailSummable
  · simpa [tail] using htotal

/-- Combines the two source estimates for one dyadic scale into the minimum
bound used by the geometric summation in `lp:hormander`. -/
private theorem per_scale_two_bounds_to_min
    {E C x : ℝ} (hC : 0 ≤ C) (hx : 0 < x)
    (hderiv : E ≤ 5 * C * x) (hkernel : E ≤ 8 * C / x) :
    E ≤ 12 * C * min x x⁻¹ := by
  by_cases hxle : x ≤ 1
  · have hmin : min x x⁻¹ = x :=
      min_eq_left (hxle.trans ((one_le_inv₀ hx).2 hxle))
    rw [hmin]
    nlinarith [hderiv, mul_nonneg hC hx.le]
  · have hxge : 1 ≤ x := le_of_not_ge hxle
    have hmin : min x x⁻¹ = x⁻¹ :=
      min_eq_right ((inv_le_one_of_one_le₀ hxge).trans hxge)
    rw [hmin]
    rw [div_eq_mul_inv] at hkernel
    nlinarith [hkernel, mul_nonneg hC (inv_nonneg.mpr hx.le)]

/-- The dyadic sum of the two competing scale bounds is strictly below four,
as used in the proof of `lp:hormander`. -/
private theorem dyadic_scale_min_tsum_lt_four (u : ℕ) (hu : 1 ≤ u) :
    (∑' j : ℕ,
      min ((u : ℝ) * dyadicScale j) (((u : ℝ) * dyadicScale j)⁻¹)) < 4 := by
  let k : ℕ := Nat.log2 u
  let r : ℝ := (u : ℝ) * dyadicScale k
  let F : ℕ → ℝ := fun j =>
    min ((u : ℝ) * dyadicScale j) (((u : ℝ) * dyadicScale j)⁻¹)
  have hu0 : u ≠ 0 := by omega
  have huR : 0 < (u : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hu0
  have hlogLowNat : 2 ^ k ≤ u := by
    exact Nat.log2_self_le hu0
  have hlogHighNat : u < 2 ^ (k + 1) := by
    simpa [k] using (Nat.lt_log2_self (n := u))
  have hlogLow : (2 : ℝ) ^ k ≤ (u : ℝ) := by exact_mod_cast hlogLowNat
  have hlogHigh : (u : ℝ) < (2 : ℝ) ^ (k + 1) := by exact_mod_cast hlogHighNat
  have hscalePow (n : ℕ) : dyadicScale n * (2 : ℝ) ^ n = 1 := by
    have h := dyadicScale_mul_two_pow_succ n
    rw [pow_succ] at h
    nlinarith [h]
  have hrLower : 1 ≤ r := by
    dsimp [r, k]
    calc
      1 = (2 : ℝ) ^ Nat.log2 u * dyadicScale (Nat.log2 u) := by
        rw [mul_comm, hscalePow]
      _ ≤ (u : ℝ) * dyadicScale (Nat.log2 u) :=
        mul_le_mul_of_nonneg_right hlogLow (dyadicScale_pos _).le
  have hrUpper : r < 2 := by
    dsimp [r, k]
    calc
      (u : ℝ) * dyadicScale (Nat.log2 u) <
          (2 : ℝ) ^ (Nat.log2 u + 1) * dyadicScale (Nat.log2 u) :=
        mul_lt_mul_of_pos_right hlogHigh (dyadicScale_pos _)
      _ = 2 := by
        rw [mul_comm]
        exact dyadicScale_mul_two_pow_succ (Nat.log2 u)
  have hscaleRatio (j : ℕ) (hjk : j ≤ k) :
      dyadicScale j = dyadicScale k * (2 : ℝ) ^ (k - j) := by
    have hkj : k = j + (k - j) := by omega
    have hexponent : j + (k - j) - j = k - j := by omega
    dsimp [dyadicScale]
    rw [hkj, pow_add, hexponent]
    calc
      (1 / 2 : ℝ) ^ j =
          (1 / 2 : ℝ) ^ j * ((1 / 2 : ℝ) * 2) ^ (k - j) := by simp
      _ = (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (k - j) * 2 ^ (k - j) := by
        rw [mul_pow]
        ring
  have hlowTerm (j : ℕ) (hjk : j ≤ k) :
      ((u : ℝ) * dyadicScale j)⁻¹ = r⁻¹ * (1 / 2 : ℝ) ^ (k - j) := by
    have hhalfPow (m : ℕ) : (1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    dsimp [r]
    rw [hscaleRatio j hjk]
    field_simp [ne_of_gt huR, ne_of_gt (dyadicScale_pos k)]
    simpa [mul_comm] using (hhalfPow (k - j)).symm
  have hgeomSum : Summable (fun j : ℕ => dyadicScale j) := by
    simpa [dyadicScale] using summable_geometric_two
  have hgeomTsum : (∑' j : ℕ, dyadicScale j) = 2 := by
    simpa [dyadicScale] using tsum_geometric_two
  have hscaleSummable : Summable (fun j : ℕ => (u : ℝ) * dyadicScale j) := by
    simpa [dyadicScale, mul_assoc] using
      summable_geometric_two.mul_left (u : ℝ)
  have hFSummable : Summable F := by
    apply Summable.of_nonneg_of_le
    · intro j
      dsimp [F]
      exact le_min (mul_nonneg (Nat.cast_nonneg _) (dyadicScale_pos j).le)
        (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (dyadicScale_pos j).le))
    · intro j
      dsimp [F]
      exact min_le_left _ _
    · exact hscaleSummable
  have hsplit := hFSummable.sum_add_tsum_nat_add (k + 1)
  have hdecomp :
      (∑' j : ℕ, F j) =
        (∑ j ∈ Finset.range (k + 1), F j) +
          ∑' m : ℕ, F (m + (k + 1)) := by
    simpa only [F] using hsplit.symm
  have hreverse :
      (∑ j ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ (k - j)) =
        ∑ j ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ j := by
    apply Finset.sum_bij (fun j _ => k - j)
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro j hj l hl hjl
      simp only [Finset.mem_range] at hj hl
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      refine ⟨k - j, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      rfl
  have hfinite : (∑ j ∈ Finset.range (k + 1), F j) ≤ 2 := by
    calc
      (∑ j ∈ Finset.range (k + 1), F j) ≤
          ∑ j ∈ Finset.range (k + 1), r⁻¹ * (1 / 2 : ℝ) ^ (k - j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j ≤ k := by
          simp only [Finset.mem_range] at hj
          omega
        calc
          F j ≤ ((u : ℝ) * dyadicScale j)⁻¹ := by
            dsimp [F]
            exact min_le_right _ _
          _ = r⁻¹ * (1 / 2 : ℝ) ^ (k - j) := hlowTerm j hjk
      _ = r⁻¹ * ∑ j ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ (k - j) := by
        rw [Finset.mul_sum]
      _ = r⁻¹ * ∑ j ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ j := by
        rw [hreverse]
      _ ≤ r⁻¹ * 2 := by
        exact mul_le_mul_of_nonneg_left (sum_geometric_two_le (k + 1)) (by positivity)
      _ ≤ 2 := by
        have hrInv : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hrLower
        have hrNonneg : 0 ≤ r := by linarith [hrLower]
        have hseriesNonneg :
            0 ≤ ∑ j ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ j := by
          apply Finset.sum_nonneg
          intro j hj
          exact pow_nonneg (by norm_num) j
        nlinarith [mul_nonneg (inv_nonneg.mpr hrNonneg)
          hseriesNonneg]
  have htailSummable : Summable (fun m : ℕ => F (m + (k + 1))) :=
    hFSummable.comp_injective (fun m n hmn => by omega)
  have htailMajorant :
      Summable (fun m : ℕ => ((u : ℝ) * dyadicScale (k + 1)) * dyadicScale m) := by
    simpa [dyadicScale, mul_assoc] using
      summable_geometric_two.mul_left ((u : ℝ) * dyadicScale (k + 1))
  have hscaleAdd (m : ℕ) :
      dyadicScale (m + (k + 1)) = dyadicScale (k + 1) * dyadicScale m := by
    dsimp [dyadicScale]
    rw [Nat.add_comm, pow_add]
  have htailPointwise (m : ℕ) :
      F (m + (k + 1)) ≤
        ((u : ℝ) * dyadicScale (k + 1)) * dyadicScale m := by
    dsimp [F]
    rw [hscaleAdd]
    calc
      min ((u : ℝ) * (dyadicScale (k + 1) * dyadicScale m))
          (((u : ℝ) * (dyadicScale (k + 1) * dyadicScale m))⁻¹) ≤
          (u : ℝ) * (dyadicScale (k + 1) * dyadicScale m) := min_le_left _ _
      _ = ((u : ℝ) * dyadicScale (k + 1)) * dyadicScale m :=
        (mul_assoc _ _ _).symm
  have htailCompare :=
    Summable.tsum_le_tsum htailPointwise htailSummable htailMajorant
  have htailTsum :
      (∑' m : ℕ, ((u : ℝ) * dyadicScale (k + 1)) * dyadicScale m) = r := by
    calc
      (∑' m : ℕ, ((u : ℝ) * dyadicScale (k + 1)) * dyadicScale m) =
          ((u : ℝ) * dyadicScale (k + 1)) * ∑' m : ℕ, dyadicScale m :=
        hgeomSum.tsum_mul_left ((u : ℝ) * dyadicScale (k + 1))
      _ = r := by rw [hgeomTsum, dyadicScale_succ]; dsimp [r]; ring
  have htail : (∑' m : ℕ, F (m + (k + 1))) ≤ r := by
    exact htailCompare.trans_eq htailTsum
  rw [hdecomp]
  linarith [hfinite, htail, hrUpper]

/-- Source-matched one-scale contribution on the strict tail. The derivative
bound gives `5 A D u t`; the two kernel bounds give `8 A D/(u t)`. -/
private theorem dyadicKernelPiece_strict_tail_difference_summable_bound
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (shift : ℤ) (u j : ℕ)
    (hshift : |shift| = (u : ℤ)) (hu : 1 ≤ u) :
    Summable (fun n : ℤ =>
      if 2 * (u : ℤ) < |n| then
        ‖dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
          dyadicKernelPiece h j (n : ℝ)‖ else 0) ∧
    (∑' n : ℤ, if 2 * (u : ℤ) < |n| then
        ‖dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
          dyadicKernelPiece h j (n : ℝ)‖ else 0) ≤
      12 * (A * D) *
        min ((u : ℝ) * dyadicScale j) (((u : ℝ) * dyadicScale j)⁻¹) := by
  let t : ℝ := dyadicScale j
  let q : ℤ → ℝ := fun n =>
    if 2 * (u : ℤ) < |n| then
      ‖dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
        dyadicKernelPiece h j (n : ℝ)‖ else 0
  let qKernel : ℤ → ℝ := fun n =>
    if 2 * (u : ℤ) < |n| then
      ‖dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
        dyadicKernelPiece h j (n : ℝ)‖ else 0
  let tailWeight : ℤ → ℝ := fun n =>
    if 2 * (u : ℤ) < |n| then dyadicKernelWeight j n else 0
  have ht : 0 < t := by dsimp [t]; exact dyadicScale_pos j
  have huReal : (u : ℝ) = |(shift : ℝ)| := by
    have hcast := congrArg (fun z : ℤ => (z : ℝ)) hshift.symm
    simpa only [Int.cast_abs, Int.cast_natCast] using hcast
  have hA : 0 ≤ A := by
    rw [A_eq]
    exact mul_nonneg (by positivity) (le_of_lt B_pos)
  have hC : 0 ≤ A * D := mul_nonneg hA h.D_nonneg
  have hDerivativeCoeff : 0 ≤ (A * D) * (u : ℝ) * t ^ 2 :=
    mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (sq_nonneg t)
  have hAllWeight := dyadicKernelWeight_summable_and_all_tsum_le j
  have hAllMajor : Summable
      (fun n : ℤ => ((A * D) * (u : ℝ) * t ^ 2) * dyadicKernelWeight j n) :=
    hAllWeight.1.mul_left ((A * D) * (u : ℝ) * t ^ 2)
  have hqNonneg (n : ℤ) : 0 ≤ q n := by
    by_cases hn : 2 * (u : ℤ) < |n|
    · simp [q, hn]
    · simp [q, hn]
  have hDerivativePointwise (n : ℤ) :
      q n ≤ ((A * D) * (u : ℝ) * t ^ 2) * dyadicKernelWeight j n := by
    by_cases hn : 2 * (u : ℤ) < |n|
    · have htail : 2 * |shift| < |n| := by simpa [hshift] using hn
      have hpoint := dyadicKernelPiece_shift_difference_pointwise_bound h j shift n htail
      simp only [q, if_pos hn]
      rw [show |(shift : ℝ)| = (u : ℝ) by simpa using huReal.symm] at hpoint
      rw [dyadicKernelWeight]
      simpa [t, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hpoint
    · simp only [q, if_neg hn]
      exact mul_nonneg hDerivativeCoeff (by
        unfold dyadicKernelWeight
        positivity)
  have hqSummable : Summable q :=
    Summable.of_nonneg_of_le hqNonneg hDerivativePointwise hAllMajor
  have hDerivativeSum : (∑' n : ℤ, q n) ≤
      5 * (A * D) * ((u : ℝ) * t) := by
    calc
      (∑' n : ℤ, q n) ≤
          ∑' n : ℤ, ((A * D) * (u : ℝ) * t ^ 2) * dyadicKernelWeight j n :=
        Summable.tsum_le_tsum hDerivativePointwise hqSummable hAllMajor
      _ = ((A * D) * (u : ℝ) * t ^ 2) *
            (∑' n : ℤ, dyadicKernelWeight j n) :=
        hAllWeight.1.tsum_mul_left ((A * D) * (u : ℝ) * t ^ 2)
      _ ≤ ((A * D) * (u : ℝ) * t ^ 2) * (5 / t) :=
        mul_le_mul_of_nonneg_left hAllWeight.2 hDerivativeCoeff
      _ = 5 * (A * D) * ((u : ℝ) * t) := by
        field_simp [ne_of_gt ht]
        <;> ring
  have hTailWeight := dyadicKernelWeight_strict_tail_summable_and_tsum_le j u
  have hKernelCoeff : 0 ≤ 2 * (A * D) * t :=
    mul_nonneg (mul_nonneg (by norm_num) hC) ht.le
  have hKernelMajor : Summable (fun n : ℤ => (2 * (A * D) * t) * tailWeight n) :=
    hTailWeight.1.mul_left (2 * (A * D) * t)
  have hKernelPointwise (n : ℤ) :
      qKernel n ≤ (2 * (A * D) * t) * tailWeight n := by
    by_cases hn : 2 * (u : ℤ) < |n|
    · have htailInt : 2 * |shift| < |n| := by simpa [hshift] using hn
      have htailReal : 2 * |(shift : ℝ)| < |(n : ℝ)| := by exact_mod_cast htailInt
      have htriangle : |(n : ℝ)| ≤
          |((n - shift : ℤ) : ℝ)| + |(shift : ℝ)| := by
        calc
          |(n : ℝ)| = |((n - shift : ℤ) : ℝ) + (shift : ℝ)| := by
            congr 1 <;> push_cast <;> ring
          _ ≤ |((n - shift : ℤ) : ℝ)| + |(shift : ℝ)| := abs_add_le _ _
      have hshiftLower : |(n : ℝ)| / 2 ≤ |((n - shift : ℤ) : ℝ)| := by
        linarith
      have hdenShift : 1 + t * |(n : ℝ)| / 2 ≤
          1 + t * |((n - shift : ℤ) : ℝ)| := by
        nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hshiftLower)]
      have hdenPlain : 1 + t * |(n : ℝ)| / 2 ≤ 1 + t * |(n : ℝ)| := by
        nlinarith [mul_nonneg ht.le (abs_nonneg (n : ℝ))]
      have hsqShift : (1 + t * |(n : ℝ)| / 2) ^ 2 ≤
          (1 + t * |((n - shift : ℤ) : ℝ)|) ^ 2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).2 hdenShift
      have hsqPlain : (1 + t * |(n : ℝ)| / 2) ^ 2 ≤
          (1 + t * |(n : ℝ)|) ^ 2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).2 hdenPlain
      have hnum : 0 ≤ A * D * t := mul_nonneg hC ht.le
      have hkernelShift := dyadicKernelPiece_pointwise_bound h j
        ((n - shift : ℤ) : ℝ)
      have hkernelPlain := dyadicKernelPiece_pointwise_bound h j (n : ℝ)
      have hkernelShift' :
          ‖dyadicKernelPiece h j ((n - shift : ℤ) : ℝ)‖ ≤
            A * D * t / (1 + t * |(n : ℝ)| / 2) ^ 2 := by
        calc
          ‖dyadicKernelPiece h j ((n - shift : ℤ) : ℝ)‖ ≤
              A * D * t / (1 + t * |((n - shift : ℤ) : ℝ)|) ^ 2 := hkernelShift
          _ ≤ A * D * t / (1 + t * |(n : ℝ)| / 2) ^ 2 :=
            div_le_div_of_nonneg_left hnum (by positivity) hsqShift
      have hkernelPlain' :
          ‖dyadicKernelPiece h j (n : ℝ)‖ ≤
            A * D * t / (1 + t * |(n : ℝ)| / 2) ^ 2 := by
        calc
          ‖dyadicKernelPiece h j (n : ℝ)‖ ≤
              A * D * t / (1 + t * |(n : ℝ)|) ^ 2 := hkernelPlain
          _ ≤ A * D * t / (1 + t * |(n : ℝ)| / 2) ^ 2 :=
            div_le_div_of_nonneg_left hnum (by positivity) hsqPlain
      have hdiff := norm_sub_le
        (dyadicKernelPiece h j ((n - shift : ℤ) : ℝ))
        (dyadicKernelPiece h j (n : ℝ))
      simp only [qKernel, tailWeight, if_pos hn]
      calc
        ‖dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
            dyadicKernelPiece h j (n : ℝ)‖ ≤
            ‖dyadicKernelPiece h j ((n - shift : ℤ) : ℝ)‖ +
              ‖dyadicKernelPiece h j (n : ℝ)‖ := hdiff
        _ ≤ A * D * t / (1 + t * |(n : ℝ)| / 2) ^ 2 +
              A * D * t / (1 + t * |(n : ℝ)| / 2) ^ 2 :=
            add_le_add hkernelShift' hkernelPlain'
        _ = (2 * (A * D) * t) * dyadicKernelWeight j n := by
          rw [dyadicKernelWeight]
          simp only [div_eq_mul_inv]
          ring
    · simp only [qKernel, tailWeight, if_neg hn, mul_zero]
      exact le_rfl
  have hqKernelNonneg (n : ℤ) : 0 ≤ qKernel n := by
    by_cases hn : 2 * (u : ℤ) < |n|
    · simp [qKernel, hn]
    · simp [qKernel, hn]
  have hqKernelSummable : Summable qKernel :=
    Summable.of_nonneg_of_le hqKernelNonneg hKernelPointwise hKernelMajor
  have hKernelSum : (∑' n : ℤ, qKernel n) ≤
      8 * (A * D) / ((u : ℝ) * t) := by
    have hTailTotal := Summable.tsum_le_tsum hKernelPointwise
      hqKernelSummable hKernelMajor
    have huPos : 0 < (u : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hu)
    have huTpos : 0 < (u : ℝ) * t := mul_pos huPos ht
    have hden : (u : ℝ) * t ≤ 1 + t * (u : ℝ) := by
      calc
        (u : ℝ) * t = t * (u : ℝ) := by ring
        _ ≤ 1 + t * (u : ℝ) := le_add_of_nonneg_left (by norm_num)
    calc
      (∑' n : ℤ, qKernel n) ≤
          ∑' n : ℤ, (2 * (A * D) * t) * tailWeight n := hTailTotal
      _ = (2 * (A * D) * t) *
            (∑' n : ℤ, tailWeight n) :=
        hTailWeight.1.tsum_mul_left (2 * (A * D) * t)
      _ ≤ (2 * (A * D) * t) *
          (4 / (t * (1 + t * (u : ℝ)))) :=
        mul_le_mul_of_nonneg_left hTailWeight.2 hKernelCoeff
      _ = 8 * (A * D) / (1 + t * (u : ℝ)) := by
        field_simp [ne_of_gt ht]
        <;> ring
      _ ≤ 8 * (A * D) / ((u : ℝ) * t) := by
        convert div_le_div_of_nonneg_left
          (show 0 ≤ 8 * (A * D) by positivity)
          huTpos hden using 1 <;> ring
  have hscaleT : 0 < (u : ℝ) * t := by
    exact mul_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hu)) ht
  have hderivInput : (∑' n : ℤ, q n) ≤
      5 * (A * D) * ((u : ℝ) * t) := hDerivativeSum
  have hkernelInput : (∑' n : ℤ, qKernel n) ≤
      8 * (A * D) / ((u : ℝ) * t) := hKernelSum
  have hmin := per_scale_two_bounds_to_min hC hscaleT hderivInput hkernelInput
  refine ⟨?_, ?_⟩
  · simpa [q] using hqSummable
  · simpa [q, mul_assoc] using hmin

private theorem kernelHormander_conditional
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (shift : ℤ) :
    Summable (fun n : ℤ =>
      if 2 * |shift| < |n| then
        ‖kernelCoefficient (torusSymbol h) (n - shift) -
          kernelCoefficient (torusSymbol h) n‖ else 0) ∧
    (∑' n : ℤ, if 2 * |shift| < |n| then
        ‖kernelCoefficient (torusSymbol h) (n - shift) -
          kernelCoefficient (torusSymbol h) n‖ else 0) ≤ H₀ * D := by
  classical
  let Q : ℤ → ℝ := fun n =>
    if 2 * |shift| < |n| then
      ‖kernelCoefficient (torusSymbol h) (n - shift) -
        kernelCoefficient (torusSymbol h) n‖ else 0
  by_cases hzero : shift = 0
  · subst shift
    have hQ : Q = fun _ : ℤ => 0 := by
      funext n
      simp [Q]
    refine ⟨?_, ?_⟩
    · simpa [Q] using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ)))
    · simpa [Q] using
        (mul_nonneg (by
          rw [H₀_eq, A_eq]
          exact mul_nonneg (by norm_num) <|
            mul_nonneg (by positivity) (le_of_lt B_pos)) h.D_nonneg)
  · let u : ℕ := shift.natAbs
    have hshift : |shift| = (u : ℤ) := by
      simpa [u] using (Int.natCast_natAbs shift).symm
    have hu0 : u ≠ 0 := by
      intro hu
      apply hzero
      have hcast : (u : ℤ) = 0 := by exact_mod_cast hu
      rw [← hshift] at hcast
      exact abs_eq_zero.mp hcast
    have hu : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hu0
    have huR : 0 < (u : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hu0)
    have hA : 0 ≤ A := by
      rw [A_eq]
      exact mul_nonneg (by positivity) (le_of_lt B_pos)
    have hAD : 0 ≤ A * D := mul_nonneg hA h.D_nonneg
    let baseNorm : ℤ → ℝ := fun n => ‖baseKernelCoefficient h n‖
    let baseTail : ℤ → ℝ := fun n =>
      if 2 * |shift| < |n| then
        ‖baseKernelCoefficient h (n - shift) - baseKernelCoefficient h n‖ else 0
    let pieceTail : ℤ → ℕ → ℝ := fun n j =>
      if 2 * |shift| < |n| then
        ‖dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
          dyadicKernelPiece h j (n : ℝ)‖ else 0
    let F : ℕ → ℝ := fun j =>
      min ((u : ℝ) * dyadicScale j) (((u : ℝ) * dyadicScale j)⁻¹)
    let C : ℝ := 12 * (A * D)
    have hbase := baseKernelCoefficient_summable_l1_estimate h
    have hbaseShiftFun :
        (fun n : ℤ => baseNorm (n - shift)) =
          baseNorm ∘ Equiv.addLeft (-shift) := by
      funext n
      simp [baseNorm, Equiv.addLeft, sub_eq_add_neg, add_comm]
    have hbaseShift : Summable (fun n : ℤ => baseNorm (n - shift)) := by
      rw [hbaseShiftFun]
      exact (Equiv.addLeft (-shift)).summable_iff.mpr hbase.1
    have hbaseShiftTsum :
        (∑' n : ℤ, baseNorm (n - shift)) = ∑' n : ℤ, baseNorm n := by
      rw [hbaseShiftFun]
      exact Equiv.tsum_eq (Equiv.addLeft (-shift)) baseNorm
    have hbaseMajor : Summable (fun n : ℤ => baseNorm (n - shift) + baseNorm n) :=
      hbaseShift.add hbase.1
    have hbaseTailNonneg (n : ℤ) : 0 ≤ baseTail n := by
      by_cases hn : 2 * |shift| < |n| <;> simp [baseTail, hn]
    have hbaseTailPointwise (n : ℤ) :
        baseTail n ≤ baseNorm (n - shift) + baseNorm n := by
      by_cases hn : 2 * |shift| < |n|
      · simp only [baseTail, if_pos hn, baseNorm]
        exact norm_sub_le _ _
      · simp only [baseTail, if_neg hn]
        exact add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hbaseTailSummable : Summable baseTail :=
      Summable.of_nonneg_of_le hbaseTailNonneg hbaseTailPointwise hbaseMajor
    have hbaseMajorTsum :
        (∑' n : ℤ, (baseNorm (n - shift) + baseNorm n)) =
          2 * (∑' n : ℤ, baseNorm n) := by
      calc
        _ = (∑' n : ℤ, baseNorm (n - shift)) + ∑' n : ℤ, baseNorm n :=
          hbaseShift.tsum_add hbase.1
        _ = 2 * (∑' n : ℤ, baseNorm n) := by rw [hbaseShiftTsum]; ring
    have hbaseTailBound : (∑' n : ℤ, baseTail n) ≤ 2 * (A * D) := by
      calc
        _ ≤ ∑' n : ℤ, (baseNorm (n - shift) + baseNorm n) :=
          Summable.tsum_le_tsum hbaseTailPointwise hbaseTailSummable hbaseMajor
        _ = 2 * (∑' n : ℤ, baseNorm n) := hbaseMajorTsum
        _ ≤ 2 * (A * D) := mul_le_mul_of_nonneg_left hbase.2 (by norm_num)
    have hFNonneg (j : ℕ) : 0 ≤ F j := by
      dsimp [F]
      exact le_min (mul_nonneg huR.le (dyadicScale_pos j).le)
        (inv_nonneg.mpr (mul_nonneg huR.le (dyadicScale_pos j).le))
    have hFLeft (j : ℕ) : F j ≤ (u : ℝ) * dyadicScale j := by
      dsimp [F]
      exact min_le_left _ _
    have hUScale : Summable (fun j : ℕ => (u : ℝ) * dyadicScale j) := by
      simpa [dyadicScale, mul_assoc] using
        summable_geometric_two.mul_left (u : ℝ)
    have hFSummable : Summable F :=
      Summable.of_nonneg_of_le hFNonneg hFLeft hUScale
    have hFBound : (∑' j : ℕ, F j) < 4 := by
      simpa [F] using dyadic_scale_min_tsum_lt_four u hu
    have hC : 0 ≤ C := by
      dsimp [C]
      exact mul_nonneg (by norm_num) hAD
    have hCFsummable : Summable (fun j : ℕ => C * F j) :=
      hFSummable.mul_left C
    have hpiece (j : ℕ) :
        Summable (fun n : ℤ => pieceTail n j) ∧
          (∑' n : ℤ, pieceTail n j) ≤ C * F j := by
      simpa [pieceTail, F, C, hshift, mul_assoc] using
        dyadicKernelPiece_strict_tail_difference_summable_bound h shift u j hshift hu
    have hpieceOuterNonneg (j : ℕ) : 0 ≤ ∑' n : ℤ, pieceTail n j :=
      tsum_nonneg (fun n => by
        by_cases hn : 2 * |shift| < |n| <;> simp [pieceTail, hn])
    have hpieceOuterSummable : Summable (fun j : ℕ => ∑' n : ℤ, pieceTail n j) :=
      Summable.of_nonneg_of_le hpieceOuterNonneg (fun j => (hpiece j).2) hCFsummable
    have hpieceProd : Summable (fun z : ℕ × ℤ => pieceTail z.2 z.1) := by
      apply (summable_prod_of_nonneg (f := fun z : ℕ × ℤ => pieceTail z.2 z.1)
        (fun z => by
          by_cases hn : 2 * |shift| < |z.2| <;>
            simp [pieceTail, hn])).2
      exact ⟨fun j => by simpa using (hpiece j).1, hpieceOuterSummable⟩
    have hpieceProdSwap : Summable (fun z : ℤ × ℕ => pieceTail z.1 z.2) := by
      change Summable (fun z : ℤ × ℕ =>
        (fun w : ℕ × ℤ => pieceTail w.2 w.1) (Equiv.prodComm ℤ ℕ z))
      exact (summable_prodComm_iff
        (α := ℕ) (β := ℤ)
        (f := fun w : ℕ × ℤ => pieceTail w.2 w.1)).2 hpieceProd
    have hpieceTotalSummable : Summable (fun n : ℤ => ∑' j : ℕ, pieceTail n j) :=
      ((summable_prod_of_nonneg (f := fun z : ℤ × ℕ => pieceTail z.1 z.2)
        (fun z => by
          by_cases hn : 2 * |shift| < |z.1| <;>
            simp [pieceTail, hn])).mp hpieceProdSwap).2
    have hpieceScaleBound :
        (∑' j : ℕ, ∑' n : ℤ, pieceTail n j) ≤ 48 * (A * D) := by
      calc
        _ ≤ ∑' j : ℕ, C * F j :=
          Summable.tsum_le_tsum (fun j => (hpiece j).2)
            hpieceOuterSummable hCFsummable
        _ = C * (∑' j : ℕ, F j) := hFSummable.tsum_mul_left C
        _ ≤ C * 4 := mul_le_mul_of_nonneg_left (le_of_lt hFBound) hC
        _ = 48 * (A * D) := by dsimp [C]; ring
    have hpieceTotalBound :
        (∑' n : ℤ, ∑' j : ℕ, pieceTail n j) ≤ 48 * (A * D) := by
      calc
        (∑' n : ℤ, ∑' j : ℕ, pieceTail n j) =
            ∑' j : ℕ, ∑' n : ℤ, pieceTail n j :=
          tsum_comm_prod (fun z : ℤ × ℕ => pieceTail z.1 z.2) hpieceProdSwap
        _ ≤ 48 * (A * D) := hpieceScaleBound
    have hbaseTailMajor : Summable baseTail := hbaseTailSummable
    have hQMajor : Summable (fun n : ℤ => baseTail n + ∑' j : ℕ, pieceTail n j) :=
      hbaseTailMajor.add hpieceTotalSummable
    have hQNonneg (n : ℤ) : 0 ≤ Q n := by
      by_cases hn : 2 * |shift| < |n| <;> simp [Q, hn]
    have hQPointwise (n : ℤ) : Q n ≤ baseTail n + ∑' j : ℕ, pieceTail n j := by
      by_cases hn : 2 * |shift| < |n|
      · have hrecShift := kernelCoefficient_dyadicKernel_reconstruction h (n - shift)
        have hrecPlain := kernelCoefficient_dyadicKernel_reconstruction h n
        have hshiftPieces : Summable (fun j : ℕ =>
            dyadicKernelPiece h j ((n - shift : ℤ) : ℝ)) := hrecShift.1.of_norm
        have hplainPieces : Summable (fun j : ℕ =>
            dyadicKernelPiece h j (n : ℝ)) := hrecPlain.1.of_norm
        have hdiffPieces : Summable (fun j : ℕ =>
            dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
              dyadicKernelPiece h j (n : ℝ)) := hshiftPieces.sub hplainPieces
        have hkernelEq :
            kernelCoefficient (torusSymbol h) (n - shift) -
              kernelCoefficient (torusSymbol h) n =
            (baseKernelCoefficient h (n - shift) - baseKernelCoefficient h n) +
              ∑' j : ℕ, (dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
                dyadicKernelPiece h j (n : ℝ)) := by
          rw [hrecShift.2, hrecPlain.2]
          calc
            _ = (baseKernelCoefficient h (n - shift) - baseKernelCoefficient h n) +
                ((∑' j : ℕ, dyadicKernelPiece h j ((n - shift : ℤ) : ℝ)) -
                  ∑' j : ℕ, dyadicKernelPiece h j (n : ℝ)) := by ring
            _ = (baseKernelCoefficient h (n - shift) - baseKernelCoefficient h n) +
                ∑' j : ℕ, (dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
                  dyadicKernelPiece h j (n : ℝ)) := by
              rw [← hshiftPieces.tsum_sub hplainPieces]
        have hnormTsum := norm_tsum_le_tsum_norm hdiffPieces.norm
        simp only [Q, if_pos hn]
        calc
          ‖kernelCoefficient (torusSymbol h) (n - shift) -
              kernelCoefficient (torusSymbol h) n‖ =
              ‖(baseKernelCoefficient h (n - shift) - baseKernelCoefficient h n) +
                ∑' j : ℕ, (dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
                  dyadicKernelPiece h j (n : ℝ))‖ := by rw [hkernelEq]
          _ ≤ ‖baseKernelCoefficient h (n - shift) - baseKernelCoefficient h n‖ +
                ‖∑' j : ℕ, (dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
                  dyadicKernelPiece h j (n : ℝ))‖ := norm_add_le _ _
          _ ≤ ‖baseKernelCoefficient h (n - shift) - baseKernelCoefficient h n‖ +
                ∑' j : ℕ, ‖dyadicKernelPiece h j ((n - shift : ℤ) : ℝ) -
                  dyadicKernelPiece h j (n : ℝ)‖ :=
              add_le_add_right hnormTsum _
          _ ≤ (baseTail n) + ∑' j : ℕ, pieceTail n j := by
              simpa [baseTail, pieceTail, hn]
      · simp only [Q, if_neg hn]
        exact add_nonneg (hbaseTailNonneg n)
          (tsum_nonneg (fun j => by
            by_cases hj : 2 * |shift| < |n| <;> simp [pieceTail, hj]))
    have hQSummable : Summable Q :=
      Summable.of_nonneg_of_le hQNonneg hQPointwise hQMajor
    have hQBound : (∑' n : ℤ, Q n) ≤ 50 * (A * D) := by
      calc
        _ ≤ ∑' n : ℤ, (baseTail n + ∑' j : ℕ, pieceTail n j) :=
          Summable.tsum_le_tsum hQPointwise hQSummable hQMajor
        _ = (∑' n : ℤ, baseTail n) + ∑' n : ℤ, ∑' j : ℕ, pieceTail n j :=
          hbaseTailSummable.tsum_add hpieceTotalSummable
        _ ≤ 2 * (A * D) + 48 * (A * D) := add_le_add hbaseTailBound hpieceTotalBound
        _ = 50 * (A * D) := by ring
    refine ⟨?_, ?_⟩
    · simpa [Q] using hQSummable
    · simpa [Q] using le_trans hQBound (by
        rw [H₀_eq]
        nlinarith [hAD])

/-- Summability companion for the exact strict-tail kernel estimate. This is
kept separate from the approved inequality statement so downstream proofs can
apply countable-subset comparisons without an extra public theorem hypothesis. -/
theorem kernelHormander_summable {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (shift : ℤ) :
    Summable (fun n : {n : ℤ // 2 * |shift| < |n|} =>
      ‖kernelCoefficient (torusSymbol h) (n.1 - shift) -
        kernelCoefficient (torusSymbol h) n.1‖) := by
  have hcond := (kernelHormander_conditional h shift).1
  have hsub : Summable (fun n : {n : ℤ // 2 * |shift| < |n|} =>
      if 2 * |shift| < |n.1| then
        ‖kernelCoefficient (torusSymbol h) (n.1 - shift) -
          kernelCoefficient (torusSymbol h) n.1‖ else 0) := by
    exact hcond.subtype (fun n : ℤ => 2 * |shift| < |n|)
  refine hsub.congr ?_
  intro n
  simp [n.property]

private theorem strictIntegerTail_tsum_subtype (shift : ℤ) (f : ℤ → ℝ) :
    (∑' n : {n : ℤ // 2 * |shift| < |n|}, f n.1) =
      ∑' n : ℤ, if 2 * |shift| < |n| then f n else 0 := by
  let S : Set ℤ := {n | 2 * |shift| < |n|}
  change (∑' n : S, f n) = ∑' n : ℤ, if 2 * |shift| < |n| then f n else 0
  rw [tsum_subtype]
  apply tsum_congr
  intro n
  simp [S, Set.indicator]

/-- The exact discrete cancellation estimate `lp:hormander` from the
approved blueprint. The strict tail is represented as a subtype sum. -/
theorem kernelHormander {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (shift : ℤ) :
    (∑' n : {n : ℤ // 2 * |shift| < |n|},
      ‖kernelCoefficient (torusSymbol h) (n.1 - shift) -
        kernelCoefficient (torusSymbol h) n.1‖) ≤ H₀ * D := by
  classical
  let S : Set ℤ := {n | 2 * |shift| < |n|}
  let g : ℤ → ℝ := fun n =>
    ‖kernelCoefficient (torusSymbol h) (n - shift) -
      kernelCoefficient (torusSymbol h) n‖
  let Q : ℤ → ℝ := fun n => if n ∈ S then g n else 0
  have hcond := kernelHormander_conditional h shift
  have htsumEq :
      (∑' n : {n : ℤ // 2 * |shift| < |n|}, g n.1) = ∑' n : ℤ, Q n := by
    calc
      _ = ∑' n : ℤ, if 2 * |shift| < |n| then g n else 0 :=
        strictIntegerTail_tsum_subtype shift g
      _ = ∑' n : ℤ, Q n := by
        apply tsum_congr
        intro n
        simp [Q, S]
  rw [htsumEq]
  simpa [Q, S, g] using hcond.2

end

end FractionalPrimes.Literature.Multiplier
