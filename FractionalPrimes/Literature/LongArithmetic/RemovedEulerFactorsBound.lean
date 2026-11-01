module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.LongArithmetic

open scoped BigOperators

private theorem harmonic_step {N : ℕ} (hN : 2 ≤ N) :
    ((N + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log (((N + 1 : ℕ) : ℝ) / N) := by
  let x : ℝ := ((N + 1 : ℕ) : ℝ) / N
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxgt : 1 < x := by
    dsimp [x]
    rw [one_lt_div hNpos]
    norm_cast
    omega
  have hbase := Real.self_sub_one_le_mul_log hxpos.le
  have hquot : x⁻¹ * (x - 1) = ((N + 1 : ℕ) : ℝ)⁻¹ := by
    dsimp [x]
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  calc
    ((N + 1 : ℕ) : ℝ)⁻¹ = x⁻¹ * (x - 1) := hquot.symm
    _ ≤ x⁻¹ * (x * Real.log x) := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hxpos.le)
    _ = Real.log x := by field_simp
    _ = Real.log (((N + 1 : ℕ) : ℝ) / N) := by rfl

private theorem harmonic_sum_Icc_two_le_log {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, (n : ℝ)⁻¹) ≤ Real.log N := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hNsmall : N = 1
    · subst N
      have hlog := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
      norm_num [Finset.sum_Icc_succ_top] at hlog ⊢
      linarith
    · have hNprev : 2 ≤ N := by omega
      have hprev := ih hNprev
      have hstep := harmonic_step hNprev
      have hstep' : ((N + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log ((N + 1 : ℝ) / N) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hstep
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hlogdiv : Real.log (N + 1 : ℝ) = Real.log N + Real.log ((N + 1 : ℝ) / N) := by
        rw [Real.log_div (by positivity) (by positivity)]
        ring
      have hlogdiv' : Real.log (N + 1 : ℝ) = Real.log (N + 1 : ℕ) := by norm_cast
      rw [← hlogdiv']
      rw [hlogdiv]
      exact add_le_add hprev hstep'

private theorem two_neg_three_fourth_le_two_thirds :
    (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 2 / 3 := by
  have hquarter : 1 / 4 ≤ Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
    norm_num at h
    linarith
  have hroot : (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 / 3 : ℝ) := by
    have hcube : (3 / 2 : ℝ) ^ 3 ≤ 2 ^ 2 := by norm_num
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ (3 / 2 : ℝ) ^ 3) hcube
        (by norm_num : 0 ≤ (1 / 3 : ℝ))
    have hleft : ((3 / 2 : ℝ) ^ 3) ^ (1 / 3 : ℝ) = 3 / 2 := by
      rw [← Real.rpow_natCast_mul (by positivity) 3 (1 / 3 : ℝ)]
      norm_num
    have hright : ((2 : ℝ) ^ 2) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)) 2 (1 / 3 : ℝ)]
      norm_num
    rw [hleft, hright] at h
    exact h
  have hpow : (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 2 ^ (-(2 / 3 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    norm_num
  have hinv : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 2 / 3 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    apply (inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos (by norm_num) _)).2
    nlinarith [mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  exact hpow.trans hinv

private theorem removedPrimeReciprocalSumBound
    {X δ : ℝ} {r : ℕ} {s : ℂ}
    (hX : Real.exp 4 ≤ X) (hr1 : 1 ≤ r) (hrX : (r : ℝ) ≤ X)
    (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ min (1 / 4) (1 / (4 * Real.log (Real.log X))))
    (hs : 1 - δ ≤ s.re) :
    (∑ p ∈ r.primeFactors, (p : ℝ) ^ (-s.re)) ≤
      2 * Real.log (Real.log X) + 2 := by
  let w : ℝ := Real.log X
  let small : Finset ℕ := r.primeFactors.filter (fun p => (p : ℝ) ≤ w)
  let large : Finset ℕ := r.primeFactors.filter (fun p => w < (p : ℝ))
  have hw : 4 ≤ w := by
    dsimp [w]
    calc
      4 = Real.log (Real.exp 4) := by rw [Real.log_exp]
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos 4) hX
  have hwpos : 0 < w := by linarith
  have hlogw : 1 ≤ Real.log w := by
    apply (Real.le_log_iff_exp_le hwpos).2
    exact le_trans (Real.exp_one_lt_three.le) (by linarith)
  have hlogwpos : 0 < Real.log w := lt_of_lt_of_le zero_lt_one hlogw
  have hδquart : δ ≤ 1 / 4 := hδ.trans (min_le_left _ _)
  have hδlog : δ ≤ 1 / (4 * Real.log w) := hδ.trans (min_le_right _ _)
  have hδmul : δ * Real.log w ≤ 1 / 4 := by
    calc
      δ * Real.log w ≤ (1 / (4 * Real.log w)) * Real.log w :=
        mul_le_mul_of_nonneg_right hδlog hlogwpos.le
      _ = 1 / 4 := by field_simp
  have hlogquarter : 1 / 4 ≤ Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
    norm_num at h
    linarith
  have hexpquarter : Real.exp (1 / 4) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hlogquarter
  have hwd : w ^ δ ≤ 2 := by
    rw [Real.rpow_def_of_pos hwpos]
    calc
      Real.exp (Real.log w * δ) ≤ Real.exp (1 / 4) :=
        Real.exp_le_exp.mpr (by nlinarith [hδmul])
      _ ≤ 2 := hexpquarter
  have hσ : (3 / 4 : ℝ) ≤ s.re := by linarith
  have hsmall :
      (∑ p ∈ small, (p : ℝ) ^ (-s.re)) ≤ 2 * Real.log w := by
    have hN : 2 ≤ ⌊w⌋₊ := by
      rw [Nat.le_floor_iff (by positivity : 0 ≤ w)]
      norm_num
      exact le_trans (by norm_num) hw
    have hsub : small ⊆ Finset.Icc 2 ⌊w⌋₊ := by
      intro p hp
      have hpMem : p ∈ r.primeFactors := (Finset.mem_filter.mp hp).1
      have hpPrime := Nat.prime_of_mem_primeFactors hpMem
      have hpSmall : (p : ℝ) ≤ w := (Finset.mem_filter.mp hp).2
      have hpN : p ≤ ⌊w⌋₊ := by
        rw [Nat.le_floor_iff' hpPrime.ne_zero]
        exact hpSmall
      exact Finset.mem_Icc.mpr ⟨hpPrime.two_le, hpN⟩
    have hterms : ∀ p ∈ small, (p : ℝ) ^ (-s.re) ≤ 2 * (p : ℝ)⁻¹ := by
      intro p hp
      have hpMem : p ∈ r.primeFactors := (Finset.mem_filter.mp hp).1
      have hpPrime := Nat.prime_of_mem_primeFactors hpMem
      have hpSmall : (p : ℝ) ≤ w := (Finset.mem_filter.mp hp).2
      have hpbase : 1 ≤ (p : ℝ) := by exact_mod_cast (le_trans (by norm_num) hpPrime.two_le)
      have hexp : -s.re ≤ -1 + δ := by linarith
      have hmono : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 + δ) :=
        Real.rpow_le_rpow_of_exponent_le hpbase hexp
      have hpδ : (p : ℝ) ^ δ ≤ w ^ δ := Real.rpow_le_rpow (by positivity) hpSmall hδ0
      have hpδ2 := hpδ.trans hwd
      rw [Real.rpow_add (by positivity : 0 < (p : ℝ))] at hmono
      rw [Real.rpow_neg (by positivity : 0 ≤ (p : ℝ))] at hmono
      calc
        (p : ℝ) ^ (-s.re) ≤ (p : ℝ)⁻¹ * (p : ℝ) ^ δ := by
          simpa [Real.rpow_neg (by positivity : 0 ≤ (p : ℝ))] using hmono
        _ ≤ (p : ℝ)⁻¹ * 2 := mul_le_mul_of_nonneg_left hpδ2 (by positivity)
        _ = 2 * (p : ℝ)⁻¹ := by ring
    calc
      (∑ p ∈ small, (p : ℝ) ^ (-s.re)) ≤ ∑ p ∈ small, 2 * (p : ℝ)⁻¹ :=
        Finset.sum_le_sum fun p hp => hterms p hp
      _ ≤ ∑ p ∈ Finset.Icc 2 ⌊w⌋₊, 2 * (p : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
      _ = 2 * ∑ p ∈ Finset.Icc 2 ⌊w⌋₊, (p : ℝ)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 2 * Real.log w := by
        have hharm := harmonic_sum_Icc_two_le_log hN
        have hNle : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hwpos.le
        have hlogN : Real.log (⌊w⌋₊ : ℝ) ≤ Real.log w :=
          Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)) hNle
        have hharm' :
            (∑ p ∈ Finset.Icc 2 ⌊w⌋₊, (p : ℝ)⁻¹) ≤ Real.log w := by
          exact hharm.trans hlogN
        nlinarith [hharm']
  have hlargeCount : (large.card : ℝ) * Real.log w ≤ w := by
    have hprodDvd : (∏ p ∈ large, p) ∣ r := by
      exact (Finset.prod_dvd_prod_of_subset (s := large) (t := r.primeFactors)
        (f := fun p : ℕ => p) (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd r)
    have hprodNat : (∏ p ∈ large, p) ≤ r := Nat.le_of_dvd (by omega : 0 < r) hprodDvd
    have hprodPos : 0 < ∏ p ∈ large, (p : ℝ) :=
      Finset.prod_pos fun p hp => by
        exact_mod_cast (Nat.prime_of_mem_primeFactors ((Finset.mem_filter.mp hp).1)).pos
    have hprodLe : ∏ p ∈ large, (p : ℝ) ≤ (r : ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast hprodNat
    have hsumlog :
        (large.card : ℝ) * Real.log w ≤ Real.log (∏ p ∈ large, (p : ℝ)) := by
      calc
        (large.card : ℝ) * Real.log w = ∑ p ∈ large, Real.log w := by simp
        _ ≤ ∑ p ∈ large, Real.log (p : ℝ) :=
          Finset.sum_le_sum fun p hp =>
            Real.log_le_log hwpos (Finset.mem_filter.mp hp).2.le
        _ = Real.log (∏ p ∈ large, (p : ℝ)) :=
          (Real.log_prod fun p hp => by
            exact_mod_cast (Nat.prime_of_mem_primeFactors ((Finset.mem_filter.mp hp).1)).ne_zero).symm
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    have hlogr : Real.log (∏ p ∈ large, (p : ℝ)) ≤ Real.log r :=
      Real.log_le_log hprodPos (by exact_mod_cast hprodLe)
    have hlogrX : Real.log r ≤ w := by
      dsimp [w]
      exact Real.log_le_log hrpos hrX
    exact hsumlog.trans (hlogr.trans hlogrX)
  have hlarge :
      (∑ p ∈ large, (p : ℝ) ^ (-s.re)) ≤ 2 := by
    have hterm : ∀ p ∈ large, (p : ℝ) ^ (-s.re) ≤ 2 / w := by
      intro p hp
      have hpLarge : w < (p : ℝ) := (Finset.mem_filter.mp hp).2
      have hpPos : 0 < (p : ℝ) := lt_trans hwpos hpLarge
      have hpBase : 1 ≤ (p : ℝ) := by linarith
      have hσpos : 0 < s.re := lt_of_lt_of_le (by norm_num) hσ
      have hbase : (p : ℝ) ^ (-s.re) ≤ w ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos hwpos hpLarge.le (by linarith)
      have hexp : -s.re ≤ -(1 - δ) := by linarith
      have hpow : w ^ (-s.re) ≤ w ^ (-(1 - δ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ w) hexp
      have hsplit : w ^ (-(1 - δ)) = w⁻¹ * w ^ δ := by
        rw [show -(1 - δ) = -1 + δ by ring, Real.rpow_add hwpos,
          Real.rpow_neg hwpos.le]
        simp
      calc
        (p : ℝ) ^ (-s.re) ≤ w ^ (-s.re) := hbase
        _ ≤ w ^ (-(1 - δ)) := hpow
        _ = w⁻¹ * w ^ δ := hsplit
        _ ≤ 2 / w := by
          calc
            w⁻¹ * w ^ δ ≤ w⁻¹ * 2 :=
              mul_le_mul_of_nonneg_left hwd (inv_nonneg.mpr hwpos.le)
            _ = 2 / w := by rw [div_eq_mul_inv]; ring
    have hsum := Finset.sum_le_sum (s := large) hterm
    calc
      (∑ p ∈ large, (p : ℝ) ^ (-s.re)) ≤ (large.card : ℝ) * (2 / w) := by
        simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum
      _ ≤ 2 := by
        have hcardDiv : (large.card : ℝ) / w ≤ 1 / Real.log w := by
          have hcard : (large.card : ℝ) ≤ w / Real.log w :=
            (le_div_iff₀ hlogwpos).2 hlargeCount
          calc
            (large.card : ℝ) / w ≤ (w / Real.log w) / w :=
              (div_le_div_iff_of_pos_right hwpos).2 hcard
            _ = 1 / Real.log w := by field_simp
        calc
          (large.card : ℝ) * (2 / w) = 2 * ((large.card : ℝ) / w) := by field_simp
          _ ≤ 2 * (1 / Real.log w) := mul_le_mul_of_nonneg_left hcardDiv (by norm_num)
          _ = 2 / Real.log w := by rw [div_eq_mul_inv]; ring
          _ ≤ 2 := by
            apply (div_le_iff₀ hlogwpos).2
            nlinarith [hlogw]
  have hpartition :
      (∑ p ∈ r.primeFactors, (p : ℝ) ^ (-s.re)) =
        (∑ p ∈ small, (p : ℝ) ^ (-s.re)) +
        (∑ p ∈ large, (p : ℝ) ^ (-s.re)) := by
    simpa [small, large, not_le] using
      (Finset.sum_filter_add_sum_filter_not r.primeFactors
        (fun p => (p : ℝ) ≤ w) (fun p => (p : ℝ) ^ (-s.re))).symm
  rw [hpartition]
  linarith

theorem removedEulerFactorsBound
    {X δ : ℝ} {r : ℕ} {s : ℂ} (z : ℕ → ℂ)
    (hX : Real.exp 4 ≤ X) (hr1 : 1 ≤ r) (hrX : (r : ℝ) ≤ X)
    (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ min (1 / 4) (1 / (4 * Real.log (Real.log X))))
    (hs : 1 - δ ≤ s.re)
    (hz : ∀ p ∈ r.primeFactors, ‖z p‖ ≤ 1) :
    (∀ p ∈ r.primeFactors, (1 : ℂ) - z p * (p : ℂ) ^ (-s) ≠ 0) ∧
      (∏ p ∈ r.primeFactors,
        (‖(1 : ℂ) - z p * (p : ℂ) ^ (-s)‖)⁻¹) ≤
          Real.exp 6 * (Real.log X) ^ 6 := by
  let w : ℝ := Real.log X
  have hw : 4 ≤ w := by
    dsimp [w]
    calc
      4 = Real.log (Real.exp 4) := by rw [Real.log_exp]
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos 4) hX
  have hwpos : 0 < w := by linarith
  have hσ : (3 / 4 : ℝ) ≤ s.re := by
    have hδquarter : δ ≤ 1 / 4 := hδ.trans (min_le_left _ _)
    linarith
  have hprimeBound (p : ℕ) (hp : p ∈ r.primeFactors) :
      ‖(p : ℂ) ^ (-s)‖ ≤ 2 / 3 := by
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpLower : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
    have hσpos : 0 < s.re := lt_of_lt_of_le (by norm_num) hσ
    have hbase : (p : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hpLower (by linarith)
    have hexp : (2 : ℝ) ^ (-s.re) ≤ 2 ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
      simpa using Complex.norm_natCast_cpow_of_pos hpPrime.pos (-s)
    rw [hnorm]
    exact (hbase.trans hexp).trans two_neg_three_fourth_le_two_thirds
  have hnonzero : ∀ p ∈ r.primeFactors, (1 : ℂ) - z p * (p : ℂ) ^ (-s) ≠ 0 := by
    intro p hp hzero
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hterm : ‖z p * (p : ℂ) ^ (-s)‖ ≤ 2 / 3 := by
      rw [norm_mul]
      calc
        ‖z p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (hz p hp) (norm_nonneg _)
        _ ≤ 2 / 3 := by simpa using hprimeBound p hp
    have heq : (1 : ℂ) = z p * (p : ℂ) ^ (-s) := sub_eq_zero.mp hzero
    have hnormeq := congrArg norm heq
    rw [norm_one] at hnormeq
    linarith
  have htermInv (p : ℕ) (hp : p ∈ r.primeFactors) :
      (‖(1 : ℂ) - z p * (p : ℂ) ^ (-s)‖)⁻¹ ≤
        Real.exp (3 * (p : ℝ) ^ (-s.re)) := by
    let u : ℝ := ‖z p * (p : ℂ) ^ (-s)‖
    have hu0 : 0 ≤ u := by positivity
    have hu : u ≤ 2 / 3 := by
      dsimp [u]
      rw [norm_mul]
      calc
        ‖z p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (hz p hp) (norm_nonneg _)
        _ ≤ 2 / 3 := by simpa using hprimeBound p hp
    have hdenPos : 0 < 1 - u := by dsimp [u]; linarith
    have hfactorPos : 0 < ‖(1 : ℂ) - z p * (p : ℂ) ^ (-s)‖ :=
      norm_pos_iff.mpr (hnonzero p hp)
    have hdenLe : 1 - u ≤ ‖(1 : ℂ) - z p * (p : ℂ) ^ (-s)‖ := by
      dsimp [u]
      have htriangle := norm_add_le (1 - z p * (p : ℂ) ^ (-s))
        (z p * (p : ℂ) ^ (-s))
      have hsum : (1 - z p * (p : ℂ) ^ (-s)) + z p * (p : ℂ) ^ (-s) = 1 := by ring
      rw [hsum, norm_one] at htriangle
      linarith
    have hrecip :
        (‖(1 : ℂ) - z p * (p : ℂ) ^ (-s)‖)⁻¹ ≤ (1 - u)⁻¹ :=
      (inv_le_inv₀ hfactorPos hdenPos).2 hdenLe
    have hgeom : (1 - u)⁻¹ ≤ 1 + 3 * u := by
      apply (inv_le_iff_one_le_mul₀ hdenPos).2
      have haux : 0 ≤ u * (2 - 3 * u) :=
        mul_nonneg hu0 (by linarith)
      nlinarith [haux]
    have hexp : 1 + 3 * u ≤ Real.exp (3 * u) := by
      have := Real.add_one_le_exp (3 * u)
      linarith
    have hterm : u ≤ (p : ℝ) ^ (-s.re) := by
      dsimp [u]
      rw [norm_mul]
      calc
        ‖z p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (hz p hp) (norm_nonneg _)
        _ = (p : ℝ) ^ (-s.re) := by
          simpa using Complex.norm_natCast_cpow_of_pos
              (Nat.prime_of_mem_primeFactors hp).pos (-s)
    have hexpMono : Real.exp (3 * u) ≤ Real.exp (3 * (p : ℝ) ^ (-s.re)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hterm (by norm_num))
    exact hrecip.trans (hgeom.trans (hexp.trans hexpMono))
  have hsum : (∑ p ∈ r.primeFactors, (p : ℝ) ^ (-s.re)) ≤
      2 * Real.log w + 2 := by
    exact removedPrimeReciprocalSumBound hX hr1 hrX hδ0 hδ hs
  have hprodExp :
      (∏ p ∈ r.primeFactors, Real.exp (3 * (p : ℝ) ^ (-s.re))) =
        Real.exp (∑ p ∈ r.primeFactors, 3 * (p : ℝ) ^ (-s.re)) := by
    induction r.primeFactors using Finset.induction with
    | empty => simp
    | @insert p t hp ih =>
      simp [hp, ih, Real.exp_add, Finset.sum_insert]
  refine ⟨hnonzero, ?_⟩
  calc
    (∏ p ∈ r.primeFactors,
      (‖(1 : ℂ) - z p * (p : ℂ) ^ (-s)‖)⁻¹) ≤
        ∏ p ∈ r.primeFactors, Real.exp (3 * (p : ℝ) ^ (-s.re)) :=
      Finset.prod_le_prod₀ (fun p hp => inv_nonneg.mpr (norm_nonneg _))
        (fun p hp => htermInv p hp)
    _ = Real.exp (∑ p ∈ r.primeFactors, 3 * (p : ℝ) ^ (-s.re)) := hprodExp
    _ = Real.exp (3 * ∑ p ∈ r.primeFactors, (p : ℝ) ^ (-s.re)) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (3 * (2 * Real.log w + 2)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by norm_num))
    _ = Real.exp 6 * (Real.log X) ^ 6 := by
      dsimp [w]
      rw [show 3 * (2 * Real.log (Real.log X) + 2) =
        6 + 6 * Real.log (Real.log X) by ring, Real.exp_add]
      congr 1
      rw [show 6 * Real.log (Real.log X) = Real.log (Real.log X) * 6 by ring,
        Real.exp_mul, Real.exp_log (by dsimp [w] at hwpos ⊢; exact hwpos)]
      simp

#print axioms removedEulerFactorsBound

end FractionalPrimes.Literature.LongArithmetic

end
