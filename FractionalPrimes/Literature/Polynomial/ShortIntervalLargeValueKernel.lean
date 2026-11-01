module

public import FractionalPrimes.ArithmeticBasicsAnalytic

/-! The scalar Gram-kernel estimate from `lgv:kernel`.  This file uses the
already checked finite first- and second-derivative estimates; it does not
formalize a mean-square or large-values theorem. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.LargeValues

open FractionalPrimes
open scoped BigOperators

/-- The angular exponential `n^(iu) = exp(i u log n)` on positive integer
indices. -/
noncomputable def scalarGramKernelPhase (u : ℝ) (n : ℤ) : ℂ :=
  Complex.exp (((u * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)

theorem scalarGramKernelPhase_eq_realExponentialPhase (u : ℝ) (n : ℤ) :
    scalarGramKernelPhase u n =
      realExponentialPhase (fun t => (u / (2 * Real.pi)) * Real.log t) n := by
  unfold scalarGramKernelPhase realExponentialPhase
  congr 1
  push_cast
  field_simp [ne_of_gt Real.pi_pos]
  <;> ring

private theorem gramKernelBound_negative_small
    (N u : ℝ) (hN : 2 ≤ N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖∑ n ∈ realIntegerInterval N N,
      realExponentialPhase (fun t => -((u / (2 * Real.pi)) * Real.log t)) n‖ ≤
      64 * (N / (1 + u) + Real.sqrt u) := by
  have hcard := realIntegerInterval_card_le N N (by linarith [hN])
  have hnorm :
      ‖∑ n ∈ realIntegerInterval N N,
        realExponentialPhase (fun t => -((u / (2 * Real.pi)) * Real.log t)) n‖ ≤
        (realIntegerInterval N N).card := by
    simpa [realExponentialPhase, kusminPhase] using
      (kusminPhase_sum_norm_le_card (realIntegerInterval N N)
        (fun t => -((u / (2 * Real.pi)) * Real.log t)))
  have hden : 0 < 1 + u := by linarith
  have hfrac : N / 2 ≤ N / (1 + u) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hden).2
    nlinarith [mul_nonneg (by linarith [hN] : 0 ≤ N) (by linarith : 0 ≤ 1 - u)]
  have hroot : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
  have hfinal : N + 1 ≤ 64 * (N / (1 + u) + Real.sqrt u) := by
    have hNlarge : N + 1 ≤ 3 * N / 2 := by nlinarith [hN]
    nlinarith
  exact hnorm.trans (hcard.trans hfinal)

private theorem gramKernelBound_negative_medium
    (N u : ℝ) (hN : 2 ≤ N) (hu1 : 1 < u) (huN : u ≤ N) :
    ‖∑ n ∈ realIntegerInterval N N,
      realExponentialPhase (fun t => -((u / (2 * Real.pi)) * Real.log t)) n‖ ≤
      64 * (N / (1 + u) + Real.sqrt u) := by
  classical
  let lo : ℤ := ⌊N⌋ + 1
  let hi : ℤ := ⌊2 * N⌋
  have hNpos : 0 < N := by linarith [hN]
  have hloN : N < (lo : ℝ) := by
    dsimp [lo]
    push_cast
    exact Int.lt_floor_add_one N
  have hhi2N : (hi : ℝ) ≤ 2 * N := by
    dsimp [hi]
    exact Int.floor_le (2 * N)
  have hloReal : (lo : ℝ) ≤ 2 * N := by
    dsimp [lo]
    push_cast
    linarith [Int.floor_le N, hN]
  have hlohi : lo ≤ hi := (Int.le_floor).2 hloReal
  have hIcc : realIntegerInterval N N = Finset.Icc lo hi := by
    ext n
    simp [realIntegerInterval, lo, hi, Finset.mem_Ico, Finset.mem_Icc,
      show N + N = 2 * N by ring]
  let m : ℕ := (hi - lo).toNat
  have hmcast : (m : ℤ) = hi - lo := by
    dsimp [m]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hlohi)
  have hmcastR : (m : ℝ) = (hi : ℝ) - (lo : ℝ) := by
    exact_mod_cast hmcast
  let a : ℝ := (lo : ℝ)
  have hend : a + (m : ℝ) = (hi : ℝ) := by
    dsimp [a]
    rw [hmcastR]
    ring
  let I : Set ℝ := Set.Icc a (a + (m : ℝ))
  have hloc : ∀ t ∈ I, N < t ∧ t ≤ 2 * N := by
    intro t ht
    have ht' : t ∈ Set.Icc a (hi : ℝ) := by
      simpa [I, hend] using ht
    exact ⟨lt_of_lt_of_le hloN ht'.1, ht'.2.trans hhi2N⟩
  have hpos : ∀ t ∈ I, 0 < t := by
    intro t ht
    exact lt_trans (by linarith [hN]) (hloc t ht).1
  let c : ℝ := u / (2 * Real.pi)
  let theta : ℝ := u / (4 * Real.pi * N)
  let f : ℝ → ℝ := fun t => -((u / (2 * Real.pi)) * Real.log t)
  let D : ℝ → ℝ := fun t => -(u / (2 * Real.pi)) * t⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcneg : -c ≤ 0 := neg_nonpos.mpr hc
  have hlogCont : ContinuousOn Real.log I := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (hpos t ht)
  have hinvCont : ContinuousOn (fun t : ℝ => t⁻¹) I := by
    apply continuousOn_inv₀.mono
    intro t ht
    exact ne_of_gt (hpos t ht)
  have hfcont : ContinuousOn f I := by
    simpa [f, c] using hlogCont.const_mul (-c)
  have hDcont : ContinuousOn D I := by
    simpa [D, c] using hinvCont.const_mul (-c)
  have hDmono : MonotoneOn D I := by
    intro x hx y hy hxy
    have hxpos := hpos x hx
    have hinv : y⁻¹ ≤ x⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hxpos hxy
    change (-c) * x⁻¹ ≤ (-c) * y⁻¹
    exact mul_le_mul_of_nonpos_left hinv hcneg
  have hderiv : ∀ t ∈ Set.Ioo a (a + (m : ℝ)), HasDerivAt f (D t) t := by
    intro t ht
    have htpos := hpos t (Set.Ioo_subset_Icc_self ht)
    simpa [f, D, c, neg_mul, mul_assoc] using
      (Real.hasDerivAt_log htpos.ne').const_mul (-(u / (2 * Real.pi)))
  have hthetaPos : 0 < theta := by
    dsimp [theta]
    positivity
  have hthetaHalf : theta ≤ 1 / 2 := by
    have hden : 0 < 4 * Real.pi * N := by positivity
    have hpi : 2 ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hmul : 2 * N ≤ 4 * Real.pi * N :=
      mul_le_mul_of_nonneg_right hpi (by linarith [hN])
    have hnum : 2 * u ≤ 4 * Real.pi * N := by
      exact (by nlinarith [huN] : 2 * u ≤ 2 * N).trans hmul
    dsimp [theta]
    apply (div_le_iff₀ hden).2
    nlinarith [hnum]
  have hmag : u / (2 * Real.pi * N) + u / (4 * Real.pi * N) ≤ 1 := by
    have hden : 0 < 4 * Real.pi * N := by positivity
    have hsum :
        u / (2 * Real.pi * N) + u / (4 * Real.pi * N) =
          (3 * u) / (4 * Real.pi * N) := by
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos]
      <;> ring
    have hpi : 3 ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hthreeu : 3 * u ≤ 3 * N := by nlinarith [huN]
    have hthreeN : 3 * N ≤ 4 * Real.pi * N :=
      mul_le_mul_of_nonneg_right hpi (by linarith [hN])
    rw [hsum]
    apply (div_le_one hden).2
    exact hthreeu.trans hthreeN
  have hcN : (-c) * N⁻¹ = -(u / (2 * Real.pi * N)) := by
    dsimp [c]
    field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos]
    <;> ring
  have hc2N : (-c) * (2 * N)⁻¹ = -(u / (4 * Real.pi * N)) := by
    dsimp [c]
    field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos]
    <;> ring
  have hDband : ∀ t ∈ I,
      (-1 : ℝ) + theta ≤ D t ∧ D t ≤ (-1 : ℝ) + 1 - theta := by
    intro t ht
    change (-1 : ℝ) + theta ≤ (-c) * t⁻¹ ∧
      (-c) * t⁻¹ ≤ (-1 : ℝ) + 1 - theta
    rcases hloc t ht with ⟨hNt, ht2N⟩
    have htpos := hpos t ht
    have hInvUpper : t⁻¹ ≤ N⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hNpos hNt.le
    have hInvLower : (2 * N)⁻¹ ≤ t⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le htpos ht2N
    have hDlower : (-c) * N⁻¹ ≤ (-c) * t⁻¹ :=
      mul_le_mul_of_nonpos_left hInvUpper hcneg
    have hDupper : (-c) * t⁻¹ ≤ (-c) * (2 * N)⁻¹ :=
      mul_le_mul_of_nonpos_left hInvLower hcneg
    constructor
    · calc
        -1 + theta ≤ (-c) * N⁻¹ := by
          rw [hcN]
          dsimp [theta]
          linarith [hmag]
        _ ≤ (-c) * t⁻¹ := hDlower
    · calc
        (-c) * t⁻¹ ≤ (-c) * (2 * N)⁻¹ := hDupper
        _ = (-1 : ℝ) + 1 - theta := by
          rw [hc2N]
          dsimp [theta]
          ring
  have hDmono' : MonotoneOn D I := hDmono
  have hDband' : ∀ t ∈ Set.Icc a (a + (m : ℝ)),
      (-1 : ℝ) + theta ≤ D t ∧ D t ≤ (-1 : ℝ) + 1 - theta := by
    simpa [I] using hDband
  have hDband'' : ∀ t ∈ Set.Icc a (a + (m : ℝ)),
      (-1 : ℤ) + theta ≤ D t ∧ D t ≤ (-1 : ℤ) + 1 - theta := by
    simpa using hDband'
  have hblock := kusmin_first_derivative_local_block hthetaPos hthetaHalf
    a m (-1) f D hfcont hDcont hDmono' hderiv hDband''
  have hsum :
      (∑ n ∈ realIntegerInterval N N,
        realExponentialPhase f n) =
      ∑ i ∈ Finset.range (m + 1), kusminPhase (f (a + (i : ℝ))) := by
    rw [hIcc]
    have hsum' := sum_int_Icc_eq_sum_range_translate
      (fun n : ℤ => kusminPhase (f (n : ℝ))) lo hi hlohi
    simpa [m, a, realExponentialPhase, kusminPhase, Int.cast_add] using hsum'
  have hkernel :
      ‖∑ n ∈ realIntegerInterval N N,
        realExponentialPhase f n‖ ≤ Real.cot (Real.pi * theta / 2) := by
    rw [hsum]
    exact hblock
  have hargPos : 0 < Real.pi * theta / 2 := by positivity
  have hargHalf : Real.pi * theta / 2 ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos, hthetaHalf]
  have hcot := real_cot_le_inv_of_mem_Ioc hargPos hargHalf
  have hcotEq : 1 / (Real.pi * theta / 2) = 8 * N / u := by
    dsimp [theta]
    field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos, ne_of_gt (by linarith : 0 < u)]
    <;> ring
  have hcot' : Real.cot (Real.pi * theta / 2) ≤ 8 * N / u := by
    rw [← hcotEq]
    exact hcot
  have hden : 0 < 1 + u := by linarith [hu1]
  have hNnonneg : 0 ≤ 8 * N := by positivity
  have hmult : 8 * N ≤ (8 * N) * u := by
    simpa using mul_le_mul_of_nonneg_left
      (by linarith [hu1] : 1 ≤ u) hNnonneg
  have hfrac : 8 * N / u ≤ 16 * N / (1 + u) := by
    apply (div_le_div_iff₀ (by linarith [hu1] : 0 < u) hden).2
    nlinarith [hmult]
  have hroot : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
  have hshort : Real.cot (Real.pi * theta / 2) ≤
      64 * (N / (1 + u) + Real.sqrt u) := by
    have hA : 0 ≤ N / (1 + u) := div_nonneg (by linarith [hN]) (by linarith [hu1])
    have hfinal : 16 * N / (1 + u) ≤
        64 * (N / (1 + u) + Real.sqrt u) := by
      have hsame : 16 * N / (1 + u) = 16 * (N / (1 + u)) := by ring
      rw [hsame]
      nlinarith [hA, hroot]
    exact le_trans hcot' (le_trans hfrac hfinal)
  simpa [f] using hkernel.trans hshort

private theorem gramKernelBound_negative_large
    (N u : ℝ) (hN : 2 ≤ N) (huN : N ≤ u) :
    ‖∑ n ∈ realIntegerInterval N N,
      realExponentialPhase (fun t => -((u / (2 * Real.pi)) * Real.log t)) n‖ ≤
      64 * (N / (1 + u) + Real.sqrt u) := by
  classical
  have hNpos : 0 < N := by linarith [hN]
  let c : ℝ := u / (2 * Real.pi)
  let f : ℝ → ℝ := fun t => -(c * Real.log t)
  let D : ℝ → ℝ := fun t => (-c) * t⁻¹
  let E : ℝ → ℝ := fun t => c * (t⁻¹) ^ 2
  have hfAt : ∀ t, 0 < t → HasDerivAt f (D t) t := by
    intro t ht
    simpa [f, D, c] using
      (Real.hasDerivAt_log ht.ne').const_mul (-c)
  have hDAt : ∀ t, 0 < t → HasDerivAt D (E t) t := by
    intro t ht
    have hinv := (hasDerivAt_id t).inv ht.ne'
    have h := hinv.const_mul (-c)
    convert h using 1
    · ext x
      simp [D]
    · dsimp [E]
      field_simp [ne_of_gt ht]
      <;> ring
  let data : HalfOpenC2Data N N := {
    length_pos := by linarith [hN]
    f := f
    firstDerivative := D
    secondDerivative := E
    f_continuous := by
      have hlog : ContinuousOn Real.log (Set.Ioc N (N + N)) := by
        apply Real.continuousOn_log.mono
        intro t ht
        exact ne_of_gt (lt_trans hNpos ht.1)
      simpa [f] using hlog.const_mul (-c)
    first_continuous := by
      have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Ioc N (N + N)) := by
        apply continuousOn_inv₀.mono
        intro t ht
        exact ne_of_gt (lt_trans hNpos ht.1)
      simpa [D] using hinv.const_mul (-c)
    second_continuous := by
      have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Ioc N (N + N)) := by
        apply continuousOn_inv₀.mono
        intro t ht
        exact ne_of_gt (lt_trans hNpos ht.1)
      simpa [E] using (hinv.pow 2).const_mul c
    f_hasDerivAt := by
      intro t ht
      have htpos : 0 < t := lt_trans hNpos ht.1
      exact hfAt t htpos
    first_hasDerivAt := by
      intro t ht
      have htpos : 0 < t := lt_trans hNpos ht.1
      exact hDAt t htpos
    f_right_hasDerivWithinAt := by
      have htpos : 0 < N + N := by positivity
      exact (hfAt (N + N) htpos).hasDerivWithinAt
    first_right_hasDerivWithinAt := by
      have htpos : 0 < N + N := by positivity
      exact (hDAt (N + N) htpos).hasDerivWithinAt
  }
  let lam : ℝ := u / (8 * Real.pi * N ^ 2)
  let Lambda : ℝ := u / (2 * Real.pi * N ^ 2)
  have huPos : 0 < u := lt_of_lt_of_le (by linarith [hN]) huN
  have hlam : 0 < lam := by
    exact div_pos huPos (by positivity)
  have hsecondLower : ∀ t ∈ Set.Ioc N (N + N),
      lam ≤ data.secondDerivative t := by
    intro t ht
    have htpos : 0 < t := lt_trans hNpos ht.1
    have ht2N : t ≤ 2 * N := by nlinarith [ht.2]
    have hinvLo : (2 * N)⁻¹ ≤ t⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le htpos ht2N
    have hinvSqLo : ((2 * N)⁻¹) ^ 2 ≤ (t⁻¹) ^ 2 := by
      have hprod := mul_nonneg
        (sub_nonneg.mpr hinvLo)
        (add_nonneg (by positivity : 0 ≤ (2 * N)⁻¹)
          (by positivity : 0 ≤ t⁻¹))
      nlinarith
    have hlambdaEq : c * ((2 * N)⁻¹) ^ 2 = lam := by
      dsimp [c, lam]
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos]
      <;> ring
    change lam ≤ c * (t⁻¹) ^ 2
    rw [← hlambdaEq]
    exact mul_le_mul_of_nonneg_left hinvSqLo (by dsimp [c]; positivity)
  have hsecondUpper : ∀ t ∈ Set.Ioc N (N + N),
      data.secondDerivative t ≤ Lambda := by
    intro t ht
    have htpos : 0 < t := lt_trans hNpos ht.1
    have hinvHi : t⁻¹ ≤ N⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hNpos ht.1.le
    have hinvSqHi : (t⁻¹) ^ 2 ≤ (N⁻¹) ^ 2 := by
      have hprod := mul_nonneg
        (sub_nonneg.mpr hinvHi)
        (add_nonneg (by positivity : 0 ≤ t⁻¹)
          (by positivity : 0 ≤ N⁻¹))
      nlinarith
    have hLambdaEq : c * (N⁻¹) ^ 2 = Lambda := by
      dsimp [c, Lambda]
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos]
      <;> ring
    change c * (t⁻¹) ^ 2 ≤ Lambda
    rw [← hLambdaEq]
    exact mul_le_mul_of_nonneg_left hinvSqHi (by dsimp [c]; positivity)
  have hsecond := data.secondDerivative_bound_14_over_5
    (le_trans (by norm_num : (1 : ℝ) ≤ 2) hN) hlam hsecondLower hsecondUpper
  have hbound :
      ‖∑ n ∈ realIntegerInterval N N,
        realExponentialPhase f n‖ ≤
        (14 / 5 : ℝ) / Real.sqrt lam * (Lambda * N + 2) := by
    simpa [data, f, realExponentialPhase, kusminPhase] using hsecond
  let s : ℝ := Real.sqrt u
  let r : ℝ := Real.sqrt (8 * Real.pi)
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (lt_of_lt_of_le (by linarith [hN]) huN)
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hsSq : s ^ 2 = u := by
    dsimp [s]
    rw [Real.sq_sqrt (le_of_lt (lt_of_lt_of_le (by linarith [hN]) huN))]
  have hrSq : r ^ 2 = 8 * Real.pi := by
    dsimp [r]
    rw [Real.sq_sqrt (by positivity)]
  have hrootDen : Real.sqrt lam = s / (r * N) := by
    dsimp [lam, s, r]
    rw [Real.sqrt_div (by positivity)]
    have hden : Real.sqrt (8 * Real.pi * N ^ 2) =
        Real.sqrt (8 * Real.pi) * N := by
      calc
        Real.sqrt (8 * Real.pi * N ^ 2) =
            Real.sqrt (8 * Real.pi) * Real.sqrt (N ^ 2) := by
          rw [Real.sqrt_mul (by positivity)]
        _ = Real.sqrt (8 * Real.pi) * N := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hNpos]
    rw [hden]
  have hLambdaN : Lambda * N = u / (2 * Real.pi * N) := by
    dsimp [Lambda]
    field_simp [ne_of_gt Real.pi_pos, ne_of_gt hNpos]
    <;> ring
  have hformula :
      (14 / 5 : ℝ) / Real.sqrt lam * (Lambda * N + 2) =
        (14 / 5) * (r / (2 * Real.pi) * s + 2 * r * N / s) := by
    rw [hrootDen, hLambdaN, ← hsSq]
    field_simp [ne_of_gt hspos, ne_of_gt hrpos, ne_of_gt hNpos,
      ne_of_gt Real.pi_pos]
    <;> ring
  have hrlt : r < 6 := by
    nlinarith [hrSq, Real.pi_lt_four, hrpos]
  have h2pi : 6 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hratio : r / (2 * Real.pi) ≤ 1 := by
    apply (div_le_one (by linarith [h2pi])).2
    exact hrlt.le.trans h2pi.le
  have htwor : 2 * r ≤ 12 := by nlinarith [hrlt]
  have hNs : N / s ≤ s := by
    apply (div_le_iff₀ hspos).2
    nlinarith [hsSq, huN]
  have hinner : r / (2 * Real.pi) * s + 2 * r * N / s ≤ 13 * s := by
    have hfirst := mul_le_mul_of_nonneg_right hratio (le_of_lt hspos)
    have hsecond : 2 * r * N / s ≤ 12 * s := by
      have hfactor : 2 * r * N / s = (2 * r) * (N / s) := by ring
      rw [hfactor]
      exact le_trans
        (mul_le_mul_of_nonneg_left hNs (by positivity))
        (mul_le_mul_of_nonneg_right htwor (le_of_lt hspos))
    nlinarith
  have hnumeric :
      (14 / 5 : ℝ) / Real.sqrt lam * (Lambda * N + 2) ≤
        64 * (N / (1 + u) + s) := by
    rw [hformula]
    have hsmall : (14 / 5 : ℝ) * (13 * s) ≤ 64 * s := by
      nlinarith [hspos]
    have hA : 0 ≤ N / (1 + u) :=
      div_nonneg (by linarith [hN]) (by positivity)
    have hbase :
        (14 / 5 : ℝ) * (r / (2 * Real.pi) * s + 2 * r * N / s) ≤
          (14 / 5) * (13 * s) :=
      mul_le_mul_of_nonneg_left hinner (by norm_num)
    have hmore : 64 * s ≤ 64 * (N / (1 + u) + s) := by nlinarith
    exact le_trans hbase (le_trans hsmall hmore)
  have htarget :
      64 * (N / (1 + u) + s) ≤
        64 * (N / (1 + u) + Real.sqrt u) := by
    simp [s]
  exact hbound.trans (hnumeric.trans htarget)

private theorem gramKernelBound_negative
    (N u : ℝ) (hN : 2 ≤ N) (hu0 : 0 ≤ u) :
    ‖∑ n ∈ realIntegerInterval N N,
      realExponentialPhase (fun t => -((u / (2 * Real.pi)) * Real.log t)) n‖ ≤
      64 * (N / (1 + u) + Real.sqrt u) := by
  by_cases huLarge : N ≤ u
  · exact gramKernelBound_negative_large N u hN huLarge
  · by_cases huSmall : u ≤ 1
    · exact gramKernelBound_negative_small N u hN hu0 huSmall
    · exact gramKernelBound_negative_medium N u hN
        (lt_of_not_ge huSmall) (le_of_not_ge huLarge)

/-- The scalar Gram-kernel estimate `lgv:kernel`, with the exact angular phase
`n^(iu) = exp(iu log n)` and the source constant 64. -/
theorem gramKernelBound (N u : ℝ) (hN : 2 ≤ N) :
    ‖∑ n ∈ realIntegerInterval N N, scalarGramKernelPhase u n‖ ≤
      64 * (N / (1 + |u|) + Real.sqrt |u|) := by
  classical
  let v : ℝ := |u|
  have hv0 : 0 ≤ v := by dsimp [v]; exact abs_nonneg u
  have hnegative := gramKernelBound_negative N v hN hv0
  have hphaseSum (w : ℝ) :
      (∑ n ∈ realIntegerInterval N N, scalarGramKernelPhase w n) =
        ∑ n ∈ realIntegerInterval N N,
          realExponentialPhase (fun t => (w / (2 * Real.pi)) * Real.log t) n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact scalarGramKernelPhase_eq_realExponentialPhase w n
  by_cases hu : 0 ≤ u
  · have hv : v = u := by dsimp [v]; exact abs_of_nonneg hu
    have hnegativeU :
        ‖∑ n ∈ realIntegerInterval N N,
          realExponentialPhase (fun t => -((u / (2 * Real.pi)) * Real.log t)) n‖ ≤
          64 * (N / (1 + |u|) + Real.sqrt |u|) := by
      simpa [v, abs_of_nonneg hu] using hnegative
    have hstar :
        (∑ n ∈ realIntegerInterval N N,
          realExponentialPhase (fun t => -((u / (2 * Real.pi)) * Real.log t)) n) =
          star (∑ n ∈ realIntegerInterval N N,
            realExponentialPhase (fun t => (u / (2 * Real.pi)) * Real.log t) n) := by
      simpa [mul_neg, neg_mul] using
        (realExponentialPhase_sum_neg
          (fun t => (u / (2 * Real.pi)) * Real.log t) N N)
    have hnorm :
        ‖∑ n ∈ realIntegerInterval N N,
          realExponentialPhase (fun t => (u / (2 * Real.pi)) * Real.log t) n‖ =
        ‖∑ n ∈ realIntegerInterval N N,
          realExponentialPhase (fun t => -((u / (2 * Real.pi)) * Real.log t)) n‖ := by
      calc
        ‖∑ n ∈ realIntegerInterval N N,
            realExponentialPhase (fun t => (u / (2 * Real.pi)) * Real.log t) n‖ =
          ‖star (∑ n ∈ realIntegerInterval N N,
            realExponentialPhase (fun t => (u / (2 * Real.pi)) * Real.log t) n)‖ := by
              rw [norm_star]
        _ = ‖∑ n ∈ realIntegerInterval N N,
            realExponentialPhase (fun t => -((u / (2 * Real.pi)) * Real.log t)) n‖ := by
              rw [← hstar]
    calc
      ‖∑ n ∈ realIntegerInterval N N, scalarGramKernelPhase u n‖ =
          ‖∑ n ∈ realIntegerInterval N N,
            realExponentialPhase (fun t => (u / (2 * Real.pi)) * Real.log t) n‖ := by
              rw [hphaseSum]
      _ = ‖∑ n ∈ realIntegerInterval N N,
            realExponentialPhase (fun t => -((u / (2 * Real.pi)) * Real.log t)) n‖ := hnorm
      _ ≤ 64 * (N / (1 + |u|) + Real.sqrt |u|) := hnegativeU
  · have huNeg : u < 0 := lt_of_not_ge hu
    have hvEq : u = -v := by
      dsimp [v]
      rw [abs_of_neg huNeg]
      ring
    have hphaseNeg :
        (∑ n ∈ realIntegerInterval N N, scalarGramKernelPhase u n) =
          ∑ n ∈ realIntegerInterval N N,
            realExponentialPhase (fun t => -((v / (2 * Real.pi)) * Real.log t)) n := by
      rw [hphaseSum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [hvEq]
      congr 1
      ring_nf
    have hnegativeV :
        ‖∑ n ∈ realIntegerInterval N N,
          realExponentialPhase (fun t => -((v / (2 * Real.pi)) * Real.log t)) n‖ ≤
          64 * (N / (1 + |u|) + Real.sqrt |u|) := by
      simpa [v] using hnegative
    calc
      ‖∑ n ∈ realIntegerInterval N N, scalarGramKernelPhase u n‖ =
          ‖∑ n ∈ realIntegerInterval N N,
            realExponentialPhase (fun t => -((v / (2 * Real.pi)) * Real.log t)) n‖ := by
              rw [hphaseNeg]
      _ ≤ 64 * (N / (1 + |u|) + Real.sqrt |u|) := hnegativeV

#print axioms gramKernelBound

end FractionalPrimes.Literature.LargeValues
