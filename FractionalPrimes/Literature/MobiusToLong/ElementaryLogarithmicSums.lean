module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Int.Order.Units
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.RingTheory.Coprime.Basic
public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletData
public import FractionalPrimes.Literature.Twisted.CharacterDataAdapter

@[expose] public section

namespace FractionalPrimes.Literature.MobiusToLong

open Set MeasureTheory intervalIntegral
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Reciprocal

theorem abs_log_sum_Icc_floor_le {y : ℝ} (hy : 1 ≤ y) :
    |(∑ m ∈ Finset.Icc 1 (Nat.floor y), Real.log (m : ℝ)) -
      (y * Real.log y - y)| ≤ 2 * Real.log (Real.exp 1 * y) := by
  let n : ℕ := Nat.floor y
  let S : ℝ := ∑ m ∈ Finset.Icc 1 n, Real.log (m : ℝ)
  let Iₙ : ℝ := ∫ t in ((1 : ℕ) : ℝ)..(n : ℝ), Real.log t
  let Iᵧ : ℝ := ∫ t in ((1 : ℕ) : ℝ)..y, Real.log t
  let In1 : ℝ := ∫ t in ((1 : ℕ) : ℝ)..((n + 1 : ℕ) : ℝ), Real.log t
  change |S - (y * Real.log y - y)| ≤ 2 * Real.log (Real.exp 1 * y)
  have hn : 1 ≤ n := by
    dsimp [n]
    exact Nat.le_floor (by exact_mod_cast hy)
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfloor_le : (n : ℝ) ≤ y := by
    dsimp [n]
    exact Nat.floor_le (by linarith)
  have hy_lt_succ : y < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one y
  have hy_le_succ : y ≤ ((n + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hy_lt_succ.le
  have hlogmono :
      MonotoneOn Real.log (Icc ((1 : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) := by
    intro x hx z hz hxz
    exact Real.log_le_log (lt_of_lt_of_le (by norm_num) hx.1) hxz
  have hlogmono_small :
      MonotoneOn Real.log (Icc ((1 : ℕ) : ℝ) (n : ℝ)) := by
    intro x hx z hz hxz
    exact Real.log_le_log (lt_of_lt_of_le (by norm_num) hx.1) hxz
  have hsum_lower_raw : Iₙ ≤
      ∑ i ∈ Finset.Ico 1 n, Real.log ((i + 1 : ℕ) : ℝ) := by
    dsimp [Iₙ]
    exact hlogmono_small.integral_le_sum_Ico (by exact_mod_cast hn)
  have hshift :
      (∑ i ∈ Finset.Ico 1 n, Real.log ((i + 1 : ℕ) : ℝ)) = S := by
    calc
      _ = ∑ m ∈ Finset.Icc 2 n, Real.log (m : ℝ) := by
        apply Finset.sum_bij (fun i _ => i + 1)
        · intro i hi
          simp only [Finset.mem_Ico] at hi
          simp only [Finset.mem_Icc]
          omega
        · intro i hi j hj hij
          omega
        · intro m hm
          simp only [Finset.mem_Icc] at hm
          refine ⟨m - 1, ?_, ?_⟩
          · simp only [Finset.mem_Ico]
            omega
          · omega
        · intro i hi
          rfl
      _ = S := by
        dsimp [S]
        have hset : insert 1 (Finset.Icc 2 n) = Finset.Icc 1 n := by
          ext m
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega
        rw [← hset]
        simp [Real.log_one]
  have hsum_lower : Iₙ ≤ S := by rw [← hshift]; exact hsum_lower_raw
  have hsum_upper : S ≤ In1 := by
    dsimp [S, In1]
    simpa only [Finset.Ico_add_one_right_eq_Icc] using
      hlogmono.sum_le_integral_Ico (a := 1) (b := n + 1) (by omega)
  have hIn_le_Iy : Iₙ ≤ Iᵧ := by
    have hdecomp : Iₙ + (∫ t in (n : ℝ)..y, Real.log t) = Iᵧ := by
      dsimp [Iₙ, Iᵧ]
      exact intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_log') (intervalIntegrable_log')
    have hnonneg : 0 ≤ ∫ t in (n : ℝ)..y, Real.log t :=
      intervalIntegral.integral_nonneg hfloor_le (fun t ht =>
        Real.log_nonneg (le_trans hnreal ht.1))
    linarith
  have hIy_le_In1 : Iᵧ ≤ In1 := by
    have hdecomp : Iᵧ + (∫ t in y..((n + 1 : ℕ) : ℝ), Real.log t) = In1 := by
      dsimp [Iᵧ, In1]
      exact intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_log') (intervalIntegrable_log')
    have hnonneg : 0 ≤ ∫ t in y..((n + 1 : ℕ) : ℝ), Real.log t :=
      intervalIntegral.integral_nonneg hy_le_succ (fun t ht =>
        Real.log_nonneg (le_trans hy ht.1))
    linarith
  have hIn_succ_decomp :
      Iₙ + (∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), Real.log t) = In1 := by
    dsimp [Iₙ, In1]
    exact intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_log') (intervalIntegrable_log')
  have hgap_piece :
      (∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), Real.log t) ≤ Real.log (y + 1) := by
    calc
      (∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), Real.log t) ≤
          ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), Real.log (y + 1) := by
        apply intervalIntegral.integral_mono_on
          (a := (n : ℝ)) (b := ((n + 1 : ℕ) : ℝ))
          (by exact_mod_cast Nat.le_succ n)
          intervalIntegrable_log' intervalIntegrable_const
        intro t ht
        exact Real.log_le_log (by linarith [hnreal, ht.1]) (by
          have ht' : t ≤ (n : ℝ) + 1 := by exact_mod_cast ht.2
          linarith [hy_le_succ])
      _ = Real.log (y + 1) := by simp [intervalIntegral.integral_const]
  have hgap : In1 - Iₙ ≤ Real.log (y + 1) := by linarith
  have hS_Iy : |S - Iᵧ| ≤ Real.log (y + 1) := by
    rw [abs_le]
    constructor <;> linarith
  have hsum_eval : Iᵧ = y * Real.log y - y + 1 := by
    dsimp [Iᵧ]
    simp [integral_log, Real.log_one]
  have hy_sq_bound : y + 1 ≤ Real.exp 1 * y ^ 2 := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      calc
        (2 : ℝ) = 1 + 1 := by norm_num
        _ ≤ Real.exp 1 := Real.add_one_le_exp 1
    have hey : Real.exp 1 ≤ Real.exp 1 * y := by
      simpa using mul_le_mul_of_nonneg_left hy (Real.exp_nonneg 1)
    have htwo : (2 : ℝ) ≤ Real.exp 1 * y := he.trans hey
    have hprod : 2 * y ≤ (Real.exp 1 * y) * y :=
      mul_le_mul_of_nonneg_right htwo (by linarith)
    calc
      y + 1 ≤ 2 * y := by linarith
      _ ≤ Real.exp 1 * y ^ 2 := by nlinarith [hprod]
  have hy_sq_pos : 0 < y + 1 := by linarith
  have hy_pos : 0 < y := by linarith
  have hlog_bound : Real.log (y + 1) ≤ 1 + 2 * Real.log y := by
    calc
      Real.log (y + 1) ≤ Real.log (Real.exp 1 * y ^ 2) :=
        Real.log_le_log hy_sq_pos hy_sq_bound
      _ = 1 + 2 * Real.log y := by
        rw [Real.log_mul (Real.exp_ne_zero 1) (pow_ne_zero 2 hy_pos.ne'),
          Real.log_exp, Real.log_pow]
        norm_num
  have hlog_exp : Real.log (Real.exp 1 * y) = 1 + Real.log y := by
    rw [Real.log_mul (Real.exp_ne_zero 1) hy_pos.ne', Real.log_exp]
  have hfinal_log : 1 + Real.log (y + 1) ≤ 2 * Real.log (Real.exp 1 * y) := by
    calc
      1 + Real.log (y + 1) ≤ 1 + (1 + 2 * Real.log y) := by nlinarith [hlog_bound]
      _ = 2 * Real.log (Real.exp 1 * y) := by rw [hlog_exp]; ring
  calc
    |S - (y * Real.log y - y)| = |(S - Iᵧ) + 1| := by
      congr 1
      rw [hsum_eval]
      ring
    _ ≤ |S - Iᵧ| + |(1 : ℝ)| := abs_add_le _ _
    _ ≤ Real.log (y + 1) + 1 := by rw [abs_one]; linarith
    _ ≤ 2 * Real.log (Real.exp 1 * y) := by nlinarith [hfinal_log]

/-- A nonprincipal character cannot have modulus one: the unique character at
level one is the principal character. This makes the nonprincipal character
clauses vacuous at q = 1, exactly as in the approved statement. -/
theorem nonprincipal_character_level_gt_one {q : ℕ} [NeZero q]
    (χ : BlueprintCharacter q) (hχ : χ ≠ principalCharacter q) : 1 < q := by
  by_contra hnot
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : q = 1 := by omega
  subst q
  exact hχ (modulus_one_character_eq_principal χ)

/-- The unweighted initial character sum is bounded by its modulus. The
partial sum convention is the exact real-cutoff sum through `Nat.floor y`. -/
theorem nonprincipal_character_sum_Icc_floor_norm_le {q : ℕ} [NeZero q]
    (χ : BlueprintCharacter q) (hχ : χ ≠ principalCharacter q)
    {y : ℝ} (hy : 1 ≤ y) :
    ‖∑ m ∈ Finset.Icc 1 (Nat.floor y), evalInt χ (m : ℤ)‖ ≤ (q : ℝ) := by
  simpa [continuedDirichletPartialSum] using
    (continuedDirichletPartialSum_norm_le_modulus χ hχ y hy)

/-- The logarithmically weighted initial character sum has the exact
`2 q log y` bound, obtained by finite Abel summation. -/
theorem nonprincipal_character_log_sum_Icc_floor_norm_le {q : ℕ} [NeZero q]
    (χ : BlueprintCharacter q) (hχ : χ ≠ principalCharacter q)
    {y : ℝ} (hy : 1 ≤ y) :
    ‖∑ m ∈ Finset.Icc 1 (Nat.floor y),
      evalInt χ (m : ℤ) * (Real.log (m : ℝ) : ℂ)‖ ≤
        2 * (q : ℝ) * Real.log y := by
  let c : ℕ → ℂ := fun n => evalInt χ (n : ℤ)
  let f : ℝ → ℂ := fun t => (Real.log t : ℂ)
  let P : ℝ → ℂ := fun t => ∑ n ∈ Finset.Icc 0 (Nat.floor t), c n
  have hq : 1 < q := nonprincipal_character_level_gt_one χ hχ
  have hc0 : c 0 = 0 := by
    dsimp [c]
    apply (evalInt_eq_zero_iff χ 0).2
    intro hcop
    have hunit : IsUnit (q : ℤ) := isCoprime_zero_left.mp hcop
    have hunit_abs : |(q : ℤ)| = 1 := Int.isUnit_iff_abs_eq.mp hunit
    have hqpos : (1 : ℤ) < (q : ℤ) := by exact_mod_cast hq
    rw [abs_of_nonneg (show (0 : ℤ) ≤ (q : ℤ) by omega)] at hunit_abs
    omega
  have hprefix_eq (t : ℝ) (ht : 1 ≤ t) :
      P t = continuedDirichletPartialSum χ t ht := by
    have heval0 : evalInt χ (0 : ℤ) = 0 := by simpa [c] using hc0
    have hhead0 : c 0 = 0 := by
      simpa [c] using heval0
    have hIcc_Ioc :
        (∑ n ∈ Finset.Icc 0 (Nat.floor t), c n) =
          ∑ n ∈ Finset.Ioc 0 (Nat.floor t), c n := by
      rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
      rw [hhead0, zero_add]
    change (∑ n ∈ Finset.Icc 0 (Nat.floor t), c n) =
      ∑ n ∈ Finset.Icc 1 (Nat.floor t), c n
    calc
      _ = ∑ n ∈ Finset.Ioc 0 (Nat.floor t), c n := hIcc_Ioc
      _ = ∑ n ∈ Finset.Icc 1 (Nat.floor t), c n := by
        rw [← Finset.Icc_add_one_left_eq_Ioc 0 (Nat.floor t)]
        simp only [zero_add]
  have hprefix_norm (t : ℝ) (ht : 1 ≤ t) : ‖P t‖ ≤ (q : ℝ) := by
    rw [hprefix_eq t ht]
    exact continuedDirichletPartialSum_norm_le_modulus χ hχ t ht
  let g : ℝ → ℂ := fun t => ((t⁻¹ : ℝ) : ℂ)
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) y) :
      HasDerivAt f ((t⁻¹ : ℝ) : ℂ) t := by
    dsimp [f]
    exact (Real.hasDerivAt_log
      (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).ofReal_comp
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) y, DifferentiableAt ℝ f t := by
    intro t ht
    exact (hderiv t ht).differentiableAt
  have hinv_cont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc (1 : ℝ) y) :=
    continuousOn_id.inv₀ fun t ht =>
      ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
  have hg_cont : ContinuousOn g (Set.Icc (1 : ℝ) y) := by
    exact Complex.continuous_ofReal.comp_continuousOn hinv_cont
  have hderiv_cont : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) y) := by
    apply hg_cont.congr
    intro t ht
    exact (hderiv t ht).deriv
  have hint : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) y) :=
    hderiv_cont.integrableOn_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul
    (c := c) (f := f) (show (0 : ℝ) ≤ 1 by norm_num) hy hdiff hint
  have habel_simpl_floor :
      (∑ k ∈ Finset.Ioc (Nat.floor (1 : ℝ)) (Nat.floor y), f k * c k) =
        f y * P y - ∫ t in Set.Ioc (1 : ℝ) y, deriv f t * P t := by
    calc
      _ = f y * (∑ n ∈ Finset.Icc 0 (Nat.floor y), c n) -
            f 1 * (∑ n ∈ Finset.Icc 0 (Nat.floor (1 : ℝ)), c n) -
              ∫ t in Set.Ioc (1 : ℝ) y,
                deriv f t * (∑ n ∈ Finset.Icc 0 (Nat.floor t), c n) := habel
      _ = f y * P y - ∫ t in Set.Ioc (1 : ℝ) y, deriv f t * P t := by
        simp [f, P, Real.log_one]
  have hfirst :
      evalInt χ ((1 : ℕ) : ℤ) * (Real.log ((1 : ℕ) : ℝ) : ℂ) = 0 := by
    have hlog_one : Real.log ((1 : ℕ) : ℝ) = 0 := by norm_num
    calc
      _ = evalInt χ ((1 : ℕ) : ℤ) * (0 : ℂ) := by rw [hlog_one]; simp
      _ = 0 := mul_zero _
  have hsum_char :
      (∑ m ∈ Finset.Icc 1 (Nat.floor y),
        evalInt χ (m : ℤ) * (Real.log (m : ℝ) : ℂ)) =
        ∑ k ∈ Finset.Ioc 1 (Nat.floor y), f k * c k := by
    have hfloor : 1 ≤ Nat.floor y := Nat.le_floor (by exact_mod_cast hy)
    rw [Finset.Icc_eq_cons_Ioc hfloor, Finset.sum_cons, hfirst, zero_add]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f, c]
    ring
  have habel_simpl :
      (∑ k ∈ Finset.Ioc 1 (Nat.floor y), f k * c k) =
        f y * P y - ∫ t in Set.Ioc (1 : ℝ) y, deriv f t * P t := by
    simpa only [Nat.floor_one] using habel_simpl_floor
  have hlog_nonneg : 0 ≤ Real.log y := Real.log_nonneg hy
  have hendpoint : ‖f y * P y‖ ≤ (q : ℝ) * Real.log y := by
    have hfy : ‖f y‖ = Real.log y := by
      simp [f, Complex.norm_real, abs_of_nonneg hlog_nonneg]
    calc
      ‖f y * P y‖ = ‖f y‖ * ‖P y‖ := norm_mul _ _
      _ = Real.log y * ‖P y‖ := by rw [hfy]
      _ ≤ Real.log y * (q : ℝ) :=
        mul_le_mul_of_nonneg_left (hprefix_norm y hy) hlog_nonneg
      _ = (q : ℝ) * Real.log y := by ring
  have hpointwise (t : ℝ) (ht : t ∈ Set.Ioc (1 : ℝ) y) :
      ‖deriv f t * P t‖ ≤ (q : ℝ) / t := by
    have htpos : 0 < t := lt_trans zero_lt_one ht.1
    have hprefix := hprefix_norm t ht.1.le
    have hderivval : deriv f t = ((t⁻¹ : ℝ) : ℂ) :=
      (hderiv t ⟨ht.1.le, ht.2⟩).deriv
    calc
      ‖deriv f t * P t‖ = t⁻¹ * ‖P t‖ := by
        rw [norm_mul, hderivval, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr htpos.le)]
      _ ≤ t⁻¹ * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hprefix (inv_nonneg.mpr htpos.le)
      _ = (q : ℝ) / t := by rw [div_eq_mul_inv]; ring
  have hnorm_ae : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Set.Ioc (1 : ℝ) y → ‖deriv f t * P t‖ ≤ (q : ℝ) / t :=
    Filter.Eventually.of_forall fun t ht => hpointwise t ht
  have hinv_nonzero : ∀ t : ℝ, t ∈ Set.uIcc (1 : ℝ) y → t ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
  have hinv_int : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 y :=
    intervalIntegrable_inv hinv_nonzero continuousOn_id
  have hmajor_int : IntervalIntegrable (fun t : ℝ => (q : ℝ) / t) volume 1 y := by
    simpa only [div_eq_mul_inv] using hinv_int.const_mul (q : ℝ)
  have hmajor_value :
      (∫ t in (1 : ℝ)..y, (q : ℝ) / t) = (q : ℝ) * Real.log y := by
    calc
      _ = (q : ℝ) * (∫ t in (1 : ℝ)..y, 1 / t) := by
        rw [show (fun t : ℝ => (q : ℝ) / t) =
          fun t => (q : ℝ) * (1 / t) by funext t; ring,
          intervalIntegral.integral_const_mul]
      _ = (q : ℝ) * Real.log y := by
        rw [integral_one_div_of_pos (by norm_num) (by linarith)]
        simp
  have hIntegral :
      ‖∫ t in Set.Ioc (1 : ℝ) y, deriv f t * P t‖ ≤
        (q : ℝ) * Real.log y := by
    calc
      _ = ‖∫ t in (1 : ℝ)..y, deriv f t * P t‖ := by
        rw [intervalIntegral.integral_of_le hy]
      _ ≤ ∫ t in (1 : ℝ)..y, (q : ℝ) / t :=
        intervalIntegral.norm_integral_le_of_norm_le hy hnorm_ae hmajor_int
      _ = (q : ℝ) * Real.log y := hmajor_value
  have hsum_eq :
      (∑ m ∈ Finset.Icc 1 (Nat.floor y),
        evalInt χ (m : ℤ) * (Real.log (m : ℝ) : ℂ)) =
        f y * P y - ∫ t in Set.Ioc (1 : ℝ) y, deriv f t * P t := by
    rw [hsum_char, habel_simpl]
  rw [hsum_eq]
  calc
    ‖f y * P y - ∫ t in Set.Ioc (1 : ℝ) y, deriv f t * P t‖ ≤
        ‖f y * P y‖ +
          ‖∫ t in Set.Ioc (1 : ℝ) y, deriv f t * P t‖ := norm_sub_le _ _
    _ ≤ (q : ℝ) * Real.log y + (q : ℝ) * Real.log y :=
      add_le_add hendpoint hIntegral
    _ = 2 * (q : ℝ) * Real.log y := by ring

end FractionalPrimes.Literature.MobiusToLong
