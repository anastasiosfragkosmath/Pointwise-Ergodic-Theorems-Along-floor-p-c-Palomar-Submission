module

public import FractionalPrimes.Chebyshev
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Finite Abel summation over the primes

This module formalizes the finite prime Abel identity and the explicit
coefficient estimate from blueprint `er:abel`.
-/

@[expose] public section

open MeasureTheory
open Filter
open scoped Topology
open scoped Nat.Prime

namespace FractionalPrimes

noncomputable section

/-- The prime-log partial sum of a sequence with values in a real normed
vector space. The `Icc 0 N` convention agrees with the paper's inclusive
prime cutoff; the zero and one terms vanish because neither is prime. -/
def primeLogPartialSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℕ → E) (N : ℕ) : E :=
  ∑ n ∈ Finset.Icc 0 N, if Nat.Prime n then
    Real.log (n : ℝ) • g n else 0

/-- The unweighted finite prime sum, with the same inclusive endpoint. -/
def primePartialSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℕ → E) (N : ℕ) : E :=
  ∑ n ∈ Finset.Icc 0 N, if Nat.Prime n then g n else 0

/-- The positive Abel coefficient `1/log n - 1/log(n+1)`. -/
def primeAbelDifference (n : ℕ) : ℝ :=
  (Real.log (n : ℝ))⁻¹ - (Real.log ((n + 1 : ℕ) : ℝ))⁻¹

/-- The positive integral kernel used to estimate the Abel coefficients. -/
def primeAbelIntegralKernel (t : ℝ) : ℝ :=
  1 / (Real.log t) ^ 2

private def primeAbelDerivativeKernel (t : ℝ) : ℝ :=
  1 / (t * (Real.log t) ^ 2)

/-- The total coefficient mass `H_N = sum_{2 ≤ n < N} n d_n`. -/
def primeAbelRemainderCoefficient (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 2 N, (n : ℝ) * primeAbelDifference n

/-- Each Abel coefficient is positive at its stated range of indices. -/
theorem primeAbelDifference_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < primeAbelDifference n := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hnlt : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self n
  have hloglt : Real.log (n : ℝ) < Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_lt_log (by positivity) hnlt
  dsimp [primeAbelDifference]
  exact sub_pos.mpr (by simpa [one_div] using one_div_lt_one_div_of_lt hlog hloglt)

private theorem primeAbelDerivativeKernel_eq_deriv {t : ℝ} (ht : 1 < t) :
    deriv (fun x : ℝ => -(Real.log x)⁻¹) t = primeAbelDerivativeKernel t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hinv := (Real.hasDerivAt_log ht0).inv hlog
  have hneg := hinv.neg
  have hformula := hneg.deriv
  have hfun : (fun x : ℝ => -(Real.log x)⁻¹) = -Real.log⁻¹ := rfl
  rw [hfun, hformula]
  dsimp [primeAbelDerivativeKernel]
  field_simp [ht0, hlog]

private theorem primeAbelIntegralKernel_continuousOn {a b : ℝ} (ha : 2 ≤ a) :
    ContinuousOn primeAbelIntegralKernel (Set.Icc a b) := by
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
        (le_trans ha hx.1)))
  have hlog_ne : ∀ x ∈ Set.Icc a b, Real.log x ≠ 0 := by
    intro x hx
    exact ne_of_gt (Real.log_pos (by linarith [ha, hx.1]))
  have hlog_sq_ne : ∀ x ∈ Set.Icc a b, (Real.log x) ^ 2 ≠ 0 := by
    intro x hx
    exact pow_ne_zero 2 (hlog_ne x hx)
  exact continuousOn_const.div (hlog.pow 2) hlog_sq_ne

private theorem primeAbelDerivativeKernel_continuousOn {a b : ℝ} (ha : 2 ≤ a) :
    ContinuousOn primeAbelDerivativeKernel (Set.Icc a b) := by
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
        (le_trans ha hx.1)))
  have hden_ne : ∀ x ∈ Set.Icc a b, x * (Real.log x) ^ 2 ≠ 0 := by
    intro x hx
    have hxpos : 0 < x := by linarith [ha, hx.1]
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith [ha, hx.1])
    exact mul_ne_zero (ne_of_gt hxpos) (pow_ne_zero 2 hlogpos.ne')
  exact continuousOn_const.div (continuousOn_id.mul (hlog.pow 2)) hden_ne

private theorem primeAbelDifference_eq_intervalIntegral {n : ℕ} (hn : 2 ≤ n) :
    primeAbelDifference n =
      ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), primeAbelDerivativeKernel t := by
  let a : ℝ := n
  let b : ℝ := (n + 1 : ℕ)
  have hab : a ≤ b := by dsimp [a, b]; exact_mod_cast (Nat.le_succ n)
  have hderiv : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ (fun x : ℝ => -(Real.log x)⁻¹) t := by
    intro t ht
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using ht
    have htone : 1 < t := by
      dsimp [a] at ht'
      have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith [ht'.1, hnR]
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one htone)
    have hlog0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos htone)
    exact ((Real.differentiableAt_log ht0).inv hlog0).neg
  have hderivEq : ∀ t ∈ Set.uIcc a b,
      deriv (fun x : ℝ => -(Real.log x)⁻¹) t = primeAbelDerivativeKernel t := by
    intro t ht
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using ht
    have htone : 1 < t := by
      dsimp [a] at ht'
      have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith [ht'.1, hnR]
    exact primeAbelDerivativeKernel_eq_deriv htone
  have hcont := primeAbelDerivativeKernel_continuousOn (a := a) (b := b)
    (by dsimp [a]; exact_mod_cast hn)
  have hinter : IntervalIntegrable primeAbelDerivativeKernel volume a b := by
    exact hcont.intervalIntegrable_of_Icc hab
  have hint : IntervalIntegrable
      (deriv fun x : ℝ => -(Real.log x)⁻¹) volume a b :=
    hinter.congr_uIoo (fun t ht =>
      (hderivEq t (Set.uIoo_subset_uIcc_self ht)).symm)
  have hftc := intervalIntegral.integral_deriv_eq_sub hderiv hint
  have hvalue : (fun x : ℝ => -(Real.log x)⁻¹) b -
      (fun x : ℝ => -(Real.log x)⁻¹) a = primeAbelDifference n := by
    simp only [a, b, primeAbelDifference, Nat.cast_add, Nat.cast_one]
    ring
  calc
    primeAbelDifference n =
        (fun x : ℝ => -(Real.log x)⁻¹) b -
          (fun x : ℝ => -(Real.log x)⁻¹) a := hvalue.symm
    _ = ∫ t in a..b, deriv (fun x : ℝ => -(Real.log x)⁻¹) t := hftc.symm
    _ = ∫ t in a..b, primeAbelDerivativeKernel t :=
      intervalIntegral.integral_congr hderivEq

/-- The weighted discrete coefficient is bounded by the corresponding unit
interval integral. -/
private theorem primeAbelCoefficientTerm_le_integral {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) * primeAbelDifference n ≤
      ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), primeAbelIntegralKernel t := by
  have ha : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_succ n)
  have hDInt : IntervalIntegrable primeAbelDerivativeKernel volume
      (n : ℝ) ((n + 1 : ℕ) : ℝ) :=
    (primeAbelDerivativeKernel_continuousOn (a := (n : ℝ))
      (b := ((n + 1 : ℕ) : ℝ)) ha).intervalIntegrable_of_Icc hb
  have hDScaled : IntervalIntegrable
      (fun t : ℝ => (n : ℝ) * primeAbelDerivativeKernel t) volume
      (n : ℝ) ((n + 1 : ℕ) : ℝ) := hDInt.const_mul (n : ℝ)
  have hKInt : IntervalIntegrable primeAbelIntegralKernel volume
      (n : ℝ) ((n + 1 : ℕ) : ℝ) :=
    (primeAbelIntegralKernel_continuousOn (a := (n : ℝ))
      (b := ((n + 1 : ℕ) : ℝ)) ha).intervalIntegrable_of_Icc hb
  have hpoint : ∀ t ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ),
      (n : ℝ) * primeAbelDerivativeKernel t ≤ primeAbelIntegralKernel t := by
    intro t ht
    have htpos : 0 < t := by linarith [ha, ht.1]
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ha, ht.1])
    have hlogsqpos : 0 < (Real.log t) ^ 2 := sq_pos_of_pos hlogpos
    change (n : ℝ) * (1 / (t * (Real.log t) ^ 2)) ≤
      1 / (Real.log t) ^ 2
    have hprod : 0 ≤ (t - (n : ℝ)) * (Real.log t) ^ 2 :=
      mul_nonneg (sub_nonneg.mpr ht.1) (le_of_lt hlogsqpos)
    have hden : 0 < t * (Real.log t) ^ 2 := mul_pos htpos hlogsqpos
    have hrewrite : (n : ℝ) * (1 / (t * (Real.log t) ^ 2)) =
        (n : ℝ) / (t * (Real.log t) ^ 2) := by ring
    rw [hrewrite]
    apply (div_le_div_iff₀ hden hlogsqpos).2
    nlinarith
  calc
    (n : ℝ) * primeAbelDifference n =
        ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ),
          (n : ℝ) * primeAbelDerivativeKernel t := by
            rw [primeAbelDifference_eq_intervalIntegral hn,
              ← intervalIntegral.integral_const_mul]
    _ ≤ ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ),
          primeAbelIntegralKernel t :=
        intervalIntegral.integral_mono_on hb hDScaled hKInt hpoint

private theorem primeAbelRemainderCoefficient_le_integral {N : ℕ}
    (hN : 2 ≤ N) :
    primeAbelRemainderCoefficient N ≤
      ∫ t in (2 : ℝ)..(N : ℝ), primeAbelIntegralKernel t := by
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpiece : ∀ n ∈ Finset.Ico 2 N,
      IntervalIntegrable primeAbelIntegralKernel volume (n : ℝ)
        ((n + 1 : ℕ) : ℝ) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Ico.mp hn).1
    have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hstep : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_succ n)
    exact (primeAbelIntegralKernel_continuousOn (a := (n : ℝ))
      (b := ((n + 1 : ℕ) : ℝ)) hnreal).intervalIntegrable_of_Icc hstep
  have hpartition :=
    intervalIntegral.sum_integral_adjacent_intervals_Ico
      (μ := volume) (f := primeAbelIntegralKernel)
      (a := fun n : ℕ => (n : ℝ)) (m := 2) (n := N) hN
      (by simpa using hpiece)
  calc
    primeAbelRemainderCoefficient N =
        ∑ n ∈ Finset.Ico 2 N,
          (n : ℝ) * primeAbelDifference n := rfl
    _ ≤ ∑ n ∈ Finset.Ico 2 N,
          ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ), primeAbelIntegralKernel t := by
        apply Finset.sum_le_sum
        intro n hn
        exact primeAbelCoefficientTerm_le_integral
          (Finset.mem_Ico.mp hn).1
    _ = ∫ t in (2 : ℝ)..(N : ℝ), primeAbelIntegralKernel t := by
        simpa using hpartition

/-- The exact explicit coefficient bound from the finite Abel lemma. -/
theorem primeAbelRemainderCoefficient_bounds {N : ℕ} (hN : 4 ≤ N) :
    0 ≤ primeAbelRemainderCoefficient N ∧
      primeAbelRemainderCoefficient N ≤
        ∫ t in (2 : ℝ)..(N : ℝ), primeAbelIntegralKernel t ∧
      (∫ t in (2 : ℝ)..(N : ℝ), primeAbelIntegralKernel t) ≤
        Real.sqrt (N : ℝ) / (Real.log 2) ^ 2 +
          4 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
  have hN2 : 2 ≤ N := by omega
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNpos : 0 < (N : ℝ) := by positivity
  have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hsqrtlo : (2 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by positivity)).2
      (by exact_mod_cast hN)
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hsqrtupper : Real.sqrt (N : ℝ) ≤ (N : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hNge1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsplitInt : IntervalIntegrable primeAbelIntegralKernel volume
      (2 : ℝ) (Real.sqrt (N : ℝ)) ∧
      IntervalIntegrable primeAbelIntegralKernel volume
        (Real.sqrt (N : ℝ)) (N : ℝ) := by
    constructor
    · exact (primeAbelIntegralKernel_continuousOn (a := (2 : ℝ))
        (b := Real.sqrt (N : ℝ)) (by norm_num)).intervalIntegrable_of_Icc hsqrtlo
    · exact (primeAbelIntegralKernel_continuousOn (a := Real.sqrt (N : ℝ))
        (b := (N : ℝ)) (by linarith)).intervalIntegrable_of_Icc hsqrtupper
  have hsplit :
      (∫ t in (2 : ℝ)..(N : ℝ), primeAbelIntegralKernel t) =
        (∫ t in (2 : ℝ)..Real.sqrt (N : ℝ), primeAbelIntegralKernel t) +
          ∫ t in Real.sqrt (N : ℝ)..(N : ℝ), primeAbelIntegralKernel t := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      hsplitInt.1 hsplitInt.2).symm
  have hsmall :
      (∫ t in (2 : ℝ)..Real.sqrt (N : ℝ), primeAbelIntegralKernel t) ≤
        Real.sqrt (N : ℝ) / (Real.log 2) ^ 2 := by
    let C : ℝ := 1 / (Real.log 2) ^ 2
    have hCpos : 0 < C := by dsimp [C]; positivity
    have hconstInt : IntervalIntegrable (fun _ : ℝ => C) volume
        (2 : ℝ) (Real.sqrt (N : ℝ)) := by
      exact continuousOn_const.intervalIntegrable_of_Icc hsqrtlo
    have hpoint : ∀ t ∈ Set.Icc (2 : ℝ) (Real.sqrt (N : ℝ)),
        primeAbelIntegralKernel t ≤ C := by
      intro t ht
      have hlogt : Real.log 2 ≤ Real.log t :=
        Real.log_le_log (by norm_num) ht.1
      have hlogtpos : 0 < Real.log t := lt_of_lt_of_le hlog2 hlogt
      have hsq : (Real.log 2) ^ 2 ≤ (Real.log t) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self (le_of_lt hlog2) hlogt
      dsimp [primeAbelIntegralKernel, C]
      exact one_div_le_one_div_of_le (sq_pos_of_pos hlog2) hsq
    calc
      _ ≤ ∫ t in (2 : ℝ)..Real.sqrt (N : ℝ), C :=
        intervalIntegral.integral_mono_on hsqrtlo hsplitInt.1 hconstInt hpoint
      _ = (Real.sqrt (N : ℝ) - 2) * C := by
        simp [intervalIntegral.integral_const]
      _ ≤ Real.sqrt (N : ℝ) * C := by
        apply mul_le_mul_of_nonneg_right
          (by linarith : Real.sqrt (N : ℝ) - 2 ≤ Real.sqrt (N : ℝ))
          (le_of_lt hCpos)
      _ = Real.sqrt (N : ℝ) / (Real.log 2) ^ 2 := by dsimp [C]; ring_nf
  have hlarge :
      (∫ t in Real.sqrt (N : ℝ)..(N : ℝ), primeAbelIntegralKernel t) ≤
        4 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    let C : ℝ := 4 / (Real.log (N : ℝ)) ^ 2
    have hCpos : 0 < C := by dsimp [C]; positivity
    have hlogsqrt : Real.log (Real.sqrt (N : ℝ)) =
        Real.log (N : ℝ) / 2 := Real.log_sqrt hNpos.le
    have hconstInt : IntervalIntegrable (fun _ : ℝ => C) volume
        (Real.sqrt (N : ℝ)) (N : ℝ) := by
      exact continuousOn_const.intervalIntegrable_of_Icc hsqrtupper
    have hpoint : ∀ t ∈ Set.Icc (Real.sqrt (N : ℝ)) (N : ℝ),
        primeAbelIntegralKernel t ≤ C := by
      intro t ht
      have hloglower : Real.log (N : ℝ) / 2 ≤ Real.log t := by
        rw [← hlogsqrt]
        exact Real.log_le_log hsqrtpos ht.1
      have hlogtpos : 0 < Real.log t := by linarith
      have hsqpos : 0 < (Real.log (N : ℝ) / 2) ^ 2 := by positivity
      have hsq : (Real.log (N : ℝ) / 2) ^ 2 ≤ (Real.log t) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self (by positivity) hloglower
      have hrecip := one_div_le_one_div_of_le hsqpos hsq
      calc
        primeAbelIntegralKernel t = 1 / (Real.log t) ^ 2 := rfl
        _ ≤ 1 / (Real.log (N : ℝ) / 2) ^ 2 := hrecip
        _ = C := by
          dsimp [C]
          field_simp [ne_of_gt hlogN]
          ring_nf
    calc
      _ ≤ ∫ t in Real.sqrt (N : ℝ)..(N : ℝ), C :=
        intervalIntegral.integral_mono_on hsqrtupper hsplitInt.2 hconstInt hpoint
      _ = ((N : ℝ) - Real.sqrt (N : ℝ)) * C := by
        simp [intervalIntegral.integral_const]
      _ ≤ (N : ℝ) * C := by
        apply mul_le_mul_of_nonneg_right
          (by linarith : (N : ℝ) - Real.sqrt (N : ℝ) ≤ (N : ℝ))
          (le_of_lt hCpos)
      _ = 4 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by dsimp [C]; ring_nf
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (by positivity)
      (le_of_lt (primeAbelDifference_pos (Finset.mem_Ico.mp hn).1))
  · exact primeAbelRemainderCoefficient_le_integral hN2
  · rw [hsplit]
    exact add_le_add hsmall hlarge

/-- The coefficient remainder is little-o of `N/log N`, as used in the
prime-counting normalization. -/
theorem primeAbelRemainderCoefficient_littleO :
    (fun N : ℕ => primeAbelRemainderCoefficient N) =o[Filter.atTop]
      fun N : ℕ => (N : ℝ) / Real.log (N : ℝ) := by
  have hlogSqrtReal : Filter.Tendsto
      (fun x : ℝ => Real.log x / Real.sqrt x) Filter.atTop (𝓝 0) := by
    have h := (paper_log_rpow_isLittleO_rpow (a := 1) (b := 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    simpa [Real.rpow_one, Real.sqrt_eq_rpow] using h
  have hlogSqrtNat : Filter.Tendsto
      (fun N : ℕ => Real.log (N : ℝ) / Real.sqrt (N : ℝ)) Filter.atTop (𝓝 0) :=
    hlogSqrtReal.comp tendsto_natCast_atTop_atTop
  have hinvLogReal : Filter.Tendsto (fun x : ℝ => (Real.log x)⁻¹)
      Filter.atTop (𝓝 0) := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hinvLogNat : Filter.Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹)
      Filter.atTop (𝓝 0) := hinvLogReal.comp tendsto_natCast_atTop_atTop
  have hmajorant : Filter.Tendsto
      (fun N : ℕ =>
        (Real.log (N : ℝ) / Real.sqrt (N : ℝ)) * ((Real.log 2) ^ 2)⁻¹ +
          4 * (Real.log (N : ℝ))⁻¹) Filter.atTop (𝓝 0) := by
    have hfirst := hlogSqrtNat.const_mul (((Real.log 2) ^ 2)⁻¹)
    have hsecond := hinvLogNat.const_mul (4 : ℝ)
    convert hfirst.add hsecond using 1 <;> ext N <;> ring
  have hratioEq (N : ℕ) (hN : 4 ≤ N) :
      (Real.sqrt (N : ℝ) / (Real.log 2) ^ 2 +
          4 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) /
          ((N : ℝ) / Real.log (N : ℝ)) =
        (Real.log (N : ℝ) / Real.sqrt (N : ℝ)) * ((Real.log 2) ^ 2)⁻¹ +
          4 * (Real.log (N : ℝ))⁻¹ := by
    have hNpos : 0 < (N : ℝ) := by positivity
    have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hlogN : Real.log (N : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
    field_simp [hNpos.ne', hsqrtpos.ne', hlog2, hlogN]
    nlinarith [Real.sq_sqrt hNpos.le]
  have hratioBound : ∀ᶠ N : ℕ in Filter.atTop,
      (primeAbelRemainderCoefficient N) /
          ((N : ℝ) / Real.log (N : ℝ)) ≤
        (Real.log (N : ℝ) / Real.sqrt (N : ℝ)) * ((Real.log 2) ^ 2)⁻¹ +
          4 * (Real.log (N : ℝ))⁻¹ := by
    filter_upwards [Filter.eventually_ge_atTop (4 : ℕ)] with N hN
    have hbounds := primeAbelRemainderCoefficient_bounds hN
    have hden : 0 < (N : ℝ) / Real.log (N : ℝ) := by
      apply div_pos
      · positivity
      · exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    calc
      _ ≤ (∫ t in (2 : ℝ)..(N : ℝ), primeAbelIntegralKernel t) /
          ((N : ℝ) / Real.log (N : ℝ)) :=
        div_le_div_of_nonneg_right hbounds.2.1 hden.le
      _ ≤ (Real.sqrt (N : ℝ) / (Real.log 2) ^ 2 +
          4 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) /
          ((N : ℝ) / Real.log (N : ℝ)) :=
        div_le_div_of_nonneg_right hbounds.2.2 hden.le
      _ = _ := hratioEq N hN
  have hratioNonneg : ∀ᶠ N : ℕ in Filter.atTop,
      0 ≤ (primeAbelRemainderCoefficient N) /
        ((N : ℝ) / Real.log (N : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop (4 : ℕ)] with N hN
    have hbounds := primeAbelRemainderCoefficient_bounds hN
    have hden : 0 < (N : ℝ) / Real.log (N : ℝ) := by
      apply div_pos
      · positivity
      · exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    exact div_nonneg hbounds.1 hden.le
  have hratio : Filter.Tendsto
      (fun N : ℕ => (primeAbelRemainderCoefficient N) /
        ((N : ℝ) / Real.log (N : ℝ))) Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hmajorant hratioNonneg hratioBound
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).2 hratio
  filter_upwards [Filter.eventually_ge_atTop (4 : ℕ)] with N hN hzero
  have hden : (N : ℝ) / Real.log (N : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply div_pos
    · positivity
    · exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  exact (hden hzero).elim

private theorem primePartialSum_succ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℕ → E) (n : ℕ) (hn : 2 ≤ n) :
    primePartialSum g (n + 1) = primePartialSum g n +
      (if Nat.Prime (n + 1) then g (n + 1) else 0) := by
  simp [primePartialSum, Finset.sum_Icc_succ_top (a := 0) (b := n) (by omega)]

private theorem primeLogPartialSum_succ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℕ → E) (n : ℕ) (hn : 2 ≤ n) :
    primeLogPartialSum g (n + 1) = primeLogPartialSum g n +
      (if Nat.Prime (n + 1) then
        Real.log ((n + 1 : ℕ) : ℝ) • g (n + 1) else 0) := by
  simp [primeLogPartialSum, Finset.sum_Icc_succ_top (a := 0) (b := n) (by omega)]

/-- The finite Abel identity, in every real normed vector space. In
particular, this gives the complex-valued and real-valued scalar identities. -/
theorem primeAbelIdentity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℕ → E) {N : ℕ} (hN : 2 ≤ N) :
    (∑ p ∈ Finset.Icc 0 N with Nat.Prime p, g p) =
      (Real.log (N : ℝ))⁻¹ • primeLogPartialSum g N +
        ∑ n ∈ Finset.Ico 2 N,
          primeAbelDifference n • primeLogPartialSum g n := by
  have hcore : ∀ k : ℕ,
      primePartialSum g (k + 2) =
        (Real.log ((k + 2 : ℕ) : ℝ))⁻¹ • primeLogPartialSum g (k + 2) +
          ∑ n ∈ Finset.Ico 2 (k + 2),
            primeAbelDifference n • primeLogPartialSum g n := by
    intro k
    induction k with
    | zero =>
        have hlog : Real.log (2 : ℝ) ≠ 0 :=
          ne_of_gt (Real.log_pos (by norm_num))
        have hp : Nat.Prime 2 := Nat.prime_two
        have hP : primePartialSum g 2 = g 2 := by
          unfold primePartialSum
          rw [Finset.sum_Icc_succ_top (a := 0) (b := 1) (by omega),
            Finset.sum_Icc_succ_top (a := 0) (b := 0) (by omega)]
          norm_num [hp]
        have hS : primeLogPartialSum g 2 = Real.log 2 • g 2 := by
          unfold primeLogPartialSum
          rw [Finset.sum_Icc_succ_top (a := 0) (b := 1) (by omega),
            Finset.sum_Icc_succ_top (a := 0) (b := 0) (by omega)]
          norm_num [hp]
        rw [hP, hS]
        simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
        norm_num only [Nat.zero_add, Nat.cast_ofNat]
        have hcoef : (Real.log (2 : ℝ))⁻¹ * Real.log 2 = 1 :=
          inv_mul_cancel₀ hlog
        rw [smul_smul, hcoef, one_smul]
    | succ k ih =>
        let n : ℕ := k + 2
        have hn : 2 ≤ n := by dsimp [n]; omega
        have hnlog : Real.log (n : ℝ) ≠ 0 := by
          apply ne_of_gt
          apply Real.log_pos
          exact_mod_cast (show 1 < n by omega)
        have hnextlog : Real.log ((n + 1 : ℕ) : ℝ) ≠ 0 := by
          apply ne_of_gt
          apply Real.log_pos
          exact_mod_cast (show 1 < n + 1 by omega)
        have hweight : (Real.log ((n + 1 : ℕ) : ℝ))⁻¹ •
            (if Nat.Prime (n + 1) then
              Real.log ((n + 1 : ℕ) : ℝ) • g (n + 1) else 0) =
              (if Nat.Prime (n + 1) then g (n + 1) else 0) := by
          by_cases hp : Nat.Prime (n + 1)
          · simp only [hp, ite_true, smul_smul]
            rw [inv_mul_cancel₀ hnextlog, one_smul]
          · simp [hp]
        have hrem :
            (∑ i ∈ Finset.Ico 2 (n + 1),
              primeAbelDifference i • primeLogPartialSum g i) =
              (∑ i ∈ Finset.Ico 2 n,
                primeAbelDifference i • primeLogPartialSum g i) +
                primeAbelDifference n • primeLogPartialSum g n := by
          rw [Finset.sum_Ico_succ_top hn]
        have hcancel :
            (Real.log ((n + 1 : ℕ) : ℝ))⁻¹ •
                (primeLogPartialSum g n +
                  (if Nat.Prime (n + 1) then
                    Real.log ((n + 1 : ℕ) : ℝ) • g (n + 1) else 0)) +
              ((∑ i ∈ Finset.Ico 2 n,
                primeAbelDifference i • primeLogPartialSum g i) +
                primeAbelDifference n • primeLogPartialSum g n) =
              (Real.log (n : ℝ))⁻¹ • primeLogPartialSum g n +
                (∑ i ∈ Finset.Ico 2 n,
                  primeAbelDifference i • primeLogPartialSum g i) +
                  (if Nat.Prime (n + 1) then g (n + 1) else 0) := by
          rw [smul_add, hweight]
          dsimp [primeAbelDifference]
          simp only [sub_smul]
          module
        calc
          primePartialSum g (k + 3) =
              primePartialSum g n +
                (if Nat.Prime (n + 1) then g (n + 1) else 0) := by
                  simpa [n] using primePartialSum_succ g n hn
          _ = (Real.log (n : ℝ))⁻¹ • primeLogPartialSum g n +
                (∑ i ∈ Finset.Ico 2 n,
                  primeAbelDifference i • primeLogPartialSum g i) +
                  (if Nat.Prime (n + 1) then g (n + 1) else 0) := by
                  rw [ih]
          _ = (Real.log ((n + 1 : ℕ) : ℝ))⁻¹ •
                (primeLogPartialSum g n +
                  (if Nat.Prime (n + 1) then
                    Real.log ((n + 1 : ℕ) : ℝ) • g (n + 1) else 0)) +
              ((∑ i ∈ Finset.Ico 2 n,
                primeAbelDifference i • primeLogPartialSum g i) +
                primeAbelDifference n • primeLogPartialSum g n) := by
                  exact hcancel.symm
          _ = (Real.log ((k + 3 : ℕ) : ℝ))⁻¹ •
                primeLogPartialSum g (k + 3) +
              ∑ i ∈ Finset.Ico 2 (k + 3),
                primeAbelDifference i • primeLogPartialSum g i := by
                  rw [show k + 3 = n + 1 by rfl,
                    primeLogPartialSum_succ g n hn, hrem]
  have h := hcore (N - 2)
  simpa only [Nat.sub_add_cancel hN, primePartialSum, Finset.sum_filter] using h

/-- Real scalar specialization of the finite Abel identity. -/
theorem primeAbelIdentity_real (g : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    (∑ p ∈ Finset.Icc 0 N with Nat.Prime p, g p) =
      (Real.log (N : ℝ))⁻¹ * primeLogPartialSum g N +
        ∑ n ∈ Finset.Ico 2 N,
          primeAbelDifference n * primeLogPartialSum g n := by
  simpa only [smul_eq_mul] using primeAbelIdentity g hN

/-- Complex scalar specialization of the finite Abel identity. -/
theorem primeAbelIdentity_complex (g : ℕ → ℂ) {N : ℕ} (hN : 2 ≤ N) :
    (∑ p ∈ Finset.Icc 0 N with Nat.Prime p, g p) =
      ((Real.log (N : ℝ))⁻¹ : ℂ) * primeLogPartialSum g N +
        ∑ n ∈ Finset.Ico 2 N,
          (primeAbelDifference n : ℂ) * primeLogPartialSum g n := by
  simpa only [Complex.real_smul, Complex.ofReal_inv] using primeAbelIdentity g hN

/-- At the constant scalar sequence, the prime-log partial sum is the
paper's existing prime-counting normalization `arithmeticData`. -/
theorem primeLogPartialSum_one_eq_arithmeticData (N : ℕ) :
    primeLogPartialSum (fun _ : ℕ => (1 : ℝ)) N =
      arithmeticData.primeLogSummatory N := by
  rw [arithmeticData_primeLogSummatory_eq]
  simp [primeLogPartialSum, Finset.sum_filter]

end

end FractionalPrimes

#print axioms FractionalPrimes.primeAbelIdentity
#print axioms FractionalPrimes.primeAbelIdentity_real
#print axioms FractionalPrimes.primeAbelIdentity_complex
#print axioms FractionalPrimes.primeAbelRemainderCoefficient_bounds
#print axioms FractionalPrimes.primeAbelRemainderCoefficient_littleO
#print axioms FractionalPrimes.primeLogPartialSum_one_eq_arithmeticData

end
