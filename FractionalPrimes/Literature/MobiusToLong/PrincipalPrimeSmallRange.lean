module

public import FractionalPrimes.Literature.MobiusToLong.ElementaryLogarithmicSums
public import FractionalPrimes.Literature.MobiusToLong.PrincipalPrimeHyperbolaSplit
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace FractionalPrimes.Literature.MobiusToLong

noncomputable section

/-- The exact first-half approximation in the proof of `lml:principal-primes`.
The outer and inner cutoffs remain the real-floor cutoffs from the source. -/
theorem principalPrimeSmallRangeApproximation {x : ℝ} (hx : 3 ≤ x) :
    |(∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
        mobiusRealCoefficient d *
          (∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))),
            Real.log (m : ℝ))) -
      x * ((Real.log x - 1) *
          (∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
            mobiusRealCoefficient d / (d : ℝ)) -
        ∑ d ∈ Finset.Icc 1 (Nat.floor (Real.sqrt x)),
          mobiusRealCoefficient d * Real.log (d : ℝ) / (d : ℝ))|
      ≤ 4 * Real.sqrt x * Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hlog3 : 1 ≤ Real.log 3 := by
    have hexp : Real.exp 1 < 3 :=
      lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hstrict : 1 < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
        hexp
    linarith
  have hlogx : 1 ≤ Real.log x :=
    le_trans hlog3 (Real.log_le_log (by norm_num) hx)
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_one : 1 ≤ Real.sqrt x := by
    have hsquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
    nlinarith [hsqrt_nonneg, hx]
  have hsqrt_le_x : Real.sqrt x ≤ x :=
    Real.sqrt_le_self_iff.mpr (Or.inr hxone)
  let S : Finset ℕ := Finset.Icc 1 (Nat.floor (Real.sqrt x))
  have hfloor_sqrt_one : 1 ≤ Nat.floor (Real.sqrt x) :=
    Nat.le_floor (by exact_mod_cast hsqrt_one)
  have hcard : (S.card : ℝ) ≤ Real.sqrt x := by
    have hcardNat : S.card = Nat.floor (Real.sqrt x) := by
      simp [S, Nat.card_Icc]
    rw [hcardNat]
    exact Nat.floor_le hsqrt_nonneg
  have hterm {d : ℕ} (hd : d ∈ S) :
      |mobiusRealCoefficient d *
          ((∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))),
              Real.log (m : ℝ)) -
            ((x / (d : ℝ)) * Real.log (x / (d : ℝ)) - x / (d : ℝ)))|
        ≤ 4 * Real.log x := by
    have hdI := Finset.mem_Icc.mp hd
    have hdpos : 0 < d := by omega
    have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hdI.1
    have hdsqrt : (d : ℝ) ≤ Real.sqrt x := by
      calc
        (d : ℝ) ≤ (Nat.floor (Real.sqrt x) : ℝ) := by exact_mod_cast hdI.2
        _ ≤ Real.sqrt x := Nat.floor_le hsqrt_nonneg
    have hdx : (d : ℝ) ≤ x := le_trans hdsqrt hsqrt_le_x
    have hypos : 0 < x / (d : ℝ) := div_pos hxpos (by exact_mod_cast hdpos)
    have hyone : 1 ≤ x / (d : ℝ) := (le_div_iff₀ (by exact_mod_cast hdpos)).2 (by
      nlinarith [mul_le_mul_of_nonneg_left hdreal hx0])
    have hy_le_x : x / (d : ℝ) ≤ x := (div_le_iff₀ (by exact_mod_cast hdpos)).2 (by
      nlinarith [mul_le_mul_of_nonneg_left hdreal hx0])
    have hlogError := abs_log_sum_Icc_floor_le hyone
    have hlogMono :
        Real.log (Real.exp 1 * (x / (d : ℝ))) ≤ 1 + Real.log x := by
      calc
        Real.log (Real.exp 1 * (x / (d : ℝ))) ≤
            Real.log (Real.exp 1 * x) := by
          apply Real.log_le_log (mul_pos (Real.exp_pos 1) hypos)
          exact mul_le_mul_of_nonneg_left hy_le_x (Real.exp_nonneg 1)
        _ = 1 + Real.log x := by
          rw [Real.log_mul (Real.exp_ne_zero 1) hxpos.ne', Real.log_exp]
    have hlogErrorBound :
        2 * Real.log (Real.exp 1 * (x / (d : ℝ))) ≤ 4 * Real.log x := by
      nlinarith [hlogMono, hlogx]
    have hmu : |mobiusRealCoefficient d| ≤ 1 := by
      dsimp [mobiusRealCoefficient]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    have harg_one : 1 ≤ Real.exp 1 * (x / (d : ℝ)) := by
      have he : 1 ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      nlinarith [hyone, Real.exp_nonneg 1]
    have hlog_nonneg : 0 ≤ 2 * Real.log (Real.exp 1 * (x / (d : ℝ))) :=
      mul_nonneg (by norm_num) (Real.log_nonneg harg_one)
    calc
      _ = |mobiusRealCoefficient d| *
          |(∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))),
              Real.log (m : ℝ)) -
            ((x / (d : ℝ)) * Real.log (x / (d : ℝ)) - x / (d : ℝ))| := by
              rw [abs_mul]
      _ ≤ 1 * (2 * Real.log (Real.exp 1 * (x / (d : ℝ)))) :=
            mul_le_mul hmu hlogError (abs_nonneg _) (by norm_num)
      _ ≤ 4 * Real.log x := by nlinarith [hlogErrorBound]
  have hmain :
      (∑ d ∈ S, mobiusRealCoefficient d *
          ((x / (d : ℝ)) * Real.log (x / (d : ℝ)) - x / (d : ℝ))) =
        x * ((Real.log x - 1) *
            (∑ d ∈ S, mobiusRealCoefficient d / (d : ℝ)) -
          ∑ d ∈ S, mobiusRealCoefficient d * Real.log (d : ℝ) / (d : ℝ)) := by
    calc
      _ = ∑ d ∈ S, x *
          ((Real.log x - 1) * (mobiusRealCoefficient d / (d : ℝ)) -
            mobiusRealCoefficient d * Real.log (d : ℝ) / (d : ℝ)) := by
              apply Finset.sum_congr rfl
              intro d hd
              have hdpos : 0 < d := by
                have h := Finset.mem_Icc.mp hd
                omega
              rw [Real.log_div hxpos.ne' (by exact_mod_cast Nat.ne_of_gt hdpos)]
              field_simp
              <;> ring
      _ = (∑ d ∈ S,
            ((x * (Real.log x - 1)) *
                (mobiusRealCoefficient d / (d : ℝ)) -
              x * (mobiusRealCoefficient d * Real.log (d : ℝ) / (d : ℝ)))) := by
              apply Finset.sum_congr rfl
              intro d hd
              ring
      _ = x * ((Real.log x - 1) *
            (∑ d ∈ S, mobiusRealCoefficient d / (d : ℝ)) -
          ∑ d ∈ S, mobiusRealCoefficient d * Real.log (d : ℝ) / (d : ℝ)) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              ring
  have herror :
      |(∑ d ∈ S, mobiusRealCoefficient d *
          (∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))),
            Real.log (m : ℝ))) -
        (∑ d ∈ S, mobiusRealCoefficient d *
          ((x / (d : ℝ)) * Real.log (x / (d : ℝ)) - x / (d : ℝ)))|
        ≤ 4 * Real.sqrt x * Real.log x := by
    calc
      _ = |∑ d ∈ S, mobiusRealCoefficient d *
          ((∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))),
            Real.log (m : ℝ)) -
            ((x / (d : ℝ)) * Real.log (x / (d : ℝ)) - x / (d : ℝ)))| := by
              congr 1
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro d hd
              ring
      _ ≤ ∑ d ∈ S, |mobiusRealCoefficient d *
          ((∑ m ∈ Finset.Icc 1 (Nat.floor (x / (d : ℝ))),
            Real.log (m : ℝ)) -
            ((x / (d : ℝ)) * Real.log (x / (d : ℝ)) - x / (d : ℝ)))| :=
              Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ S, 4 * Real.log x :=
              Finset.sum_le_sum fun d hd => hterm hd
      _ = (S.card : ℝ) * (4 * Real.log x) := by simp
      _ ≤ Real.sqrt x * (4 * Real.log x) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 4 * Real.sqrt x * Real.log x := by ring
  simpa only [S, hmain] using herror

end

end FractionalPrimes.Literature.MobiusToLong
