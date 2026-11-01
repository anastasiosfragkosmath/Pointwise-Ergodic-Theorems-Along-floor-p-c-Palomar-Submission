module

public import FractionalPrimes.Literature.DirichletAdapter.AffineFourierScaling
public import Mathlib.Analysis.PSeries

/-! Elementary reciprocal-square control for the nonzero Poisson modes. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

/-- A finite telescoping majorant for the positive reciprocal-square modes. -/
theorem reciprocal_square_partial_le (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (1 : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2) ≤
      2 - 1 / ((n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hstep :
          (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 ≤
            1 / ((n + 1 : ℕ) : ℝ) - 1 / ((n + 2 : ℕ) : ℝ) := by
        push_cast
        field_simp
        nlinarith
      calc
        (∑ i ∈ Finset.range (n + 1), (1 : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2) +
            1 / ((n + 2 : ℕ) : ℝ) ^ 2 ≤
          (2 - 1 / ((n + 1 : ℕ) : ℝ)) +
            (1 / ((n + 1 : ℕ) : ℝ) - 1 / ((n + 2 : ℕ) : ℝ)) :=
              add_le_add ih hstep
        _ = 2 - 1 / ((n + 2 : ℕ) : ℝ) := by ring

#print axioms reciprocal_square_partial_le

/-- The positive reciprocal-square series has total mass at most two. -/
theorem reciprocal_square_tsum_le_two :
    (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro n
    cases n with
    | zero => simp
    | succ n =>
        exact (reciprocal_square_partial_le n).trans (sub_le_self 2 (by positivity))

#print axioms reciprocal_square_tsum_le_two

/-- Every higher positive reciprocal-power series is bounded by the square series. -/
theorem reciprocal_power_tsum_le_two (j : ℕ) (hj : 2 ≤ j) :
    (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ j) ≤ 2 := by
  have hpoint (n : ℕ) :
      (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ j ≤
        1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    apply one_div_pow_le_one_div_pow_of_le
    · exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    · exact hj
  have hsquare : Summable (fun n : ℕ =>
      (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2))
  have hpower : Summable (fun n : ℕ =>
      (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ j) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hpoint hsquare
  exact (hpower.tsum_le_tsum hpoint hsquare).trans reciprocal_square_tsum_le_two

#print axioms reciprocal_power_tsum_le_two

/-- The nonzero integer modes in the Poisson series. -/
noncomputable def reciprocalMode (j : ℕ) (k : ℤ) : ℝ :=
  if k = 0 then 0 else 1 / |(k : ℝ)| ^ j

theorem reciprocalMode_summable (j : ℕ) (hj : 2 ≤ j) :
    Summable (reciprocalMode j) := by
  have hrpow : Summable (fun k : ℤ => |(k : ℝ)| ^ (-(j : ℝ))) :=
    Real.summable_abs_int_rpow (by exact_mod_cast hj : (1 : ℝ) < j)
  apply hrpow.congr
  intro k
  by_cases hk : k = 0
  · subst k
    have hj0 : j ≠ 0 := by omega
    simp [reciprocalMode, hj0]
  · simp only [reciprocalMode, if_neg hk]
    rw [Real.rpow_neg (abs_nonneg _), Real.rpow_natCast]
    simp

#print axioms reciprocalMode_summable

/-- The blueprint's rough constant `4` for the nonzero integer mode sum. -/
theorem reciprocal_integer_modes_le_four (j : ℕ) (hj : 2 ≤ j) :
    (∑' k : ℤ, reciprocalMode j k) ≤ 4 := by
  have hterm_pos (n : ℕ) :
      reciprocalMode j (((n + 1 : ℕ) : ℤ)) =
        (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ j := by
    rw [reciprocalMode, if_neg (show ((n + 1 : ℕ) : ℤ) ≠ 0 by omega)]
    simp only [Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have hterm_neg (n : ℕ) :
      reciprocalMode j (-(((n + 1 : ℕ) : ℤ))) =
        (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ j := by
    rw [reciprocalMode, if_neg (show -(((n + 1 : ℕ) : ℤ)) ≠ 0 by omega)]
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have hpower : Summable (fun n : ℕ =>
      (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ j) := by
    have hsquare : Summable (fun n : ℕ =>
        (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).mpr
          (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2))
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ hsquare
    intro n
    exact one_div_pow_le_one_div_pow_of_le
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) hj
  have hpos : Summable (fun n : ℕ => reciprocalMode j (n : ℤ)) := by
    apply (summable_nat_add_iff 1).mp
    convert hpower using 1
    ext n
    simpa only [Nat.cast_add, Nat.cast_one] using hterm_pos n
  have hneg : Summable (fun n : ℕ => reciprocalMode j (-((n + 1 : ℕ) : ℤ))) := by
    convert hpower using 1
    ext n
    exact hterm_neg n
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  have hfirst : (∑' n : ℕ, reciprocalMode j (n : ℤ)) =
      ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ j := by
    rw [hpos.tsum_eq_zero_add]
    have hzero : reciprocalMode j (0 : ℤ) = 0 := by simp [reciprocalMode]
    simp only [Nat.cast_zero, hzero, zero_add]
    congr 1
    funext n
    simpa only [Nat.cast_add, Nat.cast_one] using hterm_pos n
  rw [hfirst]
  have hsecond : (∑' n : ℕ, reciprocalMode j (-((n : ℤ) + 1))) =
      ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ j := by
    congr 1
    funext n
    simpa only [Nat.cast_add, Nat.cast_one] using hterm_neg n
  rw [hsecond]
  linarith [reciprocal_power_tsum_le_two j hj]

#print axioms reciprocal_integer_modes_le_four

end FractionalPrimes.Literature.DirichletAdapter

end
