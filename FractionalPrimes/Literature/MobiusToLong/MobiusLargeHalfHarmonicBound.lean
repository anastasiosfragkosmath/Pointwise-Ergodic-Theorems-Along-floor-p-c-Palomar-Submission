module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section

namespace FractionalPrimes.Literature.MobiusToLong

/-- The logarithmically weighted harmonic sum up to the real cutoff `sqrt x`
is bounded with the source's constant and floor convention. -/
theorem mobius_large_half_harmonic_bound {x : ℝ} (hx : 9 ≤ x) :
    (∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (Real.sqrt x)),
      Real.log (m : ℝ) / (m : ℝ)) ≤ 2 * (Real.log x) ^ 2 := by
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hsqrtone : (1 : ℝ) ≤ Real.sqrt x := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hxone
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogxone : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le hxpos).2
    have hexp1 : Real.exp 1 < 3 := by
      have h := Real.exp_one_lt_d9
      norm_num at h ⊢
      linarith
    exact hexp1.le.trans (by linarith)
  have hterm {m : ℕ}
      (hm : m ∈ Finset.Icc (1 : ℕ) (Nat.floor (Real.sqrt x))) :
      Real.log (m : ℝ) / (m : ℝ) ≤ Real.log x / (m : ℝ) := by
    have hmIcc := Finset.mem_Icc.mp hm
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast lt_of_lt_of_le Nat.one_pos hmIcc.1
    have hmx : (m : ℝ) ≤ x := by
      calc
        (m : ℝ) ≤ (Nat.floor (Real.sqrt x) : ℝ) := by exact_mod_cast hmIcc.2
        _ ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
        _ ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr hxone)
    exact div_le_div_of_nonneg_right (Real.log_le_log hmpos hmx) (by positivity)
  have hInvHarmonic :
      (∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (Real.sqrt x)), (m : ℝ)⁻¹) =
        (harmonic (Nat.floor (Real.sqrt x)) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp_rw [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hlogsum :
      (∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (Real.sqrt x)),
        Real.log (m : ℝ) / (m : ℝ)) ≤
        Real.log x * (harmonic (Nat.floor (Real.sqrt x)) : ℝ) := by
    calc
      _ ≤ ∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (Real.sqrt x)),
          Real.log x / (m : ℝ) := Finset.sum_le_sum fun m hm => hterm hm
      _ = Real.log x *
          (∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor (Real.sqrt x)), (m : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        simp [div_eq_mul_inv]
      _ = Real.log x * (harmonic (Nat.floor (Real.sqrt x)) : ℝ) := by
        rw [← hInvHarmonic]
  have hharmonic := harmonic_floor_le_one_add_log (Real.sqrt x) hsqrtone
  calc
    _ ≤ Real.log x * (harmonic (Nat.floor (Real.sqrt x)) : ℝ) := hlogsum
    _ ≤ Real.log x * (1 + Real.log (Real.sqrt x)) :=
      mul_le_mul_of_nonneg_left hharmonic hlogxpos.le
    _ = Real.log x * (1 + Real.log x / 2) := by
      rw [Real.log_sqrt hxpos.le]
    _ ≤ 2 * (Real.log x) ^ 2 := by nlinarith [sq_nonneg (Real.log x)]

end FractionalPrimes.Literature.MobiusToLong
