module

public import FractionalPrimes.Literature.Uniformity.LogAbsorption
public import Mathlib.Tactic.Ring

@[expose] public section
namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Uniformity
noncomputable section

/-- The exact three-term DP saving absorbs the retained logarithmic loss.
The source retained-scale threshold supplies X≥1 before this lemma is applied. -/
theorem dpLogarithmicSavings_absorption
    {X m A η κ D : ℝ} (hX : 1 ≤ X) (hm : 0 ≤ m)
    (hA : 0 < A) (hη : 0 < η) (hL : 1 ≤ Real.log X)
    (hκ : 16 * (A + m) ≤ κ) (hD : A + m ≤ D)
    (hlarge : (2 / (η / 32)) * Real.log (logAbsorptionM (η / 32) (A + m)) ≤ Real.log X) :
    (Real.log X) ^ m * ((Real.log X) ^ (-κ / 16) +
        X ^ (-η / 32) + (Real.log X) ^ (-D)) ≤
      3 * (Real.log X) ^ (-A) := by
  have hLpos : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hL
  have hAbs : (Real.log X) ^ (A + m) ≤ X ^ (η / 32) := by
    have h := log_absorption_bound (a := η / 32) (b := A + m) (K := 1) (X := X)
      (by positivity) (by linarith only [hA, hm]) (by norm_num) hX
      (by simpa only [one_mul] using hlarge)
    simpa only [one_mul] using h
  have hInv : X ^ (-η / 32) ≤ (Real.log X) ^ (-(A + m)) := by
    rw [neg_div, Real.rpow_neg (le_trans zero_le_one hX), Real.rpow_neg hLpos.le]
    simpa only [one_div] using
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLpos (A + m)) hAbs
  have hfirst : (Real.log X) ^ m * (Real.log X) ^ (-κ / 16) ≤ (Real.log X) ^ (-A) := by
    rw [← Real.rpow_add hLpos]
    apply Real.rpow_le_rpow_of_exponent_le hL
    linarith only [hκ]
  have hmiddle : (Real.log X) ^ m * X ^ (-η / 32) ≤ (Real.log X) ^ (-A) := by
    calc
      _ ≤ (Real.log X) ^ m * (Real.log X) ^ (-(A + m)) :=
        mul_le_mul_of_nonneg_left hInv (Real.rpow_nonneg hLpos.le _)
      _ = _ := by rw [← Real.rpow_add hLpos]; congr 1; ring
  have hlast : (Real.log X) ^ m * (Real.log X) ^ (-D) ≤ (Real.log X) ^ (-A) := by
    rw [← Real.rpow_add hLpos]
    apply Real.rpow_le_rpow_of_exponent_le hL
    linarith only [hD]
  calc
    _ = (Real.log X) ^ m * (Real.log X) ^ (-κ / 16) +
        (Real.log X) ^ m * X ^ (-η / 32) +
        (Real.log X) ^ m * (Real.log X) ^ (-D) := by ring
    _ ≤ (Real.log X) ^ (-A) + (Real.log X) ^ (-A) + (Real.log X) ^ (-A) :=
      add_le_add (add_le_add hfirst hmiddle) hlast
    _ = _ := by ring

#print axioms dpLogarithmicSavings_absorption
end
end FractionalPrimes.Literature.DirichletAdapter
