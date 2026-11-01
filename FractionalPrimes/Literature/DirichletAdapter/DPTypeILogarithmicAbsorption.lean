module

public import FractionalPrimes.Literature.Uniformity.LogAbsorption
public import Mathlib.Tactic

@[expose] public section
namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Uniformity
noncomputable section

/-- Absorb the two literal Type-I tail terms with a derivative order chosen
after η, as required by the approved DP proof. -/
theorem dpTypeILogarithmicAbsorption
    {X W A D η : ℝ} {j : ℕ}
    (hX : 1 ≤ X) (hL : 1 ≤ Real.log X) (hA : 0 < A)
    (hW : W = (Real.log X) ^ D)
    (hD : A + 1 ≤ D * ((j : ℝ) - 1))
    (hjη : 8 ≤ (j : ℝ) * η)
    (hlarge : 2 * Real.log (logAbsorptionM 1 (A + 1)) ≤ Real.log X) :
    Real.log X * (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) ≤
      2 * (Real.log X) ^ (-A) := by
  have hLpos : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hL
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hfirst : Real.log X * W ^ (1 - (j : ℝ)) ≤
      (Real.log X) ^ (-A) := by
    calc
      _ = (Real.log X) ^ (1 : ℝ) *
          (Real.log X) ^ (D * (1 - (j : ℝ))) := by
            rw [hW, ← Real.rpow_mul hLpos.le, Real.rpow_one]
      _ = (Real.log X) ^ (1 + D * (1 - (j : ℝ))) := by
        rw [Real.rpow_add hLpos]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by nlinarith only [hD])
  have habs : (Real.log X) ^ (A + 1) ≤ X := by
    have h := log_absorption_bound (a := 1) (b := A + 1)
      (K := 1) (X := X) (by norm_num) (by linarith)
      (by norm_num) hX (by simpa only [one_mul, div_one] using hlarge)
    simpa only [one_mul, Real.rpow_one] using h
  have hinv : X ^ (-1 : ℝ) ≤ (Real.log X) ^ (-(A + 1)) := by
    rw [Real.rpow_neg hXpos.le, Real.rpow_neg hLpos.le,
      Real.rpow_one]
    simpa only [one_div] using
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLpos (A + 1)) habs
  have hpow : X ^ (1 - (j : ℝ) * η / 4) ≤ X ^ (-1 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hX
    linarith only [hjη]
  have hmiddle : Real.log X * X ^ (1 - (j : ℝ) * η / 4) ≤
      (Real.log X) ^ (-A) := by
    calc
      _ ≤ Real.log X * X ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow hLpos.le
      _ ≤ Real.log X * (Real.log X) ^ (-(A + 1)) :=
        mul_le_mul_of_nonneg_left hinv hLpos.le
      _ = (Real.log X) ^ (1 : ℝ) *
          (Real.log X) ^ (-(A + 1)) := by rw [Real.rpow_one]
      _ = (Real.log X) ^ (1 + -(A + 1)) := by rw [Real.rpow_add hLpos]
      _ = _ := by congr 1; ring
  calc
    _ = Real.log X * W ^ (1 - (j : ℝ)) +
        Real.log X * X ^ (1 - (j : ℝ) * η / 4) := by ring
    _ ≤ (Real.log X) ^ (-A) + (Real.log X) ^ (-A) :=
      add_le_add hfirst hmiddle
    _ = _ := by ring

#print axioms dpTypeILogarithmicAbsorption
end
end FractionalPrimes.Literature.DirichletAdapter
