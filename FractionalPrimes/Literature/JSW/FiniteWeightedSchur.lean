module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The finite weighted Cauchy--Schwarz step in the source square summation. -/
@[expose] public section
namespace FractionalPrimes.Literature.JSW

 theorem finiteWeightedSchur_square_bound
    {ι κ : Type*} (K : Finset ι) (J : Finset κ) (w : ι → κ → ℝ) (v : κ → ℝ)
    {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hw : ∀ k j, 0 ≤ w k j)
    (hrow : ∀ k ∈ K, ∑ j ∈ J, w k j ≤ R)
    (hcol : ∀ j ∈ J, ∑ k ∈ K, w k j ≤ C) :
    ∑ k ∈ K, (∑ j ∈ J, w k j*v j)^2 ≤ R*C*(∑ j ∈ J, v j^2) := by
  have hCS (k : ι) : (∑ j ∈ J, w k j*v j)^2 ≤
      (∑ j ∈ J, w k j)*(∑ j ∈ J, w k j*v j^2) := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq J
      (fun j => Real.sqrt (w k j)) (fun j => Real.sqrt (w k j)*v j)
    have hsqrt (j : κ) : Real.sqrt (w k j)^2 = w k j := Real.sq_sqrt (hw k j)
    have hprod (j : κ) : Real.sqrt (w k j)*(Real.sqrt (w k j)*v j) = w k j*v j := by
      calc
        _ = (Real.sqrt (w k j))^2*v j := by ring
        _ = _ := by rw [hsqrt]
    simpa only [hprod, mul_pow, hsqrt] using hh
  calc
    _ ≤ ∑ k ∈ K, R*(∑ j ∈ J, w k j*v j^2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact (hCS k).trans (mul_le_mul_of_nonneg_right (hrow k hk)
        (Finset.sum_nonneg fun j _ => mul_nonneg (hw k j) (sq_nonneg _)))
    _ = R*(∑ j ∈ J, (∑ k ∈ K, w k j)*v j^2) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ ≤ R*(∑ j ∈ J, C*v j^2) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _)) hR
    _ = _ := by rw [← Finset.mul_sum]; ring

#print axioms finiteWeightedSchur_square_bound
end FractionalPrimes.Literature.JSW
end
