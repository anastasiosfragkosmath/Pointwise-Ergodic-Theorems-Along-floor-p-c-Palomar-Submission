module

public import FractionalPrimes.Literature.JSW.SmoothDyadicWeightSums
public import FractionalPrimes.Literature.JSW.FiniteWeightedSchur

/-! The source finite weighted square summation with the exact multiplicity. -/
@[expose] public section
namespace FractionalPrimes.Literature.JSW

theorem smoothDyadicW0_nonneg : 0 ≤ smoothDyadicW0 := by
  simpa using smoothDyadicWeight_finite_sum_le ∅

theorem smoothDyadic_finite_weighted_square_bound
    {a : ℝ} (ha : 0 < a) (K J : Finset ℤ) (v : ℤ → ℝ) :
    ∑ k ∈ K, (∑ j ∈ J, smoothDyadicWeight (jswM a ha k-j)*v j)^2 ≤
      (jswMultiplicity a ha : ℝ)*smoothDyadicW0^2*(∑ j ∈ J, v j^2) := by
  have h := finiteWeightedSchur_square_bound K J
    (fun k j => smoothDyadicWeight (jswM a ha k-j)) v
    smoothDyadicW0_nonneg (mul_nonneg (by positivity) smoothDyadicW0_nonneg)
    (fun k j => smoothDyadicWeight_nonneg _)
    (fun k _ => smoothDyadicWeight_finite_row_sum_le J _)
    (fun j _ => smoothDyadicWeight_finite_column_sum_le ha K j)
  convert h using 1 <;> ring

#print axioms smoothDyadic_finite_weighted_square_bound
end FractionalPrimes.Literature.JSW
end
