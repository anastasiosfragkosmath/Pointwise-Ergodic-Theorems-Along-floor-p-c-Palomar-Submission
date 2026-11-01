module

public import FractionalPrimes.Literature.JSW.SmoothDyadicMultiplicity
public import FractionalPrimes.Literature.JSW.RoughSquareGeometricSum

/-! Exact geometric row/column sums in the source smooth/dyadic square estimate. -/
@[expose] public section
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothDyadicWeight (n : ℤ) : ℝ := (2 : ℝ)^(-|(n : ℝ)|/2)
def smoothDyadicW0 : ℝ := (1+(2 : ℝ)^(-(1 : ℝ)/2))/(1-(2 : ℝ)^(-(1 : ℝ)/2))

theorem smoothDyadicWeight_nonneg (n : ℤ) : 0 ≤ smoothDyadicWeight n :=
  Real.rpow_nonneg (by norm_num) _

theorem smoothDyadicWeight_hasSum : HasSum smoothDyadicWeight smoothDyadicW0 := by
  have h := roughSquareGeometric_decay_hasSum (b := 2) (δ := (1 : ℝ)/2)
    (by norm_num) (by norm_num)
  convert h using 1
  · funext n
    unfold smoothDyadicWeight
    congr 1
    ring
  · unfold smoothDyadicW0
    congr 2 <;> congr 1 <;> ring

theorem smoothDyadicWeight_finite_sum_le (F : Finset ℤ) :
    ∑ n ∈ F, smoothDyadicWeight n ≤ smoothDyadicW0 := by
  rw [← smoothDyadicWeight_hasSum.tsum_eq]
  exact Summable.sum_le_tsum F (fun n _ => smoothDyadicWeight_nonneg n)
    smoothDyadicWeight_hasSum.summable

theorem smoothDyadicWeight_finite_sub_sum_le (F : Finset ℤ) (j : ℤ) :
    ∑ n ∈ F, smoothDyadicWeight (n-j) ≤ smoothDyadicW0 := by
  classical
  have hsum : (∑ n ∈ F, smoothDyadicWeight (n-j)) =
      ∑ z ∈ F.image (fun n => n-j), smoothDyadicWeight z := by
    rw [Finset.sum_image]
    intro n hn k hk heq
    change n-j = k-j at heq
    omega
  rw [hsum]
  exact smoothDyadicWeight_finite_sum_le _

theorem smoothDyadicWeight_finite_row_sum_le (F : Finset ℤ) (m : ℤ) :
    ∑ j ∈ F, smoothDyadicWeight (m-j) ≤ smoothDyadicW0 := by
  have heq (j : ℤ) : smoothDyadicWeight (m-j) = smoothDyadicWeight (j-m) := by
    unfold smoothDyadicWeight
    rw [show m-j = -(j-m) by omega, Int.cast_neg, abs_neg]
  simp_rw [heq]
  exact smoothDyadicWeight_finite_sub_sum_le F m

theorem smoothDyadicWeight_finite_column_sum_le
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ) (j : ℤ) :
    ∑ k ∈ K, smoothDyadicWeight (jswM a ha k-j) ≤
      (jswMultiplicity a ha : ℝ)*smoothDyadicW0 := by
  classical
  let T := K.image (jswM a ha)
  have hgroup := Finset.sum_fiberwise_of_maps_to (s := K) (t := T)
    (g := jswM a ha) (fun k hk => Finset.mem_image_of_mem _ hk)
    (fun k => smoothDyadicWeight (jswM a ha k-j))
  have hfiber (m : ℤ) : (∑ k ∈ K.filter (fun k => jswM a ha k=m),
      smoothDyadicWeight (jswM a ha k-j)) =
      ((K.filter (fun k => jswM a ha k=m)).card : ℝ)*smoothDyadicWeight (m-j) := by
    calc
      _ = ∑ k ∈ K.filter (fun k => jswM a ha k=m), smoothDyadicWeight (m-j) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [(Finset.mem_filter.mp hk).2]
      _ = _ := by simp
  calc
    _ = ∑ m ∈ T, ∑ k ∈ K.filter (fun k => jswM a ha k=m),
        smoothDyadicWeight (jswM a ha k-j) := hgroup.symm
    _ = ∑ m ∈ T, ((K.filter (fun k => jswM a ha k=m)).card : ℝ)*smoothDyadicWeight (m-j) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact hfiber m
    _ ≤ ∑ m ∈ T, (jswMultiplicity a ha : ℝ)*smoothDyadicWeight (m-j) := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_right _ (smoothDyadicWeight_nonneg _)
      exact_mod_cast jswM_finite_fiber_card_le ha K m
    _ = (jswMultiplicity a ha : ℝ)*(∑ m ∈ T, smoothDyadicWeight (m-j)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (smoothDyadicWeight_finite_sub_sum_le T j) (by positivity)

#print axioms smoothDyadicWeight_finite_column_sum_le
#print axioms smoothDyadicWeight_hasSum
end
end FractionalPrimes.Literature.JSW
end
