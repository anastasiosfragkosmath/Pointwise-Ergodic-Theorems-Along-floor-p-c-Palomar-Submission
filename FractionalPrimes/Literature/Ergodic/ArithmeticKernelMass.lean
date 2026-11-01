module

public import FractionalPrimes.Literature.Ergodic.FiniteWeightedKernelMass
public import FractionalPrimes.Systems

@[expose] public section
namespace FractionalPrimes
noncomputable section

def primeComparisonIntegerKernel (c : ℝ) (N : Scale) : IntegerL1Kernel :=
  finiteWeightedIntegerKernel c N (fun n => (vonMangoldtWeight n : ℂ) - 1)

theorem vonMangoldtIntegerKernel_norm_tsum_le (c : ℝ) (N : Scale) :
    (∑' m : ℤ, ‖(vonMangoldtIntegerKernel c N).coeff m‖) ≤
      Real.log (N.val : ℝ) := by
  apply finiteWeightedIntegerKernel_norm_tsum_le_of_weight_bound
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hnN := (Finset.mem_Icc.mp hn).2
  rw [Complex.norm_real, Real.norm_of_nonneg (vonMangoldtWeight_nonneg n)]
  exact vonMangoldtWeight_le_log.trans
    (Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN))

theorem primeComparisonIntegerKernel_norm_tsum_le (c : ℝ) (N : Scale) :
    (∑' m : ℤ, ‖(primeComparisonIntegerKernel c N).coeff m‖) ≤
      1 + Real.log (N.val : ℝ) := by
  apply finiteWeightedIntegerKernel_norm_tsum_le_of_weight_bound
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hnN := (Finset.mem_Icc.mp hn).2
  have hweight : ‖(vonMangoldtWeight n : ℂ)‖ ≤ Real.log (N.val : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (vonMangoldtWeight_nonneg n)]
    exact vonMangoldtWeight_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN))
  calc
    _ ≤ ‖(vonMangoldtWeight n : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by rw [norm_one]; linarith

theorem mobiusIntegerKernel_norm_tsum_le (c : ℝ) (N : Scale) :
    (∑' m : ℤ, ‖(mobiusIntegerKernel c N).coeff m‖) ≤ 1 := by
  apply finiteWeightedIntegerKernel_norm_tsum_le_of_weight_bound
  intro n _
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

theorem primeComparisonIntegerKernel_convolution
    (c : ℝ) (N : Scale) (f : ℤ → ℂ) (x : ℤ) :
    integerKernelConvolution (primeComparisonIntegerKernel c N) f x =
      vonMangoldtAverage integerShiftSystem c f N x -
        unweightedAverage integerShiftSystem c f N x := by
  rw [primeComparisonIntegerKernel, finiteWeightedIntegerKernel_convolution_eq_sum]
  simp only [vonMangoldtAverage, unweightedAverage, weightedAverage,
    integerShiftSystem_iterate_apply, one_mul,
    sub_mul, Finset.sum_sub_distrib, mul_sub]

#print axioms primeComparisonIntegerKernel_norm_tsum_le
#print axioms primeComparisonIntegerKernel_convolution
end
end FractionalPrimes
