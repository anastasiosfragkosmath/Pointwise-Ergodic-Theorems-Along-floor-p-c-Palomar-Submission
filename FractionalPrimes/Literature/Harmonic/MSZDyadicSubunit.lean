module

public import FractionalPrimes.Literature.Harmonic.MSZTimeBridge

/-! The negative-index dyadic MSZ times all use the single time-one kernel. -/

@[expose] public section

namespace FractionalPrimes.Literature.Harmonic

open FractionalPrimes.Literature.MSZ

/-- The dyadic maximal family has a constant tail for `k ≤ 0`. -/
theorem interpolatedFloorPowerMSZKernel_dyadic_nonpos
    (c : ℝ) (k : ℤ) (hk : k ≤ 0) :
    interpolatedFloorPowerMSZKernel c (mszDyadicTime k) =
      floorPowerMSZKernel c ⟨1, by norm_num⟩ := by
  have hq : (mszDyadicTime k).val ≤ 1 := by
    rw [mszDyadicTime_value]
    exact zpow_le_one_of_nonpos₀ (by norm_num : 1 ≤ (2 : ℚ)) hk
  have hr : ((mszDyadicTime k).val : ℝ) ≤ 1 := by exact_mod_cast hq
  simp only [interpolatedFloorPowerMSZKernel, dif_pos hr]

#print axioms interpolatedFloorPowerMSZKernel_dyadic_nonpos

/-- Pointwise, the nonpositive dyadic part of the MSZ family is the
same time-one average. -/
theorem mszKernelAverage_dyadic_nonpos
    (c : ℝ) (k : ℤ) (hk : k ≤ 0) (f : ℤ → ℂ) (x : ℤ) :
    mszKernelAverage (interpolatedFloorPowerMSZKernel c (mszDyadicTime k)) f x =
      mszKernelAverage (floorPowerMSZKernel c ⟨1, by norm_num⟩) f x := by
  rw [interpolatedFloorPowerMSZKernel_dyadic_nonpos c k hk]

#print axioms mszKernelAverage_dyadic_nonpos

/-- At a nonnegative integer index, the MSZ dyadic average is exactly
the paper's integer-time unweighted average at scale `2^n`. -/
theorem mszKernelAverage_dyadic_nat
    (c : ℝ) (n : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    mszKernelAverage
        (interpolatedFloorPowerMSZKernel c (mszDyadicTime (n : ℤ)))
        (f : ℤ → ℂ) x =
      localizedIntegerUnweightedAverageL2 c ⟨2 ^ n, Nat.one_le_pow n 2 (by omega)⟩ f x := by
  have htval : (((mszDyadicTime (n : ℤ)).val : ℝ)) = (2 ^ n : ℕ) := by
    rw [mszDyadicTime_value, zpow_natCast]
    norm_cast
  rw [interpolatedFloorPowerMSZKernel_average_eq_localized]
  simp only [htval]
  have hN : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  rw [localizedInterpolatedAverageL2_at_integer c (2 ^ n) hN f]

#print axioms mszKernelAverage_dyadic_nat

end FractionalPrimes.Literature.Harmonic

end
