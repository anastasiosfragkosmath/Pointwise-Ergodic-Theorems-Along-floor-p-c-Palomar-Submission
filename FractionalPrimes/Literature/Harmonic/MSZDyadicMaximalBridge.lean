module

public import FractionalPrimes.Literature.Harmonic.MSZDyadicSubunit
public import FractionalPrimes.Literature.Harmonic.UnweightedDyadicVariationAndMaximal
public import FractionalPrimes.Literature.Harmonic.CountMaximalMajorant

/-! Exact integer-time kernels and domination of every MSZ dyadic scale by the source maximal function. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.Harmonic
open FractionalPrimes.Literature.MSZ
noncomputable section

theorem interpolatedMSZKernel_integer_coeff
    (c : ℝ) (t : MSZTime) (N : Scale) (ht : (t.val : ℝ) = (N.val : ℝ)) (m : ℤ) :
    (interpolatedFloorPowerMSZKernel c t).coeff m = floorPowerRealKernelCoeff c N m := by
  by_cases hN : (N.val : ℝ) ≤ 1
  · have hNval : N.val = 1 := by
      have : N.val ≤ 1 := by exact_mod_cast hN
      omega
    have hNs : N = (⟨1,by omega⟩ : Scale) := Subtype.ext hNval
    rw [hNs] at ht ⊢
    simp [interpolatedFloorPowerMSZKernel,ht,floorPowerMSZKernel]
  · simp [interpolatedFloorPowerMSZKernel,ht,hN,convexMSZKernel,floorPowerMSZKernel]

theorem interpolatedMSZKernel_integer_average
    (c : ℝ) (t : MSZTime) (N : Scale) (ht : (t.val : ℝ) = (N.val : ℝ))
    (f : ℤ → ℂ) (x : ℤ) :
    mszKernelAverage (interpolatedFloorPowerMSZKernel c t) f x =
      unweightedAverage integerShiftSystem c f N x := by
  have hkernel : (interpolatedFloorPowerMSZKernel c t).toIntegerL1Kernel = floorPowerKernel c N := by
    apply integerL1Kernel_ext
    funext m
    change (((interpolatedFloorPowerMSZKernel c t).coeff m : ℝ) : ℂ) = _
    rw [interpolatedMSZKernel_integer_coeff c t N ht m]
    exact floorPowerRealKernelCoeff_complex c N m
  rw [mszKernelAverage,hkernel,unweightedAverage_integerShift_eq_integerKernelConvolution]

theorem mszKernelAverage_dyadic_maximal_domination
    (c : ℝ) (k : ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ENNReal.ofReal ‖mszKernelAverage (interpolatedFloorPowerMSZKernel c (mszDyadicTime k)) f x‖ ≤
      unweightedIntegerMaximal c f x := by
  by_cases hk : k ≤ 0
  · rw [mszKernelAverage_dyadic_nonpos c k hk,mszKernelAverage,floorPowerMSZKernel_toIntegerL1Kernel,
      ← unweightedAverage_integerShift_eq_integerKernelConvolution]
    exact le_iSup (fun N : Scale => ENNReal.ofReal ‖unweightedAverage integerShiftSystem c f N x‖) ⟨1,by omega⟩
  · let N : Scale := ⟨2^k.toNat,by positivity⟩
    have ht : ((mszDyadicTime k).val : ℝ) = (N.val : ℝ) := by
      have hkn : k = (k.toNat : ℤ) := by omega
      rw [mszDyadicTime_value,hkn,zpow_natCast]
      norm_cast
    rw [interpolatedMSZKernel_integer_average c (mszDyadicTime k) N ht]
    exact le_iSup (fun N : Scale => ENNReal.ofReal ‖unweightedAverage integerShiftSystem c f N x‖) N


/-- The source dyadic maximal field, with one uniform constant and actual
nonnegative real lp majorants, now follows from the checked unweighted bound. -/
theorem mszConcreteDyadicMaximalBound
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c) {q : ℝ} (hq : 1 < q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal q),
      ∃ g : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal q),
        (∀ x, 0 ≤ g x) ∧
        (∀ k x, ‖mszKernelAverage (interpolatedFloorPowerMSZKernel c (mszDyadicTime k))
          (f : ℤ → ℂ) x‖ ≤ g x) ∧ ‖g‖ ≤ M*‖f‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  have hq0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  obtain ⟨C,hC,hBoth⟩ := unweightedDyadicVariationAndMaximal hq (by norm_num : (2 : ℝ) < 3) c hc hcNon
  refine ⟨C,hC,fun f => ?_⟩
  let F := generalLpToCountLp hq0 ENNReal.ofReal_ne_top f
  have hFfun : (F : ℤ → ℂ) = (f : ℤ → ℂ) :=
    funext (generalLpToCountLp_apply hq0 ENNReal.ofReal_ne_top f)
  have hInput : eLpNorm (F : ℤ → ℂ) (ENNReal.ofReal q) Measure.count = ENNReal.ofReal ‖f‖ := by
    rw [← ofReal_lpNorm (Lp.memLp F)]
    change ENNReal.ofReal ‖F‖ = ENNReal.ofReal ‖f‖
    rw [generalLpToCountLp_norm]
  have hM := (le_add_of_nonneg_left (bot_le : (0 : ℝ≥0∞) ≤
    eLpNorm (rVariationFun 3 (unweightedDyadicFamily c (F : ℤ → ℂ)))
      (ENNReal.ofReal q) Measure.count)).trans (hBoth F)
  rw [hInput,hFfun,← ENNReal.ofReal_mul hC] at hM
  have hHM : MemLp (unweightedIntegerMaximal c (f : ℤ → ℂ)) (ENNReal.ofReal q) Measure.count :=
    memLp_iff.mpr (hM.trans_lt ENNReal.ofReal_lt_top)
  obtain ⟨g,hg,hgnonneg,hgReal,hgnorm⟩ := realSequenceMajorant_of_ennreal_eLpNorm_bound hq
    (mul_nonneg hC (norm_nonneg f)) (unweightedIntegerMaximal c (f : ℤ → ℂ)) hHM hM
  refine ⟨g,hgnonneg,?_,hgnorm⟩
  intro k x
  have h := mszKernelAverage_dyadic_maximal_domination c k (f : ℤ → ℂ) x
  rw [← hgReal x] at h
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (norm_nonneg _),ENNReal.toReal_ofReal (hgnonneg x)] at hr
  exact hr

#print axioms mszConcreteDyadicMaximalBound

#print axioms mszKernelAverage_dyadic_maximal_domination
end
end FractionalPrimes.Literature.Harmonic
end
