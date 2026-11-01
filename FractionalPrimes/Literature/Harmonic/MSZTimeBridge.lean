module

public import FractionalPrimes.Literature.Harmonic.MSZSquareFunctionBridge
public import FractionalPrimes.Literature.Harmonic.InterpolatedAverageLipschitz

/-! Transfer the checked interpolated-time Lipschitz estimate to the
counting-measure kernel-operator norm used by the MSZ data. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.Harmonic

open FractionalPrimes.Literature.MSZ

noncomputable section

local instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- At an integer time the positive MSZ kernel operator is exactly
the paper's unweighted counting-measure `L¹` average. -/
theorem floorPowerMSZKernel_L1Operator_eq_average
    (c : ℝ) (N : Scale) :
    mszKernelL1Operator (floorPowerMSZKernel c N) =
      unweightedAverageLpCLM (p := (1 : ℝ≥0∞))
        localizedIntegerShiftSystem c N := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [unweightedAverageLpCLM_apply_ae
    (p := (1 : ℝ≥0∞)) localizedIntegerShiftSystem c N f] with x hx
  rw [hx]
  change (integerKernelLpConvolutionCLM (p := (1 : ℝ≥0∞))
    (floorPowerMSZKernel c N).toIntegerL1Kernel f : ℤ → ℂ) x =
      unweightedAverage localizedIntegerShiftSystem c (f : ℤ → ℂ) N x
  rw [floorPowerMSZKernel_toIntegerL1Kernel,
    integerKernelLpConvolutionCLM_apply,
    integerKernelLpConvolution_apply_eq_integerKernelConvolution]
  have hkernel : floorPowerKernel c N =
      finiteWeightedIntegerKernel c N (fun _ => 1) := by
    rfl
  rw [hkernel, finiteWeightedIntegerKernel_convolution_eq_sum]
  simp [unweightedAverage, weightedAverage,
    localizedIntegerShiftSystem_iterate_apply]

#print axioms floorPowerMSZKernel_L1Operator_eq_average

/-- Taking a convex combination of positive kernels gives the same
convex combination of their counting-measure `L¹` operators. -/
theorem convexMSZKernel_L1Operator
    (K L : MSZKernel) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    mszKernelL1Operator (convexMSZKernel K L a ha0 ha1) =
      ((1 - a : ℝ) : ℂ) • mszKernelL1Operator K +
        (a : ℂ) • mszKernelL1Operator L := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  apply ae_count_int_iff_forall.mpr
  intro x
  have hK := integerKernelConvolutionExistsAt_of_Lp
    (by norm_num : 1 ≤ (1 : ℝ≥0∞)) K.toIntegerL1Kernel f x
  have hL := integerKernelConvolutionExistsAt_of_Lp
    (by norm_num : 1 ≤ (1 : ℝ≥0∞)) L.toIntegerL1Kernel f x
  have hKL := integerKernelConvolutionExistsAt_of_Lp
    (by norm_num : 1 ≤ (1 : ℝ≥0∞))
      (convexMSZKernel K L a ha0 ha1).toIntegerL1Kernel f x
  have hsK : Summable (fun m : ℤ =>
      K.toIntegerL1Kernel.coeff m * (f : ℤ → ℂ) (x - m)) :=
    Summable.of_norm (MeasureTheory.integrable_count_iff.mp hK)
  have hsL : Summable (fun m : ℤ =>
      L.toIntegerL1Kernel.coeff m * (f : ℤ → ℂ) (x - m)) :=
    Summable.of_norm (MeasureTheory.integrable_count_iff.mp hL)
  change (integerKernelLpConvolutionCLM (p := (1 : ℝ≥0∞))
      (convexMSZKernel K L a ha0 ha1).toIntegerL1Kernel f : ℤ → ℂ) x =
    (((1 - a : ℝ) : ℂ) •
      integerKernelLpConvolutionCLM (p := (1 : ℝ≥0∞)) K.toIntegerL1Kernel f +
      (a : ℂ) •
      integerKernelLpConvolutionCLM (p := (1 : ℝ≥0∞)) L.toIntegerL1Kernel f :
        Lp ℂ 1 (Measure.count : Measure ℤ)) x
  rw [integerKernelLpConvolutionCLM_apply,
    integerKernelLpConvolutionCLM_apply,
    integerKernelLpConvolutionCLM_apply]
  rw [ae_count_int_iff_forall.mp (Lp.coeFn_add
      (((1 - a : ℝ) : ℂ) •
        integerKernelLpConvolution (p := (1 : ℝ≥0∞)) K.toIntegerL1Kernel f)
      ((a : ℂ) •
        integerKernelLpConvolution (p := (1 : ℝ≥0∞)) L.toIntegerL1Kernel f)) x,
    Pi.add_apply,
    ae_count_int_iff_forall.mp (Lp.coeFn_smul
      (((1 - a : ℝ) : ℂ))
      (integerKernelLpConvolution (p := (1 : ℝ≥0∞)) K.toIntegerL1Kernel f)) x,
    ae_count_int_iff_forall.mp (Lp.coeFn_smul
      (a : ℂ)
      (integerKernelLpConvolution (p := (1 : ℝ≥0∞)) L.toIntegerL1Kernel f)) x]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integerKernelLpConvolution_apply_eq_integerKernelConvolution,
    integerKernelLpConvolution_apply_eq_integerKernelConvolution,
    integerKernelLpConvolution_apply_eq_integerKernelConvolution]
  rw [integerKernelConvolution_eq_tsum _ _ _ hKL,
    integerKernelConvolution_eq_tsum _ _ _ hK,
    integerKernelConvolution_eq_tsum _ _ _ hL]
  change (∑' m : ℤ,
      (((1 - a : ℝ) * K.coeff m + a * L.coeff m : ℝ) : ℂ) *
        (f : ℤ → ℂ) (x - m)) =
      ((1 - a : ℝ) : ℂ) *
        (∑' m : ℤ, (K.coeff m : ℂ) * (f : ℤ → ℂ) (x - m)) +
      (a : ℂ) *
        (∑' m : ℤ, (L.coeff m : ℂ) * (f : ℤ → ℂ) (x - m))
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
  simp_rw [add_mul, mul_assoc]
  let A : ℤ → ℂ := fun m =>
    ((1 - a : ℝ) : ℂ) *
      (K.toIntegerL1Kernel.coeff m * (f : ℤ → ℂ) (x - m))
  let B : ℤ → ℂ := fun m =>
    (a : ℂ) *
      (L.toIntegerL1Kernel.coeff m * (f : ℤ → ℂ) (x - m))
  have hA : Summable A := hsK.mul_left _
  have hB : Summable B := hsL.mul_left _
  change (∑' m : ℤ, (A m + B m)) =
    ((1 - a : ℝ) : ℂ) *
      (∑' m : ℤ, K.toIntegerL1Kernel.coeff m * (f : ℤ → ℂ) (x - m)) +
    (a : ℂ) *
      (∑' m : ℤ, L.toIntegerL1Kernel.coeff m * (f : ℤ → ℂ) (x - m))
  rw [hA.tsum_add hB]
  simp only [A, B, tsum_mul_left]

#print axioms convexMSZKernel_L1Operator

/-- The two scalar actions used by the kernel and interpolation
presentations agree on counting-measure `L¹` operators. -/
private theorem complexCast_smul_eq_real_smul_L1Operator
    (r : ℝ)
    (A : Lp ℂ 1 (Measure.count : Measure ℤ) →L[ℂ]
      Lp ℂ 1 (Measure.count : Measure ℤ)) :
    (r : ℂ) • A = r • A := by
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) r A).symm

#print axioms complexCast_smul_eq_real_smul_L1Operator

/-- The positive-time affine operator identity, with its floor and
weight kept explicit. -/
theorem positiveFloorPowerMSZKernel_L1Operator_eq_affine
    (c : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    mszKernelL1Operator
        (convexMSZKernel
          (floorPowerMSZKernel c ⟨N, hN⟩)
          (floorPowerMSZKernel c ⟨N + 1, by omega⟩)
          a ha0 ha1) =
      ((1 - a : ℝ) : ℂ) •
          unweightedAverageLpCLM (p := (1 : ℝ≥0∞))
            localizedIntegerShiftSystem c ⟨N, hN⟩ +
        a • unweightedAverageLpCLM (p := (1 : ℝ≥0∞))
          localizedIntegerShiftSystem c ⟨N + 1, by omega⟩ := by
  rw [convexMSZKernel_L1Operator,
    floorPowerMSZKernel_L1Operator_eq_average,
    floorPowerMSZKernel_L1Operator_eq_average,
    complexCast_smul_eq_real_smul_L1Operator a]

#print axioms positiveFloorPowerMSZKernel_L1Operator_eq_affine

/-- The positive dyadic-rational kernel operator is exactly the
source's interpolated counting-measure average. -/
theorem interpolatedMSZKernel_L1Operator_eq_average
    (c : ℝ) (t : MSZTime) :
    mszKernelL1Operator (interpolatedFloorPowerMSZKernel c t) =
      interpolatedUnweightedAverage (p := (1 : ℝ≥0∞))
        localizedIntegerShiftSystem c (t.val : ℝ)
        (by exact_mod_cast mszTime_pos t) := by
  let s : ℝ := (t.val : ℝ)
  by_cases hs1 : s ≤ 1
  · simpa [interpolatedFloorPowerMSZKernel,
      interpolatedUnweightedAverage, s, hs1] using
      floorPowerMSZKernel_L1Operator_eq_average c ⟨1, by norm_num⟩
  · have hspos : 0 < s := by
      dsimp [s]
      exact_mod_cast mszTime_pos t
    have hs : 1 < s := lt_of_not_ge hs1
    let N : ℕ := ⌊s⌋₊
    have hN : 1 ≤ N := by
      dsimp [N]
      exact Nat.le_floor (by exact_mod_cast hs.le)
    let a : ℝ := s - (N : ℝ)
    have ha0 : 0 ≤ a := by
      dsimp [a, N]
      exact sub_nonneg.mpr (Nat.floor_le hspos.le)
    have ha1 : a ≤ 1 := by
      dsimp [a, N]
      have hnext := Nat.lt_floor_add_one s
      exact (sub_le_iff_le_add).2 (by linarith)
    change ¬ (t.val : ℝ) ≤ 1 at hs1
    simp only [interpolatedFloorPowerMSZKernel,
      interpolatedUnweightedAverage, dif_neg hs1]
    change mszKernelL1Operator
        (convexMSZKernel
          (floorPowerMSZKernel c ⟨N, hN⟩)
          (floorPowerMSZKernel c ⟨N + 1, by omega⟩)
          a ha0 ha1) =
      ((1 - a : ℝ) : ℂ) •
          unweightedAverageLpCLM (p := (1 : ℝ≥0∞))
            localizedIntegerShiftSystem c ⟨N, hN⟩ +
        a • unweightedAverageLpCLM (p := (1 : ℝ≥0∞))
          localizedIntegerShiftSystem c ⟨N + 1, by omega⟩
    exact positiveFloorPowerMSZKernel_L1Operator_eq_affine
      c N hN a ha0 ha1

#print axioms interpolatedMSZKernel_L1Operator_eq_average

/-- The exact MSZ local-time condition for the paper's positive
interpolated kernel, with source constant `D = 4`. -/
theorem interpolatedMSZKernel_localTimeEstimate
    (c : ℝ) (t : MSZTime) (h : ℚ)
    (hh : 0 < h) (_hh1 : h ≤ 1)
    (ht : t.val + h ∈ positiveDyadicRationals) :
    ‖mszKernelL1Operator
        (interpolatedFloorPowerMSZKernel c ⟨t.val + h, ht⟩) -
      mszKernelL1Operator (interpolatedFloorPowerMSZKernel c t)‖ ≤
      4 * (h : ℝ) / (t.val : ℝ) := by
  rw [interpolatedMSZKernel_L1Operator_eq_average,
    interpolatedMSZKernel_L1Operator_eq_average]
  have htpos : 0 < (t.val : ℝ) := by
    exact_mod_cast mszTime_pos t
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast hh
  simpa only [Subtype.coe_mk, Rat.cast_add] using
    (interpolatedAverageLipschitz (p := (1 : ℝ≥0∞))
      localizedIntegerShiftSystem c (t.val : ℝ) (h : ℝ) htpos hhpos)

#print axioms interpolatedMSZKernel_localTimeEstimate

end

end FractionalPrimes.Literature.Harmonic

end
