module

public import FractionalPrimes.Literature.Ergodic.FiniteKernelTransference
public import FractionalPrimes.GeneralDiscreteLpBridge
public import FractionalPrimes.LpConvolutionCLM

/-! Exact finite-kernel representations of weighted floor-power averages. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace FractionalPrimes.Literature.Ergodic
noncomputable section

def weightedFloorKernelFinsupp (c : ℝ) (N : Scale) (w : ℕ → ℂ) : ℤ →₀ ℂ := by
  classical
  exact Finsupp.onFinset ((Finset.Icc 1 N.val).image (floorPower c))
    (finiteWeightedIntegerKernel c N w).coeff (by
      intro m hm
      by_contra hnot
      exact hm (finiteWeightedIntegerKernel_coeff_eq_zero_of_not_mem c N w hnot))

@[simp] theorem weightedFloorKernelFinsupp_apply
    (c : ℝ) (N : Scale) (w : ℕ → ℂ) (m : ℤ) :
    weightedFloorKernelFinsupp c N w m = (finiteWeightedIntegerKernel c N w).coeff m := rfl

theorem weightedFloorKernelFinsupp_convolution
    (c : ℝ) (N : Scale) (w : ℕ → ℂ) (f : ℤ → ℂ) :
    finiteKernelConvolution (weightedFloorKernelFinsupp c N w) f =
      integerKernelConvolution (finiteWeightedIntegerKernel c N w) f := by
  classical
  funext j
  unfold finiteKernelConvolution
  rw [integerKernelConvolution_eq_tsum _ _ _
    (finiteWeightedIntegerKernel_convolutionExistsAt c N w f j)]
  symm
  apply tsum_eq_sum
  intro m hm
  have hz : weightedFloorKernelFinsupp c N w m = 0 := Finsupp.notMem_support_iff.mp hm
  rw [weightedFloorKernelFinsupp_apply] at hz
  rw [hz, zero_mul]

theorem weightedFloorKernelFinsupp_systemOperator
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (N : Scale) (w : ℕ → ℂ) (f : X → ℂ) :
    finiteKernelSystemOperator S (weightedFloorKernelFinsupp c N w) f =
      weightedAverage S c w f N := by
  funext x
  have h := congrFun (weightedFloorKernelFinsupp_convolution c N w
    (fun j : ℤ => f (S.iterate (-j) x))) 0
  rw [finiteWeightedIntegerKernel_convolution_eq_sum] at h
  simpa only [finiteKernelConvolution, finiteKernelSystemOperator, weightedAverage,
    zero_sub, neg_neg] using h

#print axioms weightedFloorKernelFinsupp_systemOperator

/-- A counting-measure operator-norm bound transfers to every system with
the same constant and the exact original weighted averages. -/
theorem transferWeightedFloorKernelOperatorNorm
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    {p : ℝ} (hp : 1 < p) (c : ℝ) (N : Scale) (w : ℕ → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hdisc : letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
        (finiteWeightedIntegerKernel c N w)‖ ≤ C)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    eLpNorm (weightedAverage S c w f N) (ENNReal.ofReal p) S.μ ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) S.μ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hfinite (g : ℤ → ℂ) (hg : (Function.support g).Finite) :
      extendedLpNorm Measure.count (ENNReal.ofReal p)
          (fun j => ‖finiteKernelConvolution (weightedFloorKernelFinsupp c N w) g j‖ₑ) ≤
        ENNReal.ofReal C * extendedLpNorm Measure.count (ENNReal.ofReal p)
          (fun j => ‖g j‖ₑ) := by
    have hgseq : Memℓp g (ENNReal.ofReal p) :=
      (memℓp_zero hg).of_exponent_ge bot_le
    have hmemg : MemLp g (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
      memLp_count_of_memlp_seq_finite hp0 ENNReal.ofReal_ne_top ⟨g, hgseq⟩
    let G := hmemg.toLp g
    have hG : (G : ℤ → ℂ) = g :=
      funext (ae_count_int_iff_forall.mp hmemg.coeFn_toLp)
    have hout : (integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
        (finiteWeightedIntegerKernel c N w) G : ℤ → ℂ) =
        integerKernelConvolution (finiteWeightedIntegerKernel c N w) g := by
      funext j
      rw [integerKernelLpConvolutionCLM_apply,
        integerKernelLpConvolution_apply_eq_integerKernelConvolution, hG]
    rw [weightedFloorKernelFinsupp_convolution,
      extendedLpNorm_eq_eLpNorm _ _ _ hp0 ENNReal.ofReal_ne_top
        (measurable_of_countable _).aestronglyMeasurable,
      extendedLpNorm_eq_eLpNorm _ _ _ hp0 ENNReal.ofReal_ne_top
        (measurable_of_countable _).aestronglyMeasurable,
      ← hout, ← hG, ← Lp.enorm_def, ← Lp.enorm_def]
    change ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
        (finiteWeightedIntegerKernel c N w) G‖ₑ ≤
      ENNReal.ofReal C * ‖G‖ₑ
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal
      (((integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
        (finiteWeightedIntegerKernel c N w)).le_opNorm G).trans
          (mul_le_mul_of_nonneg_right hdisc (norm_nonneg G)))
  have hCcoe : ENNReal.ofNNReal (Real.toNNReal C) = ENNReal.ofReal C :=
    ENNReal.ofNNReal_toNNReal C
  have hfinite' := hfinite
  simp_rw [← hCcoe] at hfinite'
  have htransfer := transferFiniteKernelOperatorNorm S (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr hp.le) ENNReal.ofReal_lt_top
    (weightedFloorKernelFinsupp c N w) (Real.toNNReal C) hfinite' f hf
  rw [weightedFloorKernelFinsupp_systemOperator] at htransfer
  change eLpNorm (weightedAverage S c w f N) (ENNReal.ofReal p) S.μ ≤
    ENNReal.ofNNReal (Real.toNNReal C) * eLpNorm f (ENNReal.ofReal p) S.μ at htransfer
  rw [hCcoe] at htransfer
  exact htransfer

#print axioms transferWeightedFloorKernelOperatorNorm
end
end FractionalPrimes.Literature.Ergodic
