module

public import FractionalPrimes.Operators
public import FractionalPrimes.FiniteSupportLpConstruction
public import FractionalPrimes.LpConvolutionCLM

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open scoped ENNReal

/-- The Young inequality clause of the MSZ convolution-bounds lemma, using
the project's absolutely summable integer kernel and Mathlib's counting
measure `Lp` representation. The general kernel estimate is reused from the
already checked convolution foundation. -/
theorem convolutionYoungBound {p : ℝ≥0∞} (hp : 1 ≤ p)
    (K : IntegerL1Kernel) (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    eLpNorm (integerKernelConvolution K (f : ℤ → ℂ)) p Measure.count ≤
      (∑' m : ℤ, ‖K.coeff m‖ₑ) * eLpNorm (f : ℤ → ℂ) p Measure.count :=
  eLpNorm_integerKernelConvolution_le hp K f

/-- The standard L¹ operator associated to the MSZ convolution kernel. -/
noncomputable def convolutionL1Operator (K : IntegerL1Kernel) :
    Lp ℂ 1 (Measure.count : Measure ℤ) →L[ℂ]
      Lp ℂ 1 (Measure.count : Measure ℤ) :=
  integerKernelLpConvolutionCLM (p := 1) K

/-- The unit point mass at zero as a counting-measure `L¹` vector. -/
noncomputable def deltaZeroLp : Lp ℂ 1 (Measure.count : Measure ℤ) :=
  finiteSupportCountLpOne {0} (fun _ => 1)

@[simp]
theorem deltaZeroLp_apply (n : ℤ) :
    (deltaZeroLp : ℤ → ℂ) n = if n = 0 then 1 else 0 := by
  rw [deltaZeroLp, finiteSupportCountLpOne_apply]
  simp

theorem deltaZeroLp_norm : ‖deltaZeroLp‖ = 1 := by
  rw [deltaZeroLp, Lp.norm_def, finiteSupportCountLpOne_eLpNorm]
  norm_num

/-- Convolution of the unit mass at zero recovers the kernel pointwise. -/
theorem convolutionL1Operator_delta_apply (K : IntegerL1Kernel) (n : ℤ) :
    (convolutionL1Operator K deltaZeroLp : ℤ → ℂ) n = K.coeff n := by
  rw [convolutionL1Operator, integerKernelLpConvolutionCLM_apply,
    integerKernelLpConvolution_coeFn_eq_kernelSeries]
  rw [tsum_eq_single n]
  · simp
  · intro m hmn
    have hsub : n - m ≠ 0 := by
      intro hz
      exact hmn (sub_eq_zero.mp hz).symm
    simp [hsub]

/-- The `L¹` norm of the convolution of the unit mass is exactly the
kernel's `ℓ¹` norm. -/
theorem convolutionL1Operator_delta_norm (K : IntegerL1Kernel) :
    ‖convolutionL1Operator K deltaZeroLp‖ = ∑' m : ℤ, ‖K.coeff m‖ := by
  have hpoint :
      (convolutionL1Operator K deltaZeroLp : ℤ → ℂ) = K.coeff := by
    funext n
    exact convolutionL1Operator_delta_apply K n
  have hcoeff :
      (∑' m : ℤ, ‖K.coeff m‖ₑ) =
        ENNReal.ofReal (∑' m : ℤ, ‖K.coeff m‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun m => norm_nonneg _) K.summable_norm]
    simp [enorm_eq_nnnorm]
  rw [Lp.norm_def, hpoint,
    eLpNorm_one_eq_lintegral_enorm
      (measurable_of_countable K.coeff).aestronglyMeasurable,
    lintegral_count, hcoeff, ENNReal.toReal_ofReal]
  exact tsum_nonneg (fun m : ℤ => norm_nonneg (K.coeff m))

/-- The `L¹` convolution operator norm is exactly the `ℓ¹` kernel norm.
The lower bound is witnessed by the point mass at zero. -/
theorem convolutionL1Operator_norm_eq (K : IntegerL1Kernel) :
    ‖convolutionL1Operator K‖ = ∑' m : ℤ, ‖K.coeff m‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _
      (tsum_nonneg fun m : ℤ => norm_nonneg (K.coeff m))
    intro f
    simpa [convolutionL1Operator] using
      (integerKernelLpConvolutionCLM_norm_le (p := 1) K f)
  · calc
      (∑' m : ℤ, ‖K.coeff m‖) =
          ‖convolutionL1Operator K deltaZeroLp‖ :=
            (convolutionL1Operator_delta_norm K).symm
      _ ≤ ‖convolutionL1Operator K‖ * ‖deltaZeroLp‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖convolutionL1Operator K‖ := by rw [deltaZeroLp_norm]; ring

/-- For a real nonnegative complex coefficient, its complex norm is its real
part. -/
theorem integerKernelCoeff_norm_eq_re_of_real_nonneg
    (K : IntegerL1Kernel) (hreal : ∀ m, (K.coeff m).im = 0)
    (hnonneg : ∀ m, 0 ≤ (K.coeff m).re) (m : ℤ) :
    ‖K.coeff m‖ = (K.coeff m).re := by
  have hcoeff : K.coeff m = ((K.coeff m).re : ℂ) := by
    rw [← Complex.re_add_im (K.coeff m), hreal m]
    simp
  calc
    ‖K.coeff m‖ = ‖((K.coeff m).re : ℂ)‖ := congrArg norm hcoeff
    _ = ‖(K.coeff m).re‖ := Complex.norm_real _
    _ = (K.coeff m).re := Real.norm_of_nonneg (hnonneg m)

/-- Pointwise positive-kernel domination. The hypotheses state explicitly
that each complex coefficient is real and nonnegative; the right side is the
corresponding real convolution series against `‖f‖`. -/
theorem integerKernelConvolution_norm_le_positive_tsum
    {p : ℝ≥0∞} (hp : 1 ≤ p) (K : IntegerL1Kernel)
    (hreal : ∀ m, (K.coeff m).im = 0)
    (hnonneg : ∀ m, 0 ≤ (K.coeff m).re)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) (n : ℤ) :
    ‖integerKernelConvolution K (f : ℤ → ℂ) n‖ ≤
      ∑' m : ℤ, (K.coeff m).re * ‖f (n - m)‖ := by
  have hbound : Summable (fun m : ℤ => ‖K.coeff m‖ * ‖f‖) :=
    K.summable_norm.mul_right ‖f‖
  have hterm : Summable (fun m : ℤ =>
      ‖K.coeff m * f (n - m)‖) := by
    apply hbound.of_nonneg_of_le
    · intro m
      exact norm_nonneg _
    · intro m
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (integerLp_norm_apply_le_norm hp f (n - m)) (norm_nonneg _)
  have hexists : IntegerKernelConvolutionExistsAt K (f : ℤ → ℂ) n := by
    change Integrable (fun m : ℤ => K.coeff m * f (n - m)) Measure.count
    rw [MeasureTheory.integrable_count_iff]
    exact hterm
  calc
    ‖integerKernelConvolution K (f : ℤ → ℂ) n‖ =
        ‖∑' m : ℤ, K.coeff m * f (n - m)‖ := by
          rw [integerKernelConvolution_eq_tsum K (f : ℤ → ℂ) n hexists]
    _ ≤ ∑' m : ℤ, ‖K.coeff m * f (n - m)‖ :=
      norm_tsum_le_tsum_norm hterm
    _ = ∑' m : ℤ, (K.coeff m).re * ‖f (n - m)‖ := by
      apply tsum_congr
      intro m
      rw [norm_mul, integerKernelCoeff_norm_eq_re_of_real_nonneg K hreal hnonneg]

/-- Aggregate form of the approved MSZ convolution-bounds lemma: full-range
Young inequality, the exact `L¹` operator norm, and pointwise domination for
explicitly real nonnegative kernels. -/
theorem convolutionBounds (K : IntegerL1Kernel) :
    (∀ p : ℝ≥0∞, 1 ≤ p →
      ∀ f : Lp ℂ p (Measure.count : Measure ℤ),
        eLpNorm (integerKernelConvolution K (f : ℤ → ℂ)) p Measure.count ≤
          (∑' m : ℤ, ‖K.coeff m‖ₑ) *
            eLpNorm (f : ℤ → ℂ) p Measure.count) ∧
    (‖convolutionL1Operator K‖ = ∑' m : ℤ, ‖K.coeff m‖) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p →
      (∀ m, (K.coeff m).im = 0) →
      (∀ m, 0 ≤ (K.coeff m).re) →
      ∀ f : Lp ℂ p (Measure.count : Measure ℤ), ∀ n : ℤ,
        ‖integerKernelConvolution K (f : ℤ → ℂ) n‖ ≤
          ∑' m : ℤ, (K.coeff m).re * ‖f (n - m)‖) := by
  refine ⟨?_, ⟨convolutionL1Operator_norm_eq K, ?_⟩⟩
  · intro p hp f
    exact convolutionYoungBound hp K f
  · intro p hp hreal hnonneg f n
    exact integerKernelConvolution_norm_le_positive_tsum
      hp K hreal hnonneg f n

end FractionalPrimes.Literature.MSZ

end
