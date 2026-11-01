module

public import FractionalPrimes.ArithmeticBasics
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.Count

/-!
# Discrete kernels and Fourier transforms

The discrete convolution is expressed through Mathlib's measure-theoretic
convolution with counting measure. The `IntegerL1Kernel` structure records the
blueprint's absolute-summability hypothesis explicitly.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Almost-everywhere statements for counting measure on `ℤ` hold at every
integer, since each singleton has positive counting measure. -/
theorem ae_count_int_iff_forall {P : ℤ → Prop} :
    (∀ᵐ k ∂(Measure.count : Measure ℤ), P k) ↔ ∀ k, P k := by
  rw [MeasureTheory.ae_iff_of_countable]
  simp

/-- An absolutely summable complex kernel on the integer group. -/
structure IntegerL1Kernel where
  coeff : ℤ → ℂ
  summable_norm : Summable fun m => ‖coeff m‖

/-- Convolution of an integer kernel with a complex sequence, using counting
measure. Its pointwise sum formula is exposed only when the corresponding
integrand is integrable. -/
def integerKernelConvolution (K : IntegerL1Kernel) (f : ℤ → ℂ) : ℤ → ℂ :=
  MeasureTheory.convolution K.coeff f (ContinuousLinearMap.lsmul ℂ ℂ)
    (Measure.count : Measure ℤ)

/-- The integrability condition for the pointwise convolution at one index. -/
def IntegerKernelConvolutionExistsAt (K : IntegerL1Kernel) (f : ℤ → ℂ)
    (x : ℤ) : Prop :=
  MeasureTheory.ConvolutionExistsAt K.coeff f x
    (ContinuousLinearMap.lsmul ℂ ℂ) (Measure.count : Measure ℤ)

/-- A kernel supported on a finite set has an integrable convolution
integrand against every complex sequence under counting measure. -/
theorem integerKernelConvolutionExistsAt_of_finiteSupport
    (K : IntegerL1Kernel) (f : ℤ → ℂ) (x : ℤ) (s : Finset ℤ)
    (hs : ∀ m ∉ s, K.coeff m = 0) :
    IntegerKernelConvolutionExistsAt K f x := by
  change Integrable (fun m : ℤ => K.coeff m * f (x - m)) Measure.count
  rw [MeasureTheory.integrable_count_iff]
  apply summable_of_ne_finset_zero (s := s)
  intro m hm
  simp [hs m hm]

/-- An `ℓ²` input has bounded coordinates, so convolution against an
absolutely summable kernel is integrable at every integer. -/
theorem integerKernelConvolutionExistsAt_of_lpL2
    (K : IntegerL1Kernel) (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    IntegerKernelConvolutionExistsAt K (f : ℤ → ℂ) x := by
  have hbound : Summable (fun m : ℤ => ‖K.coeff m‖ * ‖f‖) :=
    K.summable_norm.mul_right ‖f‖
  have hnorm : Summable (fun m : ℤ =>
      ‖K.coeff m * f (x - m)‖) :=
    hbound.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) f (x - m))
        (norm_nonneg _))
  change Integrable (fun m : ℤ => K.coeff m * f (x - m)) Measure.count
  rw [MeasureTheory.integrable_count_iff]
  exact hnorm

/-- Every coordinate of an `Lᵖ` function on counting `ℤ` is bounded by its
`Lᵖ` norm, for `p ≥ 1`. -/
theorem integerLp_norm_apply_le_norm {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) (k : ℤ) :
    ‖f k‖ ≤ ‖f‖ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hbound : ‖f k‖ₑ ≤ ‖f‖ₑ := by
    simpa only [Lp.enorm_def] using
      (enorm_le_eLpNorm_count (f : ℤ → ℂ) k hp0)
  exact ENNReal.coe_le_coe.mp (by simpa only [enorm_eq_nnnorm] using hbound)

/-- An `Lᵖ` input on counting `ℤ` is bounded coordinatewise, so convolution
against an absolutely summable kernel exists at every coordinate. -/
theorem integerKernelConvolutionExistsAt_of_Lp
    {p : ℝ≥0∞} (hp : 1 ≤ p) (K : IntegerL1Kernel)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) (x : ℤ) :
    IntegerKernelConvolutionExistsAt K (f : ℤ → ℂ) x := by
  have hbound : Summable (fun m : ℤ => ‖K.coeff m‖ * ‖f‖) :=
    K.summable_norm.mul_right ‖f‖
  have hnorm : Summable (fun m : ℤ => ‖K.coeff m * f (x - m)‖) :=
    hbound.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (integerLp_norm_apply_le_norm hp f (x - m)) (norm_nonneg _))
  change Integrable (fun m : ℤ => K.coeff m * f (x - m)) Measure.count
  rw [MeasureTheory.integrable_count_iff]
  exact hnorm

/-- Finite convolution satisfies the full `Lᵖ` Young estimate by Minkowski
and translation invariance of counting measure. -/
theorem eLpNorm_finiteIntegerConvolution_le
    {p : ℝ≥0∞} (hp : 1 ≤ p) (s : Finset ℤ) (a : ℤ → ℂ)
    (f : ℤ → ℂ) (hf : AEStronglyMeasurable f (Measure.count : Measure ℤ)) :
    eLpNorm (fun k : ℤ => ∑ i ∈ s, a i * f (k - i)) p Measure.count ≤
      (∑ i ∈ s, ‖a i‖ₑ) * eLpNorm f p Measure.count := by
  classical
  have hsumFun : (fun k : ℤ => ∑ i ∈ s, a i * f (k - i)) =
      ∑ i ∈ s, fun k : ℤ => a i * f (k - i) := by
    funext k
    simp
  rw [hsumFun]
  calc
    eLpNorm (∑ i ∈ s, fun k : ℤ => a i * f (k - i)) p Measure.count ≤
        ∑ i ∈ s, eLpNorm (fun k : ℤ => a i * f (k - i)) p Measure.count :=
      eLpNorm_sum_le hp
    _ = ∑ i ∈ s, ‖a i‖ₑ * eLpNorm f p Measure.count := by
      apply Finset.sum_congr rfl
      intro i hi
      have hmp : MeasurePreserving (MeasurableEquiv.addLeft (-i))
          Measure.count Measure.count :=
        measurePreserving_add_left Measure.count (-i)
      have hfshift : AEStronglyMeasurable
          (fun k : ℤ => f (k - i)) Measure.count := by
        have hfun : (fun k : ℤ => f (k - i)) =
            f ∘ MeasurableEquiv.addLeft (-i) := by
          funext k
          simp [sub_eq_add_neg, add_comm]
        rw [hfun]
        exact hf.comp_measurePreserving hmp
      have hmul : (fun k : ℤ => a i * f (k - i)) =
          a i • (fun k : ℤ => f (k - i)) := by
        funext k
        simp [smul_eq_mul]
      rw [hmul, eLpNorm_const_smul]
      have hfun : (fun k : ℤ => f (k - i)) =
          f ∘ MeasurableEquiv.addLeft (-i) := by
        funext k
        simp [sub_eq_add_neg, add_comm]
      rw [hfun, eLpNorm_comp_measurePreserving hf hmp]
    _ = (∑ i ∈ s, ‖a i‖ₑ) * eLpNorm f p Measure.count := by
      rw [Finset.sum_mul]

/-- The translate-and-scale term in the `Lᵖ` series defining convolution by
an absolutely summable integer kernel. -/
noncomputable def integerKernelLpTerm {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (K : IntegerL1Kernel) (f : Lp ℂ p (Measure.count : Measure ℤ)) (m : ℤ) :
    Lp ℂ p (Measure.count : Measure ℤ) :=
  K.coeff m • Lp.compMeasurePreserving (MeasurableEquiv.addLeft (-m))
    (measurePreserving_add_left Measure.count (-m)) f

/-- Each `Lᵖ` summand represents the corresponding translated pointwise
kernel term almost everywhere. -/
theorem integerKernelLpTerm_coeFn {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (K : IntegerL1Kernel) (f : Lp ℂ p (Measure.count : Measure ℤ)) (m : ℤ) :
    (integerKernelLpTerm K f m : ℤ → ℂ) =ᵐ[Measure.count]
      fun k => K.coeff m * f (k - m) := by
  have hmp : MeasurePreserving (MeasurableEquiv.addLeft (-m))
      Measure.count Measure.count := measurePreserving_add_left Measure.count (-m)
  have hshift :
      (Lp.compMeasurePreserving (MeasurableEquiv.addLeft (-m)) hmp f : ℤ → ℂ) =ᵐ[
        Measure.count] fun k => f (k - m) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving f hmp] with k hk
    simpa [MeasurableEquiv.addLeft, sub_eq_add_neg, add_comm] using hk
  filter_upwards [Lp.coeFn_smul (K.coeff m)
      (Lp.compMeasurePreserving (MeasurableEquiv.addLeft (-m)) hmp f), hshift]
    with k hsmul htranslate
  calc
    (integerKernelLpTerm K f m : ℤ → ℂ) k =
        K.coeff m •
          (Lp.compMeasurePreserving (MeasurableEquiv.addLeft (-m)) hmp f :
            ℤ → ℂ) k := by
          simpa [integerKernelLpTerm] using hsmul
    _ = K.coeff m * f (k - m) := by
      rw [htranslate]
      simp [smul_eq_mul]

/-- The `Lᵖ` norms of the individual translate-and-scale terms are summable. -/
theorem integerKernelLpTerm_summable_norm {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (K : IntegerL1Kernel) (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    Summable fun m : ℤ => ‖integerKernelLpTerm K f m‖ := by
  apply Summable.of_norm
  have h := K.summable_norm.mul_right ‖f‖
  refine h.congr ?_
  intro m
  simp [integerKernelLpTerm, norm_smul, Lp.norm_compMeasurePreserving]

/-- Convolution by an `ℓ¹` kernel as the convergent series of translated
terms in `Lᵖ`. -/
noncomputable def integerKernelLpConvolution {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (K : IntegerL1Kernel) (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    Lp ℂ p (Measure.count : Measure ℤ) :=
  ∑' m : ℤ, integerKernelLpTerm K f m

/-- The `Lᵖ` operator norm of the series-defined convolution is bounded by the
`ℓ¹` norm of its kernel. -/
theorem integerKernelLpConvolution_norm_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (K : IntegerL1Kernel) (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    ‖integerKernelLpConvolution K f‖ ≤ (∑' m : ℤ, ‖K.coeff m‖) * ‖f‖ := by
  have hs := integerKernelLpTerm_summable_norm K f
  calc
    ‖integerKernelLpConvolution K f‖ ≤
        ∑' m : ℤ, ‖integerKernelLpTerm K f m‖ := by
      exact norm_tsum_le_tsum_norm hs
    _ = (∑' m : ℤ, ‖K.coeff m‖) * ‖f‖ := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro m
      simp [integerKernelLpTerm, norm_smul, Lp.norm_compMeasurePreserving]

/-- The representative of the `Lᵖ` series is almost everywhere its pointwise
series of translated terms. -/
theorem integerKernelLpConvolution_coeFn_eq_tsum_ae {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (K : IntegerL1Kernel) (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    (integerKernelLpConvolution K f : ℤ → ℂ) =ᵐ[Measure.count]
      fun k => ∑' m : ℤ, (integerKernelLpTerm K f m : ℤ → ℂ) k := by
  unfold integerKernelLpConvolution
  apply Lp.coeFn_tsum
  exact (tsum_enorm_ne_top_iff_summable_norm).2
    (integerKernelLpTerm_summable_norm K f)

/-- The completed `Lᵖ` convolution is almost everywhere the pointwise
counting-measure series. -/
theorem integerKernelLpConvolution_coeFn_eq_kernelSeries_ae
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (K : IntegerL1Kernel)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    (integerKernelLpConvolution K f : ℤ → ℂ) =ᵐ[Measure.count]
      fun k => ∑' m : ℤ, K.coeff m * f (k - m) := by
  have hseries := integerKernelLpConvolution_coeFn_eq_tsum_ae K f
  have hterms : ∀ᵐ k ∂Measure.count, ∀ m : ℤ,
      (integerKernelLpTerm K f m : ℤ → ℂ) k = K.coeff m * f (k - m) := by
    rw [ae_all_iff]
    intro m
    exact integerKernelLpTerm_coeFn K f m
  filter_upwards [hseries, hterms] with k hk hterms
  rw [hk]
  apply tsum_congr
  exact hterms

/-- The completed `Lᵖ` convolution agrees pointwise with the kernel series on
the counting-measure integer model. -/
theorem integerKernelLpConvolution_coeFn_eq_kernelSeries
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (K : IntegerL1Kernel)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) (k : ℤ) :
    (integerKernelLpConvolution K f : ℤ → ℂ) k =
      ∑' m : ℤ, K.coeff m * f (k - m) := by
  exact (ae_count_int_iff_forall.mp
    (integerKernelLpConvolution_coeFn_eq_kernelSeries_ae K f)) k

/-- A finitely supported input makes the convolution integrand summable at
each point, even when the kernel itself is not finitely supported. -/
theorem integerKernelConvolutionExistsAt_of_finiteInputSupport
    (K : IntegerL1Kernel) (f : ℤ → ℂ) (x : ℤ) (s : Finset ℤ)
    (hs : ∀ j ∉ s, f j = 0) :
    IntegerKernelConvolutionExistsAt K f x := by
  classical
  let A := s.image (fun j : ℤ => x - j)
  have hzero (m : ℤ) (hm : m ∉ A) : f (x - m) = 0 := by
    by_contra hne
    have hmem : x - m ∈ s := by
      by_contra hnot
      exact hne (hs (x - m) hnot)
    apply hm
    simp only [A, Finset.mem_image]
    exact ⟨x - m, hmem, by omega⟩
  change Integrable (fun m : ℤ => K.coeff m * f (x - m)) Measure.count
  rw [MeasureTheory.integrable_count_iff]
  apply summable_of_ne_finset_zero (s := A)
  intro m hm
  simp [hzero m hm]

/-- With its integrability condition, the Mathlib convolution is exactly the
counting-measure series `(K*f)(x)=∑ₘ K(m)f(x-m)`. -/
theorem integerKernelConvolution_eq_tsum (K : IntegerL1Kernel) (f : ℤ → ℂ)
    (x : ℤ) (h : IntegerKernelConvolutionExistsAt K f x) :
    integerKernelConvolution K f x =
      ∑' m : ℤ, K.coeff m * f (x - m) := by
  unfold integerKernelConvolution IntegerKernelConvolutionExistsAt at *
  rw [MeasureTheory.convolution]
  rw [MeasureTheory.integral_countable h]
  simp [smul_eq_mul]

/-- The series-defined `Lᵖ` operator agrees at every integer with Mathlib's
counting-measure convolution of the same input representative. -/
theorem integerKernelLpConvolution_apply_eq_integerKernelConvolution
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (K : IntegerL1Kernel)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) (k : ℤ) :
    (integerKernelLpConvolution K f : ℤ → ℂ) k =
      integerKernelConvolution K (f : ℤ → ℂ) k := by
  rw [integerKernelLpConvolution_coeFn_eq_kernelSeries K f]
  symm
  exact integerKernelConvolution_eq_tsum K (f : ℤ → ℂ) k
    (integerKernelConvolutionExistsAt_of_Lp Fact.out K f k)

/-- Young's inequality for the paper's pointwise convolution by an absolutely
summable integer kernel, in the full range `1 ≤ p ≤ ∞`. -/
theorem eLpNorm_integerKernelConvolution_le
    {p : ℝ≥0∞} (hp : 1 ≤ p) (K : IntegerL1Kernel)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    eLpNorm (integerKernelConvolution K (f : ℤ → ℂ)) p Measure.count ≤
      (∑' m : ℤ, ‖K.coeff m‖ₑ) *
        eLpNorm (f : ℤ → ℂ) p Measure.count := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  have hpoint : integerKernelConvolution K (f : ℤ → ℂ) =
      (integerKernelLpConvolution K f : ℤ → ℂ) := by
    funext k
    exact (integerKernelLpConvolution_apply_eq_integerKernelConvolution K f k).symm
  have hcoeff : (∑' m : ℤ, ‖K.coeff m‖ₑ) =
      ENNReal.ofReal (∑' m : ℤ, ‖K.coeff m‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun m => norm_nonneg _) K.summable_norm]
    simp [enorm_eq_nnnorm]
  rw [hpoint, ← Lp.enorm_def (integerKernelLpConvolution K f),
    ← Lp.enorm_def f, hcoeff]
  calc
    ‖integerKernelLpConvolution K f‖ₑ =
        ENNReal.ofReal ‖integerKernelLpConvolution K f‖ :=
      (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal ((∑' m : ℤ, ‖K.coeff m‖) * ‖f‖) := by
      rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
      exact integerKernelLpConvolution_norm_le K f
    _ = ENNReal.ofReal (∑' m : ℤ, ‖K.coeff m‖) * ‖f‖ₑ := by
      rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]

/-- The absolutely convergent Fourier transform of an `ℓ¹(ℤ)` kernel. -/
noncomputable def integerKernelFourierTransform (K : IntegerL1Kernel) (ξ : ℝ) : ℂ :=
  ∑' m : ℤ, K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ))

/-- At period one, the project's real-frequency phase agrees exactly with
Mathlib's integer Fourier monomial on `AddCircle`. -/
theorem unitFrequencyPhase_int_mul_eq_addCircleFourier (n : ℤ) (x : ℝ) :
    unitFrequencyPhase ((n : ℝ) * x) =
      ((_root_.fourier (T := (1 : ℝ)) n) (x : AddCircle (1 : ℝ))) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  rw [_root_.fourier_coe_apply (T := (1 : ℝ))]
  unfold unitFrequencyPhase
  congr 1
  push_cast
  norm_num
  ring

theorem summable_integerKernelFourier_terms (K : IntegerL1Kernel) (ξ : ℝ) :
    Summable fun m : ℤ => K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ)) := by
  apply Summable.of_norm
  simpa [norm_mul, norm_unitFrequencyPhase] using K.summable_norm

/-- The Fourier transform of an absolutely summable kernel is bounded by its
absolute coefficient sum. -/
theorem integerKernelFourierTransform_norm_le (K : IntegerL1Kernel) (ξ : ℝ) :
    ‖integerKernelFourierTransform K ξ‖ ≤ ∑' m : ℤ, ‖K.coeff m‖ := by
  unfold integerKernelFourierTransform
  have hs := summable_integerKernelFourier_terms K ξ
  calc
    ‖∑' m : ℤ, K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ))‖ ≤
        ∑' m : ℤ, ‖K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ))‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ = ∑' m : ℤ, ‖K.coeff m‖ := by
      apply tsum_congr
      intro m
      simp [norm_mul, norm_unitFrequencyPhase]

/-- Convolution by an absolutely summable kernel acts on a frequency character
by multiplication by the kernel's Fourier transform. -/
theorem integerKernelConvolution_character (K : IntegerL1Kernel) (ξ : ℝ)
    (x : ℤ) :
    integerKernelConvolution K (fun y : ℤ =>
      unitFrequencyPhase (ξ * (y : ℝ))) x =
        integerKernelFourierTransform K ξ * unitFrequencyPhase (ξ * (x : ℝ)) := by
  have hsum : Summable (fun m : ℤ =>
      ‖K.coeff m * unitFrequencyPhase (ξ * ((x - m : ℤ) : ℝ))‖) := by
    simpa [norm_mul, norm_unitFrequencyPhase] using K.summable_norm
  have hint : Integrable
      (fun m : ℤ => K.coeff m * unitFrequencyPhase (ξ * ((x - m : ℤ) : ℝ)))
      (Measure.count : Measure ℤ) := by
    rw [MeasureTheory.integrable_count_iff]
    exact hsum
  have hexists : IntegerKernelConvolutionExistsAt K
      (fun y : ℤ => unitFrequencyPhase (ξ * (y : ℝ))) x := by
    exact hint
  rw [integerKernelConvolution_eq_tsum K _ x hexists]
  unfold integerKernelFourierTransform
  calc
    (∑' m : ℤ,
        K.coeff m * unitFrequencyPhase (ξ * ((x - m : ℤ) : ℝ))) =
      ∑' m : ℤ,
        (K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ))) *
          unitFrequencyPhase (ξ * (x : ℝ)) := by
            apply tsum_congr
            intro m
            have harg : ξ * ((x - m : ℤ) : ℝ) =
                (-ξ * (m : ℝ)) + ξ * (x : ℝ) := by
              push_cast
              ring
            calc
              K.coeff m * unitFrequencyPhase
                  (ξ * ((x - m : ℤ) : ℝ)) =
                K.coeff m * (unitFrequencyPhase (-ξ * (m : ℝ)) *
                  unitFrequencyPhase (ξ * (x : ℝ))) := by
                    rw [harg, unitFrequencyPhase_add]
              _ = (K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ))) *
                  unitFrequencyPhase (ξ * (x : ℝ)) := by ring
    _ = (∑' m : ℤ,
        K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ))) *
          unitFrequencyPhase (ξ * (x : ℝ)) := by
            rw [tsum_mul_right]

private theorem sum_image_indicator {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (g : β → ℂ) :
    (∑ b ∈ s.image f, (∑ a ∈ s, if f a = b then (1 : ℂ) else 0) * g b) =
      ∑ a ∈ s, g (f a) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [eq_comm]
  simp_rw [ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq']
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_image]
  rw [if_pos ⟨x, hx, rfl⟩]

private theorem sum_image_weighted_indicator {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (w : α → ℂ) (g : β → ℂ) :
    (∑ b ∈ s.image f,
      (∑ a ∈ s, if f a = b then w a else 0) * g b) =
      ∑ a ∈ s, w a * g (f a) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [eq_comm, ite_mul]
  simp_rw [zero_mul]
  simp only [Finset.sum_ite_eq']
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_image]
  rw [if_pos ⟨x, hx, rfl⟩]

/-- The finite convolution kernel associated to a weighted fractional-power
average. Its coefficient is the normalized sum of all weights landing at the
same integer time. -/
noncomputable def finiteWeightedIntegerKernel (c : ℝ) (N : Scale)
    (w : ℕ → ℂ) : IntegerL1Kernel where
  coeff m := (N.1 : ℂ)⁻¹ *
    ∑ n ∈ Finset.Icc 1 N.1,
      if floorPower c n = m then w n else 0
  summable_norm := by
    classical
    apply summable_of_ne_finset_zero
      (s := (Finset.Icc 1 N.1).image (floorPower c))
    intro m hm
    have hne : ∀ n ∈ Finset.Icc 1 N.1, floorPower c n ≠ m := by
      intro n hn heq
      exact hm (Finset.mem_image.mpr ⟨n, hn, heq⟩)
    have hsum :
        (∑ n ∈ Finset.Icc 1 N.1,
          if floorPower c n = m then w n else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [hne n hn]
    change ‖(N.1 : ℂ)⁻¹ *
      (∑ n ∈ Finset.Icc 1 N.1,
        if floorPower c n = m then w n else 0)‖ = 0
    rw [hsum]
    simp

/-- Coefficients of a finite weighted kernel vanish outside the image of its
index interval under the floor-time map. -/
theorem finiteWeightedIntegerKernel_coeff_eq_zero_of_not_mem
    (c : ℝ) (N : Scale) (w : ℕ → ℂ) {m : ℤ}
    (hm : m ∉ (Finset.Icc 1 N.1).image (floorPower c)) :
    (finiteWeightedIntegerKernel c N w).coeff m = 0 := by
  classical
  have hne : ∀ n ∈ Finset.Icc 1 N.1, floorPower c n ≠ m := by
    intro n hn heq
    exact hm (Finset.mem_image.mpr ⟨n, hn, heq⟩)
  have hsum :
      (∑ n ∈ Finset.Icc 1 N.1, if floorPower c n = m then w n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [hne n hn]
  change (N.1 : ℂ)⁻¹ *
    (∑ n ∈ Finset.Icc 1 N.1, if floorPower c n = m then w n else 0) = 0
  rw [hsum]
  simp

/-- Finite weighted kernels always define convolution at every point, without
an additional integrability assumption. -/
theorem finiteWeightedIntegerKernel_convolutionExistsAt
    (c : ℝ) (N : Scale) (w : ℕ → ℂ) (f : ℤ → ℂ) (x : ℤ) :
    IntegerKernelConvolutionExistsAt (finiteWeightedIntegerKernel c N w) f x := by
  apply integerKernelConvolutionExistsAt_of_finiteSupport
    (s := (Finset.Icc 1 N.1).image (floorPower c))
  intro m hm
  exact finiteWeightedIntegerKernel_coeff_eq_zero_of_not_mem c N w hm

/-- Convolution by the finite weighted kernel is exactly the corresponding
finite weighted shift average on `ℤ`. -/
theorem finiteWeightedIntegerKernel_convolution_eq_sum
    (c : ℝ) (N : Scale) (w : ℕ → ℂ) (f : ℤ → ℂ) (x : ℤ) :
    integerKernelConvolution (finiteWeightedIntegerKernel c N w) f x =
      (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
        w n * f (x - floorPower c n) := by
  classical
  let I := Finset.Icc 1 N.1
  let S := I.image (floorPower c)
  have h_exists := finiteWeightedIntegerKernel_convolutionExistsAt c N w f x
  rw [integerKernelConvolution_eq_tsum _ _ _ h_exists]
  have hzero (m : ℤ) (hm : m ∉ S) :
      (finiteWeightedIntegerKernel c N w).coeff m * f (x - m) = 0 := by
    have hcoeff := finiteWeightedIntegerKernel_coeff_eq_zero_of_not_mem c N w
      (by simpa [I, S] using hm)
    rw [hcoeff]
    simp
  rw [tsum_eq_sum (s := S) hzero]
  change (∑ b ∈ I.image (floorPower c),
      ((N.1 : ℂ)⁻¹ *
        (∑ n ∈ I, if floorPower c n = b then w n else 0)) * f (x - b)) = _
  calc
    _ = ∑ b ∈ I.image (floorPower c), (N.1 : ℂ)⁻¹ *
          ((∑ n ∈ I, if floorPower c n = b then w n else 0) * f (x - b)) := by
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = (N.1 : ℂ)⁻¹ * ∑ b ∈ I.image (floorPower c),
          (∑ n ∈ I, if floorPower c n = b then w n else 0) * f (x - b) := by
      rw [← Finset.mul_sum]
    _ = (N.1 : ℂ)⁻¹ * ∑ n ∈ I, w n * f (x - floorPower c n) := by
      rw [sum_image_weighted_indicator]
    _ = _ := rfl

/-- The Fourier transform of the finite weighted kernel is the exact
normalized weighted exponential sum. -/
theorem finiteWeightedIntegerKernel_fourier (c ξ : ℝ) (N : Scale)
    (w : ℕ → ℂ) :
    integerKernelFourierTransform (finiteWeightedIntegerKernel c N w) ξ =
      (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
        w n * unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) := by
  classical
  let I := Finset.Icc 1 N.1
  let S := I.image (floorPower c)
  have hzero (m : ℤ) (hm : m ∉ S) :
      (finiteWeightedIntegerKernel c N w).coeff m *
        unitFrequencyPhase (-ξ * (m : ℝ)) = 0 := by
    have hne : ∀ n ∈ I, floorPower c n ≠ m := by
      intro n hn heq
      exact hm (Finset.mem_image.mpr ⟨n, hn, heq⟩)
    have hsum :
        (∑ n ∈ I, if floorPower c n = m then w n else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [hne n hn]
    change ((N.1 : ℂ)⁻¹ *
      (∑ n ∈ I, if floorPower c n = m then w n else 0)) *
        unitFrequencyPhase (-ξ * (m : ℝ)) = 0
    rw [hsum]
    simp
  rw [integerKernelFourierTransform, tsum_eq_sum (s := S) hzero]
  change (∑ b ∈ I.image (floorPower c),
      ((N.1 : ℂ)⁻¹ *
        (∑ n ∈ I, if floorPower c n = b then w n else 0)) *
        unitFrequencyPhase (-ξ * (b : ℝ))) = _
  calc
    _ = ∑ b ∈ I.image (floorPower c), (N.1 : ℂ)⁻¹ *
          ((∑ n ∈ I, if floorPower c n = b then w n else 0) *
            unitFrequencyPhase (-ξ * (b : ℝ))) := by
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = (N.1 : ℂ)⁻¹ * ∑ b ∈ I.image (floorPower c),
          (∑ n ∈ I, if floorPower c n = b then w n else 0) *
            unitFrequencyPhase (-ξ * (b : ℝ)) := by
      rw [← Finset.mul_sum]
    _ = (N.1 : ℂ)⁻¹ * ∑ n ∈ I,
          w n * unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) := by
      rw [sum_image_weighted_indicator]
    _ = _ := rfl

/-- The compensating weight that converts the `1/N` finite-kernel convention
to the paper's prime-average normalization `1/π(N)`. -/
noncomputable def primeKernelWeight (N : ℕ) (p : ℕ) : ℂ :=
  if p.Prime then (N : ℂ) * (Nat.primeCounting N : ℂ)⁻¹ else 0

/-- The prime-restricted integer kernel, represented on `[1,N]` with the
paper's exact `π(N)` normalization. -/
noncomputable def primeIntegerKernel (c : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    IntegerL1Kernel :=
  finiteWeightedIntegerKernel c ⟨N, by omega⟩ (primeKernelWeight N)

/-- The Fourier transform of the prime kernel has precisely the `π(N)⁻¹`
normalization and the prime-restricted phase sum. -/
theorem primeIntegerKernel_fourier (c ξ : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    integerKernelFourierTransform (primeIntegerKernel c N hN) ξ =
      (Nat.primeCounting N : ℂ)⁻¹ *
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          unitFrequencyPhase (-ξ * (floorPower c p : ℝ)) := by
  classical
  let NS : Scale := ⟨N, by omega⟩
  have hπ : Nat.primeCounting N ≠ 0 :=
    Nat.ne_of_gt (primeCounting_pos_of_two_le hN)
  rw [primeIntegerKernel, finiteWeightedIntegerKernel_fourier]
  change (NS.1 : ℂ)⁻¹ *
      ∑ n ∈ Finset.Icc 1 N,
        primeKernelWeight N n * unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) = _
  have hsum :
      (∑ n ∈ Finset.Icc 1 N,
        primeKernelWeight N n * unitFrequencyPhase (-ξ * (floorPower c n : ℝ))) =
      (N : ℂ) * (Nat.primeCounting N : ℂ)⁻¹ *
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          unitFrequencyPhase (-ξ * (floorPower c p : ℝ)) := by
    let C : ℂ := (N : ℂ) * (Nat.primeCounting N : ℂ)⁻¹
    change (∑ n ∈ Finset.Icc 1 N,
      (if n.Prime then C else 0) *
        unitFrequencyPhase (-ξ * (floorPower c n : ℝ))) = _
    calc
      _ = ∑ n ∈ Finset.Icc 1 N, C *
            (if n.Prime then unitFrequencyPhase (-ξ * (floorPower c n : ℝ))
              else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hp : n.Prime <;> simp [hp]
      _ = C * ∑ n ∈ Finset.Icc 1 N,
            (if n.Prime then unitFrequencyPhase (-ξ * (floorPower c n : ℝ))
              else 0) := by rw [← Finset.mul_sum]
      _ = C * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            unitFrequencyPhase (-ξ * (floorPower c p : ℝ)) := by
        rw [← Finset.sum_filter]
  rw [hsum]
  have hN0 : (N : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (by omega)
  have hπ0 : (Nat.primeCounting N : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hπ
  dsimp [NS]
  field_simp [hN0, hπ0]
  

/-- The finite von Mangoldt kernel at scale `N`. -/
noncomputable def vonMangoldtIntegerKernel (c : ℝ) (N : Scale) :
    IntegerL1Kernel :=
  finiteWeightedIntegerKernel c N (fun n => (vonMangoldtWeight n : ℂ))

/-- Exact Fourier multiplier identity for the finite von Mangoldt kernel. -/
theorem vonMangoldtIntegerKernel_fourier (c ξ : ℝ) (N : Scale) :
    integerKernelFourierTransform (vonMangoldtIntegerKernel c N) ξ =
      (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
        (vonMangoldtWeight n : ℂ) *
          unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) := by
  exact finiteWeightedIntegerKernel_fourier c ξ N
    (fun n => (vonMangoldtWeight n : ℂ))

/-- The finite Möbius kernel at scale `N`. -/
noncomputable def mobiusIntegerKernel (c : ℝ) (N : Scale) :
    IntegerL1Kernel :=
  finiteWeightedIntegerKernel c N (fun n => (mobiusWeight n : ℂ))

/-- Exact Fourier multiplier identity for the finite Möbius kernel. -/
theorem mobiusIntegerKernel_fourier (c ξ : ℝ) (N : Scale) :
    integerKernelFourierTransform (mobiusIntegerKernel c N) ξ =
      (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
        (mobiusWeight n : ℂ) *
          unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) := by
  exact finiteWeightedIntegerKernel_fourier c ξ N
    (fun n => (mobiusWeight n : ℂ))

/-- The finite kernel of the unweighted fractional-power average on `ℤ`.
Each index contributes the point mass at `⌊n^c⌋`, with mass `1/N`. -/
noncomputable def floorPowerKernel (c : ℝ) (N : Scale) : IntegerL1Kernel where
  coeff m := (N.1 : ℂ)⁻¹ *
    ∑ n ∈ Finset.Icc 1 N.1, if floorPower c n = m then 1 else 0
  summable_norm := by
    classical
    apply summable_of_ne_finset_zero
      (s := (Finset.Icc 1 N.1).image (floorPower c))
    intro m hm
    have hne : ∀ n ∈ Finset.Icc 1 N.1, floorPower c n ≠ m := by
      intro n hn heq
      exact hm (Finset.mem_image.mpr ⟨n, hn, heq⟩)
    have hsum :
        (∑ n ∈ Finset.Icc 1 N.1, if floorPower c n = m then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [hne n hn]
    change ‖(N.1 : ℂ)⁻¹ *
      (∑ n ∈ Finset.Icc 1 N.1, if floorPower c n = m then (1 : ℂ) else 0)‖ = 0
    rw [hsum]
    simp

/-- The Fourier transform of the exact finite kernel is the multiplier `bN`
from the blueprint, with no endpoint or frequency-sign change. -/
theorem floorPowerKernelFourier_eq_bN (c ξ : ℝ) (N : Scale) :
    integerKernelFourierTransform (floorPowerKernel c N) ξ = bN c ξ N := by
  classical
  let I := Finset.Icc 1 N.1
  let S := I.image (floorPower c)
  have hzero (m : ℤ) (hm : m ∉ S) :
      (floorPowerKernel c N).coeff m * unitFrequencyPhase (-ξ * (m : ℝ)) = 0 := by
    have hne : ∀ n ∈ I, floorPower c n ≠ m := by
      intro n hn heq
      exact hm (Finset.mem_image.mpr ⟨n, hn, heq⟩)
    have hsum :
        (∑ n ∈ I, if floorPower c n = m then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [hne n hn]
    change ((N.1 : ℂ)⁻¹ *
      (∑ n ∈ I, if floorPower c n = m then (1 : ℂ) else 0)) *
        unitFrequencyPhase (-ξ * (m : ℝ)) = 0
    rw [hsum]
    simp
  rw [integerKernelFourierTransform, tsum_eq_sum (s := S) hzero]
  change (∑ b ∈ I.image (floorPower c),
      ((N.1 : ℂ)⁻¹ *
        (∑ n ∈ I, if floorPower c n = b then (1 : ℂ) else 0)) *
        unitFrequencyPhase (-ξ * (b : ℝ))) =
    (N.1 : ℂ)⁻¹ * ∑ n ∈ I,
      unitFrequencyPhase (-ξ * (floorPower c n : ℝ))
  calc
    _ = ∑ b ∈ I.image (floorPower c), (N.1 : ℂ)⁻¹ *
          ((∑ n ∈ I, if floorPower c n = b then (1 : ℂ) else 0) *
            unitFrequencyPhase (-ξ * (b : ℝ))) := by
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = (N.1 : ℂ)⁻¹ * ∑ b ∈ I.image (floorPower c),
          (∑ n ∈ I, if floorPower c n = b then (1 : ℂ) else 0) *
            unitFrequencyPhase (-ξ * (b : ℝ)) := by
      rw [← Finset.mul_sum]
    _ = (N.1 : ℂ)⁻¹ * ∑ n ∈ I,
          unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) := by
      rw [sum_image_indicator]
    _ = bN c ξ N := by rfl

end

end FractionalPrimes
