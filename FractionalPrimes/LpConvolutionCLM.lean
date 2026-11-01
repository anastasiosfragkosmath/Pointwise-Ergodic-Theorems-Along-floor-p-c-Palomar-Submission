module

public import FractionalPrimes.Operators
public import Mathlib.Topology.Algebra.InfiniteSum.Module

@[expose] public section

/-!
# The counting-`Lp` convolution as a continuous linear map

Each translate in the existing series definition is an isometry multiplied
by the corresponding kernel coefficient. Its operator norm is therefore
summable, so the series itself is a continuous linear map.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The `m`-th translate-and-scale operator in the convolution series. -/
noncomputable def integerKernelLpTermCLM (K : IntegerL1Kernel) (m : ℤ) :
    Lp ℂ p (Measure.count : Measure ℤ) →L[ℂ]
      Lp ℂ p (Measure.count : Measure ℤ) :=
  K.coeff m •
    (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := p)
      (μ := Measure.count) (μb := Measure.count) ℂ (MeasurableEquiv.addLeft (-m))
      (measurePreserving_add_left Measure.count (-m))).toContinuousLinearMap

/-- Applying the bundled translate operator gives the existing pointwise
series summand in `Lp`. -/
theorem integerKernelLpTermCLM_apply (K : IntegerL1Kernel)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) (m : ℤ) :
    integerKernelLpTermCLM K m f = integerKernelLpTerm K f m := by
  simp [integerKernelLpTermCLM, integerKernelLpTerm,
    MeasureTheory.Lp.compMeasurePreservingₗᵢ,
    MeasureTheory.Lp.compMeasurePreservingₗ]

/-- The operator norms of the translate summands form a summable family. -/
theorem integerKernelLpTermCLM_norm_le (K : IntegerL1Kernel) (m : ℤ) :
    ‖integerKernelLpTermCLM (p := p) K m‖ ≤ ‖K.coeff m‖ := by
  rw [integerKernelLpTermCLM, norm_smul]
  have hshift :
      ‖(Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := p)
        (μ := Measure.count) (μb := Measure.count) ℂ (MeasurableEquiv.addLeft (-m))
        (measurePreserving_add_left Measure.count (-m))).toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖(Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := p)
        (μ := Measure.count) (μb := Measure.count) ℂ (MeasurableEquiv.addLeft (-m))
        (measurePreserving_add_left Measure.count (-m))) f‖ ≤ 1 * ‖f‖
    rw [LinearIsometry.norm_map]
    norm_num
  calc
    ‖K.coeff m‖ *
        ‖(Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := p)
          (μ := Measure.count) (μb := Measure.count) ℂ (MeasurableEquiv.addLeft (-m))
          (measurePreserving_add_left Measure.count (-m))).toContinuousLinearMap‖ ≤
      ‖K.coeff m‖ * 1 := mul_le_mul_of_nonneg_left hshift (norm_nonneg _)
    _ = ‖K.coeff m‖ := by ring

theorem integerKernelLpTermCLM_summable_norm (K : IntegerL1Kernel) :
    Summable fun m : ℤ => ‖integerKernelLpTermCLM (p := p) K m‖ := by
  exact K.summable_norm.of_nonneg_of_le
    (fun m => norm_nonneg _)
    (fun m => integerKernelLpTermCLM_norm_le K m)

/-- The operator-valued summands are summable in the complete space of
continuous linear maps. -/
theorem integerKernelLpTermCLM_summable (K : IntegerL1Kernel) :
    Summable fun m : ℤ => integerKernelLpTermCLM (p := p) K m :=
  (integerKernelLpTermCLM_summable_norm (p := p) K).of_norm

/-- Convolution by an absolutely summable kernel, as a continuous linear map
on every counting-measure `Lp` space with `p ≥ 1`. -/
noncomputable def integerKernelLpConvolutionCLM (K : IntegerL1Kernel) :
    Lp ℂ p (Measure.count : Measure ℤ) →L[ℂ]
      Lp ℂ p (Measure.count : Measure ℤ) :=
  ∑' m : ℤ, integerKernelLpTermCLM (p := p) K m

/-- The bundled continuous linear map agrees with the pre-existing
series-defined convolution on every `Lp` input. -/
theorem integerKernelLpConvolutionCLM_apply (K : IntegerL1Kernel)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    integerKernelLpConvolutionCLM (p := p) K f = integerKernelLpConvolution K f := by
  let eval :
      (Lp ℂ p (Measure.count : Measure ℤ) →L[ℂ]
        Lp ℂ p (Measure.count : Measure ℤ)) →L[ℂ]
        Lp ℂ p (Measure.count : Measure ℤ) :=
    ContinuousLinearMap.apply ℂ (Lp ℂ p (Measure.count : Measure ℤ)) f
  have heval := eval.map_tsum (integerKernelLpTermCLM_summable (p := p) K)
  change (∑' m : ℤ, integerKernelLpTermCLM (p := p) K m) f = _
  rw [integerKernelLpConvolution]
  simpa [eval, integerKernelLpTermCLM_apply] using heval

/-- The bundled convolution map retains the existing full Young estimate. -/
theorem integerKernelLpConvolutionCLM_norm_le (K : IntegerL1Kernel)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    ‖integerKernelLpConvolutionCLM (p := p) K f‖ ≤
      (∑' m : ℤ, ‖K.coeff m‖) * ‖f‖ := by
  rw [integerKernelLpConvolutionCLM_apply]
  exact integerKernelLpConvolution_norm_le K f

end

end FractionalPrimes
