module

public import FractionalPrimes.Literature.JSW.SmoothDyadicAdjointOperator

/-! Complex linearity and norm one for the existing finite-exponent probability convolution. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem lpProbabilityConvolution_smul
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    (c : ℂ) (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    lpComplexMeasureConvolution (ENNReal.ofReal p) (initialSquareSigmaComplexMeasure μ) (c • F) =
      c • lpComplexMeasureConvolution (ENNReal.ofReal p) (initialSquareSigmaComplexMeasure μ) F := by
  have hF := lpComplexSigmaConvolution_ae_eq_jswConvolution_of_memLp hp μ F
    (F : ℝ → ℂ) (Lp.memLp F) Filter.EventuallyEq.rfl
  have hc := lpComplexSigmaConvolution_ae_eq_jswConvolution_of_memLp hp μ (c • F)
    (fun x => c • F x) ((Lp.memLp F).const_smul c) (Lp.coeFn_smul c F)
  have hout := Lp.coeFn_smul c
    (lpComplexMeasureConvolution (ENNReal.ofReal p) (initialSquareSigmaComplexMeasure μ) F)
  apply Lp.ext
  filter_upwards [hF,hc,hout] with x hFx hcx hox
  rw [hcx,hox,Pi.smul_apply,hFx]
  exact integral_smul c (fun y : ℝ => F (x-y))

def lpProbabilityConvolutionCLinearMap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  letI : IsFiniteMeasure (initialSquareSigmaComplexMeasure μ).variation := by
    rw [initialSquareSigmaComplexMeasure_variation_eq]
    infer_instance
  exact {
    toFun := lpComplexMeasureConvolution (ENNReal.ofReal p) (initialSquareSigmaComplexMeasure μ)
    map_add' := (lpComplexMeasureConvolutionRLinearMap (ENNReal.ofReal p)
      ENNReal.ofReal_ne_top (initialSquareSigmaComplexMeasure μ)).map_add
    map_smul' := lpProbabilityConvolution_smul μ hp }

theorem lpProbabilityConvolution_norm_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    ‖lpProbabilityConvolutionCLinearMap μ hp F‖ ≤ ‖F‖ := by
  letI : IsFiniteMeasure (initialSquareSigmaComplexMeasure μ).variation := by
    rw [initialSquareSigmaComplexMeasure_variation_eq]
    infer_instance
  have h := norm_lpComplexMeasureConvolution_le ENNReal.ofReal_ne_top
    (initialSquareSigmaComplexMeasure μ) F
  change ‖lpComplexMeasureConvolution (ENNReal.ofReal p) (initialSquareSigmaComplexMeasure μ) F‖ ≤ ‖F‖
  simpa only [initialSquareSigmaComplexMeasure_variation_eq, Measure.real,
    measure_univ, ENNReal.toReal_one, one_mul] using h

def lpProbabilityConvolutionCCLM
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
  (lpProbabilityConvolutionCLinearMap μ hp).mkContinuous 1 (by
    intro F
    simpa only [one_mul] using lpProbabilityConvolution_norm_le μ hp F)

#print axioms lpProbabilityConvolution_norm_le
#print axioms lpProbabilityConvolution_smul
end
end FractionalPrimes.Literature.JSW
end
