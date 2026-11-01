module

public import FractionalPrimes.Literature.JSW.SmoothDyadicBlockDecay
public import FractionalPrimes.Literature.JSW.DyadicMartingaleJump
public import FractionalPrimes.Literature.JSW.PositiveMaximalNuVectorBound
public import FractionalPrimes.Literature.JSW.DyadicL2ExponentBridge

/-! Continuous error operators, with the exponent kept explicit throughout. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothPsiLpOperator
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (τ : ℝ) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  let μ := Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)
  letI : IsProbabilityMeasure μ := initialSquarePsiDilateProbabilityMeasure_isProbability hSupp τ
  let μc := initialSquareSigmaComplexMeasure μ
  letI : IsFiniteMeasure μc.variation := by
    dsimp [μc]
    rw [initialSquareSigmaComplexMeasure_variation_eq]
    infer_instance
  exact lpComplexMeasureConvolutionCLM (ENNReal.ofReal p) ENNReal.ofReal_ne_top μc

def smoothDyadicErrorLpOperator
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (τ : ℝ) (m : ℤ) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
  smoothPsiLpOperator hSupp p τ-(dyadicAverageLpCLM hp m).restrictScalars ℝ

theorem smoothDyadicErrorLpOperator_ae_eq
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (τ : ℝ) (m : ℤ)
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) (g : ℝ → ℂ)
    (hg : Measurable g) (hgm : MemLp g (ENNReal.ofReal p) volume)
    (hF : (F : ℝ → ℂ) =ᵐ[volume] g) :
    (smoothDyadicErrorLpOperator hSupp hp τ m F : ℝ → ℂ) =ᵐ[volume]
      (fun x => jswConvolution
        (Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)) g x-
        dyadicAverage m g x) := by
  let μ := Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)
  letI : IsProbabilityMeasure μ := initialSquarePsiDilateProbabilityMeasure_isProbability hSupp τ
  have hconv : (smoothPsiLpOperator hSupp p τ F : ℝ → ℂ) =ᵐ[volume] jswConvolution μ g :=
    lpComplexSigmaConvolution_ae_eq_jswConvolution hp μ F g hg hgm hF
  have havg := dyadicAverageLpCLM_coeFn hp m F
  have hsub := Lp.coeFn_sub (smoothPsiLpOperator hSupp p τ F) (dyadicAverageLpCLM hp m F)
  filter_upwards [hconv, havg, hsub] with x hxconv hxavg hxsub
  change (smoothPsiLpOperator hSupp p τ F-dyadicAverageLpCLM hp m F :
    Lp ℂ (ENNReal.ofReal p) volume) x = _
  rw [hxsub, Pi.sub_apply, hxconv, hxavg, dyadicAverage_eq_of_ae_eq_jump hF m x]

theorem smoothDyadicErrorLpOperator_ae_eq_of_memLp
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (τ : ℝ) (m : ℤ)
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) (g : ℝ → ℂ)
    (hgm : MemLp g (ENNReal.ofReal p) volume)
    (hF : (F : ℝ → ℂ) =ᵐ[volume] g) :
    (smoothDyadicErrorLpOperator hSupp hp τ m F : ℝ → ℂ) =ᵐ[volume]
      (fun x => jswConvolution
        (Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)) g x-
        dyadicAverage m g x) := by
  let g' := hgm.aestronglyMeasurable.mk g
  have hgg' : g =ᵐ[volume] g' := hgm.aestronglyMeasurable.ae_eq_mk
  have hg' : Measurable g' := hgm.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hg'm : MemLp g' (ENNReal.ofReal p) volume := (memLp_congr_ae hgg').mp hgm
  have hrep := smoothDyadicErrorLpOperator_ae_eq hSupp hp τ m F g' hg' hg'm (hF.trans hgg')
  let μ := Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)
  letI : IsProbabilityMeasure μ := initialSquarePsiDilateProbabilityMeasure_isProbability hSupp τ
  have hconv := integral_sub_translation_congr_ae μ g' g hgg'.symm
  filter_upwards [hrep, hconv] with x hx hxconv
  change jswConvolution μ g' x = jswConvolution μ g x at hxconv
  rw [hx, hxconv, dyadicAverage_eq_of_ae_eq_jump hgg'.symm m x]

#print axioms smoothDyadicErrorLpOperator_ae_eq_of_memLp
#print axioms smoothDyadicErrorLpOperator_ae_eq
end
end FractionalPrimes.Literature.JSW
end
