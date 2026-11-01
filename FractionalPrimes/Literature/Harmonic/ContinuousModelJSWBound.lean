module

public import FractionalPrimes.Literature.Harmonic.ContinuousModelJSWMeasure

/-! The checked JSW estimate on the actual model Schwartz extension, without an analytic premise. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.Harmonic
noncomputable section

def continuousModelJSWConstant (c : ℝ) (hc : 1 < c) (p r : ℝ) : ℝ :=
  JSW.jswMeasureVariationConstant (continuousModelBaseMeasure_support c hc)
    (fun ξ hξ => continuousModelBaseMeasure_fourier_decay c hc hξ)
    (inv_pos.mpr (by linarith : 0 < c)) (by linarith : 0 < c) p r

theorem continuousModelSchwartzExtension_jsw_bound
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r) (c : ℝ) (hc : 1 < c)
    (g : ℤ →₀ ℂ) :
    eLpNorm (fun x => FractionalPrimes.Literature.Variation.orderedRVariation r
      (fun k : ℤ => continuousModelAllDyadicConvolutionFamily c hc g k x))
      (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (continuousModelJSWConstant c hc p r)*
        eLpNorm (continuousModelSchwartzExtension g : ℝ → ℂ) (ENNReal.ofReal p) volume := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hc0 : 0 < c := by linarith
  let H := continuousModelSchwartzExtension g
  have hH : MemLp (H : ℝ → ℂ) (ENNReal.ofReal p) volume := H.memLp _ _
  let F := hH.toLp (H : ℝ → ℂ)
  have hbound := JSW.dyadicMeasureVariation (continuousModelBaseMeasure_support c hc)
    (fun ξ hξ => continuousModelBaseMeasure_fourier_decay c hc hξ)
    (inv_pos.mpr hc0) hc0 hp hr F
  have hrep (k : ℤ) : JSW.jswConvolution
      (Measure.map (fun z : ℝ => JSW.jswTau c hc0 k*z) (continuousModelBaseMeasure c))
        (F : ℝ → ℂ) =ᵐ[volume] continuousModelAllDyadicConvolutionFamily c hc g k := by
    have h := JSW.integral_sub_translation_congr_ae
      (Measure.map (fun z : ℝ => JSW.jswTau c hc0 k*z) (continuousModelBaseMeasure c))
      (F : ℝ → ℂ) (H : ℝ → ℂ) hH.coeFn_toLp
    rw [continuousModelBaseMeasure_dilate c hc k] at h
    rw [continuousModelBaseMeasure_dilate c hc k]
    exact h
  have hv : (fun x => JSW.jswVariation r (fun k : ℤ => JSW.jswConvolution
      (Measure.map (fun z : ℝ => JSW.jswTau c hc0 k*z) (continuousModelBaseMeasure c))
        (F : ℝ → ℂ) x)) =ᵐ[volume]
      (fun x => FractionalPrimes.Literature.Variation.orderedRVariation r
        (fun k : ℤ => continuousModelAllDyadicConvolutionFamily c hc g k x)) := by
    filter_upwards [ae_all_iff.mpr hrep] with x hx
    exact congrArg (FractionalPrimes.Literature.Variation.orderedRVariation r) (funext hx)
  rw [eLpNorm_congr_ae hv, eLpNorm_congr_ae hH.coeFn_toLp] at hbound
  exact hbound

#print axioms continuousModelSchwartzExtension_jsw_bound
end
end FractionalPrimes.Literature.Harmonic
end
