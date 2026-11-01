module

public import FractionalPrimes.Literature.JSW.MeasureJumpFullRange

/-! The full approved JSW variation conclusion for actual measure convolutions. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
open FractionalPrimes.Literature.Variation
namespace FractionalPrimes.Literature.JSW
noncomputable section

def jswMeasureVariationConstant
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D a : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D*|ξ|^(-β))
    (hβ : 0 < β) (ha : 0 < a) (p r : ℝ) : ℝ :=
  let A := jswMeasureUniformJumpConstant hSupp hdecay hβ ha
  2*max (weakVariationConstant ((1+p)/2) r (A ((1+p)/2)) 1)
    (weakVariationConstant (2*p) r (A (2*p)) 1)*
      (p*(1/(p-(1+p)/2)+1/(2*p-p)))^(1/p)

/-- `lj:jsw-main`: actual full integer-scale measure-convolution variation,
with precisely the source endpoint choices and interpolation constant recipe. -/
theorem dyadicMeasureVariation
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D a p r : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D*|ξ|^(-β))
    (hβ : 0 < β) (ha : 0 < a) (hp : 1 < p) (hr : 2 < r)
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    eLpNorm (fun x => jswVariation r (fun k : ℤ => jswConvolution
      (Measure.map (fun z : ℝ => jswTau a ha k*z) σ) (F : ℝ → ℂ) x))
      (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (jswMeasureVariationConstant hSupp hdecay hβ ha p r)*
        eLpNorm (F : ℝ → ℂ) (ENNReal.ofReal p) volume := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let U := jswMeasureFullRangeJumpFamily hSupp hdecay hβ ha
  have hp₀ : 1 < (1+p)/2 := by linarith
  have hp₀p : (1+p)/2 < p := by linarith
  have hpp₁ : p < 2*p := by linarith
  have hbound := strongVariationOfJump (volume : Measure ℝ) (jswMeasureRawOperator σ a ha)
    U ((1+p)/2) p (2*p) r hp₀ hp₀p hpp₁ hr F
  have hrep (k : ℤ) : (((U.extension p (hp₀.trans hp₀p) k).map F) : ℝ → ℂ) =ᵐ[volume]
      jswConvolution (Measure.map (fun z : ℝ => jswTau a ha k*z) σ) (F : ℝ → ℂ) := by
    exact lpComplexSigmaConvolution_ae_eq_jswConvolution_of_memLp hp _ F (F : ℝ → ℂ)
      (Lp.memLp F) Filter.EventuallyEq.rfl
  have hvar : orderedRVariationFun r
      (fun k : ℤ => (((U.extension p (hp₀.trans hp₀p) k).map F) : ℝ → ℂ)) =ᵐ[volume]
      (fun x => jswVariation r (fun k : ℤ => jswConvolution
        (Measure.map (fun z : ℝ => jswTau a ha k*z) σ) (F : ℝ → ℂ) x)) := by
    filter_upwards [ae_all_iff.mpr hrep] with x hx
    exact congrArg (orderedRVariation r) (funext hx)
  have hn := eLpNorm_congr_ae hvar (p := ENNReal.ofReal p)
  rw [← hn]
  exact hbound

#print axioms dyadicMeasureVariation
end
end FractionalPrimes.Literature.JSW
end
