module

public import FractionalPrimes.Literature.JSW.DyadicMeasureVariation

/-! The source harmonic JSW corollary, with literal dilation 2^(a k). -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.External
noncomputable section

/-- `ha:jsw`: the checked one-dimensional Fourier-decay variation corollary. -/
theorem jswDyadicVariation
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D a p r : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖Literature.JSW.measureSplittingFourier σ ξ‖ ≤ D*|ξ|^(-β))
    (hβ : 0 < β) (ha : 0 < a) (hp : 1 < p) (hr : 2 < r)
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    eLpNorm (fun x => Literature.JSW.jswVariation r (fun k : ℤ => Literature.JSW.jswConvolution
      (Measure.map (fun z : ℝ => Real.rpow 2 (a*(k : ℝ))*z) σ) (F : ℝ → ℂ) x))
      (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (Literature.JSW.jswMeasureVariationConstant hSupp hdecay hβ ha p r)*
        eLpNorm (F : ℝ → ℂ) (ENNReal.ofReal p) volume := by
  simpa only [Literature.JSW.jswTau_eq_rpow] using
    Literature.JSW.dyadicMeasureVariation hSupp hdecay hβ ha hp hr F

#print axioms jswDyadicVariation
end
end FractionalPrimes.External
end
