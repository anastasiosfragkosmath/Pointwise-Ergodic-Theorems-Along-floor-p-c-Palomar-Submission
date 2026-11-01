module

public import FractionalPrimes.Literature.JSW.MeasureJumpEndpointMoments

/-! The exact full-range jump-to-variation data for actual probability-measure dilates. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
open FractionalPrimes.Literature.Variation
namespace FractionalPrimes.Literature.JSW
noncomputable section

def jswMeasureUniformJumpConstant
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D a : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D*|ξ|^(-β))
    (hβ : 0 < β) (ha : 0 < a) (v : ℝ) : ℝ := by
  classical
  exact if hv : 1 < v then jswMeasureJumpConstant v a ha
    (Classical.choose (measureDilateJumpMoments hSupp hdecay hβ hv ha)) else 0

def jswMeasureFullRangeJumpFamily
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D a : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D*|ξ|^(-β))
    (hβ : 0 < β) (ha : 0 < a) :
    FullRangeJumpOperatorFamily (volume : Measure ℝ) (jswMeasureRawOperator σ a ha) where
  A := jswMeasureUniformJumpConstant hSupp hdecay hβ ha
  B := fun _ => 1
  A_nonneg v hv := by
    simp only [jswMeasureUniformJumpConstant, dif_pos hv]
    exact (Classical.choose_spec (measureDilateJumpMoments hSupp hdecay hβ hv ha)).2.1
  B_nonneg _ _ := by norm_num
  measurable_raw g k := probabilityConvolutionRawLinearMap_measurable _ g
  extension v hv k := probabilityConvolutionLayerCakeExtension _ hv
  fixed v hv g k := probabilityConvolutionRawLinearMap_moment_le _ hv g
  jump := by
    intro v hv J _ _ e g t ht
    simp only [jswMeasureUniformJumpConstant, dif_pos hv]
    exact (Classical.choose_spec (measureDilateJumpMoments hSupp hdecay hβ hv ha)).2.2 e g t ht

#print axioms jswMeasureFullRangeJumpFamily
end
end FractionalPrimes.Literature.JSW
end
