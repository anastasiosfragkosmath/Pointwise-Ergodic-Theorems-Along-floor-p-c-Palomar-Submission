module

public import FractionalPrimes.Literature.JSW.SmoothPsiReflectedAtom
public import FractionalPrimes.Literature.JSW.SmoothDyadicDensityIdentity

/-! Exact reflected-density and probability-convolution identities. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem smoothPsiReflectedConvolution_eq_plus
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {τ : ℝ} (hτ : 0 < τ) (g : ℝ → ℂ) (x : ℝ) :
    smoothPsiReflectedConvolution σ τ g x =
      ∫ t, g (x+t) ∂(Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)) := by
  have hneg := (Measure.measurePreserving_neg volume).integral_comp
    (Homeomorph.neg ℝ).measurableEmbedding
    (fun y : ℝ => Complex.ofReal (smoothPsiReflectedDensity σ τ (x-y))*g y)
  have hid : smoothPsiReflectedConvolution σ τ g x =
      smoothPsiDensityConvolution σ τ (fun y => g (-y)) (-x) := by
    rw [smoothPsiReflectedConvolution, ← hneg]
    apply integral_congr_ae
    filter_upwards [] with y
    congr 2
    dsimp [smoothPsiReflectedDensity]
    congr 1
    ring
  rw [hid, smoothPsiDensityConvolution_eq_probability_all hτ]
  unfold jswConvolution
  congr 1
  funext t
  congr 1
  ring

theorem smoothPsiReflectedConvolution_eq_map_neg
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {τ : ℝ} (hτ : 0 < τ) (g : ℝ → ℂ) (x : ℝ) :
    smoothPsiReflectedConvolution σ τ g x =
      jswConvolution (Measure.map Neg.neg
        (Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ))) g x := by
  rw [smoothPsiReflectedConvolution_eq_plus hτ, jswConvolution]
  have hm : MeasurableEmbedding (Neg.neg : ℝ → ℝ) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  rw [hm.integral_map]
  simp only [sub_neg_eq_add]

#print axioms smoothPsiReflectedConvolution_eq_map_neg
end
end FractionalPrimes.Literature.JSW
end
