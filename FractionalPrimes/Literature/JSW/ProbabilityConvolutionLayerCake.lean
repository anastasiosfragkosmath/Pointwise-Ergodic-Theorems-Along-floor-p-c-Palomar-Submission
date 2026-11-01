module

public import FractionalPrimes.Literature.JSW.ProbabilityConvolutionComplexLinear
public import FractionalPrimes.Literature.JSW.BoundedMeasurableConvolution
public import FractionalPrimes.Literature.JSW.RoughSquareRawStrongEndpoints
public import FractionalPrimes.Literature.Variation.StrongVariationOfJump
public import FractionalPrimes.Literature.Variation.WeakVariationOfJumpLp

/-! Actual probability convolutions supply the common raw and finite-Lp variation interfaces. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
open FractionalPrimes.Literature.Variation
namespace FractionalPrimes.Literature.JSW
noncomputable section

def probabilityConvolutionLayerCakeExtension
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 < p) :
    LayerCakeLpExtension (volume : Measure ℝ) (ENNReal.ofReal p)
      (ENNReal.one_le_ofReal.mpr hp.le) (probabilityConvolutionRawLinearMap μ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  refine { map := lpProbabilityConvolutionCCLM μ hp, agrees := ?_ }
  intro g hg
  rw [probabilityConvolutionRawLinearMap_eq μ g.1 g.2.1 g.2.2.1]
  exact lpComplexSigmaConvolution_ae_eq_jswConvolution_of_memLp hp μ
    (hg.toLp g.1) g.1 hg hg.coeFn_toLp

theorem probabilityConvolutionRawLinearMap_measurable
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : LayerCakeInput (volume : Measure ℝ)) :
    Measurable (probabilityConvolutionRawLinearMap μ g.1) := by
  rw [probabilityConvolutionRawLinearMap_eq μ g.1 g.2.1 g.2.2.1]
  exact measurable_jswConvolution_of_measurable μ g.2.1

theorem probabilityConvolutionRawLinearMap_eLpNorm_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 < p)
    (g : LayerCakeInput (volume : Measure ℝ)) :
    eLpNorm (probabilityConvolutionRawLinearMap μ g.1) (ENNReal.ofReal p) volume ≤
      eLpNorm g.1 (ENNReal.ofReal p) volume := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hg := roughSquare_layerCakeInput_memLp g (ENNReal.ofReal p)
  let F := hg.toLp g.1
  let Y := lpProbabilityConvolutionCLinearMap μ hp F
  have hrep : (Y : ℝ → ℂ) =ᵐ[volume] probabilityConvolutionRawLinearMap μ g.1 := by
    rw [probabilityConvolutionRawLinearMap_eq μ g.1 g.2.1 g.2.2.1]
    exact lpComplexSigmaConvolution_ae_eq_jswConvolution_of_memLp hp μ F g.1 hg hg.coeFn_toLp
  have hy : MemLp (probabilityConvolutionRawLinearMap μ g.1) (ENNReal.ofReal p) volume :=
    (Lp.memLp Y).ae_eq hrep
  have hnY : ‖Y‖ = lpNorm (probabilityConvolutionRawLinearMap μ g.1) (ENNReal.ofReal p) volume :=
    congrArg ENNReal.toReal (eLpNorm_congr_ae hrep)
  have hnF : ‖F‖ = lpNorm g.1 (ENNReal.ofReal p) volume :=
    congrArg ENNReal.toReal (eLpNorm_congr_ae hg.coeFn_toLp)
  have hn := lpProbabilityConvolution_norm_le μ hp F
  change ‖Y‖ ≤ ‖F‖ at hn
  rw [hnY,hnF] at hn
  have h := eLpNorm_le_mul_of_lpNorm_le (A := 1) hy hg (by simpa only [one_mul] using hn)
  simpa only [ENNReal.ofReal_one, one_mul] using h

theorem probabilityConvolutionRawLinearMap_moment_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 < p)
    (g : LayerCakeInput (volume : Measure ℝ)) :
    complexLpMoment p volume (probabilityConvolutionRawLinearMap μ g.1) ≤
      (ENNReal.ofReal (1 : ℝ)).rpow p*complexLpMoment p volume g.1 := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  rw [complexLpMoment_eq_eLpNorm_rpow volume hp0 _
    (probabilityConvolutionRawLinearMap_measurable μ g),
    complexLpMoment_eq_eLpNorm_rpow volume hp0 _ g.2.1]
  simp only [ENNReal.ofReal_one, ENNReal.rpow_eq_pow, ENNReal.one_rpow, one_mul]
  exact ENNReal.rpow_le_rpow (probabilityConvolutionRawLinearMap_eLpNorm_le μ hp g) hp0.le

#print axioms probabilityConvolutionRawLinearMap_moment_le
#print axioms probabilityConvolutionLayerCakeExtension
end
end FractionalPrimes.Literature.JSW
end
