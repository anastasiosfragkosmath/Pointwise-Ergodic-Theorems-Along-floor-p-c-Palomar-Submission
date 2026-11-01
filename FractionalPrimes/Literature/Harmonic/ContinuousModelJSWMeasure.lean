module

public import FractionalPrimes.Literature.Harmonic.JSWAdapter
public import FractionalPrimes.Literature.Harmonic.ContinuousModelVariation

/-! The actual fractional-power model probability and its exact source JSW hypotheses. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.Harmonic
noncomputable section

def continuousModelBaseMeasure (c : ℝ) : Measure ℝ := continuousModelDyadicPushforward c 0

theorem continuousModelBaseMeasure_eq_map (c : ℝ) :
    continuousModelBaseMeasure c = Measure.map (fun u : ℝ => u^c)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  simp only [continuousModelBaseMeasure,continuousModelDyadicPushforward,
    continuousModelDilation,zpow_zero,Real.one_rpow,one_mul]

instance continuousModelBaseMeasure_isProbability (c : ℝ) :
    IsProbabilityMeasure (continuousModelBaseMeasure c) := by
  letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  rw [continuousModelBaseMeasure_eq_map]
  infer_instance

theorem continuousModelBaseMeasure_support (c : ℝ) (hc : 1 < c) :
    (continuousModelBaseMeasure c).support ⊆ Set.Icc (-(1 : ℝ)) 1 := by
  simpa only [continuousModelBaseMeasure,continuousModelDilation,zpow_zero,Real.one_rpow] using
    continuousModelDyadicPushforward_support_subset c hc 0

theorem continuousModelBaseMeasure_fourier (c ξ : ℝ) :
    JSW.measureSplittingFourier (continuousModelBaseMeasure c) ξ = continuousModelV c 1 ξ := by
  rw [JSW.measureSplittingFourier,continuousModelBaseMeasure_eq_map,
    integral_map (by fun_prop) (by fun_prop)]
  rw [continuousModelV,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [] with u
  unfold unitFrequencyPhase
  congr 1
  push_cast
  simp only [Real.one_rpow,Complex.ofReal_one,mul_one]
  ring

theorem continuousModelBaseMeasure_fourier_decay (c : ℝ) (hc : 1 < c)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖JSW.measureSplittingFourier (continuousModelBaseMeasure c) ξ‖ ≤
      continuousModelK c*|ξ|^(-c⁻¹) := by
  rw [continuousModelBaseMeasure_fourier]
  have hK : 0 ≤ continuousModelK c := by
    have hc0 : 0 < c := by linarith
    unfold continuousModelK
    positivity
  calc
    _ ≤ continuousModelK c*min 1 (|ξ|^(-c⁻¹)) := by
      simpa only [continuousModelMin,if_neg hξ,Real.one_rpow,mul_one] using
        continuousModelV_norm_le_min (ξ := ξ) hc (by norm_num : (0 : ℝ) < 1)
    _ ≤ _ := mul_le_mul_of_nonneg_left (min_le_right _ _) hK

theorem continuousModelDilation_eq_jswTau (c : ℝ) (hc : 1 < c) (k : ℤ) :
    continuousModelDilation c k = JSW.jswTau c (by linarith : 0 < c) k := by
  exact (Real.rpow_zpow_comm (by norm_num : (0 : ℝ) ≤ 2) c k).symm

theorem continuousModelBaseMeasure_dilate (c : ℝ) (hc : 1 < c) (k : ℤ) :
    Measure.map (fun z : ℝ => JSW.jswTau c (by linarith : 0 < c) k*z)
      (continuousModelBaseMeasure c) = continuousModelDyadicPushforward c k := by
  rw [continuousModelBaseMeasure_eq_map,Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def,continuousModelDyadicPushforward,continuousModelDilation_eq_jswTau c hc k]

#print axioms continuousModelBaseMeasure_fourier_decay
#print axioms continuousModelBaseMeasure_dilate
end
end FractionalPrimes.Literature.Harmonic
end
