module

public import FractionalPrimes.Literature.Ergodic.WeightedKernelTransference
public import Mathlib.MeasureTheory.Function.LpSeminorm.Count

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
open Literature.Ergodic
noncomputable section

/-- The zero-frequency scalar is controlled by the discrete convolution norm,
by the already-proved transference theorem on a one-point probability system. -/
theorem weightedScalarMean_norm_le_discreteOperatorNorm
    {p : ℝ} (hp : 1 < p) (c : ℝ) (N : Scale) (w : ℕ → ℂ) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ‖(N.val : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.val, w n‖ ≤
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) (finiteWeightedIntegerKernel c N w)‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  let S : InvertibleSystem Unit := {
    μ := Measure.dirac ()
    sigmaFinite := by infer_instance
    T := MeasurableEquiv.refl Unit
    preserves := MeasurePreserving.id (Measure.dirac ()) }
  let T := integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) (finiteWeightedIntegerKernel c N w)
  have hf : MemLp (fun _ : Unit => (1 : ℂ)) (ENNReal.ofReal p) S.μ := by
    change MemLp (fun _ : Unit => (1 : ℂ)) (ENNReal.ofReal p) (Measure.dirac ())
    exact memLp_const 1
  have h := transferWeightedFloorKernelOperatorNorm S hp c N w ‖T‖ (norm_nonneg _) (by rfl)
    (fun _ : Unit => (1 : ℂ)) hf
  change eLpNorm (weightedAverage S c w (fun _ : Unit => (1 : ℂ)) N)
      (ENNReal.ofReal p) (Measure.dirac ()) ≤
    ENNReal.ofReal ‖T‖ * eLpNorm (fun _ : Unit => (1 : ℂ))
      (ENNReal.ofReal p) (Measure.dirac ()) at h
  rw [eLpNorm_dirac _ _ hp0, eLpNorm_dirac _ _ hp0, enorm_one, mul_one] at h
  have hvalue : weightedAverage S c w (fun _ : Unit => (1 : ℂ)) N () =
      (N.val : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.val, w n := by
    simp only [weightedAverage, mul_one]
  rw [hvalue, ← ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg T)).mp h

#print axioms weightedScalarMean_norm_le_discreteOperatorNorm
end
end FractionalPrimes
