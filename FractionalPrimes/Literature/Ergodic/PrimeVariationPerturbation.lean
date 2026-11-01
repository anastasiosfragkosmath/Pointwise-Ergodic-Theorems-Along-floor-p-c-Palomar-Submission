module

public import FractionalPrimes.Literature.Ergodic.SequenceArithmeticOperators

/-! Application of the proved perturbation theorem to the actual arithmetic
averages. The outstanding arithmetic comparison is explicitly retained. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
open Literature.Harmonic
noncomputable section

theorem vonMangoldtDiscreteVariation_of_operatorDecay
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r) (c : FractionalExponent)
    (hdecay : letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ∀ D : ℝ, 0 < D → ∃ C : ℝ, ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
          (primeComparisonIntegerKernel c.value N)‖ ≤
            C * (Real.log (N.val : ℝ)) ^ (-D)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : IntegerSequenceLp p,
      eLpNorm (rVariationFun r (fun N =>
          vonMangoldtAverage integerShiftSystem c.value (f : ℤ → ℂ) N))
          (ENNReal.ofReal p) Measure.count ≤
        C * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  let Q : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p := fun N =>
    integerKernelConvolutionRealExponentCLM p hp (vonMangoldtIntegerKernel c.value N)
  let P : Scale → IntegerSequenceLp p →L[ℂ] IntegerSequenceLp p := fun N =>
    integerKernelConvolutionRealExponentCLM p hp (floorPowerKernel c.value N)
  let E := fun N => Q N - P N
  let I := fun N => Q (perturbationSuccessorScale N) - Q N
  obtain ⟨CP, _hCP, hCP⟩ := unweightedVariation hp hr c.value c.one_lt c.nonIntegral
  have hP (f : IntegerSequenceLp p) :
      eLpNorm (rVariationFun r (fun N => (P N f : ℤ → ℂ)))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal CP * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
    let F := generalLpToCountLp hp0 ENNReal.ofReal_ne_top f
    have hF : (F : ℤ → ℂ) = (f : ℤ → ℂ) :=
      funext (generalLpToCountLp_apply hp0 ENNReal.ofReal_ne_top f)
    have h := hCP F
    rw [hF] at h
    have hrep : (fun N => (P N f : ℤ → ℂ)) =
        (fun N => unweightedAverage integerShiftSystem c.value (f : ℤ → ℂ) N) := by
      funext N x
      exact unweightedSequenceOperator_apply p hp c.value N f x
    rw [hrep]
    exact h
  have hE (N : Scale) :
      E N = integerKernelConvolutionRealExponentCLM p hp
        (primeComparisonIntegerKernel c.value N) :=
    (primeComparisonSequenceOperator_eq_sub p hp c.value N).symm
  have hEdecay : ∀ D : ℝ, 0 < D → ∃ C : ℝ, ∀ N : Scale, 3 ≤ N.val →
      ‖E N‖ ≤ C * (Real.log (N.val : ℝ)) ^ (-D) := by
    intro D hD
    obtain ⟨C, hC⟩ := hdecay D hD
    refine ⟨C, fun N hN => ?_⟩
    rw [hE N]
    exact (integerKernelConvolutionRealExponentCLM_norm_le p hp _).trans (hC N hN)
  have hI (N : Scale) :
      ‖I N‖ ≤ 2 * (Real.log (2 * (N.val : ℝ)) / ((N.val : ℝ) + 1)) :=
    vonMangoldtSequenceOperator_increment_norm p hp c N
  obtain ⟨C, hC, hvar⟩ := variationOfLogarithmicPerturbation hp hr.le
    (fun N => (Q N).toLinearMap) (fun N => (P N).toLinearMap) E I
    (fun _ => rfl) (fun _ => rfl) CP 2 hP hEdecay hI
  refine ⟨C, hC, fun f => ?_⟩
  have hrep : (fun N => (Q N f : ℤ → ℂ)) =
      (fun N => vonMangoldtAverage integerShiftSystem c.value (f : ℤ → ℂ) N) := by
    funext N x
    exact vonMangoldtSequenceOperator_apply p hp c.value N f x
  have h := hvar f
  change eLpNorm (rVariationFun r (fun N => (Q N f : ℤ → ℂ)))
    (ENNReal.ofReal p) Measure.count ≤
    C * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count at h
  rw [hrep] at h
  exact h

#print axioms vonMangoldtDiscreteVariation_of_operatorDecay
end
end FractionalPrimes
