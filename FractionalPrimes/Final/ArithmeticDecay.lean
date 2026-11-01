module
public import FractionalPrimes.Final.WeightedConvergence
public import FractionalPrimes.Literature.Ergodic.PrimePsiFromOperatorDecay
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- The already verified arithmetic source supplies arbitrary logarithmic
decay; no arithmetic proposition is added as a hypothesis. -/
theorem arithmeticDiscreteDecay {p : ℝ} (hp : 1 < p) (c : FractionalExponent) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ∀ D : ℝ, 0 < D → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : Scale, 3 ≤ N.val →
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
          (primeComparisonIntegerKernel c.value N)‖ +
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
          (mobiusIntegerKernel c.value N)‖ ≤
        C * (Real.log (N.val : ℝ)) ^ (-D : ℝ) :=
  arithmeticComparisonDiscreteOperatorDecayOf_OAISource_DP_PTW hp c.one_lt c.nonIntegral
    Literature.DirichletAdapter.shortIntervalDirichletTask_of_sourceComponents
    Literature.Polynomial.restrictedPolynomialTwistedTask_of_OAISource

theorem primeCountingAsymptotic (c : FractionalExponent) :
    Tendsto (fun N : ℕ =>
      (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  have hpsi := paperPsi_div_tendsto_one_of_operatorDecay (p := 2) (by norm_num) c.value
    (by
      letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
      intro D hD
      obtain ⟨C, _, hC⟩ := arithmeticDiscreteDecay (p := 2) (by norm_num) c D hD
      refine ⟨C, ?_⟩
      intro N hN
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hC N hN))
  have h := (primeCountingNormalization_of_paperPsi_div_tendsto_one hpsi).2.2.1
  simpa only [paperPi, Nat.floor_natCast] using h

#print axioms arithmeticDiscreteDecay
#print axioms primeCountingAsymptotic
end
end FractionalPrimes.Final
