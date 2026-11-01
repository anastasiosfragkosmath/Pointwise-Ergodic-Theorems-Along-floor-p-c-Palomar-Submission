module

public import FractionalPrimes.Literature.Ergodic.WeightedKernelTransference
public import FractionalPrimes.Literature.Ergodic.ArithmeticDiscreteOperatorDecay

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
open Literature.Ergodic
noncomputable section

theorem primeComparisonWeightedAverage_eq
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (N : Scale) (f : X → ℂ) :
    weightedAverage S c (fun n => (vonMangoldtWeight n : ℂ) - 1) f N =
      vonMangoldtAverage S c f N - unweightedAverage S c f N := by
  funext x
  simp only [weightedAverage, vonMangoldtAverage, unweightedAverage,
    Pi.sub_apply, sub_mul, one_mul, Finset.sum_sub_distrib, mul_sub]

/-- The sum of the two actual arithmetic operator bounds transfers with the
same constant to each invertible measure-preserving system. -/
theorem arithmeticComparisonSystemNorm_le_of_discrete
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    {p : ℝ} (hp : 1 < p) (c : ℝ) (N : Scale) (B : ℝ)
    (hdisc : letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
        (primeComparisonIntegerKernel c N)‖ +
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
        (mobiusIntegerKernel c N)‖ ≤ B)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    eLpNorm (vonMangoldtAverage S c f N - unweightedAverage S c f N)
        (ENNReal.ofReal p) S.μ +
      eLpNorm (mobiusAverage S c f N) (ENNReal.ofReal p) S.μ ≤
        ENNReal.ofReal B * eLpNorm f (ENNReal.ofReal p) S.μ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let E := ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
    (primeComparisonIntegerKernel c N)‖
  let M := ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
    (mobiusIntegerKernel c N)‖
  have hE : 0 ≤ E := norm_nonneg _
  have hM : 0 ≤ M := norm_nonneg _
  have he := transferWeightedFloorKernelOperatorNorm S hp c N
    (fun n => (vonMangoldtWeight n : ℂ) - 1) E hE (by rfl) f hf
  rw [primeComparisonWeightedAverage_eq] at he
  have hm := transferWeightedFloorKernelOperatorNorm S hp c N
    (fun n => (mobiusWeight n : ℂ)) M hM (by rfl) f hf
  change eLpNorm (mobiusAverage S c f N) (ENNReal.ofReal p) S.μ ≤
    ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) S.μ at hm
  calc
    _ ≤ ENNReal.ofReal E * eLpNorm f (ENNReal.ofReal p) S.μ +
        ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) S.μ := add_le_add he hm
    _ = ENNReal.ofReal (E + M) * eLpNorm f (ENNReal.ofReal p) S.μ := by
      rw [ENNReal.ofReal_add hE hM, add_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hdisc) bot_le

#print axioms arithmeticComparisonSystemNorm_le_of_discrete
end
end FractionalPrimes
