module

public import FractionalPrimes.Literature.Harmonic.MSZDyadicMaximalBridge
public import FractionalPrimes.Literature.Harmonic.MSZSquareFunctionBridge
public import FractionalPrimes.Literature.Harmonic.LocalizedSquareSummability

/-! All concrete MSZ admissibility fields for the actual interpolated unweighted averages. -/
@[expose] public section
open scoped ENNReal
namespace FractionalPrimes.Literature.Harmonic
open FractionalPrimes.Literature.MSZ
noncomputable section

def unweightedMSZAdmissibleData
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (q : ℝ) (hq : 1 < q) (hq2 : q ≤ 2) : AdmissibleData := by
  let M := Classical.choose (mszConcreteDyadicMaximalBound c hc hcNon hq)
  have hM := Classical.choose_spec (mszConcreteDyadicMaximalBound c hc hcNon hq)
  refine {
    q := q
    q_gt_one := hq
    q_le_two := hq2
    D := 4
    D_nonneg := by norm_num
    Mq := M
    Mq_nonneg := hM.1
    kernel := interpolatedFloorPowerMSZKernel c
    projections := mszFrequencyProjection c hc
    projections_preserve_l1_add_linf := fun h f hf =>
      mszFrequencyProjection_preserve_l1_add_linf c hc h hf
    projectionsL2 := mszFrequencyProjectionL2 c hc
    projectionsL2_agree := mszFrequencyProjectionL2_agree c hc
    symmetric_resolution := mszFrequencyProjectionL2_symmetricResolution c hc
    P := frequencyProjectionFiniteSquareFunctionBound
    P_nonneg := ?_
    square_function_summable := ?_
    square_function_bound := ?_
    a := localizedSquareCoefficient c hc hcNon
    a_nonneg := mszLocalizedSquareCoefficient_nonneg c hc hcNon
    localized_increment_summable := mszGridIncrement_commonProjection_square_summable c hc hcNon
    localized_increment_bound := mszLocalizedIncrementSquareFunction_bound c hc hcNon
    a_summability := ?_
    local_time_estimate := interpolatedMSZKernel_localTimeEstimate c
    dyadic_maximal_bound := hM.2 }
  · intro s hs
    unfold frequencyProjectionFiniteSquareFunctionBound
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (frequencyProjectionSignedLpBound_nonneg hs)
  · intro s hs f x
    letI : Fact (1 ≤ ENNReal.ofReal s) := ⟨ENNReal.one_le_ofReal.mpr hs.le⟩
    exact mszFrequencyProjection_square_summable c hc s hs f x
  · intro s hs f
    letI : Fact (1 ≤ ENNReal.ofReal s) := ⟨ENNReal.one_le_ofReal.mpr hs.le⟩
    exact mszFrequencyProjection_squareFunction_bound c hc s hs f
  · intro ε ρ hε hρ
    simpa only [Real.rpow_eq_pow, neg_mul] using
      localizedSquareCoefficient_summable c hc hcNon ε ρ hε hρ

#print axioms unweightedMSZAdmissibleData
end
end FractionalPrimes.Literature.Harmonic
end
