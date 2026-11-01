module

public import FractionalPrimes.Literature.JSW.SmoothDyadicFiniteExpansion

/-! Passing from finite dyadic expansions to arbitrary L2 inputs. -/
@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem smoothDyadic_finite_energy_of_memLp
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    [Fact (1 ≤ ENNReal.ofReal (2 : ℝ))]
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ)
    {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal (2 : ℝ)) volume) :
    ∑ k ∈ K, ‖smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num)
      (jswTau a ha k) (jswM a ha k) (hf.toLp f)‖^2 ≤
      (smoothDyadicSquareConstant a ha)^2 * ‖hf.toLp f‖^2 := by
  let δ := fun j : ℤ => dyadicDifferenceLpAt (by norm_num : ENNReal.ofReal (2 : ℝ) = 2) hf j
  let R := fun k : ℤ => smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num)
    (jswTau a ha k) (jswM a ha k)
  have hsum := dyadicDifferenceLpAt_hasSum (by norm_num : ENNReal.ofReal (2 : ℝ) = 2) hf
  have hlim : Tendsto (fun J : Finset ℤ => ∑ k ∈ K, ‖R k (∑ j ∈ J, δ j)‖^2)
      atTop (𝓝 (∑ k ∈ K, ‖R k (hf.toLp f)‖^2)) := by
    apply tendsto_finset_sum
    intro k hk
    exact (((R k).continuous.tendsto (hf.toLp f)).comp hsum).norm.pow 2
  exact le_of_tendsto hlim (Filter.Eventually.of_forall fun J =>
    smoothDyadic_finite_expansion_energy hSupp ha K J hf)

theorem smoothDyadic_finite_energy
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    [Fact (1 ≤ ENNReal.ofReal (2 : ℝ))]
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ)
    (F : Lp ℂ (ENNReal.ofReal (2 : ℝ)) (volume : Measure ℝ)) :
    ∑ k ∈ K, ‖smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num)
      (jswTau a ha k) (jswM a ha k) F‖^2 ≤
      (smoothDyadicSquareConstant a ha)^2 * ‖F‖^2 := by
  have heq : (Lp.memLp F).toLp (F : ℝ → ℂ) = F := by
    apply Lp.ext
    exact (Lp.memLp F).coeFn_toLp
  have h := smoothDyadic_finite_energy_of_memLp hSupp ha K (Lp.memLp F)
  simpa only [heq] using h

#print axioms smoothDyadic_finite_energy
end
end FractionalPrimes.Literature.JSW
end
