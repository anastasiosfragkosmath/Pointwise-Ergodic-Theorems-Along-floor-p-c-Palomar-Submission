module

public import FractionalPrimes.Literature.JSW.RoughSquareStageExponents
public import FractionalPrimes.Literature.JSW.RoughSquareDenseExtension

/-! The prescribed midpoint exponents stay in the strict bootstrap range. -/

@[expose] public section
namespace FractionalPrimes.Literature.JSW

open MeasureTheory
open scoped ENNReal

theorem roughSquareStage_upper_midpoint_region
    {q p : ℝ} (hq : 1 < q) (hp : 2 < p)
    (hr : |p⁻¹ - (2 : ℝ)⁻¹| < (2*q)⁻¹) :
    let u := (p + roughSquareUpper q)/2
    p < u ∧ |u⁻¹ - (2 : ℝ)⁻¹| < (2*q)⁻¹ := by
  have hqm : 0 < q-1 := by linarith
  have ht := (upper_maximal_exponent_criterion hp hq).2 hr
  have hmul := (lt_div_iff₀ (by linarith : 0 < p-2)).mp ht
  have hpU : p < roughSquareUpper q := by
    unfold roughSquareUpper
    apply (lt_div_iff₀ hqm).2
    nlinarith
  dsimp only
  have hu : p < (p + roughSquareUpper q)/2 := by linarith
  refine ⟨hu, (upper_maximal_exponent_criterion (by linarith) hq).1 ?_⟩
  apply (lt_div_iff₀ (by linarith : 0 < (p+roughSquareUpper q)/2-2)).2
  have hmid : (p+roughSquareUpper q)/2 < roughSquareUpper q := by linarith
  have hm := (lt_div_iff₀ hqm).mp hmid
  nlinarith

theorem roughSquareStage_lower_midpoint_region
    {q p : ℝ} (hq : 1 < q) (hp : 1 < p) (hp2 : p < 2)
    (hr : |p⁻¹ - (2 : ℝ)⁻¹| < (2*q)⁻¹) :
    let u := (roughSquareLower q+p)/2
    1 < u ∧ u < p ∧ |u⁻¹ - (2 : ℝ)⁻¹| < (2*q)⁻¹ := by
  have hqp : 0 < q+1 := by linarith
  have ht := (lower_maximal_exponent_criterion hp hp2 hq).2 hr
  have hmul := (lt_div_iff₀ (by linarith : 0 < 2-p)).mp ht
  have hLp : roughSquareLower q < p := by
    unfold roughSquareLower
    apply (div_lt_iff₀ hqp).2
    nlinarith
  have hL1 : 1 < roughSquareLower q := by
    unfold roughSquareLower
    apply (lt_div_iff₀ hqp).2
    linarith
  dsimp only
  have hu1 : 1 < (roughSquareLower q+p)/2 := by linarith
  have hup : (roughSquareLower q+p)/2 < p := by linarith
  refine ⟨hu1, hup, (lower_maximal_exponent_criterion hu1 (by linarith) hq).1 ?_⟩
  apply (lt_div_iff₀ (by linarith : 0 < 2-(roughSquareLower q+p)/2)).2
  have hmid : roughSquareLower q < (roughSquareLower q+p)/2 := by linarith
  have hm := (div_lt_iff₀ hqp).mp hmid
  nlinarith

theorem roughSquareFinite_stage_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq : 1 < q)
    (hMax : ∀ s : ℝ, q < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hp : 1 < p) (hp2 : p ≠ 2)
    (hr : |p⁻¹ - (2 : ℝ)⁻¹| < (2*q)⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Finset ℤ)
      (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)),
      lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp p b hp k.1 f : ℝ → ℂ) x))
        (ENNReal.ofReal p) volume ≤ K * ‖f‖ := by
  by_cases hlow : p < 2
  · obtain ⟨hu, hup, hur⟩ := roughSquareStage_lower_midpoint_region hq hp hlow hr
    exact roughSquareFinite_bound_lp_below_two hSupp hσ hb hβ hq hMax hu hup hlow hur
  · have hhigh : 2 < p := lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm hp2)
    obtain ⟨hpu, hur⟩ := roughSquareStage_upper_midpoint_region hq hhigh hr
    exact roughSquareFinite_bound_lp_above_two hSupp hσ hb hβ hq hMax hhigh hpu hur

#print axioms roughSquareFinite_stage_bound
#print axioms roughSquareStage_upper_midpoint_region
#print axioms roughSquareStage_lower_midpoint_region
end FractionalPrimes.Literature.JSW
end
