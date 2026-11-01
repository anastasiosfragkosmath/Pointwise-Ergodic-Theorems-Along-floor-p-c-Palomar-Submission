module

public import FractionalPrimes.Literature.JSW.RoughSquarePositiveMaximal
public import FractionalPrimes.Literature.JSW.RoughSquareStageThresholds

/-! Finite recursion closing the source rough-measure square bootstrap. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem roughSquare_positive_maximal_initial
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (hp : 2 < p) :
    ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b p B := by
  let B := weakTypeInterpolationStrongTwoInfinityConstant p
    (initialSquareSigmaPositiveMaximalB2 β D b)
  refine ⟨B, ?_, ?_⟩
  · have hbase : 0 ≤ p/(p-2) := div_nonneg (by linarith) (by linarith)
    have hA := initialSquareSigmaPositiveMaximalB2_nonneg (D := D) hb hβ
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hbase _))
      (Real.rpow_nonneg hA _)
  · intro g hg
    exact countableGeometricSigmaPositiveMaximalBound hSupp hdecay hb hβ hp
      (fun k : ℤ => k) g hg

theorem roughSquare_positive_maximal_stages
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (n : ℕ) :
    ∀ p : ℝ, roughSquareThreshold n < p →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b p B := by
  induction n with
  | zero =>
    intro p hp
    exact roughSquare_positive_maximal_initial hSupp hdecay hb hβ (by simpa using hp)
  | succ n ih =>
    intro p hp
    by_cases hhigh : 2 < p
    · exact roughSquare_positive_maximal_initial hSupp hdecay hb hβ hhigh
    · have hq := roughSquareThreshold_one_lt n
      have hp1 : 1 < p := lt_trans (roughSquareThreshold_one_lt (n+1)) hp
      have hσ := (measureSplitting σ hSupp β hβ D hdecay).1
      apply roughSquare_positive_maximal_stage hSupp hσ hb hβ hq ih hp1
      by_cases heq : p = 2
      · subst p
        simp only [sub_self, abs_zero]
        exact inv_pos.mpr (mul_pos (by norm_num) (by linarith))
      · have hp2 : p < 2 := by rcases lt_or_gt_of_ne heq with h | h <;> linarith
        apply roughSquareThreshold_region_of_lower hq hp1 hp2
        simpa only [roughSquareThreshold_succ] using hp

theorem roughSquare_positive_maximal_all
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (hp : 1 < p) :
    ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b p B := by
  obtain ⟨n, hn⟩ := roughSquareThreshold_eventually_below hp
  exact roughSquare_positive_maximal_stages hSupp hdecay hb hβ n p hn

theorem roughSquare_full_bound_all
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (hp : 1 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      (∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal
        (‖(localizedSquareNuLpConvolution hSupp p b hp k f : ℝ → ℂ) x‖^2)) < ∞) ∧
      eLpNorm (geometricNuSquareFunction hSupp hp b f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (K * ‖f‖) := by
  obtain ⟨n, hn⟩ := roughSquareThreshold_exists_region hp
  exact roughSquare_full_stage_bound_all hSupp
    (measureSplitting σ hSupp β hβ D hdecay).1 hb hβ
    (roughSquareThreshold_one_lt n)
    (roughSquare_positive_maximal_stages hSupp hdecay hb hβ n) hp hn

theorem roughSquare_positive_maximal_reflected
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (hp : 1 < p) :
    ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound (Measure.map Neg.neg σ) b p B := by
  apply roughSquare_positive_maximal_all (D := D) (β := β) (measureSplittingSupport_map_neg σ hSupp) ?_ hb hβ hp
  intro ξ hξ
  rw [measureSplittingFourier_map_neg]
  simpa only [abs_neg] using hdecay (-ξ) (neg_ne_zero.mpr hξ)

/-- The approved `lj:rough-square` conclusions: the actual full ν square
function and both geometric positive maximal operators, for every finite p>1.
The proof uses only the initial source assumptions and finite stage recursion. -/
theorem roughMeasureSquareBound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (hp : 1 < p) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      (∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal
        (‖(localizedSquareNuLpConvolution hSupp p b hp k f : ℝ → ℂ) x‖^2)) < ∞) ∧
      eLpNorm (geometricNuSquareFunction hSupp hp b f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (K * ‖f‖)) ∧
    (∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b p B) ∧
    (∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound (Measure.map Neg.neg σ) b p B) := by
  exact ⟨roughSquare_full_bound_all hSupp hdecay hb hβ hp,
    roughSquare_positive_maximal_all hSupp hdecay hb hβ hp,
    roughSquare_positive_maximal_reflected hSupp hdecay hb hβ hp⟩

#print axioms roughMeasureSquareBound
#print axioms roughSquare_positive_maximal_reflected
#print axioms roughSquare_positive_maximal_all
#print axioms roughSquare_full_bound_all
end
end FractionalPrimes.Literature.JSW
end
