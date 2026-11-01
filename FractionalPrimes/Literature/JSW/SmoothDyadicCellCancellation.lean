module

public import FractionalPrimes.Literature.JSW.SmoothDyadicKernelSupport
public import FractionalPrimes.Literature.JSW.DyadicAverageAlgebra

/-! Exact countable-cell cancellation for the source centered test function. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem integral_cellConstant_mul_eq_zero
    (j : ℤ) (a g : ℝ → ℂ)
    (hstep : ∀ l : ℤ, ∃ c : ℂ, ∀ y ∈ dyadicInterval j l, a y = c)
    (hcancel : ∀ l : ℤ, ∫ y in dyadicInterval j l, g y ∂volume = 0)
    (hint : Integrable (fun y => a y*g y) volume) :
    (∫ y, a y*g y ∂volume) = 0 := by
  let Q : ℤ → Set ℝ := fun l => dyadicInterval j l
  have hcover : ⋃ l, Q l = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨dyadicIntervalIndex j y, mem_dyadicIntervalIndex j y⟩
  have hQ (l : ℤ) : MeasurableSet (Q l) := measurableSet_Ico
  have hdisj : Pairwise (fun l k : ℤ => Disjoint (Q l) (Q k)) := by
    intro l k hlk
    rw [Set.disjoint_left]
    intro y hyl hyk
    apply hlk
    exact (dyadicIntervalIndex_eq_of_mem hyl).symm.trans (dyadicIntervalIndex_eq_of_mem hyk)
  have hterm (l : ℤ) : (∫ y in Q l, a y*g y ∂volume) = 0 := by
    obtain ⟨c,hc⟩ := hstep l
    calc
      _ = ∫ y in Q l, c*g y ∂volume := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (hQ l)] with y hy
        rw [hc y hy]
      _ = c*(∫ y in Q l, g y ∂volume) := integral_const_mul _ _
      _ = 0 := by rw [hcancel l]; simp
  have hIntUnion : IntegrableOn (fun y => a y*g y) (⋃ l, Q l) volume := by
    rw [hcover]
    exact hint.integrableOn
  calc
    _ = ∫ y in ⋃ l, Q l, a y*g y ∂volume := by simp only [hcover, Measure.restrict_univ]
    _ = ∑' l : ℤ, ∫ y in Q l, a y*g y ∂volume := integral_iUnion hQ hdisj hIntUnion
    _ = 0 := by simp only [hterm, tsum_zero]

theorem integral_centeredPsi_mul_dyadicDifference_eq_zero
    {σ : Measure ℝ} [IsProbabilityMeasure σ] (τ : ℝ) (j : ℤ) (x : ℝ)
    {f : ℝ → ℂ} (hf : LocallyIntegrable f volume)
    (hint : Integrable (fun y : ℝ =>
      Complex.ofReal (τ⁻¹*measureSplittingPsi σ ((x-smoothDyadicCellCenter j y)/τ)) *
        dyadicDifference j f y) volume) :
    (∫ y : ℝ, Complex.ofReal (τ⁻¹*measureSplittingPsi σ
      ((x-smoothDyadicCellCenter j y)/τ)) * dyadicDifference j f y ∂volume) = 0 := by
  apply integral_cellConstant_mul_eq_zero j _ _ ?_
    (fun l => dyadicDifference_integral_eq_zero hf j l) hint
  intro l
  refine ⟨Complex.ofReal (τ⁻¹*measureSplittingPsi σ
    ((x-((l : ℝ)+1/2)*(2 : ℝ)^j)/τ)), ?_⟩
  intro y hy
  simp only [smoothDyadicCellCenter, dyadicIntervalIndex_eq_of_mem hy]

#print axioms integral_centeredPsi_mul_dyadicDifference_eq_zero
#print axioms integral_cellConstant_mul_eq_zero
end
end FractionalPrimes.Literature.JSW
end
