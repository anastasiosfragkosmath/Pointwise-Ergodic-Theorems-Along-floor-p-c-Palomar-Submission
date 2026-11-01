module

public import FractionalPrimes.Literature.JSW.SmoothDyadicKernelMass
public import FractionalPrimes.Literature.JSW.SmoothDyadicCellCancellation
public import FractionalPrimes.Literature.JSW.DyadicAverageL2Expansion

/-! Integrability of the actual centered test against L2 dyadic differences. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem memLp_two_of_band_bound
    {F : ℝ → ℂ} {R M c : ℝ} (hM : 0 ≤ M) (hF : Measurable F)
    (hbound : ∀ y, ‖F y‖ ≤ M) (hzero : ∀ y, R < |y-c| → F y = 0) :
    MemLp F 2 volume := by
  let S := Set.Icc (c-R) (c+R)
  have hfin : volume S ≠ ∞ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hdom : MemLp (S.indicator (fun _ : ℝ => M)) 2 volume :=
    memLp_indicator_const 2 measurableSet_Icc.nullMeasurableSet M (Or.inr hfin)
  apply hdom.mono' hF.stronglyMeasurable.aestronglyMeasurable
  filter_upwards [] with y
  by_cases hy : y ∈ S
  · rw [Set.indicator_of_mem hy]
    exact hbound y
  · have hfar : R < |y-c| := by
      apply lt_of_not_ge
      intro hle
      apply hy
      rcases abs_le.mp hle with ⟨ha,hb⟩
      constructor <;> linarith
    simp [Set.indicator_of_notMem hy, hzero y hfar]

theorem centeredPsiTest_memLp_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (j : ℤ) (x : ℝ) :
    MemLp (fun y : ℝ => Complex.ofReal
      (τ⁻¹*measureSplittingPsi σ ((x-smoothDyadicCellCenter j y)/τ))) 2 volume := by
  let M := τ⁻¹*lpNorm φ ∞ volume
  have hM : 0 ≤ M := mul_nonneg (inv_nonneg.mpr hτ.le) lpNorm_nonneg
  have hmeas : Measurable (fun y : ℝ => Complex.ofReal
      (τ⁻¹*measureSplittingPsi σ ((x-smoothDyadicCellCenter j y)/τ))) := by
    have hc := smoothDyadicCellCenter_measurable j
    have hψ := (measureSplittingPsi_contDiff σ).continuous.measurable
    fun_prop
  apply memLp_two_of_band_bound (R := 2*τ+(2 : ℝ)^j) (c := x) hM hmeas
  · intro y
    have hψ := measureSplittingPsi_iteratedDeriv_pointwise_bound σ 0
      ((x-smoothDyadicCellCenter j y)/τ)
    simp only [iteratedDeriv_zero] at hψ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hτ]
    exact mul_le_mul_of_nonneg_left hψ (inv_nonneg.mpr hτ.le)
  · intro y hy
    have hd := smoothDyadicCellCenter_distance j y
    have hp : 0 < (2 : ℝ)^j := zpow_pos (by norm_num) _
    have htri := abs_sub_le x (smoothDyadicCellCenter j y) y
    rw [abs_sub_comm (smoothDyadicCellCenter j y) y] at htri
    have hfar : 2*τ < |x-smoothDyadicCellCenter j y| := by
      rw [abs_sub_comm y x] at hy
      linarith
    have hout : (x-smoothDyadicCellCenter j y)/τ ∉ Set.Icc (-(2 : ℝ)) 2 := by
      intro hi
      have h := abs_le.mpr hi
      rw [abs_div, abs_of_pos hτ] at h
      have := (div_le_iff₀ hτ).1 h
      linarith
    simp [measureSplittingPsi_eq_zero_of_not_mem_Icc σ hSupp hout]

theorem centeredPsiTest_mul_dyadicDifference_integrable
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (j : ℤ) (x : ℝ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun y : ℝ => Complex.ofReal
      (τ⁻¹*measureSplittingPsi σ ((x-smoothDyadicCellCenter j y)/τ)) *
        dyadicDifference j f y) volume := by
  exact (centeredPsiTest_memLp_two hSupp hτ j x).integrable_mul
    (memLp_dyadicDifference_two_of_memLp hf j)

#print axioms centeredPsiTest_mul_dyadicDifference_integrable
#print axioms centeredPsiTest_memLp_two
end
end FractionalPrimes.Literature.JSW
end
