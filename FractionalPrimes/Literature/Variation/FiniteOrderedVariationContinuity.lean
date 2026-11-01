module

public import FractionalPrimes.Literature.Variation.FiniteOrderedVariationReal
public import Mathlib.Topology.Order.Lattice

/-!
# Continuity of finite ordered variation

This is the finite-coordinate continuity step in the density argument for
blueprint `lv:jump-to-variation`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- The maximum norm on a finite coordinate set preserves pointwise
sequential limits. -/
theorem finiteOrderedSequenceMaxNorm_tendsto_of_pointwise
    {I : Type*} [Fintype I] (u : ℕ → I → ℂ) (v : I → ℂ)
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (v i))) :
    Tendsto (fun n => finiteOrderedSequenceMaxNorm (u n)) atTop
      (𝓝 (finiteOrderedSequenceMaxNorm v)) := by
  classical
  by_cases hI : Nonempty I
  · let hUniv : (Finset.univ : Finset I).Nonempty :=
      Finset.univ_nonempty_iff.mpr hI
    unfold finiteOrderedSequenceMaxNorm
    simp only [dif_pos hI]
    apply Filter.Tendsto.finset_sup'_nhds_apply hUniv
    intro i hi
    exact continuous_norm.continuousAt.tendsto.comp (hu i)
  · simp [finiteOrderedSequenceMaxNorm, hI]

/-- If every coordinate tends to zero, finite ordered variation tends to
zero. -/
theorem finiteOrderedVariationReal_tendsto_zero_of_pointwise
    {I : Type*} [LinearOrder I] [Fintype I]
    (r : ℝ) (hr : 0 < r) (u : ℕ → I → ℂ)
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 0)) :
    Tendsto (fun n => finiteOrderedVariationReal r (u n)) atTop (𝓝 0) := by
  have hmax : Tendsto (fun n => finiteOrderedSequenceMaxNorm (u n)) atTop
      (𝓝 0) := by
    have h := finiteOrderedSequenceMaxNorm_tendsto_of_pointwise u
      (fun _ : I => 0) hu
    simpa [finiteOrderedSequenceMaxNorm] using h
  have hmaxENN : Tendsto
      (fun n => ENNReal.ofReal (finiteOrderedSequenceMaxNorm (u n)))
      atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hmax
    simpa [Function.comp_def] using h
  let C : ℝ≥0∞ :=
    2 * (Fintype.card I : ℝ≥0∞).rpow r⁻¹
  have hCtop : C ≠ ∞ := by
    apply ne_of_lt
    dsimp [C]
    exact ENNReal.mul_lt_top (by simp)
      (ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.mpr hr.le) (by simp))
  have hupper : Tendsto
      (fun n => C * ENNReal.ofReal (finiteOrderedSequenceMaxNorm (u n)))
      atTop (𝓝 0) := by
    have h := (ENNReal.continuous_const_mul hCtop).continuousAt.tendsto.comp hmaxENN
    simpa [Function.comp_def] using h
  have hvariationENN : Tendsto (fun n => orderedRVariation r (u n))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro n
      exact bot_le
    · intro n
      simpa [C, mul_assoc] using
        orderedRVariation_le_two_card_rpow_maxNorm r (u n) hr
  have htoReal :=
    (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hvariationENN
  simpa [finiteOrderedVariationReal, Function.comp_def] using htoReal

/-- On a finite ordered index set, real-valued ordered variation is
continuous under coordinatewise convergence. -/
theorem finiteOrderedVariationReal_tendsto_of_pointwise
    {I : Type*} [LinearOrder I] [Fintype I]
    (r : ℝ) (hr : 1 ≤ r) (u : ℕ → I → ℂ) (v : I → ℂ)
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (v i))) :
    Tendsto (fun n => finiteOrderedVariationReal r (u n)) atTop
      (𝓝 (finiteOrderedVariationReal r v)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  let d : ℕ → I → ℂ := fun n i => u n i - v i
  have hdPoint (i : I) : Tendsto (fun n => d n i) atTop (𝓝 0) := by
    dsimp [d]
    have hconst : Tendsto (fun _ : ℕ => v i) atTop (𝓝 (v i)) :=
      tendsto_const_nhds
    simpa using (hu i).sub hconst
  have hdVariation : Tendsto
      (fun n => finiteOrderedVariationReal r (d n)) atTop (𝓝 0) :=
    finiteOrderedVariationReal_tendsto_zero_of_pointwise r hr0 d hdPoint
  have hdist (n : ℕ) :
      dist (finiteOrderedVariationReal r (u n))
          (finiteOrderedVariationReal r v) ≤
        finiteOrderedVariationReal r (d n) := by
    have huv : finiteOrderedVariationReal r (u n) ≤
        finiteOrderedVariationReal r v + finiteOrderedVariationReal r (d n) := by
      have h := finiteOrderedVariationReal_add_le r hr v (d n)
      have heq : v + d n = u n := by
        funext i
        simp [d]
      simpa only [heq] using h
    have hsym : finiteOrderedVariationReal r (fun i => v i - u n i) =
        finiteOrderedVariationReal r (d n) := by
      have heq : (fun i => v i - u n i) = (-1 : ℂ) • d n := by
        funext i
        simp [d]
      rw [heq, finiteOrderedVariationReal_smul r hr0]
      norm_num
    have hvu : finiteOrderedVariationReal r v ≤
        finiteOrderedVariationReal r (u n) + finiteOrderedVariationReal r (d n) := by
      have h := finiteOrderedVariationReal_add_le r hr (u n)
        (fun i => v i - u n i)
      have heq : u n + (fun i => v i - u n i) = v := by
        funext i
        simp
      rw [heq, hsym] at h
      exact h
    rw [Real.dist_eq]
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) hdist hdVariation

/-- Finite-family coordinatewise almost-everywhere convergence implies
almost-everywhere convergence of the real ordered variations. -/
theorem finiteOrderedVariationRealFun_tendsto_ae
    {I X : Type*} [LinearOrder I] [Fintype I] [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (hr : 1 ≤ r)
    (F : I → X → ℂ) (G : ℕ → I → X → ℂ)
    (hconv : ∀ i, ∀ᵐ x ∂μ,
      Tendsto (fun n => G n i x) atTop (𝓝 (F i x))) :
    ∀ᵐ x ∂μ,
      Tendsto (fun n => finiteOrderedVariationRealFun r (G n) x) atTop
        (𝓝 (finiteOrderedVariationRealFun r F x)) := by
  have hcommon : ∀ᵐ x ∂μ, ∀ i,
      Tendsto (fun n => G n i x) atTop (𝓝 (F i x)) := by
    rw [ae_all_iff]
    exact hconv
  filter_upwards [hcommon] with x hx
  exact finiteOrderedVariationReal_tendsto_of_pointwise r hr
    (fun n i => G n i x) (fun i => F i x) hx

end

end FractionalPrimes.Literature.Variation

end
