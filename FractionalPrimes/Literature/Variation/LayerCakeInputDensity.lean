module

public import FractionalPrimes.Literature.Variation.LayerCakeInterpolation
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Bounded finite-support density for the layer-cake domain

This is the exact density input used in blueprint `lv:jump-to-variation`.
Finite-valued `L^p` simple functions are measurable and bounded, and their
nonzero support has finite measure when `0 < p < ∞`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

/-- Every measurable `L^p` function with finite positive exponent admits
bounded measurable finite-measure-support approximants converging in
`eLpNorm`; a subsequence also converges almost everywhere. -/
theorem exists_layerCakeInput_approximation
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ} (hp : 0 < p) (f : X → ℂ) (hf : Measurable f)
    (hfp : MemLp f (ENNReal.ofReal p) μ) :
    ∃ (g : ℕ → LayerCakeInput μ) (ns : ℕ → ℕ),
      (∀ n, MemLp (g n).1 (ENNReal.ofReal p) μ) ∧
      StrictMono ns ∧
      Tendsto
        (fun n => eLpNorm ((g n).1 - f) (ENNReal.ofReal p) μ)
        atTop (𝓝 0) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => (g (ns n)).1 x) atTop (𝓝 (f x))) := by
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact (ENNReal.ofReal_pos.mpr hp).ne'
  have hPTop : P ≠ ∞ := by
    dsimp [P]
    exact ENNReal.ofReal_ne_top
  let s : ℕ → SimpleFunc X ℂ := fun n =>
    SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp) n
  have hsMem (n : ℕ) : MemLp (s n) P μ := by
    dsimp [s]
    exact SimpleFunc.memLp_approxOn_range hf hfp n
  have hsAdmissible (n : ℕ) : LayerCakeAdmissible μ (s n) := by
    refine ⟨(s n).measurable, (s n).exists_forall_norm_le, ?_⟩
    simpa only [Function.support] using
      (s n).measure_support_lt_top_of_memLp (hsMem n) hP0 hPTop
  let g : ℕ → LayerCakeInput μ := fun n => ⟨s n, hsAdmissible n⟩
  have hgMem (n : ℕ) : MemLp (g n).1 P μ := by
    exact hsMem n
  have hnorm : Tendsto (fun n => eLpNorm ((g n).1 - f) P μ)
      atTop (𝓝 0) := by
    have happrox := SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
      (p := P) hPTop hf hfp.eLpNorm_lt_top
    simpa only [g, s] using happrox
  have hmeasure : TendstoInMeasure μ (fun n => (g n).1) atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm hP0 hnorm
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  exact ⟨g, ns, hgMem, hns, hnorm, hae⟩

end

end FractionalPrimes.Literature.Variation

end
