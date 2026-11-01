module

public import FractionalPrimes.Literature.JSW.WeakTypeInterpolation

/-!
# Dense extension for continuous nonlinear `L^p` maps

The interpolation proof supplies estimates on bounded measurable inputs with
finite-measure support. This lemma extends such an estimate to all of `L^p`
for any continuous map between the input and output `L^p` spaces. In
particular, it does not require the map to be linear; finite maximal families
are intended applications once their continuity has been established.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- A bound for a continuous, possibly nonlinear map of `L^p` spaces that
holds on the bounded finite-measure-support class holds on all `L^p` inputs.
The constant is unchanged. -/
theorem weakTypeInterpolation_extend_dense_continuous
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {p : ℝ} (hp : 1 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (S : Lp ℂ (ENNReal.ofReal p) μ → Lp ℝ (ENNReal.ofReal p) ν)
    (hS : Continuous S) (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ (g : Variation.LayerCakeInput μ)
      (hg : MemLp g.1 (ENNReal.ofReal p) μ),
      eLpNorm (S (hg.toLp g.1) : Y → ℝ)
          (ENNReal.ofReal p) ν ≤
        ENNReal.ofReal C * eLpNorm g.1 (ENNReal.ofReal p) μ)
    (f : Lp ℂ (ENNReal.ofReal p) μ) :
    eLpNorm (S f : Y → ℝ) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal C * eLpNorm (f : X → ℂ) (ENNReal.ofReal p) μ := by
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hp0 : 0 < p := by linarith
  obtain ⟨g, _inputNs, hgMem, _hinputNs, hgnorm, _hinputAE⟩ :=
    Variation.exists_layerCakeInput_approximation μ hp0 (f : X → ℂ)
      (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  let gLp : ℕ → Lp ℂ P μ := fun n => (hgMem n).toLp (g n).1
  have hgLpTendsto : Tendsto gLp atTop (𝓝 f) := by
    simpa only [P, gLp, Lp.toLp_coeFn] using
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => (g n).1) hgMem (f : X → ℂ) (Lp.memLp f)).mpr hgnorm
  let outputs : ℕ → Lp ℝ P ν := fun n => S (gLp n)
  have houtputsTendsto : Tendsto outputs atTop (𝓝 (S f)) :=
    (hS.tendsto f).comp hgLpTendsto
  have hOutputNormTendsto :
      Tendsto (fun n => eLpNorm (outputs n : Y → ℝ) P ν)
        atTop (𝓝 (eLpNorm (S f : Y → ℝ) P ν)) := by
    have henorm := continuous_enorm.continuousAt.tendsto.comp houtputsTendsto
    simpa only [Function.comp_def, outputs, Lp.enorm_def, P] using henorm
  have hInputNormTendsto :
      Tendsto (fun n => eLpNorm (g n).1 P μ) atTop
        (𝓝 (eLpNorm (f : X → ℂ) P μ)) := by
    have henorm := continuous_enorm.continuousAt.tendsto.comp hgLpTendsto
    have henorm' : Tendsto (fun n => eLpNorm (g n).1 P μ) atTop
        (𝓝 ‖f‖ₑ) := by
      simpa only [gLp, Lp.enorm_toLp, Function.comp_def] using henorm
    simpa only [Lp.enorm_def, P] using henorm'
  have hfiniteBound (n : ℕ) :
      eLpNorm (outputs n : Y → ℝ) P ν ≤
        ENNReal.ofReal C * eLpNorm (g n).1 P μ := by
    simpa only [P, outputs, gLp] using hbound (g n) (hgMem n)
  have hrhsTendsto : Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (g n).1 P μ) atTop
      (𝓝 (ENNReal.ofReal C * eLpNorm (f : X → ℂ) P μ)) :=
    ENNReal.Tendsto.const_mul hInputNormTendsto
      (Or.inr ENNReal.ofReal_ne_top)
  have hliminf :
      atTop.liminf
          (fun n => eLpNorm (outputs n : Y → ℝ) P ν) ≤
        ENNReal.ofReal C * eLpNorm (f : X → ℂ) P μ := by
    calc
      atTop.liminf
          (fun n => eLpNorm (outputs n : Y → ℝ) P ν) ≤
          atTop.liminf
            (fun n => ENNReal.ofReal C * eLpNorm (g n).1 P μ) :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hfiniteBound)
      _ = ENNReal.ofReal C * eLpNorm (f : X → ℂ) P μ :=
        hrhsTendsto.liminf_eq
  rw [hOutputNormTendsto.liminf_eq] at hliminf
  simpa only [P] using hliminf

#print axioms weakTypeInterpolation_extend_dense_continuous

end

end FractionalPrimes.Literature.JSW

end
