module

public import FractionalPrimes.Literature.Variation.FiniteVariationWeakOperator
public import FractionalPrimes.Literature.Variation.LayerCakeInputDensity
public import FractionalPrimes.Literature.Variation.FiniteLpOperatorAE
public import FractionalPrimes.Literature.Variation.FiniteOrderedVariationContinuity
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Extending the finite strong-variation estimate to arbitrary `L^p` inputs

This module implements the finite-index density and Fatou step in blueprint
`lv:jump-to-variation`.  A bundled continuous `L^p` operator is required to
agree almost everywhere with the common raw operator on the prescribed dense
class of bounded measurable functions with finite-measure support.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- The exact consistency data between a raw operator on functions and its
continuous extension to scalar `L^p`. -/
structure LayerCakeLpExtension
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (p : ℝ≥0∞)
    (hp : 1 ≤ p)
    (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) where
  map : letI : Fact (1 ≤ p) := ⟨hp⟩
    Lp ℂ p μ →L[ℂ] Lp ℂ p μ
  agrees : letI : Fact (1 ≤ p) := ⟨hp⟩
    ∀ (g : LayerCakeInput μ) (hg : MemLp g.1 p μ),
      ((map (hg.toLp g.1) : X → ℂ) =ᵐ[μ] T g.1)

/-- The finite-index arbitrary-`L^p` form of the strong variation estimate.
This is the density/Fatou step of blueprint `lv:jump-to-variation`; its bound
is exactly the bound already proved on `LayerCakeInput`. -/
theorem finiteStrongVariationOfJump_Lp
    {I X : Type*} [LinearOrder I] [Fintype I] [MeasurableSpace X]
    (μ : Measure X) (p₀ p p₁ r A₀ B₀ A₁ B₁ : ℝ)
    (T : I → ((X → ℂ) →ₗ[ℂ] (X → ℂ)))
    (hp₀one : 1 < p₀) (hp : p₀ < p) (hp₁ : p < p₁) (hr : 2 < r)
    (Tp : ∀ i, LayerCakeLpExtension μ (ENNReal.ofReal p)
      (ENNReal.one_le_ofReal.mpr (hp₀one.trans hp).le) (T i))
    (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁)
    (hTmeas : ∀ (g : LayerCakeInput μ) (i : I), Measurable (T i g.1))
    (hfixed₀ : ∀ (g : LayerCakeInput μ) (i : I),
      complexLpMoment p₀ μ (T i g.1) ≤
        (ENNReal.ofReal B₀).rpow p₀ * complexLpMoment p₀ μ g.1)
    (hjump₀ : ∀ (g : LayerCakeInput μ) (threshold : ℝ), 0 < threshold →
      (∫⁻ x, (jumpAmplitude (fun i => T i g.1) threshold x).rpow p₀ ∂μ) ≤
        (ENNReal.ofReal A₀).rpow p₀ * complexLpMoment p₀ μ g.1)
    (hfixed₁ : ∀ (g : LayerCakeInput μ) (i : I),
      complexLpMoment p₁ μ (T i g.1) ≤
        (ENNReal.ofReal B₁).rpow p₁ * complexLpMoment p₁ μ g.1)
    (hjump₁ : ∀ (g : LayerCakeInput μ) (threshold : ℝ), 0 < threshold →
      (∫⁻ x, (jumpAmplitude (fun i => T i g.1) threshold x).rpow p₁ ∂μ) ≤
        (ENNReal.ofReal A₁).rpow p₁ * complexLpMoment p₁ μ g.1)
    (f : Lp ℂ (ENNReal.ofReal p) μ) :
    eLpNorm
        (finiteOrderedVariationRealFun r
          (fun i => ((Tp i).map f : X → ℂ)))
        (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal
          (2 * max (weakVariationConstant p₀ r A₀ B₀)
              (weakVariationConstant p₁ r A₁ B₁) *
            (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) *
        eLpNorm (f : X → ℂ) (ENNReal.ofReal p) μ := by
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hpone : 1 < p := hp₀one.trans hp
  let _ : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hpone.le⟩
  have hp0 : 0 < p := zero_lt_one.trans hpone
  obtain ⟨g, _inputNs, hgMem, _hinputNs, hgnorm, _hinputAE⟩ :=
    exists_layerCakeInput_approximation μ hp0 (f : X → ℂ)
      (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  let gLp : ℕ → Lp ℂ P μ := fun n => (hgMem n).toLp (g n).1
  have hgLp_tendsto : Tendsto gLp atTop (𝓝 f) := by
    simpa only [gLp, Lp.toLp_coeFn] using
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => (g n).1) hgMem (f : X → ℂ) (Lp.memLp f)).mpr hgnorm
  obtain ⟨ns, hns, hoperatorAE⟩ :=
    exists_strictMono_tendsto_ae_continuousLinearMap_fintype μ
      (fun i => (Tp i).map) gLp f hgLp_tendsto
  have hrawAE : ∀ i, ∀ᵐ x ∂μ,
      Tendsto (fun n => T i (g (ns n)).1 x) atTop
        (𝓝 (((Tp i).map f : X → ℂ) x)) := by
    intro i
    have hagree : ∀ᵐ x ∂μ, ∀ n,
        (((Tp i).map (gLp (ns n)) : X → ℂ) x) =
          T i (g (ns n)).1 x := by
      rw [ae_all_iff]
      intro n
      exact (Tp i).agrees (g (ns n)) (hgMem (ns n))
    filter_upwards [hoperatorAE i, hagree] with x hx hagreeX
    exact hx.congr' (Filter.Eventually.of_forall hagreeX)
  have hvariationAE : ∀ᵐ x ∂μ,
      Tendsto
        (fun n => finiteOrderedVariationRealFun r
          (fun i => T i (g (ns n)).1) x)
        atTop
        (𝓝 (finiteOrderedVariationRealFun r
          (fun i => ((Tp i).map f : X → ℂ)) x)) :=
    finiteOrderedVariationRealFun_tendsto_ae μ r (by linarith)
      (fun i => ((Tp i).map f : X → ℂ))
      (fun n i => T i (g (ns n)).1) hrawAE
  let C : ℝ≥0∞ := ENNReal.ofReal
    (2 * max (weakVariationConstant p₀ r A₀ B₀)
        (weakVariationConstant p₁ r A₁ B₁) *
      (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p))
  have hfiniteBound (n : ℕ) :
      eLpNorm
          (finiteOrderedVariationRealFun r
            (fun i => T i (g (ns n)).1)) P μ ≤
        C * eLpNorm (g (ns n)).1 P μ := by
    simpa only [P, C] using
      finiteStrongVariationOfJump μ p₀ p p₁ r A₀ B₀ A₁ B₁ T
        (zero_lt_one.trans hp₀one) hp hp₁ hr hA₀ hB₀ hA₁ hB₁
        hTmeas hfixed₀ hjump₀ hfixed₁ hjump₁ (g (ns n))
  have htargetMeas : Measurable
      (finiteOrderedVariationRealFun r
        (fun i => ((Tp i).map f : X → ℂ))) :=
    measurable_finiteOrderedVariationRealFun r
      (fun i => ((Tp i).map f : X → ℂ))
      (fun i => (Lp.stronglyMeasurable ((Tp i).map f)).measurable)
  have hfatou :
      eLpNorm
          (finiteOrderedVariationRealFun r
            (fun i => ((Tp i).map f : X → ℂ))) P μ ≤
        atTop.liminf (fun n => eLpNorm
          (finiteOrderedVariationRealFun r
            (fun i => T i (g (ns n)).1)) P μ) :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => (measurable_finiteOrderedVariationRealFun r
        (fun i => T i (g (ns n)).1)
        (fun i => hTmeas (g (ns n)) i)).aestronglyMeasurable)
      (finiteOrderedVariationRealFun r
        (fun i => ((Tp i).map f : X → ℂ)))
      htargetMeas.aestronglyMeasurable hvariationAE
  have hnorm_tendsto : Tendsto (fun n => eLpNorm (g (ns n)).1 P μ)
      atTop (𝓝 (eLpNorm (f : X → ℂ) P μ)) := by
    have hsubseq : Tendsto (fun n => gLp (ns n)) atTop (𝓝 f) :=
      hgLp_tendsto.comp hns.tendsto_atTop
    have henorm := continuous_enorm.continuousAt.tendsto.comp hsubseq
    have henorm' : Tendsto (fun n => eLpNorm (g (ns n)).1 P μ)
        atTop (𝓝 ‖f‖ₑ) := by
      simpa only [gLp, Lp.enorm_toLp, Function.comp_def] using henorm
    simpa only [Lp.enorm_def, P] using henorm'
  have hrhs_tendsto : Tendsto
      (fun n => C * eLpNorm (g (ns n)).1 P μ) atTop
      (𝓝 (C * eLpNorm (f : X → ℂ) P μ)) :=
    ENNReal.Tendsto.const_mul hnorm_tendsto
      (Or.inr (by dsimp [C]; exact ENNReal.ofReal_ne_top))
  have hliminf :
      atTop.liminf (fun n => eLpNorm
          (finiteOrderedVariationRealFun r
            (fun i => T i (g (ns n)).1)) P μ) ≤
        C * eLpNorm (f : X → ℂ) P μ := by
    calc
      atTop.liminf (fun n => eLpNorm
          (finiteOrderedVariationRealFun r
            (fun i => T i (g (ns n)).1)) P μ) ≤
          atTop.liminf (fun n => C * eLpNorm (g (ns n)).1 P μ) :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hfiniteBound)
      _ = C * eLpNorm (f : X → ℂ) P μ := hrhs_tendsto.liminf_eq
  exact hfatou.trans hliminf

end

end FractionalPrimes.Literature.Variation

end
