module

public import FractionalPrimes.Literature.Variation.LayerCakeInterpolation
public import FractionalPrimes.Literature.Variation.FiniteOrderedVariationReal
public import FractionalPrimes.Literature.Variation.WeakVariationConstant

/-!
# Finite variation as a layer-cake weak operator

This module packages finite-family ordered variation into the exact operator
interface used by blueprint `lv:interpolation`.  The two endpoint constants
are enlarged only to their source-prescribed maximum.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- An endpoint weak-variation estimate remains valid after enlarging its
explicit root constant. -/
theorem weakVariationOfJump_measure_le_commonConstant
    {I X : Type*} [LinearOrder I] [Fintype I] [MeasurableSpace X]
    (μ : Measure X) {p r A B W : ℝ} (F : I → X → ℂ) (f : X → ℂ)
    (hp : 0 < p) (hr : 2 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∀ i, Measurable (F i)) (hf : Measurable f)
    (hfixed : ∀ i, complexLpMoment p μ (F i) ≤
      (ENNReal.ofReal B).rpow p * complexLpMoment p μ f)
    (hjump : ∀ threshold : ℝ, 0 < threshold →
      (∫⁻ x, (jumpAmplitude F threshold x).rpow p ∂μ) ≤
        (ENNReal.ofReal A).rpow p * complexLpMoment p μ f)
    (hW : weakVariationConstant p r A B ≤ W)
    {t : ℝ} (ht : 0 < t) :
    μ {x | ENNReal.ofReal t < orderedRVariationFun r F x} ≤
      (ENNReal.ofReal (W / t)).rpow p * complexLpMoment p μ f := by
  have hweak := weakVariationOfJump μ p r A B F f hp hr hA hB hF hf
    hfixed hjump
  have hbase := hweak t ht
  have hdiv : weakVariationConstant p r A B / t ≤ W / t :=
    div_le_div_of_nonneg_right hW ht.le
  have hroot :
      (ENNReal.ofReal (weakVariationConstant p r A B / t)).rpow p ≤
        (ENNReal.ofReal (W / t)).rpow p :=
    ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hdiv) hp.le
  have hcoefficient :
      ENNReal.ofReal (weakVariationConstantPow p r A B) *
          (ENNReal.ofReal t).rpow (-p) =
        (ENNReal.ofReal (weakVariationConstant p r A B / t)).rpow p := by
    simpa only [ENNReal.rpow_eq_pow] using
      weakVariationConstant_levelCoefficient hp hr hA hB ht
  calc
    μ {x | ENNReal.ofReal t < orderedRVariationFun r F x} ≤
        ENNReal.ofReal (weakVariationConstantPow p r A B) *
          (ENNReal.ofReal t).rpow (-p) * complexLpMoment p μ f := hbase
    _ = (ENNReal.ofReal (weakVariationConstant p r A B / t)).rpow p *
          complexLpMoment p μ f := by
      rw [hcoefficient]
    _ ≤ (ENNReal.ofReal (W / t)).rpow p * complexLpMoment p μ f :=
      mul_le_mul hroot le_rfl zero_le zero_le

/-- For a finite linearly ordered family of linear operators, the real-valued
ordered variation is a `LayerCakeWeakOperator` with common endpoint constant
`max W₀ W₁`.  The assumptions are precisely the moment form of the checked
fixed-time and jump hypotheses. -/
def finiteVariationWeakOperator
    {I X : Type*} [LinearOrder I] [Fintype I] [MeasurableSpace X]
    (μ : Measure X) (p₀ p₁ r A₀ B₀ A₁ B₁ : ℝ)
    (T : I → ((X → ℂ) →ₗ[ℂ] (X → ℂ)))
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hr : 2 < r)
    (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁)
    (hTmeas : ∀ (f : LayerCakeInput μ) (i : I), Measurable (T i f.1))
    (hfixed₀ : ∀ (f : LayerCakeInput μ) (i : I),
      complexLpMoment p₀ μ (T i f.1) ≤
        (ENNReal.ofReal B₀).rpow p₀ * complexLpMoment p₀ μ f.1)
    (hjump₀ : ∀ (f : LayerCakeInput μ) (threshold : ℝ), 0 < threshold →
      (∫⁻ x, (jumpAmplitude (fun i => T i f.1) threshold x).rpow p₀ ∂μ) ≤
        (ENNReal.ofReal A₀).rpow p₀ * complexLpMoment p₀ μ f.1)
    (hfixed₁ : ∀ (f : LayerCakeInput μ) (i : I),
      complexLpMoment p₁ μ (T i f.1) ≤
        (ENNReal.ofReal B₁).rpow p₁ * complexLpMoment p₁ μ f.1)
    (hjump₁ : ∀ (f : LayerCakeInput μ) (threshold : ℝ), 0 < threshold →
      (∫⁻ x, (jumpAmplitude (fun i => T i f.1) threshold x).rpow p₁ ∂μ) ≤
        (ENNReal.ofReal A₁).rpow p₁ * complexLpMoment p₁ μ f.1) :
    LayerCakeWeakOperator μ p₀ p₁
      (max (weakVariationConstant p₀ r A₀ B₀)
        (weakVariationConstant p₁ r A₁ B₁)) where
  apply f := finiteOrderedVariationRealFun r (fun i => T i f.1)
  measurable_apply f :=
    measurable_finiteOrderedVariationRealFun r (fun i => T i f.1)
      (fun i => hTmeas f i)
  nonneg_apply f x := finiteOrderedVariationReal_nonneg r (fun i => T i f.1 x)
  subadditive f g _hfg x := by
    change finiteOrderedVariationReal r (fun i => T i (f.1 + g.1) x) ≤
      finiteOrderedVariationReal r (fun i => T i f.1 x) +
        finiteOrderedVariationReal r (fun i => T i g.1 x)
    have hlinear : (fun i => T i (f.1 + g.1) x) =
        (fun i => T i f.1 x) + (fun i => T i g.1 x) := by
      funext i
      change T i (f.1 + g.1) x = T i f.1 x + T i g.1 x
      simp only [map_add, Pi.add_apply]
    rw [hlinear]
    exact finiteOrderedVariationReal_add_le r (by linarith) _ _
  absolutely_homogeneous c f _hcf x := by
    change finiteOrderedVariationReal r (fun i => T i (c • f.1) x) =
      ‖c‖ * finiteOrderedVariationReal r (fun i => T i f.1 x)
    have hlinear : (fun i => T i (c • f.1) x) =
        c • (fun i => T i f.1 x) := by
      funext i
      change T i (c • f.1) x = c * T i f.1 x
      rw [map_smul]
      rfl
    rw [hlinear]
    exact finiteOrderedVariationReal_smul r (by linarith) c _
  weak_p₀ f t ht := by
    rw [finiteOrderedVariationRealFun_levelSet r (by linarith)
      (fun i => T i f.1) t ht.le]
    exact weakVariationOfJump_measure_le_commonConstant μ
      (fun i => T i f.1) f.1 hp₀ hr hA₀ hB₀
      (fun i => hTmeas f i) f.2.1 (hfixed₀ f) (hjump₀ f)
      (le_max_left _ _) ht
  weak_p₁ f t ht := by
    rw [finiteOrderedVariationRealFun_levelSet r (by linarith)
      (fun i => T i f.1) t ht.le]
    exact weakVariationOfJump_measure_le_commonConstant μ
      (fun i => T i f.1) f.1 hp₁ hr hA₁ hB₁
      (fun i => hTmeas f i) f.2.1 (hfixed₁ f) (hjump₁ f)
      (le_max_right _ _) ht

/-- The finite-family bounded-support case of blueprint
`lv:jump-to-variation`.  This is the direct application of the exact
layer-cake lemma to the finite ordered-variation weak operator. -/
theorem finiteStrongVariationOfJump
    {I X : Type*} [LinearOrder I] [Fintype I] [MeasurableSpace X]
    (μ : Measure X) (p₀ p p₁ r A₀ B₀ A₁ B₁ : ℝ)
    (T : I → ((X → ℂ) →ₗ[ℂ] (X → ℂ)))
    (hp₀ : 0 < p₀) (hp : p₀ < p) (hp₁ : p < p₁) (hr : 2 < r)
    (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁)
    (hTmeas : ∀ (f : LayerCakeInput μ) (i : I), Measurable (T i f.1))
    (hfixed₀ : ∀ (f : LayerCakeInput μ) (i : I),
      complexLpMoment p₀ μ (T i f.1) ≤
        (ENNReal.ofReal B₀).rpow p₀ * complexLpMoment p₀ μ f.1)
    (hjump₀ : ∀ (f : LayerCakeInput μ) (threshold : ℝ), 0 < threshold →
      (∫⁻ x, (jumpAmplitude (fun i => T i f.1) threshold x).rpow p₀ ∂μ) ≤
        (ENNReal.ofReal A₀).rpow p₀ * complexLpMoment p₀ μ f.1)
    (hfixed₁ : ∀ (f : LayerCakeInput μ) (i : I),
      complexLpMoment p₁ μ (T i f.1) ≤
        (ENNReal.ofReal B₁).rpow p₁ * complexLpMoment p₁ μ f.1)
    (hjump₁ : ∀ (f : LayerCakeInput μ) (threshold : ℝ), 0 < threshold →
      (∫⁻ x, (jumpAmplitude (fun i => T i f.1) threshold x).rpow p₁ ∂μ) ≤
        (ENNReal.ofReal A₁).rpow p₁ * complexLpMoment p₁ μ f.1)
    (f : LayerCakeInput μ) :
    eLpNorm (finiteOrderedVariationRealFun r (fun i => T i f.1))
        (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal
          (2 * max (weakVariationConstant p₀ r A₀ B₀)
              (weakVariationConstant p₁ r A₁ B₁) *
            (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) *
        eLpNorm f.1 (ENNReal.ofReal p) μ := by
  have hW : 0 ≤ max (weakVariationConstant p₀ r A₀ B₀)
      (weakVariationConstant p₁ r A₁ B₁) :=
    (weakVariationConstant_nonneg hp₀ hr hA₀ hB₀).trans
      (le_max_left _ _)
  have hp₁pos : 0 < p₁ := (hp₀.trans hp).trans hp₁
  exact layerCake_interpolation
    (finiteVariationWeakOperator μ p₀ p₁ r A₀ B₀ A₁ B₁ T hp₀ hp₁pos hr
      hA₀ hB₀ hA₁ hB₁ hTmeas hfixed₀ hjump₀ hfixed₁ hjump₁)
    hp₀ hp hp₁ hW f

end

end FractionalPrimes.Literature.Variation

end
