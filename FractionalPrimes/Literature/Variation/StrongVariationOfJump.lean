module

public import FractionalPrimes.Literature.Variation.FiniteStrongVariationLp
public import FractionalPrimes.Literature.Variation.OrderedVariationLpExhaustion

/-!
# Strong variation from a full range of jump bounds

This module completes blueprint theorem `lv:jump-to-variation`.  It first
passes the exact finite-index estimate through a finite exhaustion of an
arbitrary countable linear order, then packages the source's hypotheses for
every scalar exponent `1 < v < ∞`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

universe uI uX

/-- Countable-index closure at three fixed exponents.  Uniformity over finite
subsets is expressed by quantifying over finite linear orders embedded into
the ambient ordered index type. -/
theorem strongVariationOfJump_atExponents
    {I : Type uI} {X : Type uX}
    [LinearOrder I] [Countable I] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ]
    (p₀ p p₁ r A₀ B₀ A₁ B₁ : ℝ)
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
    (hjump₀ : ∀ {J : Type uI} [LinearOrder J] [Fintype J]
      (e : J ↪o I) (g : LayerCakeInput μ) (threshold : ℝ),
      0 < threshold →
        (∫⁻ x, (jumpAmplitude (fun j => T (e j) g.1) threshold x).rpow p₀ ∂μ) ≤
          (ENNReal.ofReal A₀).rpow p₀ * complexLpMoment p₀ μ g.1)
    (hfixed₁ : ∀ (g : LayerCakeInput μ) (i : I),
      complexLpMoment p₁ μ (T i g.1) ≤
        (ENNReal.ofReal B₁).rpow p₁ * complexLpMoment p₁ μ g.1)
    (hjump₁ : ∀ {J : Type uI} [LinearOrder J] [Fintype J]
      (e : J ↪o I) (g : LayerCakeInput μ) (threshold : ℝ),
      0 < threshold →
        (∫⁻ x, (jumpAmplitude (fun j => T (e j) g.1) threshold x).rpow p₁ ∂μ) ≤
          (ENNReal.ofReal A₁).rpow p₁ * complexLpMoment p₁ μ g.1)
    (f : Lp ℂ (ENNReal.ofReal p) μ) :
    eLpNorm
        (orderedRVariationFun r
          (fun i => ((Tp i).map f : X → ℂ)))
        (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal
          (2 * max (weakVariationConstant p₀ r A₀ B₀)
              (weakVariationConstant p₁ r A₁ B₁) *
            (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) *
        eLpNorm (f : X → ℂ) (ENNReal.ofReal p) μ := by
  have hpone : 1 < p := hp₀one.trans hp
  have hp0 : 0 < p := zero_lt_one.trans hpone
  let _ : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hpone.le⟩
  let K : Set.FiniteExhaustion (Set.univ : Set I) :=
    Set.countable_univ.finiteExhaustion
  let F : I → X → ℂ := fun i => ((Tp i).map f : X → ℂ)
  have hF (i : I) : Measurable (F i) :=
    (Lp.stronglyMeasurable ((Tp i).map f)).measurable
  rw [eLpNorm_orderedRVariationFun_eq_iSup_trunc K μ r p hp0 F hF]
  apply iSup_le
  intro N
  let _ : Fintype (K N) := Fintype.ofFinite (K N)
  let eN : K N ↪o I := OrderEmbedding.subtype (fun i => i ∈ K N)
  let TN : K N → ((X → ℂ) →ₗ[ℂ] (X → ℂ)) := fun i => T i.1
  let TpN : ∀ i, LayerCakeLpExtension μ (ENNReal.ofReal p)
      (ENNReal.one_le_ofReal.mpr (hp₀one.trans hp).le) (TN i) :=
    fun i => Tp i.1
  have hfinite :
      eLpNorm
          (finiteOrderedVariationRealFun r
            (fun i : K N => ((Tp i.1).map f : X → ℂ)))
          (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal
            (2 * max (weakVariationConstant p₀ r A₀ B₀)
                (weakVariationConstant p₁ r A₁ B₁) *
              (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) *
          eLpNorm (f : X → ℂ) (ENNReal.ofReal p) μ := by
    exact finiteStrongVariationOfJump_Lp (I := K N) (X := X) μ
      p₀ p p₁ r A₀ B₀ A₁ B₁ TN hp₀one hp hp₁ hr TpN
      hA₀ hB₀ hA₁ hB₁
      (fun g i => hTmeas g i.1)
      (fun g i => hfixed₀ g i.1)
      (fun g threshold hthreshold =>
        hjump₀ (J := ↥(K N)) eN g threshold hthreshold)
      (fun g i => hfixed₁ g i.1)
      (fun g threshold hthreshold =>
        hjump₁ (J := ↥(K N)) eN g threshold hthreshold) f
  rw [eLpNorm_orderedRVariationTruncFun_eq_subtypeReal
    K μ r (by linarith) F hF N (ENNReal.ofReal p)]
  change eLpNorm
      (finiteOrderedVariationRealFun r
        (fun i : K N => ((Tp i.1).map f : X → ℂ)))
      (ENNReal.ofReal p) μ ≤ _
  exact hfinite

/-- The source-faithful full-range data in blueprint
`lv:jump-to-variation`.  The same raw linear operators underlie every scalar
`L^v` extension, and the endpoint estimates are uniform over finite ordered
subsets of the ambient index set. -/
structure FullRangeJumpOperatorFamily
    {I : Type uI} {X : Type uX} [LinearOrder I] [MeasurableSpace X]
    (μ : Measure X) (T : I → ((X → ℂ) →ₗ[ℂ] (X → ℂ))) where
  A : ℝ → ℝ
  B : ℝ → ℝ
  A_nonneg : ∀ v, 1 < v → 0 ≤ A v
  B_nonneg : ∀ v, 1 < v → 0 ≤ B v
  measurable_raw : ∀ (g : LayerCakeInput μ) (i : I), Measurable (T i g.1)
  extension : ∀ (v : ℝ) (hv : 1 < v) (i : I),
    LayerCakeLpExtension μ (ENNReal.ofReal v)
      (ENNReal.one_le_ofReal.mpr hv.le) (T i)
  fixed : ∀ (v : ℝ) (_hv : 1 < v) (g : LayerCakeInput μ) (i : I),
    complexLpMoment v μ (T i g.1) ≤
      (ENNReal.ofReal (B v)).rpow v * complexLpMoment v μ g.1
  jump : ∀ (v : ℝ) (_hv : 1 < v)
    {J : Type uI} [LinearOrder J] [Fintype J]
    (e : J ↪o I) (g : LayerCakeInput μ) (threshold : ℝ),
    0 < threshold →
      (∫⁻ x, (jumpAmplitude (fun j => T (e j) g.1) threshold x).rpow v ∂μ) ≤
        (ENNReal.ofReal (A v)).rpow v * complexLpMoment v μ g.1

/-- Strong ordered variation from the blueprint's full range of fixed-time
and jump bounds, with the literal displayed interpolation constant. -/
theorem strongVariationOfJump
    {I : Type uI} {X : Type uX}
    [LinearOrder I] [Countable I] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ]
    (T : I → ((X → ℂ) →ₗ[ℂ] (X → ℂ)))
    (U : FullRangeJumpOperatorFamily μ T)
    (p₀ p p₁ r : ℝ)
    (hp₀one : 1 < p₀) (hp : p₀ < p) (hp₁ : p < p₁) (hr : 2 < r)
    (f : Lp ℂ (ENNReal.ofReal p) μ) :
    eLpNorm
        (orderedRVariationFun r
          (fun i => ((U.extension p (hp₀one.trans hp) i).map f : X → ℂ)))
        (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal
          (2 * max
              (weakVariationConstant p₀ r (U.A p₀) (U.B p₀))
              (weakVariationConstant p₁ r (U.A p₁) (U.B p₁)) *
            (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) *
        eLpNorm (f : X → ℂ) (ENNReal.ofReal p) μ := by
  apply strongVariationOfJump_atExponents μ
    p₀ p p₁ r (U.A p₀) (U.B p₀) (U.A p₁) (U.B p₁) T
    hp₀one hp hp₁ hr (U.extension p (hp₀one.trans hp))
    (U.A_nonneg p₀ hp₀one) (U.B_nonneg p₀ hp₀one)
    (U.A_nonneg p₁ ((hp₀one.trans hp).trans hp₁))
    (U.B_nonneg p₁ ((hp₀one.trans hp).trans hp₁))
    U.measurable_raw
    (U.fixed p₀ hp₀one)
    (U.jump p₀ hp₀one)
    (U.fixed p₁ ((hp₀one.trans hp).trans hp₁))
    (U.jump p₁ ((hp₀one.trans hp).trans hp₁)) f

end

end FractionalPrimes.Literature.Variation

end
