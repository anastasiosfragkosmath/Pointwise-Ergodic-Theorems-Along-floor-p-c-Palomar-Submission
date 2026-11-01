module

public import FractionalPrimes.Literature.Variation.FiniteChainVariation
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Fatou passage for ordered variation

These lemmas implement the coordinatewise lower-semicontinuity and Fatou
passage used in the density step of `lv:jump-to-variation`.  The index type is
the blueprint's arbitrary countable linear order, rather than the project's
special dyadic scale type.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- Positive real powers commute with sequential liminf in `ℝ≥0∞`. -/
private theorem ennreal_rpow_liminf_eq_orderedVariation
    {p : ℝ} (hp : 0 < p) (f : ℕ → ℝ≥0∞) :
    (liminf f atTop) ^ p = liminf (fun n => (f n) ^ p) atTop := by
  have h : ENNReal.orderIsoRpow p hp (liminf f atTop) =
      liminf (fun n => ENNReal.orderIsoRpow p hp (f n)) atTop := by
    exact OrderIso.liminf_apply (ENNReal.orderIsoRpow p hp)
  simpa only [ENNReal.orderIsoRpow_apply] using h

/-- A fixed finite ordered-chain contribution is continuous under
coordinatewise convergence. -/
theorem finiteChainVariation_tendsto_of_pointwise
    {I : Type*} [LinearOrder I] {r : ℝ} {length : ℕ}
    (chain : StrictOrderedChain I length)
    (u : ℕ → I → ℂ) (v : I → ℂ)
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (v i))) :
    Tendsto (fun n => finiteChainVariation r (u n) chain) atTop
      (𝓝 (finiteChainVariation r v chain)) := by
  unfold finiteChainVariation
  have hterm : ∀ i : Fin length,
      Tendsto
        (fun n =>
          (ENNReal.ofReal ‖u n (chain.point i.succ) -
            u n (chain.point i.castSucc)‖).rpow r)
        atTop
        (𝓝 ((ENNReal.ofReal ‖v (chain.point i.succ) -
          v (chain.point i.castSucc)‖).rpow r)) := by
    intro i
    have hdiff := (hu (chain.point i.succ)).sub
      (hu (chain.point i.castSucc))
    have hnorm : Tendsto
        (fun n => ENNReal.ofReal ‖u n (chain.point i.succ) -
          u n (chain.point i.castSucc)‖)
        atTop
        (𝓝 (ENNReal.ofReal ‖v (chain.point i.succ) -
          v (chain.point i.castSucc)‖)) := by
      exact (ENNReal.continuous_ofReal.comp continuous_norm).tendsto _ |>.comp hdiff
    exact (ENNReal.continuous_rpow_const (y := r)).tendsto _ |>.comp hnorm
  have hsum : Tendsto
      (fun n => ∑ i : Fin length,
        (ENNReal.ofReal ‖u n (chain.point i.succ) -
          u n (chain.point i.castSucc)‖).rpow r)
      atTop
      (𝓝 (∑ i : Fin length,
        (ENNReal.ofReal ‖v (chain.point i.succ) -
          v (chain.point i.castSucc)‖).rpow r)) := by
    apply tendsto_finsetSum
    intro i hi
    exact hterm i
  exact (ENNReal.continuous_rpow_const (y := r⁻¹)).tendsto _ |>.comp hsum

/-- Ordered variation is lower semicontinuous under coordinatewise
convergence. -/
theorem orderedRVariation_le_liminf_of_pointwise
    {I : Type*} [LinearOrder I] {r : ℝ}
    (u : ℕ → I → ℂ) (v : I → ℂ)
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (v i))) :
    orderedRVariation r v ≤ liminf (fun n => orderedRVariation r (u n)) atTop := by
  unfold orderedRVariation
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  have hchain := finiteChainVariation_tendsto_of_pointwise
    (r := r) chain u v hu
  have hle : ∀ᶠ n in atTop,
      finiteChainVariation r (u n) chain ≤ orderedRVariation r (u n) :=
    Eventually.of_forall fun n =>
      finiteChainVariation_le_orderedRVariation r (u n) chain
  have hlim := liminf_le_liminf hle
  rw [hchain.liminf_eq] at hlim
  exact hlim

/-- Coordinatewise almost-everywhere convergence on a countable ordered
index set gives the pointwise full-variation liminf inequality almost
everywhere. -/
theorem orderedRVariationFun_le_liminf_ae
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (F : I → X → ℂ)
    (G : ℕ → I → X → ℂ)
    (hconv : ∀ i, ∀ᵐ x ∂μ,
      Tendsto (fun n => G n i x) atTop (𝓝 (F i x))) :
    ∀ᵐ x ∂μ, orderedRVariationFun r F x ≤
      liminf (fun n => orderedRVariationFun r (G n) x) atTop := by
  have hcommon : ∀ᵐ x ∂μ, ∀ i : I,
      Tendsto (fun n => G n i x) atTop (𝓝 (F i x)) := by
    rw [ae_all_iff]
    exact hconv
  filter_upwards [hcommon] with x hx
  exact orderedRVariation_le_liminf_of_pointwise
    (r := r) (fun n i => G n i x) (fun i => F i x) (fun i => hx i)

/-- The lower-semicontinuity inequality persists after every positive real
power. -/
theorem orderedRVariationFun_rpow_le_liminf_ae
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (μ : Measure X) (r p : ℝ) (hp : 0 < p) (F : I → X → ℂ)
    (G : ℕ → I → X → ℂ)
    (hconv : ∀ i, ∀ᵐ x ∂μ,
      Tendsto (fun n => G n i x) atTop (𝓝 (F i x))) :
    ∀ᵐ x ∂μ, (orderedRVariationFun r F x) ^ p ≤
      liminf (fun n => (orderedRVariationFun r (G n) x) ^ p) atTop := by
  filter_upwards [orderedRVariationFun_le_liminf_ae μ r F G hconv] with x hx
  have hpow := (ENNReal.orderIsoRpow p hp).monotone hx
  simpa only [ENNReal.orderIsoRpow_apply,
    ennreal_rpow_liminf_eq_orderedVariation hp] using hpow

/-- Fatou's inequality for the `p`th power of ordered variation under
coordinatewise almost-everywhere convergence. -/
theorem lintegral_orderedRVariationFun_rpow_le_liminf
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (μ : Measure X) (r p : ℝ) (hp : 0 < p)
    (F : I → X → ℂ) (G : ℕ → I → X → ℂ)
    (hconv : ∀ i, ∀ᵐ x ∂μ,
      Tendsto (fun n => G n i x) atTop (𝓝 (F i x)))
    (hG : ∀ n i, Measurable (G n i)) :
    ∫⁻ x, (orderedRVariationFun r F x) ^ p ∂μ ≤
      liminf
        (fun n => ∫⁻ x, (orderedRVariationFun r (G n) x) ^ p ∂μ)
        atTop := by
  calc
    ∫⁻ x, (orderedRVariationFun r F x) ^ p ∂μ ≤
        ∫⁻ x, liminf
          (fun n => (orderedRVariationFun r (G n) x) ^ p) atTop ∂μ :=
      lintegral_mono_ae
        (orderedRVariationFun_rpow_le_liminf_ae μ r p hp F G hconv)
    _ ≤ liminf
        (fun n => ∫⁻ x, (orderedRVariationFun r (G n) x) ^ p ∂μ)
        atTop :=
      lintegral_liminf_le fun n =>
        (ENNReal.continuous_rpow_const (y := p)).measurable.comp
          (measurable_orderedRVariationFun r (G n) (hG n))

/-- A uniform powered-integral bound for approximating ordered variations
passes to their coordinatewise limit. -/
theorem lintegral_orderedRVariationFun_rpow_le_of_uniform
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (μ : Measure X) (r p : ℝ) (hp : 0 < p)
    (F : I → X → ℂ) (G : ℕ → I → X → ℂ)
    (hconv : ∀ i, ∀ᵐ x ∂μ,
      Tendsto (fun n => G n i x) atTop (𝓝 (F i x)))
    (hG : ∀ n i, Measurable (G n i)) (C : ℝ≥0∞)
    (hbound : ∀ n,
      ∫⁻ x, (orderedRVariationFun r (G n) x) ^ p ∂μ ≤ C) :
    ∫⁻ x, (orderedRVariationFun r F x) ^ p ∂μ ≤ C := by
  refine (lintegral_orderedRVariationFun_rpow_le_liminf
    μ r p hp F G hconv hG).trans ?_
  exact liminf_le_of_frequently_le' (Frequently.of_forall hbound)

end

end FractionalPrimes.Literature.Variation

end
