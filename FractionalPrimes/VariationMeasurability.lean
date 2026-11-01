module

public import FractionalPrimes.Variation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Measurability of countable-chain variation

The project variation is a supremum over finite chains of positive scales.
This module makes the countability of those chains explicit and proves the
measurability needed before a variation inequality can be interpreted in an
`L^p` space.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- Positive real powers commute with the liminf in `ℝ≥0∞`, via the order
isomorphism supplied by Mathlib. -/
theorem ennreal_rpow_liminf_eq {p : ℝ} (hp : 0 < p) (f : ℕ → ℝ≥0∞) :
    (Filter.liminf f Filter.atTop) ^ p =
      Filter.liminf (fun n => (f n) ^ p) Filter.atTop := by
  have h : ENNReal.orderIsoRpow p hp (Filter.liminf f Filter.atTop) =
      Filter.liminf (fun n => ENNReal.orderIsoRpow p hp (f n)) Filter.atTop := by
    exact OrderIso.liminf_apply (ENNReal.orderIsoRpow p hp)
  simpa only [ENNReal.orderIsoRpow_apply] using h

/-- A strict finite scale chain is determined by its index function. -/
def strictScaleChainEmbedding (length : ℕ) :
    StrictScaleChain length ↪ (Fin (length + 1) → Scale) where
  toFun := StrictScaleChain.index
  inj' := by
    intro a b hab
    cases a
    cases b
    cases hab
    rfl

/-- The chain contribution to pointwise variation is measurable when every scale is measurable. -/
theorem measurable_chainVariationFun {X : Type*} [MeasurableSpace X] (r : ℝ)
    (F : Scale → X → ℂ) (hF : ∀ N, Measurable (F N)) {length : ℕ}
    (chain : StrictScaleChain length) :
    Measurable (fun x =>
      (∑ i : Fin length,
        (ENNReal.ofReal ‖F (chain.index i.succ) x -
          F (chain.index i.castSucc) x‖).rpow r).rpow r⁻¹) := by
  have hsum : Measurable (fun x =>
      ∑ i : Fin length,
        (ENNReal.ofReal ‖F (chain.index i.succ) x -
          F (chain.index i.castSucc) x‖).rpow r) := by
    apply Finset.measurable_fun_sum
    intro i _
    convert (ENNReal.continuous_rpow_const (y := r)).measurable.comp
      (Measurable.ennreal_ofReal
        (((hF (chain.index i.succ)).sub (hF (chain.index i.castSucc))).norm)) using 1
    ext x
    simp only [Function.comp_apply, ENNReal.rpow_eq_pow, Pi.sub_apply]
  convert (ENNReal.continuous_rpow_const (y := r⁻¹)).measurable.comp hsum using 1
  ext x
  simp only [Function.comp_apply, ENNReal.rpow_eq_pow]

/-- The chain contribution to pointwise variation is a.e. measurable when every scale is. -/
theorem aemeasurable_chainVariationFun {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (F : Scale → X → ℂ) (hF : ∀ N, AEMeasurable (F N) μ)
    {length : ℕ} (chain : StrictScaleChain length) :
    AEMeasurable (fun x =>
      (∑ i : Fin length,
        (ENNReal.ofReal ‖F (chain.index i.succ) x -
          F (chain.index i.castSucc) x‖).rpow r).rpow r⁻¹) μ := by
  have hsum : AEMeasurable (fun x =>
      ∑ i : Fin length,
        (ENNReal.ofReal ‖F (chain.index i.succ) x -
          F (chain.index i.castSucc) x‖).rpow r) μ := by
    apply Finset.aemeasurable_fun_sum
    intro i _
    convert (ENNReal.continuous_rpow_const (y := r)).measurable.aemeasurable.comp_aemeasurable
      (AEMeasurable.ennreal_ofReal
        (((hF (chain.index i.succ)).sub (hF (chain.index i.castSucc))).norm)) using 1
    ext x
    simp only [Function.comp_apply, ENNReal.rpow_eq_pow, Pi.sub_apply]
  convert (ENNReal.continuous_rpow_const (y := r⁻¹)).measurable.aemeasurable.comp_aemeasurable hsum using 1
  ext x
  simp only [Function.comp_apply, ENNReal.rpow_eq_pow]

/-- Pointwise variation restricted to chains whose scale values are at most
the natural cutoff `N`. -/
def rVariationTruncFun {X : Type*} (r : ℝ) (F : Scale → X → ℂ) (N : ℕ) :
    X → ℝ≥0∞ :=
  fun x => rVariationTrunc r (fun n => F n x) N

/-- A finite-stage variation is measurable whenever each input scale is. -/
theorem measurable_rVariationTruncFun {X : Type*} [MeasurableSpace X]
    (r : ℝ) (F : Scale → X → ℂ) (hF : ∀ N, Measurable (F N)) (K : ℕ) :
    Measurable (rVariationTruncFun r F K) := by
  unfold rVariationTruncFun rVariationTrunc
  apply Measurable.iSup
  intro length
  let _ : Countable (StrictScaleChain length) :=
    (strictScaleChainEmbedding length).countable
  apply Measurable.iSup
  intro chain
  by_cases hbound : ∀ i, (chain.index i).1 ≤ K
  · simpa [hbound, chainVariation] using measurable_chainVariationFun r F hF chain
  · simp [hbound]

/-- A finite-stage variation is a.e. measurable whenever each input scale
is a.e. measurable. -/
theorem aemeasurable_rVariationTruncFun {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (F : Scale → X → ℂ)
    (hF : ∀ N, AEMeasurable (F N) μ) (K : ℕ) :
    AEMeasurable (rVariationTruncFun r F K) μ := by
  unfold rVariationTruncFun rVariationTrunc
  apply AEMeasurable.iSup
  intro length
  let _ : Countable (StrictScaleChain length) :=
    (strictScaleChainEmbedding length).countable
  apply AEMeasurable.iSup
  intro chain
  by_cases hbound : ∀ i, (chain.index i).1 ≤ K
  · simpa [hbound, chainVariation] using aemeasurable_chainVariationFun μ r F hF chain
  · simp [hbound]

/-- The full pointwise variation is the supremum of its scale-cutoff
truncations. -/
theorem rVariationFun_eq_iSup_trunc {X : Type*} (r : ℝ)
    (F : Scale → X → ℂ) :
    rVariationFun r F = fun x => ⨆ N : ℕ, rVariationTruncFun r F N x := by
  funext x
  simp only [rVariationFun_apply, rVariationTruncFun]
  exact rVariation_eq_iSup_trunc r (fun n => F n x)

/-- The truncation functions increase pointwise with the scale cutoff. -/
theorem monotone_rVariationTruncFun {X : Type*} (r : ℝ)
    (F : Scale → X → ℂ) : Monotone (rVariationTruncFun r F) := by
  intro N M hNM x
  exact rVariationTrunc_mono r (fun n => F n x) hNM

/-- Monotone convergence for the nonnegative pointwise variation: its
integral is the supremum of the integrals of the scale-cutoff truncations. -/
theorem lintegral_rVariationFun_eq_iSup_trunc {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (F : Scale → X → ℂ)
    (hF : ∀ N, Measurable (F N)) :
    ∫⁻ x, rVariationFun r F x ∂μ =
      ⨆ N : ℕ, ∫⁻ x, rVariationTruncFun r F N x ∂μ := by
  rw [rVariationFun_eq_iSup_trunc r F]
  exact lintegral_iSup
    (fun N => measurable_rVariationTruncFun r F hF N)
    (monotone_rVariationTruncFun r F)

/-- Monotone convergence for the `p`th powers of the finite-scale
truncations. -/
theorem lintegral_rVariationFun_rpow_eq_iSup_trunc
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (r p : ℝ) (hp : 0 < p)
    (F : Scale → X → ℂ) (hF : ∀ N, Measurable (F N)) :
    ∫⁻ x, (rVariationFun r F x) ^ p ∂μ =
      ⨆ N : ℕ, ∫⁻ x, (rVariationTruncFun r F N x) ^ p ∂μ := by
  have hrepr : (fun x => (rVariationFun r F x) ^ p) =
      fun x => ⨆ N : ℕ, (rVariationTruncFun r F N x) ^ p := by
    funext x
    rw [rVariationFun_eq_iSup_trunc r F]
    change ENNReal.orderIsoRpow p hp (⨆ N : ℕ, rVariationTruncFun r F N x) = _
    rw [OrderIso.map_iSup]
    rfl
  rw [hrepr]
  apply lintegral_iSup
  · intro N
    exact (ENNReal.continuous_rpow_const (y := p)).measurable.comp
      (measurable_rVariationTruncFun r F hF N)
  · intro N M hNM x
    exact (ENNReal.orderIsoRpow p hp).monotone
      (monotone_rVariationTruncFun r F hNM x)

/-- Coordinatewise a.e. convergence on the countable scale set gives the
full-variation liminf inequality almost everywhere. -/
theorem rVariationFun_le_liminf_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (F : Scale → X → ℂ)
    (G : ℕ → Scale → X → ℂ)
    (hconv : ∀ N, ∀ᵐ x ∂μ,
      Filter.Tendsto (fun m => G m N x) Filter.atTop (nhds (F N x))) :
    ∀ᵐ x ∂μ, rVariationFun r F x ≤
      Filter.liminf (fun m => rVariationFun r (G m) x) Filter.atTop := by
  have hcommon : ∀ᵐ x ∂μ, ∀ N : Scale,
      Filter.Tendsto (fun m => G m N x) Filter.atTop (nhds (F N x)) := by
    rw [ae_all_iff]
    exact hconv
  filter_upwards [hcommon] with x hx
  exact rVariation_le_liminf_of_pointwise (r := r)
    (fun m N => G m N x) (fun N => F N x) (fun N => hx N)

/-- The lower-semicontinuity inequality also holds after taking any positive
real power of the nonnegative variation. -/
theorem rVariationFun_rpow_le_liminf_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r p : ℝ) (hp : 0 < p) (F : Scale → X → ℂ)
    (G : ℕ → Scale → X → ℂ)
    (hconv : ∀ N, ∀ᵐ x ∂μ,
      Filter.Tendsto (fun m => G m N x) Filter.atTop (nhds (F N x))) :
    ∀ᵐ x ∂μ, (rVariationFun r F x) ^ p ≤
      Filter.liminf (fun m => (rVariationFun r (G m) x) ^ p) Filter.atTop := by
  filter_upwards [rVariationFun_le_liminf_ae μ r F G hconv] with x hx
  have hpow := (ENNReal.orderIsoRpow p hp).monotone hx
  simpa only [ENNReal.orderIsoRpow_apply, ennreal_rpow_liminf_eq hp] using hpow

/-- Pointwise variation is measurable when every scale member is measurable. -/
theorem measurable_rVariationFun {X : Type*} [MeasurableSpace X] (r : ℝ)
    (F : Scale → X → ℂ) (hF : ∀ N, Measurable (F N)) :
    Measurable (rVariationFun r F) := by
  have hrepr : rVariationFun r F =
      fun x => ⨆ (length : ℕ) (chain : StrictScaleChain length),
        (∑ i : Fin length,
          (ENNReal.ofReal ‖F (chain.index i.succ) x -
            F (chain.index i.castSucc) x‖).rpow r).rpow r⁻¹ := by
    funext x
    rw [rVariationFun_apply, rVariation_eq]
  rw [hrepr]
  apply Measurable.iSup
  intro length
  let _ : Countable (StrictScaleChain length) :=
    (strictScaleChainEmbedding length).countable
  apply Measurable.iSup
  intro chain
  exact measurable_chainVariationFun r F hF chain

/-- Pointwise variation is a.e. measurable when every scale member is a.e. measurable. -/
theorem aemeasurable_rVariationFun {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (F : Scale → X → ℂ) (hF : ∀ N, AEMeasurable (F N) μ) :
    AEMeasurable (rVariationFun r F) μ := by
  have hrepr : rVariationFun r F =
      fun x => ⨆ (length : ℕ) (chain : StrictScaleChain length),
        (∑ i : Fin length,
          (ENNReal.ofReal ‖F (chain.index i.succ) x -
            F (chain.index i.castSucc) x‖).rpow r).rpow r⁻¹ := by
    funext x
    rw [rVariationFun_apply, rVariation_eq]
  rw [hrepr]
  apply AEMeasurable.iSup
  intro length
  let _ : Countable (StrictScaleChain length) :=
    (strictScaleChainEmbedding length).countable
  apply AEMeasurable.iSup
  intro chain
  exact aemeasurable_chainVariationFun μ r F hF chain

/-- Fatou's inequality for the `p`th power of the variation under
coordinatewise a.e. convergence. -/
theorem lintegral_rVariationFun_rpow_le_liminf
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (r p : ℝ) (hp : 0 < p)
    (F : Scale → X → ℂ) (G : ℕ → Scale → X → ℂ)
    (hconv : ∀ N, ∀ᵐ x ∂μ,
      Filter.Tendsto (fun m => G m N x) Filter.atTop (nhds (F N x)))
    (hG : ∀ m, ∀ N, Measurable (G m N)) :
    ∫⁻ x, (rVariationFun r F x) ^ p ∂μ ≤
      Filter.liminf (fun m => ∫⁻ x, (rVariationFun r (G m) x) ^ p ∂μ)
        Filter.atTop := by
  calc
    ∫⁻ x, (rVariationFun r F x) ^ p ∂μ ≤
        ∫⁻ x, Filter.liminf
          (fun m => (rVariationFun r (G m) x) ^ p) Filter.atTop ∂μ :=
      lintegral_mono_ae (rVariationFun_rpow_le_liminf_ae μ r p hp F G hconv)
    _ ≤ Filter.liminf
        (fun m => ∫⁻ x, (rVariationFun r (G m) x) ^ p ∂μ) Filter.atTop :=
      lintegral_liminf_le (fun m =>
        (ENNReal.continuous_rpow_const (y := p)).measurable.comp
          (measurable_rVariationFun r (G m) (hG m)))

/-- A uniform bound for the `p`th-power integrals of approximating variations
passes to the limit variation. -/
theorem lintegral_rVariationFun_rpow_le_of_uniform
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (r p : ℝ) (hp : 0 < p)
    (F : Scale → X → ℂ) (G : ℕ → Scale → X → ℂ)
    (hconv : ∀ N, ∀ᵐ x ∂μ,
      Filter.Tendsto (fun m => G m N x) Filter.atTop (nhds (F N x)))
    (hG : ∀ m, ∀ N, Measurable (G m N)) (C : ℝ≥0∞)
    (hbound : ∀ m, ∫⁻ x, (rVariationFun r (G m) x) ^ p ∂μ ≤ C) :
    ∫⁻ x, (rVariationFun r F x) ^ p ∂μ ≤ C := by
  refine (lintegral_rVariationFun_rpow_le_liminf μ r p hp F G hconv hG).trans ?_
  exact Filter.liminf_le_of_frequently_le'
    (Filter.Frequently.of_forall hbound)

/-- Fatou's inequality for the pointwise variation under coordinatewise a.e.
convergence of the underlying scale families. -/
theorem lintegral_rVariationFun_le_liminf {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (F : Scale → X → ℂ)
    (G : ℕ → Scale → X → ℂ)
    (hconv : ∀ N, ∀ᵐ x ∂μ,
      Filter.Tendsto (fun m => G m N x) Filter.atTop (nhds (F N x)))
    (hG : ∀ m, ∀ N, Measurable (G m N)) :
    ∫⁻ x, rVariationFun r F x ∂μ ≤
      Filter.liminf (fun m => ∫⁻ x, rVariationFun r (G m) x ∂μ) Filter.atTop := by
  calc
    ∫⁻ x, rVariationFun r F x ∂μ ≤
        ∫⁻ x, Filter.liminf (fun m => rVariationFun r (G m) x) Filter.atTop ∂μ :=
      lintegral_mono_ae (rVariationFun_le_liminf_ae μ r F G hconv)
    _ ≤ Filter.liminf (fun m => ∫⁻ x, rVariationFun r (G m) x ∂μ) Filter.atTop :=
      lintegral_liminf_le (fun m => measurable_rVariationFun r (G m) (hG m))

/-- The project-scale specialization of the blueprint's countable-variation
limit bridge. The cutoffs `N` enumerate increasing finite subsets of `Scale`;
the four conclusions are pointwise lower semicontinuity, powered Fatou,
uniform powered-integral bound transfer, and monotone convergence of the
restricted variations. -/
theorem countableVariationFatou {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r p : ℝ) (hr : 1 ≤ r) (hp : 1 ≤ p)
    (F : Scale → X → ℂ) (G : ℕ → Scale → X → ℂ)
    (hF : ∀ N, Measurable (F N))
    (hG : ∀ m N, Measurable (G m N))
    (hconv : ∀ N, ∀ᵐ x ∂μ,
      Filter.Tendsto (fun m => G m N x) Filter.atTop (nhds (F N x))) :
    (∀ᵐ x ∂μ, rVariationFun r F x ≤
      Filter.liminf (fun m => rVariationFun r (G m) x) Filter.atTop) ∧
    (∫⁻ x, (rVariationFun r F x) ^ p ∂μ ≤
      Filter.liminf (fun m => ∫⁻ x, (rVariationFun r (G m) x) ^ p ∂μ)
        Filter.atTop) ∧
    (∀ C : ℝ≥0∞,
      (∀ m, ∫⁻ x, (rVariationFun r (G m) x) ^ p ∂μ ≤ C) →
        ∫⁻ x, (rVariationFun r F x) ^ p ∂μ ≤ C) ∧
    (∫⁻ x, (rVariationFun r F x) ^ p ∂μ =
      ⨆ N : ℕ, ∫⁻ x, (rVariationTruncFun r F N x) ^ p ∂μ) := by
  refine ⟨rVariationFun_le_liminf_ae μ r F G hconv,
    lintegral_rVariationFun_rpow_le_liminf μ r p (by linarith) F G hconv hG,
    ?_, lintegral_rVariationFun_rpow_eq_iSup_trunc μ r p (by linarith) F hF⟩
  intro C hbound
  exact lintegral_rVariationFun_rpow_le_of_uniform μ r p (by linarith)
    F G hconv hG C hbound

end

end FractionalPrimes

end
