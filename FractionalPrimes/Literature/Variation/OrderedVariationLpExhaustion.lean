module

public import FractionalPrimes.Literature.Variation.OrderedVariationExhaustion
public import FractionalPrimes.Literature.Variation.FiniteOrderedVariationReal
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-!
# `L^p` norm passage through a finite exhaustion of ordered variation

This is the final analytic limit lemma used in blueprint
`lv:jump-to-variation`: the norm of full countable ordered variation is the
supremum of the norms of its increasing finite-exhaustion truncations.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- For a positive finite exponent, `eLpNorm` commutes with the increasing
finite exhaustion of a countable ordered variation. -/
theorem eLpNorm_orderedRVariationFun_eq_iSup_trunc
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (K : Set.FiniteExhaustion (Set.univ : Set I))
    (μ : Measure X) (r p : ℝ) (hp : 0 < p)
    (F : I → X → ℂ) (hF : ∀ i, Measurable (F i)) :
    eLpNorm (orderedRVariationFun r F) (ENNReal.ofReal p) μ =
      ⨆ N : ℕ,
        eLpNorm (orderedRVariationTruncFun K r F N)
          (ENNReal.ofReal p) μ := by
  have hpE0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpETop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hfullMeas : AEStronglyMeasurable (orderedRVariationFun r F) μ :=
    (measurable_orderedRVariationFun r F hF).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpE0 hpETop hfullMeas]
  simp only [ENNReal.toReal_ofReal hp.le, enorm_eq_self]
  rw [lintegral_orderedRVariationFun_rpow_eq_iSup_trunc
    K μ r p hp F hF]
  calc
    (⨆ N : ℕ,
        ∫⁻ x, (orderedRVariationTruncFun K r F N x) ^ p ∂μ) ^ (1 / p) =
        ⨆ N : ℕ,
          (∫⁻ x, (orderedRVariationTruncFun K r F N x) ^ p ∂μ) ^
            (1 / p) := by
      change ENNReal.orderIsoRpow (1 / p) (one_div_pos.mpr hp)
          (⨆ N : ℕ,
            ∫⁻ x, (orderedRVariationTruncFun K r F N x) ^ p ∂μ) = _
      rw [OrderIso.map_iSup]
      rfl
    _ = ⨆ N : ℕ,
        eLpNorm (orderedRVariationTruncFun K r F N)
          (ENNReal.ofReal p) μ := by
      congr 1
      funext N
      symm
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpE0 hpETop
        (measurable_orderedRVariationTruncFun K r F hF N).aestronglyMeasurable]
      simp only [ENNReal.toReal_ofReal hp.le, enorm_eq_self]

/-- A finite-exhaustion truncation has the same `eLpNorm` as the real-valued
finite ordered variation on the corresponding finite subtype. -/
theorem eLpNorm_orderedRVariationTruncFun_eq_subtypeReal
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (K : Set.FiniteExhaustion (Set.univ : Set I))
    (μ : Measure X) (r : ℝ) (hr : 0 < r)
    (F : I → X → ℂ) (hF : ∀ i, Measurable (F i))
    (N : ℕ) (p : ℝ≥0∞) :
    eLpNorm (orderedRVariationTruncFun K r F N) p μ =
      eLpNorm
        (finiteOrderedVariationRealFun r
          (fun i : K N => F i.1)) p μ := by
  let _ : Fintype (K N) := Fintype.ofFinite (K N)
  apply eLpNorm_congr_enorm_ae
    (measurable_orderedRVariationTruncFun K r F hF N).aestronglyMeasurable
    (measurable_finiteOrderedVariationRealFun r
      (fun i : K N => F i.1) (fun i => hF i.1)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    change ‖orderedRVariationTrunc K r (fun i => F i x) N‖ₑ =
      ‖finiteOrderedVariationReal r (fun i : K N => F i.1 x)‖ₑ
    rw [enorm_eq_self,
      Real.enorm_of_nonneg
        (finiteOrderedVariationReal_nonneg r (fun i : K N => F i.1 x)),
      ofReal_finiteOrderedVariationReal r hr]
    exact orderedRVariationTrunc_eq_subtype K r (fun i => F i x) N

end

end FractionalPrimes.Literature.Variation

end
