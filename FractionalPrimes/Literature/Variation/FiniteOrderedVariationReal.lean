module

public import FractionalPrimes.Literature.Variation.FiniteChainVariationAlgebra
public import FractionalPrimes.Literature.Variation.FiniteOrderedVariation
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Real-valued finite ordered variation

Layer-cake interpolation is phrased for nonnegative real outputs.  Ordered
variation naturally takes values in `ℝ≥0∞`; on a finite index type it is
finite, so `ENNReal.toReal` gives an exact real-valued interface preserving
measurability, subadditivity, homogeneity, and strict level sets.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Real-valued ordered variation.  This is exact on finite index types. -/
def finiteOrderedVariationReal
    {I : Type*} [LinearOrder I] (r : ℝ) (u : I → ℂ) : ℝ :=
  (orderedRVariation r u).toReal

/-- Pointwise real-valued ordered variation of a finite family. -/
def finiteOrderedVariationRealFun
    {I X : Type*} [LinearOrder I] (r : ℝ) (F : I → X → ℂ) : X → ℝ :=
  fun x => finiteOrderedVariationReal r (fun i => F i x)

theorem finiteOrderedVariationReal_nonneg
    {I : Type*} [LinearOrder I] (r : ℝ) (u : I → ℂ) :
    0 ≤ finiteOrderedVariationReal r u :=
  ENNReal.toReal_nonneg

/-- Converting the finite real variation back to `ℝ≥0∞` recovers the
original variation exactly. -/
theorem ofReal_finiteOrderedVariationReal
    {I : Type*} [LinearOrder I] [Fintype I]
    (r : ℝ) (hr : 0 < r) (u : I → ℂ) :
    ENNReal.ofReal (finiteOrderedVariationReal r u) = orderedRVariation r u := by
  unfold finiteOrderedVariationReal
  rw [ENNReal.ofReal_toReal]
  exact (orderedRVariation_lt_top_of_pos r u hr).ne

/-- The real-valued finite variation is measurable for a measurable finite
family. -/
theorem measurable_finiteOrderedVariationRealFun
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (r : ℝ) (F : I → X → ℂ) (hF : ∀ i, Measurable (F i)) :
    Measurable (finiteOrderedVariationRealFun r F) := by
  unfold finiteOrderedVariationRealFun finiteOrderedVariationReal
  exact (measurable_orderedRVariationFun r F hF).ennreal_toReal

/-- Exact subadditivity of the real-valued finite variation. -/
theorem finiteOrderedVariationReal_add_le
    {I : Type*} [LinearOrder I] [Fintype I]
    (r : ℝ) (hr : 1 ≤ r) (u v : I → ℂ) :
    finiteOrderedVariationReal r (u + v) ≤
      finiteOrderedVariationReal r u + finiteOrderedVariationReal r v := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have huTop : orderedRVariation r u ≠ ∞ :=
    (orderedRVariation_lt_top_of_pos r u hr0).ne
  have hvTop : orderedRVariation r v ≠ ∞ :=
    (orderedRVariation_lt_top_of_pos r v hr0).ne
  unfold finiteOrderedVariationReal
  calc
    (orderedRVariation r (u + v)).toReal ≤
        (orderedRVariation r u + orderedRVariation r v).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨huTop, hvTop⟩)
        (orderedRVariation_add_le r hr u v)
    _ = (orderedRVariation r u).toReal +
          (orderedRVariation r v).toReal := ENNReal.toReal_add huTop hvTop

/-- Exact absolute homogeneity of the real-valued finite variation. -/
theorem finiteOrderedVariationReal_smul
    {I : Type*} [LinearOrder I] [Fintype I]
    (r : ℝ) (hr : 0 < r) (c : ℂ) (u : I → ℂ) :
    finiteOrderedVariationReal r (c • u) =
      ‖c‖ * finiteOrderedVariationReal r u := by
  unfold finiteOrderedVariationReal
  rw [orderedRVariation_smul r hr c u,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (norm_nonneg c)]

/-- Strict real level sets agree with strict `ℝ≥0∞` level sets of the
original finite variation. -/
theorem finiteOrderedVariationRealFun_levelSet
    {I X : Type*} [LinearOrder I] [Fintype I]
    (r : ℝ) (hr : 0 < r) (F : I → X → ℂ)
    (t : ℝ) (ht : 0 ≤ t) :
    {x | t < finiteOrderedVariationRealFun r F x} =
      {x | ENNReal.ofReal t < orderedRVariationFun r F x} := by
  ext x
  unfold finiteOrderedVariationRealFun finiteOrderedVariationReal
  exact (ENNReal.ofReal_lt_iff_lt_toReal ht
    (orderedRVariation_lt_top_of_pos r (fun i => F i x) hr).ne).symm

end

end FractionalPrimes.Literature.Variation

end
