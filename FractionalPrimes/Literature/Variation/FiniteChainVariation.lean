module

public import FractionalPrimes.Variation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Homogeneous variation on a general linear order

The manuscript's jump-to-variation bridge ranges over an arbitrary finite,
then countable, linearly ordered index set.  The existing `rVariation` is
indexed specifically by positive natural scales, so this file records the
same finite-chain construction with the index type left generic.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A finite strictly increasing chain in a linearly ordered index type.
`length` counts the increments, so the chain has `length + 1` entries. -/
structure StrictOrderedChain (I : Type*) [LinearOrder I] (length : ℕ) where
  point : Fin (length + 1) → I
  strictMono : StrictMono point

/-- The `ℓ^r` increment contribution of one finite ordered chain. -/
def finiteChainVariation {I : Type*} [LinearOrder I] (r : ℝ) (u : I → ℂ)
    {length : ℕ} (chain : StrictOrderedChain I length) : ℝ≥0∞ :=
  (∑ i : Fin length,
    (ENNReal.ofReal ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖).rpow r).rpow r⁻¹

/-- The homogeneous `r`-variation over all finite increasing chains in an
arbitrary linear order.  For a finite index type, only finitely many chain
lengths are nonempty, and this supremum is the finite maximum in the
blueprint.  For a countable index type, it is the stated supremum over
finite chains. -/
def orderedRVariation {I : Type*} [LinearOrder I] (r : ℝ) (u : I → ℂ) : ℝ≥0∞ :=
  ⨆ (length : ℕ) (chain : StrictOrderedChain I length),
    finiteChainVariation r u chain

/-- Every fixed finite-chain contribution is bounded by the full
variation. -/
theorem finiteChainVariation_le_orderedRVariation {I : Type*} [LinearOrder I]
    (r : ℝ) (u : I → ℂ) {length : ℕ} (chain : StrictOrderedChain I length) :
    finiteChainVariation r u chain ≤ orderedRVariation r u := by
  exact le_iSup_of_le length (le_iSup_of_le chain le_rfl)

/-- The contribution of one fixed ordered chain for a family of measurable
functions. -/
def finiteChainVariationFun {I X : Type*} [LinearOrder I] (r : ℝ)
    (F : I → X → ℂ) {length : ℕ} (chain : StrictOrderedChain I length) :
    X → ℝ≥0∞ :=
  fun x => finiteChainVariation r (fun i => F i x) chain

/-- A fixed finite-chain contribution is measurable when every sequence
member is measurable. -/
theorem measurable_finiteChainVariationFun {I X : Type*} [LinearOrder I]
    [MeasurableSpace X] (r : ℝ) (F : I → X → ℂ)
    (hF : ∀ i, Measurable (F i)) {length : ℕ}
    (chain : StrictOrderedChain I length) :
    Measurable (finiteChainVariationFun r F chain) := by
  have hsum : Measurable (fun x =>
      ∑ i : Fin length,
        (ENNReal.ofReal ‖F (chain.point i.succ) x -
          F (chain.point i.castSucc) x‖).rpow r) := by
    apply Finset.measurable_fun_sum
    intro i hi
    convert (ENNReal.continuous_rpow_const (y := r)).measurable.comp
      (Measurable.ennreal_ofReal
        (((hF (chain.point i.succ)).sub (hF (chain.point i.castSucc))).norm)) using 1
    ext x
    simp only [Function.comp_apply, ENNReal.rpow_eq_pow, Pi.sub_apply]
  convert (ENNReal.continuous_rpow_const (y := r⁻¹)).measurable.comp hsum using 1
  ext x
  simp only [Function.comp_apply, finiteChainVariationFun, finiteChainVariation,
    ENNReal.rpow_eq_pow]

/-- Embed the chain structure into its underlying finite tuple. -/
def strictOrderedChainEmbedding {I : Type*} [LinearOrder I] (length : ℕ) :
    StrictOrderedChain I length ↪ (Fin (length + 1) → I) where
  toFun := StrictOrderedChain.point
  inj' := by
    intro a b hab
    cases a
    cases b
    cases hab
    rfl

/-- Pointwise homogeneous variation for a family indexed by a generic linear
order. -/
def orderedRVariationFun {I X : Type*} [LinearOrder I] (r : ℝ)
    (F : I → X → ℂ) : X → ℝ≥0∞ :=
  fun x => orderedRVariation r (fun i => F i x)

/-- Pointwise variation is measurable when the index order is countable and
every member of the family is measurable. -/
theorem measurable_orderedRVariationFun {I X : Type*} [LinearOrder I]
    [Countable I] [MeasurableSpace X] (r : ℝ) (F : I → X → ℂ)
    (hF : ∀ i, Measurable (F i)) :
    Measurable (orderedRVariationFun r F) := by
  unfold orderedRVariationFun orderedRVariation
  apply Measurable.iSup
  intro length
  let _ : Countable (StrictOrderedChain I length) :=
    (strictOrderedChainEmbedding length).countable
  apply Measurable.iSup
  intro chain
  exact measurable_finiteChainVariationFun r F hF chain

end

end FractionalPrimes.Literature.Variation
