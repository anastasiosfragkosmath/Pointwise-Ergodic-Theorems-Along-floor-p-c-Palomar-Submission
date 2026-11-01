module

public import FractionalPrimes.Core
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Separated jump counts

This file starts the source-order implementation of blueprint item
`lv:jump-count`.  A finite family is represented by two endpoint maps on
`Fin n`; the global count is the supremum over all such finite families.
For finite ordered index sets the cardinality bound below makes this
supremum a finite maximum, while for countable index sets the same
definition permits an infinite count.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A family of `n` separated jumps in an ordered sequence.  The pairwise
condition on the intervals is equivalent to the displayed consecutive
ordering `s₁ < t₁ ≤ s₂ < t₂ ≤ ⋯`. -/
def SeparatedJumpFamily {I : Type*} [LinearOrder I] (u : I → ℂ)
    (threshold : ℝ) {n : ℕ} (s t : Fin n → I) : Prop :=
  ((∀ i, s i < t i) ∧ (∀ i j, i < j → t i ≤ s j)) ∧
    (∀ i, threshold < ‖u (t i) - u (s i)‖)

/-- The number of `λ`-jumps of a sequence, as the supremum of the sizes of
all finite separated families.  The empty family is included at `n = 0`.
For finite index sets this is the largest admissible natural number; for
countable index sets it is the supremum over finite subsets. -/
def separatedJumpCount {I : Type*} [LinearOrder I] (u : I → ℂ) (threshold : ℝ) :
    ℝ≥0∞ := by
  classical
  exact ⨆ n : ℕ, ⨆ s : Fin n → I, ⨆ t : Fin n → I,
    if SeparatedJumpFamily u threshold s t then (n : ℝ≥0∞) else 0

/-- Every witnessed separated family contributes its cardinality to the
global jump count. -/
theorem ofNat_le_separatedJumpCount_of_family
    {I : Type*} [LinearOrder I] (u : I → ℂ) (threshold : ℝ) {n : ℕ}
    (s t : Fin n → I) (h : SeparatedJumpFamily u threshold s t) :
    (n : ℝ≥0∞) ≤ separatedJumpCount u threshold := by
  unfold separatedJumpCount
  exact le_iSup_of_le n <| le_iSup_of_le s <| le_iSup_of_le t <| by simp [h]

/-- A finite ordered set has at most its cardinality many separated jumps. -/
theorem separatedJumpCount_le_card
    {I : Type*} [LinearOrder I] [Fintype I] (u : I → ℂ) (threshold : ℝ) :
    separatedJumpCount u threshold ≤ (Fintype.card I : ℝ≥0∞) := by
  classical
  unfold separatedJumpCount
  apply iSup_le
  intro n
  apply iSup_le
  intro s
  apply iSup_le
  intro t
  by_cases h : SeparatedJumpFamily u threshold s t
  · have ht : StrictMono t := by
      intro i j hij
      exact lt_of_le_of_lt (h.1.2 i j hij) (h.1.1 j)
    have hcard : n ≤ Fintype.card I := by
      have hcard' := Fintype.card_le_of_injective t ht.injective
      simpa using hcard'
    rw [if_pos h]
    exact_mod_cast hcard
  · simp [h]

/-- The separated jump count is measurable for a countable ordered index
set when every sequence member is measurable.  The proof follows the same
countable-supremum pattern as `measurable_rVariationFun`. -/
theorem measurable_separatedJumpCount
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (F : I → X → ℂ) (threshold : ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (fun x => separatedJumpCount (fun i => F i x) threshold) := by
  classical
  unfold separatedJumpCount
  apply Measurable.iSup
  intro n
  letI : Countable (Fin n → I) := by infer_instance
  apply Measurable.iSup
  intro s
  apply Measurable.iSup
  intro t
  have hthresholdSet : MeasurableSet {x : X | ∀ i : Fin n,
        threshold < ‖F (t i) x - F (s i) x‖} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const
        (((hF (t i)).sub (hF (s i))).norm)
  have hfamilySet : MeasurableSet
      {x : X | SeparatedJumpFamily (fun i => F i x) threshold s t} := by
    change MeasurableSet
      ({x : X | (∀ i, s i < t i) ∧ (∀ i j, i < j → t i ≤ s j)} ∩
        {x : X | ∀ i : Fin n,
          threshold < ‖F (t i) x - F (s i) x‖})
    exact (MeasurableSet.const _).inter hthresholdSet
  exact Measurable.ite hfamilySet measurable_const measurable_const

end

end FractionalPrimes.Literature.Variation
