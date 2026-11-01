module

public import FractionalPrimes.Literature.Variation.JumpCount
import Mathlib.Data.Nat.Find

/-!
# Finite separated jump counts

For a finite ordered index set, the source defines the jump count as the
largest natural number for which a separated family exists.  This file
packages that maximum using `Nat.findGreatest` and identifies its ENNReal
image with the all-finite-families supremum from `JumpCount.lean`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open scoped ENNReal

noncomputable section

/-- There is a separated family of exactly `n` jumps. -/
def HasSeparatedJumpNumber {I : Type*} [LinearOrder I] (u : I → ℂ)
    (threshold : ℝ) (n : ℕ) : Prop :=
  ∃ s t : Fin n → I, SeparatedJumpFamily u threshold s t

/-- Any separated family on a finite ordered set has at most one interval
per index. -/
theorem separatedJumpFamily_card_le
    {I : Type*} [LinearOrder I] [Fintype I] (u : I → ℂ) (threshold : ℝ)
    {n : ℕ} {s t : Fin n → I} (h : SeparatedJumpFamily u threshold s t) :
    n ≤ Fintype.card I := by
  have ht : StrictMono t := by
    intro i j hij
    exact lt_of_le_of_lt (h.1.2 i j hij) (h.1.1 j)
  simpa using Fintype.card_le_of_injective t ht.injective

/-- The finite separated jump count, chosen as the largest admissible
natural number up to the cardinality of the index set. -/
noncomputable def finiteSeparatedJumpCount
    {I : Type*} [LinearOrder I] [Fintype I] (u : I → ℂ) (threshold : ℝ) : ℕ := by
  classical
  exact Nat.findGreatest (HasSeparatedJumpNumber u threshold) (Fintype.card I)

/-- The finite maximum is attained by a separated family. -/
theorem finiteSeparatedJumpCount_isAttained
    {I : Type*} [LinearOrder I] [Fintype I] (u : I → ℂ) (threshold : ℝ) :
    HasSeparatedJumpNumber u threshold (finiteSeparatedJumpCount u threshold) := by
  classical
  have hzero : HasSeparatedJumpNumber u threshold 0 := by
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    simp [SeparatedJumpFamily]
  unfold finiteSeparatedJumpCount
  exact Nat.findGreatest_spec (P := HasSeparatedJumpNumber u threshold)
    (m := 0) (n := Fintype.card I) (Nat.zero_le _) hzero

/-- The finite maximum dominates every admissible separated family. -/
theorem le_finiteSeparatedJumpCount_of_family
    {I : Type*} [LinearOrder I] [Fintype I] (u : I → ℂ) (threshold : ℝ)
    {n : ℕ} (h : HasSeparatedJumpNumber u threshold n) :
    n ≤ finiteSeparatedJumpCount u threshold := by
  classical
  unfold finiteSeparatedJumpCount
  exact Nat.le_findGreatest (by
    obtain ⟨s, t, hst⟩ := h
    exact separatedJumpFamily_card_le u threshold hst) h

/-- The finite jump count is bounded by the number of indices. -/
theorem finiteSeparatedJumpCount_le_card
    {I : Type*} [LinearOrder I] [Fintype I] (u : I → ℂ) (threshold : ℝ) :
    finiteSeparatedJumpCount u threshold ≤ Fintype.card I := by
  classical
  unfold finiteSeparatedJumpCount
  exact Nat.findGreatest_le _

/-- On a finite ordered set, the ENNReal supremum over all finite separated
families is exactly the cast of the largest admissible natural number. -/
theorem separatedJumpCount_eq_finiteSeparatedJumpCount
    {I : Type*} [LinearOrder I] [Fintype I] (u : I → ℂ) (threshold : ℝ) :
    separatedJumpCount u threshold =
      (finiteSeparatedJumpCount u threshold : ℝ≥0∞) := by
  classical
  apply le_antisymm
  · unfold separatedJumpCount
    apply iSup_le
    intro n
    apply iSup_le
    intro s
    apply iSup_le
    intro t
    by_cases h : SeparatedJumpFamily u threshold s t
    · have hmax : n ≤ finiteSeparatedJumpCount u threshold :=
        le_finiteSeparatedJumpCount_of_family u threshold ⟨s, t, h⟩
      rw [if_pos h]
      exact_mod_cast hmax
    · simp [h]
  · obtain ⟨s, t, h⟩ := finiteSeparatedJumpCount_isAttained u threshold
    exact ofNat_le_separatedJumpCount_of_family u threshold s t h

end

end FractionalPrimes.Literature.Variation
