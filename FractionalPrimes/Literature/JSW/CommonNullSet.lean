module

public import FractionalPrimes.Literature.JSW.Conventions

/-!
# One exceptional null set for a countable family

This file implements the final representative-bookkeeping sentence in the
proof of `lj:vector-duality`.  Once Fubini (or another argument) has supplied
one almost-everywhere assertion for each member of a countable family, these
lemmas place all assertions outside one common null set.
-/

@[expose] public section

open MeasureTheory

namespace FractionalPrimes.Literature.JSW

/-- Countably many almost-everywhere assertions hold simultaneously almost
everywhere. -/
theorem ae_forall_of_countable {α ι : Type*} [MeasurableSpace α]
    [Countable ι] (μ : Measure α) {P : ι → α → Prop}
    (hP : ∀ i, ∀ᵐ x ∂μ, P i x) :
    ∀ᵐ x ∂μ, ∀ i, P i x := by
  exact ae_all_iff.mpr hP

/-- Explicit common exceptional set for a countable family of
almost-everywhere assertions. -/
theorem exists_common_null_set_of_countable {α ι : Type*}
    [MeasurableSpace α] [Countable ι] (μ : Measure α)
    {P : ι → α → Prop} (hP : ∀ i, ∀ᵐ x ∂μ, P i x) :
    ∃ N : Set α, μ N = 0 ∧ ∀ x, x ∉ N → ∀ i, P i x := by
  let N : Set α := {x | ¬ ∀ i, P i x}
  refine ⟨N, ?_, ?_⟩
  · exact ae_iff.mp (ae_forall_of_countable μ hP)
  · intro x hx
    exact not_not.mp hx

/-- Representatives of a countable family of almost-everywhere equivalence
classes agree with their chosen versions simultaneously off one null set. -/
theorem exists_common_null_set_for_representatives {α β ι : Type*}
    [MeasurableSpace α] [Countable ι] (μ : Measure α)
    (f g : ι → α → β) (hfg : ∀ i, f i =ᵐ[μ] g i) :
    ∃ N : Set α, μ N = 0 ∧ ∀ x, x ∉ N → ∀ i, f i x = g i x := by
  exact exists_common_null_set_of_countable μ hfg

end FractionalPrimes.Literature.JSW
