module

public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalAndTV
public import Mathlib.Data.List.Sort

/-!
# Restriction monotonicity for finite ordered total variation

This file proves the first claim of blueprint item `lu:tv-calculus` for the
exact finite inhomogeneous variation definition in
`ProgressionMaximalAndTV.lean`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

noncomputable section

private theorem listAdjacentVariation_cons (g : ℤ → ℂ) (a : ℤ) (l : List ℤ) :
    listAdjacentVariation g (a :: l) =
      (match l with
       | [] => 0
       | b :: _ => ‖g b - g a‖) + listAdjacentVariation g l := by
  cases l <;> simp [listAdjacentVariation, List.consecutivePairs, List.zip, List.tail]

private def listPathVariationFrom (g : ℤ → ℂ) (z : ℤ) : List ℤ → ℝ
  | [] => 0
  | a :: l => ‖g a - g z‖ + listAdjacentVariation g (a :: l)

private theorem listPathVariationFrom_cons_eq_adjacent (g : ℤ → ℂ) (a : ℤ)
    (l : List ℤ) :
    listPathVariationFrom g a l = listAdjacentVariation g (a :: l) := by
  cases l with
  | nil =>
      simp [listPathVariationFrom, listAdjacentVariation, List.consecutivePairs,
        List.zip, List.tail]
  | cons b bs =>
      simp [listPathVariationFrom, listAdjacentVariation_cons]

private theorem listPathVariationFrom_mono_cons (g : ℤ → ℂ) (z a : ℤ)
    (l : List ℤ) :
    listPathVariationFrom g z l ≤ listPathVariationFrom g z (a :: l) := by
  cases l with
  | nil =>
      simp [listPathVariationFrom, listAdjacentVariation, List.consecutivePairs,
        List.zip, List.tail, norm_nonneg]
  | cons b bs =>
      simp only [listPathVariationFrom]
      calc
        ‖g b - g z‖ + listAdjacentVariation g (b :: bs) ≤
            (‖g a - g z‖ + ‖g b - g a‖) +
              listAdjacentVariation g (b :: bs) := by
                apply add_le_add
                · calc
                  ‖g b - g z‖ = ‖(g b - g a) + (g a - g z)‖ := by
                    congr 1
                    abel
                  _ ≤ ‖g b - g a‖ + ‖g a - g z‖ := norm_add_le (g b - g a) (g a - g z)
                  _ = ‖g a - g z‖ + ‖g b - g a‖ := add_comm _ _
                · exact le_rfl
        _ = listPathVariationFrom g z (a :: b :: bs) := by
          simp [listPathVariationFrom, listAdjacentVariation_cons, add_assoc, add_comm]

private theorem listPathVariationFrom_le_of_sublist (g : ℤ → ℂ) {l₁ l₂ : List ℤ}
    (h : List.Sublist l₁ l₂) (z : ℤ) :
    listPathVariationFrom g z l₁ ≤ listPathVariationFrom g z l₂ := by
  revert z
  induction h with
  | slnil => intro z; simp [listPathVariationFrom]
  | cons a h ih =>
      intro z
      exact (ih z).trans (listPathVariationFrom_mono_cons g z a _)
  | cons_cons a h ih =>
      intro z
      have hv := by
        simpa only [listPathVariationFrom_cons_eq_adjacent g a] using ih a
      simp only [listPathVariationFrom]
      exact add_le_add_right hv _

private theorem listAdjacentVariation_le_pathVariationFrom (g : ℤ → ℂ) (z : ℤ)
    (l : List ℤ) :
    listAdjacentVariation g l ≤ listPathVariationFrom g z l := by
  cases l with
  | nil => simp [listAdjacentVariation, listPathVariationFrom]
  | cons a as =>
      simp only [listPathVariationFrom]
      exact le_add_of_nonneg_left (norm_nonneg _)

private theorem listAdjacentVariation_le_of_sublist (g : ℤ → ℂ) {l₁ l₂ : List ℤ}
    (h : List.Sublist l₁ l₂) : listAdjacentVariation g l₁ ≤ listAdjacentVariation g l₂ := by
  cases l₂ with
  | nil =>
      have : l₁ = [] := by simpa using h
      simp [this, listAdjacentVariation]
  | cons a as =>
      calc
        listAdjacentVariation g l₁ ≤ listPathVariationFrom g a l₁ :=
          listAdjacentVariation_le_pathVariationFrom g a l₁
        _ ≤ listPathVariationFrom g a (a :: as) :=
          listPathVariationFrom_le_of_sublist g h a
        _ = listAdjacentVariation g (a :: as) := by
          cases as <;> simp [listPathVariationFrom, listAdjacentVariation]

private theorem list_foldl_max_le_iff (l : List ℝ) (b c : ℝ) :
    l.foldl max b ≤ c ↔ b ≤ c ∧ ∀ x ∈ l, x ≤ c := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
      simp [List.foldl_cons, ih, and_assoc, and_left_comm, and_comm]

private theorem listSupNorm_le_of_sublist (g : ℤ → ℂ) {l₁ l₂ : List ℤ}
    (h : List.Sublist l₁ l₂) : listSupNorm g l₁ ≤ listSupNorm g l₂ := by
  unfold listSupNorm
  apply (list_foldl_max_le_iff _ _ _).2
  have hupper := (list_foldl_max_le_iff (l₂.map fun n => ‖g n‖) 0
    ((l₂.map fun n => ‖g n‖).foldl max 0)).1 le_rfl
  refine ⟨hupper.1, ?_⟩
  intro x hx
  rcases List.mem_map.mp hx with ⟨n, hn, rfl⟩
  exact hupper.2 _ (List.mem_map.mpr ⟨_, h.subset hn, rfl⟩)

private theorem sort_sublist_of_subset {A B : Finset ℤ} (hAB : A ⊆ B) :
    List.Sublist (A.sort (· ≤ ·)) (B.sort (· ≤ ·)) := by
  apply List.sublist_of_subperm_of_sortedLE
  · apply (Finset.sort_nodup A (· ≤ ·)).subperm
    intro z hz
    exact (Finset.mem_sort (s := B) (r := (· ≤ ·))).2
      (hAB ((Finset.mem_sort (s := A) (r := (· ≤ ·))).1 hz))
  · exact (Finset.pairwise_sort A (· ≤ ·)).sortedLE
  · exact (Finset.pairwise_sort B (· ≤ ·)).sortedLE

/-- Restricting a finite ordered set cannot increase its inhomogeneous total
variation.  This is the first claim of blueprint item `lu:tv-calculus`. -/
theorem finiteOrderedTotalVariation_mono_of_subset {A B : Finset ℤ}
    (hAB : A ⊆ B) (g : ℤ → ℂ) :
    finiteOrderedTotalVariation A g ≤ finiteOrderedTotalVariation B g := by
  unfold finiteOrderedTotalVariation
  have hsort := sort_sublist_of_subset hAB
  exact add_le_add
    (listSupNorm_le_of_sublist g hsort)
    (listAdjacentVariation_le_of_sublist g hsort)

end

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.finiteOrderedTotalVariation_mono_of_subset
