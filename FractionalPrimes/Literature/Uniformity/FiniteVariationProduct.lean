module

public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalAndTV
public import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Product estimate for finite inhomogeneous total variation

This file proves the finite-set product clause used in `lu:tv-calculus`,
using the exact finite variation definition from `ProgressionMaximalAndTV`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

noncomputable section

private theorem list_foldl_max_le_iff (l : List ℝ) (b c : ℝ) :
    l.foldl max b ≤ c ↔ b ≤ c ∧ ∀ x ∈ l, x ≤ c := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
      simp [List.foldl_cons, ih, and_assoc, and_left_comm, and_comm]

private theorem list_foldl_max_nonneg (l : List ℝ) {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => simpa using hb
  | cons a l ih =>
      rw [List.foldl_cons]
      exact ih (le_trans hb (le_max_left b a))

private theorem listSupNorm_nonneg (g : ℤ → ℂ) (l : List ℤ) :
    0 ≤ listSupNorm g l := by
  exact list_foldl_max_nonneg _ le_rfl

private theorem listAdjacentVariation_nonneg (g : ℤ → ℂ) (l : List ℤ) :
    0 ≤ listAdjacentVariation g l := by
  unfold listAdjacentVariation
  induction l.consecutivePairs with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (norm_nonneg _) ih

private theorem norm_le_listSupNorm (g : ℤ → ℂ) (l : List ℤ) {n : ℤ}
    (hn : n ∈ l) : ‖g n‖ ≤ listSupNorm g l := by
  unfold listSupNorm
  have hupper := (list_foldl_max_le_iff (l.map fun m => ‖g m‖) 0
    ((l.map fun m => ‖g m‖).foldl max 0)).1 le_rfl
  exact hupper.2 _ (List.mem_map.mpr ⟨n, hn, rfl⟩)

private theorem listSupNorm_mul_le (g h : ℤ → ℂ) (l : List ℤ) :
    listSupNorm (fun n => g n * h n) l ≤ listSupNorm g l * listSupNorm h l := by
  unfold listSupNorm
  apply (list_foldl_max_le_iff _ _ _).2
  refine ⟨mul_nonneg (listSupNorm_nonneg g l) (listSupNorm_nonneg h l), ?_⟩
  intro x hx
  rcases List.mem_map.mp hx with ⟨n, hn, rfl⟩
  have hg := norm_le_listSupNorm g l hn
  have hh := norm_le_listSupNorm h l hn
  calc
    ‖g n * h n‖ = ‖g n‖ * ‖h n‖ := norm_mul _ _
    _ ≤ listSupNorm g l * listSupNorm h l :=
      mul_le_mul hg hh (norm_nonneg _) (listSupNorm_nonneg g l)

private theorem list_sum_map_le {α : Type*} (l : List α) (f k : α → ℝ)
    (h : ∀ x ∈ l, f x ≤ k x) :
    (l.map f).sum ≤ (l.map k).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      apply add_le_add
      · exact h a (by simp)
      · apply ih
        intro x hx
        exact h x (by simp [hx])

private theorem list_sum_map_add (α : Type*) (l : List α) (f k : α → ℝ) :
    (l.map fun x => f x + k x).sum = (l.map f).sum + (l.map k).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, add_assoc, add_left_comm]

private theorem list_sum_map_mul_right (α : Type*) (l : List α) (f : α → ℝ)
    (c : ℝ) :
    (l.map fun x => f x * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, add_mul]

private theorem list_sum_map_mul_left (α : Type*) (l : List α) (f : α → ℝ)
    (c : ℝ) :
    (l.map fun x => c * f x).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, mul_add]

private theorem norm_product_increment_le (g h : ℤ → ℂ) (l : List ℤ)
    (a b : ℤ) (ha : a ∈ l) (hb : b ∈ l) :
    ‖g b * h b - g a * h a‖ ≤
      ‖g b - g a‖ * listSupNorm h l +
        listSupNorm g l * ‖h b - h a‖ := by
  have hmul : g b * h b - g a * h a =
      (g b - g a) * h b + g a * (h b - h a) := by ring
  calc
    ‖g b * h b - g a * h a‖ =
        ‖(g b - g a) * h b + g a * (h b - h a)‖ := by rw [hmul]
    _ ≤ ‖(g b - g a) * h b‖ + ‖g a * (h b - h a)‖ := norm_add_le _ _
    _ = ‖g b - g a‖ * ‖h b‖ + ‖g a‖ * ‖h b - h a‖ := by simp
    _ ≤ ‖g b - g a‖ * listSupNorm h l +
          listSupNorm g l * ‖h b - h a‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (norm_le_listSupNorm h l hb)
          (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_right (norm_le_listSupNorm g l ha)
          (norm_nonneg _)

private theorem listAdjacentVariation_mul_le (g h : ℤ → ℂ) (l : List ℤ) :
    listAdjacentVariation (fun n => g n * h n) l ≤
      listAdjacentVariation g l * listSupNorm h l +
        listSupNorm g l * listAdjacentVariation h l := by
  let pairs := l.consecutivePairs
  have hbound (p : ℤ × ℤ) (hp : p ∈ pairs) :
      ‖g p.2 * h p.2 - g p.1 * h p.1‖ ≤
        ‖g p.2 - g p.1‖ * listSupNorm h l +
          listSupNorm g l * ‖h p.2 - h p.1‖ := by
    have hp' : p ∈ l.zip l.tail := by simpa [pairs, List.consecutivePairs] using hp
    have hfst : p.1 ∈ l := (List.of_mem_zip hp').1
    have hsnd : p.2 ∈ l := (List.mem_of_mem_tail (List.of_mem_zip hp').2)
    exact norm_product_increment_le g h l p.1 p.2 hfst hsnd
  unfold listAdjacentVariation
  dsimp only [pairs]
  calc
    (l.consecutivePairs.map fun p => ‖g p.2 * h p.2 - g p.1 * h p.1‖).sum ≤
        (l.consecutivePairs.map fun p =>
          ‖g p.2 - g p.1‖ * listSupNorm h l +
            listSupNorm g l * ‖h p.2 - h p.1‖).sum := by
          apply list_sum_map_le
          intro p hp
          exact hbound p hp
    _ = listAdjacentVariation g l * listSupNorm h l +
          listSupNorm g l * listAdjacentVariation h l := by
          simp only [list_sum_map_add]
          rw [list_sum_map_mul_right, list_sum_map_mul_left]
          rfl

/-- The inhomogeneous finite total variation is submultiplicative under
pointwise multiplication of complex-valued functions.  This holds also for
the empty finite set. -/
theorem finiteOrderedTotalVariation_mul_le (P : Finset ℤ) (g h : ℤ → ℂ) :
    finiteOrderedTotalVariation P (fun n => g n * h n) ≤
      finiteOrderedTotalVariation P g * finiteOrderedTotalVariation P h := by
  let l := P.sort (· ≤ ·)
  let Sg := listSupNorm g l
  let Sh := listSupNorm h l
  let Vg := listAdjacentVariation g l
  let Vh := listAdjacentVariation h l
  have hS : listSupNorm (fun n => g n * h n) l ≤ Sg * Sh := listSupNorm_mul_le g h l
  have hV : listAdjacentVariation (fun n => g n * h n) l ≤ Vg * Sh + Sg * Vh := by
    simpa [Sg, Sh, Vg, Vh] using listAdjacentVariation_mul_le g h l
  have hSg : 0 ≤ Sg := listSupNorm_nonneg g l
  have hSh : 0 ≤ Sh := listSupNorm_nonneg h l
  have hVg : 0 ≤ Vg := listAdjacentVariation_nonneg g l
  have hVh : 0 ≤ Vh := listAdjacentVariation_nonneg h l
  change listSupNorm (fun n => g n * h n) l +
      listAdjacentVariation (fun n => g n * h n) l ≤
    (Sg + Vg) * (Sh + Vh)
  calc
    _ ≤ Sg * Sh + (Vg * Sh + Sg * Vh) := add_le_add hS hV
    _ ≤ (Sg + Vg) * (Sh + Vh) := by nlinarith [mul_nonneg hVg hVh]

end

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.finiteOrderedTotalVariation_mul_le
