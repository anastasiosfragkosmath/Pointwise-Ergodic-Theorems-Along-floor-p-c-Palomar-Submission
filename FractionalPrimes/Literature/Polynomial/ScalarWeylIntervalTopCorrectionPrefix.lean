module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylTopCorrectionPrefix

/-!
# Integer-interval transport for the rational top correction

The checked monomial-phase variation estimate is stated for the finite
ordered variation on an integer interval. This file transports that bound to
the consecutive range sequence used by the finite Abel-prefix lemma.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open FractionalPrimes.Literature.Uniformity

private def scalarWeyl_intervalIndexEmbedding (lo : ℤ) : ℕ ↪o ℤ :=
  OrderEmbedding.ofMapLEIff
    (Nat.castEmbedding.trans (addLeftEmbedding lo)) (by
      intro x y
      simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
        addLeftEmbedding_apply]
      rw [add_le_add_iff_left lo, Nat.cast_le])

private theorem scalarWeyl_intervalIndexEmbedding_toEmbedding (lo : ℤ) :
    (scalarWeyl_intervalIndexEmbedding lo).toEmbedding =
      Nat.castEmbedding.trans (addLeftEmbedding lo) := by
  apply Function.Embedding.ext
  intro j
  rfl

private theorem scalarWeyl_list_foldl_max_ge (l : List ℝ) (b : ℝ) :
    b ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldl_cons]
      exact (le_max_left b a).trans (ih (max b a))

private theorem scalarWeyl_list_foldl_max_mono (l : List ℝ)
    {b c : ℝ} (hbc : b ≤ c) : l.foldl max b ≤ l.foldl max c := by
  induction l generalizing b c with
  | nil => exact hbc
  | cons a l ih =>
      simp only [List.foldl_cons]
      exact ih (max_le_max_right a hbc)

private theorem scalarWeyl_list_foldl_max_ge_of_mem {l : List ℝ} {x : ℝ}
    (hx : x ∈ l) : x ≤ l.foldl max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
      simp only [List.mem_cons] at hx
      change x ≤ l.foldl max (max 0 a)
      rcases hx with hxa | hx
      · subst x
        exact (le_max_right 0 a).trans
          (scalarWeyl_list_foldl_max_ge l (max 0 a))
      · exact (ih hx).trans
          (scalarWeyl_list_foldl_max_mono l (le_max_left 0 a))

private theorem scalarWeyl_norm_le_listSupNorm_of_mem (g : ℤ → ℂ)
    {l : List ℤ} {x : ℤ} (hx : x ∈ l) :
    ‖g x‖ ≤ listSupNorm g l := by
  unfold listSupNorm
  apply scalarWeyl_list_foldl_max_ge_of_mem
  exact List.mem_map.mpr ⟨x, hx, rfl⟩

private theorem scalarWeyl_consecutivePairs_map {α β : Type*}
    (φ : α → β) (l : List α) :
    (l.map φ).consecutivePairs =
      l.consecutivePairs.map (fun p => (φ p.1, φ p.2)) := by
  induction l with
  | nil => simp [List.consecutivePairs]
  | cons a l ih =>
      cases l with
      | nil => simp [List.consecutivePairs]
      | cons b bs =>
          change (φ a, φ b) :: (List.map φ (b :: bs)).consecutivePairs =
            (φ a, φ b) :: ((b :: bs).consecutivePairs).map
              (fun p => (φ p.1, φ p.2))
          exact congrArg (List.cons (φ a, φ b)) ih

private theorem scalarWeyl_consecutivePairs_range_succ (k : ℕ) :
    (List.range (k + 2)).consecutivePairs =
      (0, 1) :: (List.map (fun p => (p.1 + 1, p.2 + 1))
        ((List.range (k + 1)).consecutivePairs)) := by
  have hmap : List.map Nat.succ (List.range (k + 1)) =
      Nat.succ 0 :: List.map Nat.succ (List.map Nat.succ (List.range k)) := by
    rw [List.range_succ_eq_map]
    simp
  rw [show k + 2 = (k + 1) + 1 by omega, List.range_succ_eq_map]
  change (0 :: List.map Nat.succ (List.range (k + 1))).zip
      (List.map Nat.succ (List.range (k + 1))) = _
  rw [hmap, List.zip_cons_cons]
  have hzip :
      (List.map Nat.succ (List.range (k + 1))).zip
          (List.map Nat.succ (List.map Nat.succ (List.range k))) =
        (List.map Nat.succ (List.range (k + 1))).consecutivePairs := by
    simp [List.consecutivePairs, List.range_succ_eq_map]
  rw [← hmap, hzip]
  norm_num
  rw [scalarWeyl_consecutivePairs_map Nat.succ (List.range (k + 1))]

private theorem scalarWeyl_consecutivePairs_range (N : ℕ) :
    (List.range N).consecutivePairs =
      (List.range (N - 1)).map (fun j => (j, j + 1)) := by
  induction N with
  | zero => simp [List.consecutivePairs]
  | succ N ih =>
      cases N with
      | zero => simp [List.consecutivePairs]
      | succ k =>
          rw [scalarWeyl_consecutivePairs_range_succ k, ih]
          simp [List.range_succ_eq_map, Function.comp_def]

private theorem scalarWeyl_listAdjacentVariation_range_map
    (g : ℤ → ℂ) (φ : ℕ → ℤ) (N : ℕ) :
    listAdjacentVariation g ((List.range N).map φ) =
      (List.map (fun j => ‖g (φ (j + 1)) - g (φ j)‖)
        (List.range (N - 1))).sum := by
  unfold listAdjacentVariation
  rw [scalarWeyl_consecutivePairs_map, scalarWeyl_consecutivePairs_range]
  simp [List.map_map, Function.comp_def]

private theorem scalarWeyl_list_sum_map_range_eq_finset {α : Type*}
    [AddCommMonoid α] (f : ℕ → α) (N : ℕ) :
    ((List.range N).map f).sum = ∑ j ∈ Finset.range N, f j := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.range_succ, List.map_append]
      simp [List.sum_append, ih, Finset.sum_range_succ]

private theorem scalarWeyl_listAdjacentVariation_range_map_finset
    (g : ℤ → ℂ) (φ : ℕ → ℤ) (N : ℕ) :
    listAdjacentVariation g ((List.range N).map φ) =
      ∑ j ∈ Finset.range (N - 1), ‖g (φ (j + 1)) - g (φ j)‖ := by
  rw [scalarWeyl_listAdjacentVariation_range_map,
    scalarWeyl_list_sum_map_range_eq_finset]

private theorem scalarWeyl_Ico_sort_eq_range_map
    (lo hi : ℤ) (L : ℕ) (hL : L = (hi - lo).toNat) :
    (Finset.Ico lo hi).sort (· ≤ ·) =
      (List.range L).map (scalarWeyl_intervalIndexEmbedding lo) := by
  let e := scalarWeyl_intervalIndexEmbedding lo
  have hpoints : Finset.Ico lo hi =
      (Finset.range L).map e.toEmbedding := by
    rw [show e.toEmbedding =
        Nat.castEmbedding.trans (addLeftEmbedding lo) by
          simpa [e] using scalarWeyl_intervalIndexEmbedding_toEmbedding lo]
    simpa [hL] using Int.Ico_eq_finset_map lo hi
  rw [hpoints]
  rw [← Finset.map_sort e.toEmbedding (Finset.range L) (· ≤ ·) (· ≤ ·)]
  · rw [Finset.sort_range]
    rfl
  · intro x hx y hy
    exact e.le_iff_le.symm

/-- A finite ordered-variation bound on `Ico lo hi` yields the endpoint plus
the exact consecutive-increment budget for its range reindexing. This is the
transport needed to apply finite Abel summation to the source interval. -/
theorem scalarWeyl_IcoVariation_to_rangeBudget
    (lo hi : ℤ) (d L : ℕ) (hL : L = (hi - lo).toNat) (hLpos : 0 < L)
    (θ W : ℝ)
    (hTV : finiteOrderedTotalVariation (Finset.Ico lo hi)
      (fun n => unitFrequencyPhase (θ * (n : ℝ) ^ d)) ≤ W) :
    ‖unitFrequencyPhase
        (θ * ((lo : ℝ) + ((L - 1 : ℕ) : ℝ)) ^ d)‖ +
      ∑ i ∈ Finset.range (L - 1),
        ‖unitFrequencyPhase
            (θ * ((lo : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ d) -
          unitFrequencyPhase
            (θ * ((lo : ℝ) + (i : ℝ)) ^ d)‖ ≤ W := by
  let e := scalarWeyl_intervalIndexEmbedding lo
  let g : ℤ → ℂ := fun n => unitFrequencyPhase (θ * (n : ℝ) ^ d)
  have hsort := scalarWeyl_Ico_sort_eq_range_map lo hi L hL
  have hlastMem : e (L - 1) ∈ (List.range L).map e := by
    apply List.mem_map.mpr
    exact ⟨L - 1, List.mem_range.mpr (Nat.sub_lt hLpos (by norm_num)), rfl⟩
  have hlast : ‖g (e (L - 1))‖ ≤ listSupNorm g ((Finset.Ico lo hi).sort (· ≤ ·)) := by
    rw [hsort]
    exact scalarWeyl_norm_le_listSupNorm_of_mem g hlastMem
  have hadj :
      listAdjacentVariation g ((Finset.Ico lo hi).sort (· ≤ ·)) =
        ∑ i ∈ Finset.range (L - 1), ‖g (e (i + 1)) - g (e i)‖ := by
    rw [hsort, scalarWeyl_listAdjacentVariation_range_map_finset]
  have hTV' :
      listSupNorm g ((Finset.Ico lo hi).sort (· ≤ ·)) +
        listAdjacentVariation g ((Finset.Ico lo hi).sort (· ≤ ·)) ≤ W := by
    simpa [g, finiteOrderedTotalVariation] using hTV
  have hbudget :
      ‖g (e (L - 1))‖ +
        ∑ i ∈ Finset.range (L - 1), ‖g (e (i + 1)) - g (e i)‖ ≤ W := by
    calc
      _ = ‖g (e (L - 1))‖ +
          listAdjacentVariation g ((Finset.Ico lo hi).sort (· ≤ ·)) := by rw [hadj]
      _ ≤ listSupNorm g ((Finset.Ico lo hi).sort (· ≤ ·)) +
          listAdjacentVariation g ((Finset.Ico lo hi).sort (· ≤ ·)) :=
        add_le_add hlast le_rfl
      _ ≤ W := hTV'
  simpa [e, g, scalarWeyl_intervalIndexEmbedding,
    Int.cast_add, Int.cast_natCast] using hbudget

/-- The checked shift/affine-recurrence denominator output feeds directly
into the source interval Abel step. The variation premise is exactly the
finite ordered monomial-phase bound on `J`; the theorem transports it to the
range sequence, applies the rational correction, and returns an initial
half-open subinterval of `J`. -/
theorem scalarWeyl_Ico_topCorrection_initialPrefix
    {N d r : ℕ} {R αd A : ℝ}
    (lo hi : ℤ)
    (hr : 1 ≤ r) (hN : 1 ≤ N) (hR : 0 ≤ R) (hA : 0 < A)
    (hdist : realDistanceToIntegers ((r : ℝ) * αd) ≤
      R / ((N : ℝ) ^ d))
    (f : ℤ → ℂ)
    (hlarge : A ≤ ‖∑ n ∈ Finset.Ico lo hi,
      f n * unitFrequencyPhase (αd * (n : ℝ) ^ d)‖)
    (hTV : ∀ θ : ℝ,
      |θ| ≤ R / ((r : ℝ) * (N : ℝ) ^ d) →
        finiteOrderedTotalVariation (Finset.Ico lo hi)
          (fun n => unitFrequencyPhase (θ * (n : ℝ) ^ d)) ≤ 1 + 8 * R) :
    ∃ a : ℤ, ∃ k : ℕ,
      k < (hi - lo).toNat ∧
      Finset.Ico lo (lo + ((k + 1 : ℕ) : ℤ)) ⊆ Finset.Ico lo hi ∧
      |αd - (a : ℝ) / (r : ℝ)| ≤
        R / ((r : ℝ) * (N : ℝ) ^ d) ∧
      A / (1 + 8 * R) ≤
        ‖∑ n ∈ Finset.Ico lo (lo + ((k + 1 : ℕ) : ℤ)),
          f n * unitFrequencyPhase
            (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d)‖ := by
  classical
  let L : ℕ := (hi - lo).toNat
  let e : ℕ ↪o ℤ := scalarWeyl_intervalIndexEmbedding lo
  let t : ℕ → ℝ := fun j => (e j : ℝ)
  let f' : ℕ → ℂ := fun j => f (e j)
  have hpoints : Finset.Ico lo hi = (Finset.range L).map e.toEmbedding := by
    rw [show e.toEmbedding =
        Nat.castEmbedding.trans (addLeftEmbedding lo) by
          simpa [e] using scalarWeyl_intervalIndexEmbedding_toEmbedding lo]
    simpa [L] using Int.Ico_eq_finset_map lo hi
  have hsum :
      (∑ n ∈ Finset.Ico lo hi,
        f n * unitFrequencyPhase (αd * (n : ℝ) ^ d)) =
        ∑ j ∈ Finset.range L,
          f' j * unitFrequencyPhase (αd * t j ^ d) := by
    rw [hpoints, Finset.sum_map]
    rfl
  have hlargeRange : A ≤
      ‖∑ j ∈ Finset.range L,
        f' j * unitFrequencyPhase (αd * t j ^ d)‖ := by
    rw [← hsum]
    exact hlarge
  have hLpos : 0 < L := by
    by_contra hnot
    have hLzero : L = 0 := by omega
    rw [hLzero] at hlargeRange
    simp at hlargeRange
    linarith
  have hvariation : ∀ θ : ℝ,
      |θ| ≤ R / ((r : ℝ) * (N : ℝ) ^ d) →
        ‖unitFrequencyPhase (θ * t (L - 1) ^ d)‖ +
          ∑ i ∈ Finset.range (L - 1),
            ‖unitFrequencyPhase (θ * t (i + 1) ^ d) -
              unitFrequencyPhase (θ * t i ^ d)‖ ≤ 1 + 8 * R := by
    intro θ hθ
    have hTVθ := hTV θ hθ
    have hbudget := scalarWeyl_IcoVariation_to_rangeBudget
      lo hi d L (by rfl) hLpos θ (1 + 8 * R) hTVθ
    simpa [t, e, scalarWeyl_intervalIndexEmbedding] using hbudget
  obtain ⟨a, k, hk, happrox, hprefix⟩ :=
    scalarWeyl_topCorrection_initialPrefix
      hr hN hR hA hdist t f' hlargeRange hvariation
  have hprefixPoints :
      Finset.Ico lo (lo + ((k + 1 : ℕ) : ℤ)) =
        (Finset.range (k + 1)).map e.toEmbedding := by
    rw [show e.toEmbedding =
        Nat.castEmbedding.trans (addLeftEmbedding lo) by
          simpa [e] using scalarWeyl_intervalIndexEmbedding_toEmbedding lo]
    simpa using Int.Ico_eq_finset_map lo (lo + ((k + 1 : ℕ) : ℤ))
  have hrangeSubset : Finset.range (k + 1) ⊆ Finset.range L := by
    intro j hj
    apply Finset.mem_range.mpr
    exact lt_of_lt_of_le (Finset.mem_range.mp hj) (by omega)
  have hprefixSubset :
      Finset.Ico lo (lo + ((k + 1 : ℕ) : ℤ)) ⊆ Finset.Ico lo hi := by
    rw [hprefixPoints, hpoints]
    exact (Finset.map_subset_map).2 hrangeSubset
  have hprefixSum :
      (∑ n ∈ Finset.Ico lo (lo + ((k + 1 : ℕ) : ℤ)),
        f n * unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * (n : ℝ) ^ d)) =
        ∑ j ∈ Finset.range (k + 1),
          f' j * unitFrequencyPhase (((a : ℝ) / (r : ℝ)) * t j ^ d) := by
    rw [hprefixPoints, Finset.sum_map]
    rfl
  refine ⟨a, k, hk, hprefixSubset, happrox, ?_⟩
  rw [hprefixSum]
  exact hprefix

end FractionalPrimes.Literature.Polynomial

end
