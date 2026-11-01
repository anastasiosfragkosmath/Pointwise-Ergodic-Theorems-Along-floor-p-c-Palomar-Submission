module

public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalAndTV
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Data.List.Sort

/-!
# C¹ calculus bound for inhomogeneous total variation

This file formalizes the final clause of `lu:tv-calculus` for integer points
in a real compact interval, with the existing inhomogeneous variation.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open MeasureTheory Set

noncomputable section

private theorem list_foldl_max_le_iff (l : List ℝ) (b c : ℝ) :
    l.foldl max b ≤ c ↔ b ≤ c ∧ ∀ x ∈ l, x ≤ c := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
      simp [List.foldl_cons, ih, and_assoc, and_left_comm, and_comm]

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

private def listAdjacentIntervalIntegral (F : ℝ → ℝ) : List ℝ → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: xs => (∫ t in a..b, F t) + listAdjacentIntervalIntegral F (b :: xs)

private def listPartitionIntervalIntegral (F : ℝ → ℝ) (lo hi : ℝ) : List ℝ → ℝ
  | [] => ∫ t in lo..hi, F t
  | a :: xs => (∫ t in lo..a, F t) + listPartitionIntervalIntegral F a hi xs

private theorem listAdjacentIntervalIntegral_eq_pair_sum (F : ℝ → ℝ) (l : List ℝ) :
    listAdjacentIntervalIntegral F l =
      (l.consecutivePairs.map fun p => ∫ t in p.1..p.2, F t).sum := by
  induction l with
  | nil => simp [listAdjacentIntervalIntegral, List.consecutivePairs]
  | cons a l ih =>
      cases l with
      | nil => simp [listAdjacentIntervalIntegral, List.consecutivePairs]
      | cons b bs =>
          simp [listAdjacentIntervalIntegral, List.consecutivePairs, ih]

private theorem consecutivePairs_cast (l : List ℤ) :
    (l.map fun n : ℤ => (n : ℝ)).consecutivePairs =
      l.consecutivePairs.map fun p => ((p.1 : ℝ), (p.2 : ℝ)) := by
  induction l with
  | nil => simp [List.consecutivePairs]
  | cons a l ih =>
      cases l with
      | nil => simp [List.consecutivePairs]
      | cons b bs =>
          simpa [List.consecutivePairs, List.zip_cons_cons] using
            congrArg (List.cons ((a : ℝ), (b : ℝ))) ih

private theorem consecutivePairs_order {α : Type*} [Preorder α] (l : List α)
    (hsorted : l.SortedLE) : ∀ p ∈ l.consecutivePairs, p.1 ≤ p.2 := by
  induction l with
  | nil => intro p hp; simp [List.consecutivePairs] at hp
  | cons a l ih =>
      cases l with
      | nil => intro p hp; simp [List.consecutivePairs] at hp
      | cons b bs =>
          intro p hp
          have hab : a ≤ b := hsorted.pairwise.rel_head_tail (by simp)
          have hp' : p ∈ (a, b) :: ((b :: bs).zip bs) := by
            simpa [List.consecutivePairs] using hp
          rcases List.mem_cons.mp hp' with heq | htail
          · subst p
            exact hab
          · exact ih hsorted.pairwise.tail.sortedLE p htail

private theorem listPartitionIntervalIntegral_eq (F : ℝ → ℝ) {u v lo hi : ℝ}
    (hcont : ContinuousOn F (Set.Icc u v))
    (hulo : u ≤ lo) (hlohi : lo ≤ hi) (hhiv : hi ≤ v)
    (l : List ℝ) (hsorted : l.SortedLE)
    (hwithin : ∀ x ∈ l, x ∈ Set.Icc lo hi) :
    listPartitionIntervalIntegral F lo hi l = ∫ t in lo..hi, F t := by
  induction l generalizing lo hulo hlohi with
  | nil => simp [listPartitionIntervalIntegral]
  | cons a l ih =>
      have ha := hwithin a (by simp)
      have htailSorted : l.SortedLE := hsorted.pairwise.tail.sortedLE
      have htailWithin : ∀ x ∈ l, x ∈ Set.Icc a hi := by
        intro x hx
        have hax : a ≤ x := hsorted.pairwise.rel_head_tail (by simpa using hx)
        exact ⟨hax, (hwithin x (by simp [hx])).2⟩
      have h1 : IntervalIntegrable F MeasureTheory.volume lo a :=
        (hcont.mono (Set.Icc_subset_Icc hulo (le_trans ha.2 hhiv))).intervalIntegrable_of_Icc
          ha.1
      have h2 : IntervalIntegrable F MeasureTheory.volume a hi :=
        (hcont.mono (Set.Icc_subset_Icc (le_trans hulo ha.1) hhiv)).intervalIntegrable_of_Icc ha.2
      calc
        (∫ t in lo..a, F t) + listPartitionIntervalIntegral F a hi l =
            (∫ t in lo..a, F t) + ∫ t in a..hi, F t := by
              rw [ih (lo := a) (le_trans hulo ha.1) ha.2 htailSorted htailWithin]
        _ = ∫ t in lo..hi, F t := intervalIntegral.integral_add_adjacent_intervals h1 h2

private theorem listAdjacentIntervalIntegral_le_partition (F : ℝ → ℝ) {u v lo hi : ℝ}
    (hNonneg : ∀ x ∈ Set.Icc u v, 0 ≤ F x)
    (hulo : u ≤ lo) (hlohi : lo ≤ hi) (hhiv : hi ≤ v)
    (l : List ℝ) (hsorted : l.SortedLE)
    (hwithin : ∀ x ∈ l, x ∈ Set.Icc lo hi) :
    listAdjacentIntervalIntegral F l ≤ listPartitionIntervalIntegral F lo hi l := by
  induction l generalizing lo hulo hlohi with
  | nil =>
      simp only [listAdjacentIntervalIntegral, listPartitionIntervalIntegral]
      exact intervalIntegral.integral_nonneg hlohi fun x hx =>
        hNonneg x ⟨le_trans hulo hx.1, le_trans hx.2 hhiv⟩
  | cons a l ih =>
      have ha := hwithin a (by simp)
      have htailSorted : l.SortedLE := hsorted.pairwise.tail.sortedLE
      have htailWithin : ∀ x ∈ l, x ∈ Set.Icc a hi := by
        intro x hx
        have hax : a ≤ x := hsorted.pairwise.rel_head_tail (by simpa using hx)
        exact ⟨hax, (hwithin x (by simp [hx])).2⟩
      cases l with
      | nil =>
          simp only [listAdjacentIntervalIntegral, listPartitionIntervalIntegral]
          apply add_nonneg
          · exact intervalIntegral.integral_nonneg ha.1 fun x hx =>
              hNonneg x ⟨le_trans hulo hx.1, le_trans hx.2 (le_trans ha.2 hhiv)⟩
          · exact intervalIntegral.integral_nonneg ha.2 fun x hx =>
              hNonneg x ⟨le_trans hulo (le_trans ha.1 hx.1), le_trans hx.2 hhiv⟩
      | cons b bs =>
          have hab : a ≤ b := hsorted.pairwise.rel_head_tail (by simp)
          have htailSorted' : (b :: bs).SortedLE := htailSorted
          have htailWithin' : ∀ x ∈ b :: bs, x ∈ Set.Icc b hi := by
            intro x hx
            have hbx : b ≤ x := by
              rcases List.mem_cons.mp hx with rfl | hx
              · rfl
              · exact htailSorted'.pairwise.rel_head_tail hx
            exact ⟨hbx, (hwithin x (by simp [hx])).2⟩
          have htail := ih (lo := b) (le_trans hulo (le_trans ha.1 hab))
            (by
              have hb := hwithin b (by simp)
              exact hb.2)
            htailSorted' htailWithin'
          simp only [listAdjacentIntervalIntegral, listPartitionIntervalIntegral]
          have hleft : 0 ≤ ∫ t in lo..a, F t :=
            intervalIntegral.integral_nonneg ha.1 fun x hx =>
              hNonneg x ⟨le_trans hulo hx.1, le_trans hx.2 (le_trans ha.2 hhiv)⟩
          calc
            (∫ t in a..b, F t) + listAdjacentIntervalIntegral F (b :: bs) ≤
                (∫ t in a..b, F t) + listPartitionIntervalIntegral F b hi (b :: bs) :=
              add_le_add_right htail _
            _ ≤ (∫ t in lo..a, F t) +
                ((∫ t in a..b, F t) + listPartitionIntervalIntegral F b hi (b :: bs)) :=
              le_add_of_nonneg_left hleft
            _ = listPartitionIntervalIntegral F lo hi (a :: b :: bs) := by
              simp [listPartitionIntervalIntegral]

private theorem listAdjacentIntervalIntegral_le (F : ℝ → ℝ) {u v : ℝ}
    (huv : u ≤ v) (hNonneg : ∀ x ∈ Set.Icc u v, 0 ≤ F x)
    (hcont : ContinuousOn F (Set.Icc u v)) (l : List ℝ) (hsorted : l.SortedLE)
    (hwithin : ∀ x ∈ l, x ∈ Set.Icc u v) :
    listAdjacentIntervalIntegral F l ≤ ∫ t in u..v, F t := by
  calc
    listAdjacentIntervalIntegral F l ≤ listPartitionIntervalIntegral F u v l :=
      listAdjacentIntervalIntegral_le_partition F hNonneg le_rfl huv le_rfl l hsorted hwithin
    _ = ∫ t in u..v, F t := listPartitionIntervalIntegral_eq F hcont le_rfl huv le_rfl l hsorted hwithin

private theorem integral_norm_derivWithin_eq (g : ℝ → ℂ) {u v a b : ℝ}
    (hua : u ≤ a) (hab : a ≤ b) (hbv : b ≤ v) :
    (∫ t in a..b, ‖derivWithin g (Set.Icc a b) t‖) =
      ∫ t in a..b, ‖derivWithin g (Set.Icc u v) t‖ := by
  by_cases hab' : a = b
  · subst b
    simp
  have hablt : a < b := lt_of_le_of_ne hab hab'
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  apply MeasureTheory.integral_congr_ae
  rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have hlocal : t ∈ Set.Ioo a b := ht
  have houter : t ∈ Set.Ioo u v := ⟨lt_of_le_of_lt hua hlocal.1,
    lt_of_lt_of_le hlocal.2 hbv⟩
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hlocal.1 hlocal.2),
    derivWithin_of_mem_nhds (Icc_mem_nhds houter.1 houter.2)]

private theorem norm_sub_le_integral_norm_derivWithin (g : ℝ → ℂ) {u v a b : ℝ}
    (hg : ContDiffOn ℝ 1 g (Set.Icc u v))
    (hua : u ≤ a) (hab : a ≤ b) (hbv : b ≤ v) :
    ‖g b - g a‖ ≤ ∫ t in a..b, ‖derivWithin g (Set.Icc u v) t‖ := by
  have hsub : Set.Icc a b ⊆ Set.Icc u v := Set.Icc_subset_Icc hua hbv
  have hgab : ContDiffOn ℝ 1 g (Set.Icc a b) := hg.mono hsub
  have hftc := intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hgab hab
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (f := fun t => derivWithin g (Set.Icc a b) t) (μ := MeasureTheory.volume) hab
  rw [hftc] at hnorm
  exact hnorm.trans_eq (integral_norm_derivWithin_eq g hua hab hbv)

/-- The compact-interval norm supremum, represented using the conditionally
complete real supremum of the range. -/
def intervalNormSup (u v : ℝ) (g : ℝ → ℂ) : ℝ :=
  sSup (Set.range fun t : Set.Icc u v => ‖g (t : ℝ)‖)

private theorem intervalNormSup_bddAbove {u v : ℝ} (g : ℝ → ℂ)
    (hg : ContinuousOn g (Set.Icc u v)) :
    BddAbove (Set.range fun t : Set.Icc u v => ‖g (t : ℝ)‖) := by
  have hnorm : ContinuousOn (fun t : ℝ => ‖g t‖) (Set.Icc u v) := hg.norm
  have himage : Set.range (fun t : Set.Icc u v => ‖g (t : ℝ)‖) =
      (fun t : ℝ => ‖g t‖) '' Set.Icc u v := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  rw [himage]
  exact isCompact_Icc.bddAbove_image hnorm

private theorem norm_le_intervalNormSup {u v : ℝ} (g : ℝ → ℂ)
    (hg : ContinuousOn g (Set.Icc u v)) {t : ℝ} (ht : t ∈ Set.Icc u v) :
    ‖g t‖ ≤ intervalNormSup u v g := by
  unfold intervalNormSup
  apply le_csSup (intervalNormSup_bddAbove g hg)
  exact ⟨⟨t, ht⟩, rfl⟩

private theorem intervalNormSup_nonneg {u v : ℝ} (huv : u ≤ v) (g : ℝ → ℂ)
    (hg : ContinuousOn g (Set.Icc u v)) : 0 ≤ intervalNormSup u v g := by
  have hu : u ∈ Set.Icc u v := ⟨le_rfl, huv⟩
  exact (norm_nonneg _).trans (norm_le_intervalNormSup g hg hu)

private theorem listSupNorm_le_intervalNormSup {u v : ℝ} (huv : u ≤ v) (g : ℝ → ℂ)
    (hg : ContinuousOn g (Set.Icc u v))
    (l : List ℤ) (hwithin : ∀ n ∈ l, (n : ℝ) ∈ Set.Icc u v) :
    listSupNorm (fun n : ℤ => g n) l ≤ intervalNormSup u v g := by
  unfold listSupNorm
  apply (list_foldl_max_le_iff _ _ _).2
  refine ⟨intervalNormSup_nonneg huv g hg, ?_⟩
  intro x hx
  rcases List.mem_map.mp hx with ⟨n, hn, rfl⟩
  exact norm_le_intervalNormSup g hg (hwithin n hn)

private theorem finite_variation_c1_bound (P : Finset ℤ) {u v : ℝ}
    (huv : u ≤ v) (g : ℝ → ℂ) (hg : ContDiffOn ℝ 1 g (Set.Icc u v))
    (hP : ∀ n ∈ P, (n : ℝ) ∈ Set.Icc u v) :
    finiteOrderedTotalVariation P (fun n : ℤ => g n) ≤
      intervalNormSup u v g + ∫ t in u..v, ‖derivWithin g (Set.Icc u v) t‖ := by
  classical
  by_cases huv' : u = v
  · subst v
    have hcard : P.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' : (a : ℝ) = u := le_antisymm (hP a ha).2 (hP a ha).1
      have hb' : (b : ℝ) = u := le_antisymm (hP b hb).2 (hP b hb).1
      exact_mod_cast ha'.trans hb'.symm
    have hlen : (P.sort (· ≤ ·)).length ≤ 1 := by
      rw [Finset.length_sort]
      exact hcard
    have hvariation : listAdjacentVariation (fun n : ℤ => g n) (P.sort (· ≤ ·)) = 0 := by
      unfold listAdjacentVariation
      cases hs : P.sort (· ≤ ·) with
      | nil => simp [List.consecutivePairs]
      | cons a rest =>
          cases rest with
          | nil => simp [List.consecutivePairs]
          | cons b bs =>
              have hlen' : (a :: b :: bs).length ≤ 1 := by
                rw [← hs, Finset.length_sort]
                exact hcard
              simp at hlen'
    have hsup : listSupNorm (fun n : ℤ => g n) (P.sort (· ≤ ·)) ≤
        intervalNormSup u u g := by
      apply listSupNorm_le_intervalNormSup le_rfl g hg.continuousOn
      intro n hn
      exact hP n ((Finset.mem_sort (s := P) (r := (· ≤ ·))).1 hn)
    unfold finiteOrderedTotalVariation
    simpa [hvariation] using add_le_add_right hsup 0
  · have huvlt : u < v := lt_of_le_of_ne huv huv'
    let B : ℝ → ℝ := fun t => ‖derivWithin g (Set.Icc u v) t‖
    have hBcont : ContinuousOn B (Set.Icc u v) := by
      exact (hg.continuousOn_derivWithin (uniqueDiffOn_Icc huvlt) (by norm_num)).norm
    have hBnonneg : ∀ t ∈ Set.Icc u v, 0 ≤ B t := fun t _ => norm_nonneg _
    let ns := P.sort (· ≤ ·)
    have hnsSorted : ns.SortedLE := (Finset.pairwise_sort P (· ≤ ·)).sortedLE
    have hnsWithin : ∀ n ∈ ns, (n : ℝ) ∈ Set.Icc u v := by
      intro n hn
      exact hP n ((Finset.mem_sort (s := P) (r := (· ≤ ·))).1 hn)
    have hrealSorted : (ns.map fun n : ℤ => (n : ℝ)).SortedLE := by
      apply List.sortedLE_iff_pairwise.mpr
      rw [List.pairwise_map]
      exact hnsSorted.pairwise.imp fun h => Int.cast_le.mpr h
    have hrealWithin : ∀ x ∈ ns.map fun n : ℤ => (n : ℝ), x ∈ Set.Icc u v := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨n, hn, rfl⟩
      exact hnsWithin n hn
    have hIntegralSum :
        listAdjacentIntervalIntegral B (ns.map fun n : ℤ => (n : ℝ)) ≤
          ∫ t in u..v, B t :=
      listAdjacentIntervalIntegral_le B huv hBnonneg hBcont
        (ns.map fun n : ℤ => (n : ℝ)) hrealSorted hrealWithin
    have hVariationSum :
        listAdjacentVariation (fun n : ℤ => g n) ns ≤
          listAdjacentIntervalIntegral B (ns.map fun n : ℤ => (n : ℝ)) := by
      rw [listAdjacentIntervalIntegral_eq_pair_sum, consecutivePairs_cast]
      unfold listAdjacentVariation
      simp only [List.map_map]
      apply list_sum_map_le
      intro p hp
      have hp' : p ∈ ns.zip ns.tail := by simpa [List.consecutivePairs] using hp
      have hfst : p.1 ∈ ns := (List.of_mem_zip hp').1
      have hsndTail := (List.of_mem_zip hp').2
      have hsnd : p.2 ∈ ns := List.mem_of_mem_tail hsndTail
      have horder : p.1 ≤ p.2 := consecutivePairs_order ns hnsSorted p hp'
      have hpa := hnsWithin p.1 hfst
      have hpb := hnsWithin p.2 hsnd
      simpa [B] using norm_sub_le_integral_norm_derivWithin g hg
        hpa.1 (by exact_mod_cast horder) hpb.2
    have hSup := listSupNorm_le_intervalNormSup huv g hg.continuousOn ns hnsWithin
    unfold finiteOrderedTotalVariation
    have hsum := hVariationSum.trans hIntegralSum
    exact add_le_add hSup hsum

/-- C¹ variation estimate on an arbitrary ordered subset of the integer
points in `[u,v]`.  The left side is the extended total variation, as defined
for arbitrary sets in `lu:ap-tv`; the bounded interval makes its value finite. -/
theorem orderedTotalVariation_le_sup_add_integral {u v : ℝ} (huv : u ≤ v)
    (g : ℝ → ℂ) (hg : ContDiffOn ℝ 1 g (Set.Icc u v)) (P : Set ℤ)
    (hP : ∀ n ∈ P, (n : ℝ) ∈ Set.Icc u v) :
    orderedTotalVariation P (fun n : ℤ => g n) ≤
      ENNReal.ofReal (intervalNormSup u v g +
        ∫ t in u..v, ‖derivWithin g (Set.Icc u v) t‖) := by
  unfold orderedTotalVariation
  apply iSup_le
  intro F
  have hF : ∀ n ∈ F.1, n ∈ P := F.2
  have hfinite := finite_variation_c1_bound F.1 huv g hg (fun n hn => hP n (hF n hn))
  exact ENNReal.ofReal_le_ofReal hfinite

end

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.orderedTotalVariation_le_sup_add_integral
