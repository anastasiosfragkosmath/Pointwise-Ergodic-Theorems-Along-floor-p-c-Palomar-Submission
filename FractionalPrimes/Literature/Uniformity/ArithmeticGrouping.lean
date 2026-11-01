module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity.Combinatorics

open scoped BigOperators
noncomputable section

/-- A finite indexed list of nonnegative weights with total mass one.  The
indices retain multiplicity when two weights happen to be equal. -/
structure GroupingPredicates (k : ℕ) where
  weight : Fin k → ℝ
  positive_length : 0 < k
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum_eq_one : ∑ i, weight i = 1

/-- The total weight assigned to a labelled set of indices. -/
def subsetWeightSum {k : ℕ} (w : GroupingPredicates k)
    (s : Finset (Fin k)) : ℝ :=
  ∑ i ∈ s, w.weight i

namespace GroupingPredicates

/-- The type-I grouping predicate `I_θ`. -/
def I {k : ℕ} (w : GroupingPredicates k) (θ : ℝ) : Prop :=
  ∃ i : Fin k, 1 - θ ≤ w.weight i

/-- The type-I₂ grouping predicate `I2_θ`; the two indices are distinct. -/
def I2 {k : ℕ} (w : GroupingPredicates k) (θ : ℝ) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧
    (3 / 2 : ℝ) * (1 - θ) ≤ w.weight i + w.weight j

/-- The minor type-II grouping predicate `IImin_θ`.  The two labelled sets
are disjoint and partition the full index set; empty parts are permitted. -/
def IImin {k : ℕ} (w : GroupingPredicates k) (θ : ℝ) : Prop :=
  ∃ J J' : Finset (Fin k),
    Disjoint J J' ∧ J ∪ J' = Finset.univ ∧
      1 - θ ≤ subsetWeightSum w J ∧ subsetWeightSum w J ≤ θ ∧
      1 - θ ≤ subsetWeightSum w J' ∧ subsetWeightSum w J' ≤ θ

/-- The major type-II grouping predicate `IImaj_θ`.  The three labelled
sets are pairwise disjoint and partition the full index set. -/
def IImaj {k : ℕ} (w : GroupingPredicates k) (θ : ℝ) : Prop :=
  ∃ I J J' : Finset (Fin k),
    Disjoint I J ∧ Disjoint I J' ∧ Disjoint J J' ∧
      I ∪ J ∪ J' = Finset.univ ∧
      2 * θ - 1 ≤ subsetWeightSum w I ∧
      subsetWeightSum w I ≤ 4 * θ - 2 ∧
      |subsetWeightSum w J - subsetWeightSum w J'| ≤ 2 * θ - 1

end GroupingPredicates

/-- Assign the next weight to a group with smaller current total, choosing
the first group in a tie. -/
def balanceStep (p : ℝ × ℝ) (w : ℝ) : ℝ × ℝ :=
  if p.1 ≤ p.2 then (p.1 + w, p.2) else (p.1, p.2 + w)

/-- Process a finite list of weights by repeatedly applying `balanceStep`. -/
def greedyBalance : List ℝ → ℝ × ℝ → ℝ × ℝ
  | [], p => p
  | w :: ws, p => greedyBalance ws (balanceStep p w)

private theorem balanceStep_total (p : ℝ × ℝ) (w : ℝ) :
    (balanceStep p w).1 + (balanceStep p w).2 = p.1 + p.2 + w := by
  by_cases h : p.1 ≤ p.2 <;> simp [balanceStep, h] <;> ring

private theorem balanceStep_gap {p : ℝ × ℝ} {w d : ℝ}
    (_hd : 0 ≤ d) (hgap : |p.1 - p.2| ≤ d)
    (hw0 : 0 ≤ w) (hwd : w ≤ d) :
    |(balanceStep p w).1 - (balanceStep p w).2| ≤ d := by
  by_cases h : p.1 ≤ p.2
  · have hdiff : 0 ≤ p.2 - p.1 ∧ p.2 - p.1 ≤ d := by
      have habs := abs_le.mp hgap
      constructor <;> linarith
    rw [abs_le]
    simp [balanceStep, h]
    constructor <;> linarith
  · have hdiff : 0 ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ d := by
      have habs := abs_le.mp hgap
      constructor <;> linarith
    rw [abs_le]
    simp [balanceStep, h]
    constructor <;> linarith

private theorem greedyBalance_total (weights : List ℝ) (p : ℝ × ℝ) :
    (greedyBalance weights p).1 + (greedyBalance weights p).2 =
      p.1 + p.2 + weights.sum := by
  induction weights generalizing p with
  | nil => simp [greedyBalance]
  | cons w ws ih =>
      simp only [greedyBalance, List.sum_cons]
      rw [ih (balanceStep p w), balanceStep_total]
      ring

private theorem greedyBalance_gap (weights : List ℝ) (p : ℝ × ℝ) (d : ℝ)
    (hd : 0 ≤ d) (hgap : |p.1 - p.2| ≤ d)
    (hw : ∀ w ∈ weights, 0 ≤ w ∧ w ≤ d) :
    |(greedyBalance weights p).1 - (greedyBalance weights p).2| ≤ d := by
  induction weights generalizing p with
  | nil => simpa [greedyBalance] using hgap
  | cons w ws ih =>
      have hwstep := hw w (by simp)
      have htail (x : ℝ) (hx : x ∈ ws) : 0 ≤ x ∧ x ≤ d :=
        hw x (by simp [hx])
      simpa only [greedyBalance] using
        ih (balanceStep p w)
          (balanceStep_gap hd hgap hwstep.1 hwstep.2) htail

/-- Split a list immediately after the first weight that reaches the
threshold when added to the running total.  If the threshold has not yet
been reached, the algorithm continues through the list. -/
def firstCrossingSplit (a s : ℝ) : List ℝ → List ℝ × List ℝ
  | [] => ([], [])
  | w :: ws =>
      if a ≤ s + w then ([w], ws)
      else
        let tail := firstCrossingSplit a (s + w) ws
        (w :: tail.1, tail.2)

private theorem firstCrossingSplit_spec (weights : List ℝ) (s a d : ℝ)
    (hs : s < a) (htotal : a ≤ s + weights.sum)
    (hw : ∀ x ∈ weights, 0 ≤ x ∧ x ≤ d) :
    weights = (firstCrossingSplit a s weights).1 ++
        (firstCrossingSplit a s weights).2 ∧
      a ≤ s + (firstCrossingSplit a s weights).1.sum ∧
      s + (firstCrossingSplit a s weights).1.sum ≤ a + d := by
  induction weights generalizing s with
  | nil => simp at htotal; linarith
  | cons w ws ih =>
      have hw0 := hw w (by simp)
      by_cases hcross : a ≤ s + w
      · have hupper : s + w ≤ a + d := by linarith
        simp [firstCrossingSplit, hcross, hupper]
      · have hsw : s + w < a := lt_of_not_ge hcross
        have htailTotal : a ≤ (s + w) + ws.sum := by
          have h := htotal
          simp only [List.sum_cons] at h
          linarith
        have htailWeight (x : ℝ) (hx : x ∈ ws) : 0 ≤ x ∧ x ≤ d :=
          hw x (by simp [hx])
        have hrec := ih (s + w) hsw htailTotal htailWeight
        simp only [firstCrossingSplit, if_neg hcross]
        rcases hrec with ⟨hdecomp, hlow, hhigh⟩
        constructor
        · simpa only [List.cons_append] using congrArg (List.cons w) hdecomp
        · constructor
          · simpa only [List.sum_cons, add_assoc] using hlow
          · simpa only [List.sum_cons, add_assoc] using hhigh

/-- Balancing lemma for a finite list, with the first threshold crossing
retained as a prefix.  The two running group totals stay within `d`, and
the stopped total belongs to `[a, a + d]`. -/
theorem balanceFiniteList (u v a d : ℝ) (weights : List ℝ)
    (hd : 0 ≤ d) (hgap : |u - v| ≤ d)
    (hw : ∀ w ∈ weights, 0 ≤ w ∧ w ≤ d)
    (hinitial : u + v < a)
    (htotal : a ≤ u + v + weights.sum) :
    ∃ pre suffix : List ℝ,
      weights = pre ++ suffix ∧
      a ≤ (greedyBalance pre (u, v)).1 +
        (greedyBalance pre (u, v)).2 ∧
      (greedyBalance pre (u, v)).1 +
        (greedyBalance pre (u, v)).2 ≤ a + d ∧
      |(greedyBalance pre (u, v)).1 -
        (greedyBalance pre (u, v)).2| ≤ d := by
  let split := firstCrossingSplit a (u + v) weights
  have hsplit := firstCrossingSplit_spec weights (u + v) a d
    hinitial (by simpa [add_assoc] using htotal) hw
  refine ⟨split.1, split.2, ?_, ?_, ?_, ?_⟩
  · exact hsplit.1
  · rw [greedyBalance_total]
    exact hsplit.2.1
  · rw [greedyBalance_total]
    exact hsplit.2.2
  · apply greedyBalance_gap split.1 (u, v) d hd hgap
    intro x hx
    apply hw x
    rw [hsplit.1]
    exact List.mem_append_left _ hx

/-- A label-preserving result of the same greedy balancing rule. -/
structure GreedyAssignment (α : Type*) where
  leftItems : List α
  rightItems : List α
  leftTotal : ℝ
  rightTotal : ℝ

/-- Assign a finite indexed list to two labelled groups, with the current
smaller-total rule and the first group chosen at a tie. -/
def greedyAssignment {α : Type*} (weight : α → ℝ) :
    List α → ℝ × ℝ → GreedyAssignment α
  | [], p => ⟨[], [], p.1, p.2⟩
  | x :: xs, p =>
      let tail := greedyAssignment weight xs (balanceStep p (weight x))
      if p.1 ≤ p.2 then
        { tail with leftItems := x :: tail.leftItems }
      else
        { tail with rightItems := x :: tail.rightItems }

private theorem greedyAssignment_totals_eq {α : Type*} (weight : α → ℝ)
    (items : List α) (p : ℝ × ℝ) :
    (greedyAssignment weight items p).leftTotal =
        (greedyBalance (items.map weight) p).1 ∧
      (greedyAssignment weight items p).rightTotal =
        (greedyBalance (items.map weight) p).2 := by
  induction items generalizing p with
  | nil => simp [greedyAssignment, greedyBalance]
  | cons x xs ih =>
      by_cases h : p.1 ≤ p.2
      · simpa [greedyAssignment, greedyBalance, balanceStep, h] using
          ih (balanceStep p (weight x))
      · simpa [greedyAssignment, greedyBalance, balanceStep, h] using
          ih (balanceStep p (weight x))

private theorem greedyAssignment_item_weights {α : Type*} (weight : α → ℝ)
    (items : List α) (p : ℝ × ℝ) :
    (greedyAssignment weight items p).leftTotal =
        p.1 + ((greedyAssignment weight items p).leftItems.map weight).sum ∧
      (greedyAssignment weight items p).rightTotal =
        p.2 + ((greedyAssignment weight items p).rightItems.map weight).sum := by
  induction items generalizing p with
  | nil => simp [greedyAssignment]
  | cons x xs ih =>
      by_cases h : p.1 ≤ p.2
      · have htail := ih (balanceStep p (weight x))
        simp only [greedyAssignment, balanceStep, h, ite_true] at htail ⊢
        rcases htail with ⟨hleft, hright⟩
        constructor
        · simpa [List.map_cons, List.sum_cons, add_assoc] using hleft
        · simpa using hright
      · have htail := ih (balanceStep p (weight x))
        simp only [greedyAssignment, balanceStep, h, ite_false] at htail ⊢
        rcases htail with ⟨hleft, hright⟩
        constructor
        · simpa using hleft
        · simpa [List.map_cons, List.sum_cons, add_assoc] using hright

private theorem greedyAssignment_perm {α : Type*} [DecidableEq α]
    (weight : α → ℝ) (items : List α) (p : ℝ × ℝ) :
    List.Perm items
      ((greedyAssignment weight items p).leftItems ++
        (greedyAssignment weight items p).rightItems) := by
  induction items generalizing p with
  | nil => simp [greedyAssignment]
  | cons x xs ih =>
      by_cases h : p.1 ≤ p.2
      · have htail := ih (balanceStep p (weight x))
        simpa [greedyAssignment, balanceStep, h, List.cons_append] using
          htail.cons x
      · have htail := ih (balanceStep p (weight x))
        let l := (greedyAssignment weight xs (balanceStep p (weight x))).leftItems
        let r := (greedyAssignment weight xs (balanceStep p (weight x))).rightItems
        have hmove : List.Perm (x :: (l ++ r)) (l ++ x :: r) := by
          have hs : List.Perm ([x] ++ l) (l ++ [x]) := List.perm_append_comm
          simpa [List.cons_append, List.append_assoc] using hs.append_right r
        have hfirst : List.Perm (x :: xs) (x :: (l ++ r)) := by
          simpa [l, r] using htail.cons x
        have hcomp := hfirst.trans hmove
        simpa [greedyAssignment, balanceStep, h, l, r] using hcomp

/-- A labelled-list form of the finite balancing lemma. It additionally
returns the two actual groups, retaining distinct indices with equal weights. -/
theorem balanceFiniteIndexedList {α : Type*} [DecidableEq α]
    (weight : α → ℝ) (u v a d : ℝ) (items : List α)
    (hd : 0 ≤ d) (hgap : |u - v| ≤ d)
    (hw : ∀ x ∈ items, 0 ≤ weight x ∧ weight x ≤ d)
    (hinitial : u + v < a)
    (htotal : a ≤ u + v + (items.map weight).sum) :
    ∃ pre suffix : List α,
      items = pre ++ suffix ∧
      a ≤ (greedyAssignment weight pre (u, v)).leftTotal +
        (greedyAssignment weight pre (u, v)).rightTotal ∧
      (greedyAssignment weight pre (u, v)).leftTotal +
        (greedyAssignment weight pre (u, v)).rightTotal ≤ a + d ∧
      |(greedyAssignment weight pre (u, v)).leftTotal -
        (greedyAssignment weight pre (u, v)).rightTotal| ≤ d := by
  let split := firstCrossingSplit a (u + v) (items.map weight)
  have hsplit := firstCrossingSplit_spec (items.map weight) (u + v) a d
    hinitial (by simpa [add_assoc] using htotal)
    (by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact hw x hx)
  let pre := items.take split.1.length
  let suffix := items.drop split.1.length
  have hsplitMap : (items.map weight).take split.1.length = split.1 := by
    rw [hsplit.1]
    calc
      (split.1 ++ split.2).take split.1.length =
          split.1.take split.1.length :=
        List.take_append_of_le_length (by exact le_rfl)
      _ = split.1 := List.take_length
  have hitems : items = pre ++ suffix := by
    simp [pre, suffix, List.take_append_drop]
  have htotalBounds :
      a ≤ u + v + (pre.map weight).sum ∧
        u + v + (pre.map weight).sum ≤ a + d := by
    have hpreMap : (pre.map weight).sum = split.1.sum := by
      dsimp [pre]
      rw [List.map_take, hsplitMap]
    simpa [hpreMap] using hsplit.2
  have hweight (x : α) (hx : x ∈ pre) :
      0 ≤ weight x ∧ weight x ≤ d := by
    apply hw x
    have hsub : items.take split.1.length ⊆ items :=
      (List.take_sublist split.1.length items).subset
    simpa [pre] using hsub hx
  have hassign := greedyAssignment_totals_eq weight pre (u, v)
  have hgapAssign :
      |(greedyAssignment weight pre (u, v)).leftTotal -
          (greedyAssignment weight pre (u, v)).rightTotal| ≤ d := by
    rw [hassign.1, hassign.2]
    apply greedyBalance_gap (pre.map weight) (u, v) d hd hgap
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact hweight x hx
  have htotAssign :
      (greedyAssignment weight pre (u, v)).leftTotal +
          (greedyAssignment weight pre (u, v)).rightTotal =
        u + v + (pre.map weight).sum := by
    rw [hassign.1, hassign.2]
    exact greedyBalance_total (pre.map weight) (u, v)
  refine ⟨pre, suffix, hitems, ?_, ?_, hgapAssign⟩
  · rw [htotAssign]
    exact htotalBounds.1
  · rw [htotAssign]
    exact htotalBounds.2

/-- An indexed list of all weights in decreasing order. The merge sort keeps
equal weights at distinct indices rather than collapsing them. -/
private noncomputable def sortedGroupingIndices {k : ℕ}
    (w : GroupingPredicates k) : List (Fin k) :=
  ((Finset.univ : Finset (Fin k)).toList).mergeSort
    (fun i j => w.weight j ≤ w.weight i)

private theorem sortedGroupingIndices_sorted {k : ℕ}
    (w : GroupingPredicates k) :
    (sortedGroupingIndices w).Pairwise (fun i j => w.weight j ≤ w.weight i) := by
  let r : Fin k → Fin k → Prop := fun i j => w.weight j ≤ w.weight i
  letI : IsTrans (Fin k) r := ⟨by
    intro i j l hij hjl
    exact le_trans hjl hij⟩
  letI : @Std.Total (Fin k) r := ⟨by
    intro i j
    rcases le_total (w.weight i) (w.weight j) with hij | hji
    · exact Or.inr hij
    · exact Or.inl hji⟩
  simpa [sortedGroupingIndices, r] using
    (List.pairwise_mergeSort' r ((Finset.univ : Finset (Fin k)).toList))

private theorem sortedGroupingIndices_perm {k : ℕ}
    (w : GroupingPredicates k) :
    List.Perm (sortedGroupingIndices w)
      ((Finset.univ : Finset (Fin k)).toList) := by
  exact List.mergeSort_perm _ _

private theorem sortedGroupingIndices_nodup {k : ℕ}
    (w : GroupingPredicates k) : (sortedGroupingIndices w).Nodup := by
  exact (sortedGroupingIndices_perm w).nodup_iff.mpr
    (Finset.nodup_toList (Finset.univ : Finset (Fin k)))

private theorem sortedGroupingIndices_toFinset {k : ℕ}
    (w : GroupingPredicates k) :
    (sortedGroupingIndices w).toFinset = (Finset.univ : Finset (Fin k)) := by
  ext i
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact (sortedGroupingIndices_perm w).symm.subset (by simp)

private theorem sortedGroupingIndices_length {k : ℕ}
    (w : GroupingPredicates k) : (sortedGroupingIndices w).length = k := by
  calc
    (sortedGroupingIndices w).length =
        ((Finset.univ : Finset (Fin k)).toList).length :=
      (sortedGroupingIndices_perm w).length_eq
    _ = k := by simp

private theorem listWeightSum_eq_subsetWeightSum {k : ℕ}
    (w : GroupingPredicates k) (l : List (Fin k)) (hl : l.Nodup) :
    (l.map w.weight).sum = subsetWeightSum w l.toFinset := by
  induction l with
  | nil => simp [subsetWeightSum]
  | cons i l ih =>
      rcases List.nodup_cons.mp hl with ⟨hi, hl⟩
      simp [subsetWeightSum, List.map_cons, List.sum_cons,
        Finset.sum_insert, hi, ih hl]

private theorem subsetWeightSum_univ {k : ℕ} (w : GroupingPredicates k) :
    subsetWeightSum w (Finset.univ : Finset (Fin k)) = 1 := by
  simpa [subsetWeightSum] using w.weight_sum_eq_one

private theorem subsetWeightSum_union_disjoint {k : ℕ}
    (w : GroupingPredicates k) {s t : Finset (Fin k)} (hst : Disjoint s t) :
    subsetWeightSum w (s ∪ t) = subsetWeightSum w s + subsetWeightSum w t := by
  simp [subsetWeightSum, Finset.sum_union hst]

private theorem subsetWeightSum_compl {k : ℕ} (w : GroupingPredicates k)
    (s : Finset (Fin k)) :
    subsetWeightSum w ((Finset.univ : Finset (Fin k)) \ s) =
      1 - subsetWeightSum w s := by
  have hdisj : Disjoint s ((Finset.univ : Finset (Fin k)) \ s) :=
    Finset.disjoint_left.mpr (by
      intro i his hcompl
      exact (Finset.mem_sdiff.mp hcompl).2 his)
  have hunion : s ∪ ((Finset.univ : Finset (Fin k)) \ s) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ s)
  have hsum : subsetWeightSum w s +
      subsetWeightSum w ((Finset.univ : Finset (Fin k)) \ s) = 1 := by
    have h := subsetWeightSum_union_disjoint w hdisj
    rw [hunion, subsetWeightSum_univ] at h
    exact h.symm
  linarith

/-- Take the longest initial segment whose accumulated weight stays below
the given threshold. The first omitted item, when present, would cross the
threshold strictly. -/
private def maximalPrefixBelow {α : Type*} (weight : α → ℝ) (a s : ℝ) :
    List α → List α × List α
  | [] => ([], [])
  | x :: xs =>
      if s + weight x ≤ a then
        let tail := maximalPrefixBelow weight a (s + weight x) xs
        (x :: tail.1, tail.2)
      else
        ([], x :: xs)

private theorem maximalPrefixBelow_spec {α : Type*} (weight : α → ℝ)
    (a s : ℝ) (items : List α) (hs : s ≤ a) :
    items = (maximalPrefixBelow weight a s items).1 ++
        (maximalPrefixBelow weight a s items).2 ∧
      s + ((maximalPrefixBelow weight a s items).1.map weight).sum ≤ a ∧
      ((maximalPrefixBelow weight a s items).2 = [] ∨
        ∃ x xs, (maximalPrefixBelow weight a s items).2 = x :: xs ∧
          a < s + ((maximalPrefixBelow weight a s items).1.map weight).sum +
            weight x) := by
  induction items generalizing s with
  | nil =>
      simp [maximalPrefixBelow, hs]
  | cons x xs ih =>
      by_cases hfit : s + weight x ≤ a
      · have hrec := ih (s := s + weight x) hfit
        simp only [maximalPrefixBelow, if_pos hfit]
        rcases hrec with ⟨hdecomp, hbound, hcross⟩
        refine ⟨?_, ?_, ?_⟩
        · calc
            x :: xs = x :: ((maximalPrefixBelow weight a (s + weight x) xs).1 ++
                (maximalPrefixBelow weight a (s + weight x) xs).2) :=
              congrArg (List.cons x) hdecomp
            _ = (x :: (maximalPrefixBelow weight a (s + weight x) xs).1) ++
                (maximalPrefixBelow weight a (s + weight x) xs).2 := by simp
        · simpa [List.map_cons, List.sum_cons, add_assoc] using hbound
        · rcases hcross with hnil | ⟨y, ys, htail, hcross⟩
          · exact Or.inl hnil
          · refine Or.inr ⟨y, ys, htail, ?_⟩
            simpa [List.map_cons, List.sum_cons, add_assoc] using hcross
      · have hcross : a < s + weight x := lt_of_not_ge hfit
        simp only [maximalPrefixBelow, if_neg hfit]
        exact ⟨by simp, by simpa using hs,
          Or.inr ⟨x, xs, rfl, by simpa using hcross⟩⟩

private theorem maximalPrefixBelow_cons_of_fit {α : Type*} (weight : α → ℝ)
    (a s : ℝ) (x : α) (xs : List α) (hfit : s + weight x ≤ a) :
    maximalPrefixBelow weight a s (x :: xs) =
      (x :: (maximalPrefixBelow weight a (s + weight x) xs).1,
        (maximalPrefixBelow weight a (s + weight x) xs).2) := by
  simp [maximalPrefixBelow, hfit]

/-- A permutation partition of a noduplicated list induces a disjoint
partition of its finite index set. -/
private theorem listPartitionToFinset {α : Type*} [DecidableEq α]
    (items left right : List α)
    (hperm : List.Perm items (left ++ right)) (hitems : items.Nodup) :
    left.Nodup ∧ right.Nodup ∧
      Disjoint left.toFinset right.toFinset ∧
      left.toFinset ∪ right.toFinset = items.toFinset := by
  have hconcat : (left ++ right).Nodup := hperm.nodup_iff.mp hitems
  have hparts := List.nodup_append'.mp hconcat
  refine ⟨hparts.1, hparts.2.1, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hxleft hxright
    have hne := (List.disjoint_iff_ne.mp hparts.2.2) x
      (List.mem_toFinset.mp hxleft) x (List.mem_toFinset.mp hxright)
    exact hne rfl
  · ext x
    simp only [Finset.mem_union, List.mem_toFinset]
    simpa [List.mem_append] using (hperm.mem_iff (a := x)).symm

/-- Complete two disjoint labelled groups by their complement. -/
private theorem complementPartition {α : Type*} [Fintype α] [DecidableEq α]
    (J J' : Finset α) :
    ∃ I : Finset α,
      I = Finset.univ \ (J ∪ J') ∧
        Disjoint I J ∧ Disjoint I J' ∧ I ∪ J ∪ J' = Finset.univ := by
  let I := Finset.univ \ (J ∪ J')
  have hIJ : Disjoint I J := by
    apply Finset.disjoint_left.mpr
    intro x hxI hxJ
    exact (Finset.mem_sdiff.mp hxI).2 (Finset.mem_union_left _ hxJ)
  have hIJ' : Disjoint I J' := by
    apply Finset.disjoint_left.mpr
    intro x hxI hxJ'
    exact (Finset.mem_sdiff.mp hxI).2 (Finset.mem_union_right _ hxJ')
  have hcover : I ∪ J ∪ J' = Finset.univ := by
    ext x
    simp [I]
  exact ⟨I, rfl, hIJ, hIJ', hcover⟩

private theorem majorFromTwoGroups {k : ℕ} (w : GroupingPredicates k)
    (J J' : Finset (Fin k)) (hJJ' : Disjoint J J')
    (hlow : (1 / 2 : ℝ) ≤ subsetWeightSum w J + subsetWeightSum w J')
    (hhigh : subsetWeightSum w J + subsetWeightSum w J' ≤ 3 / 4)
    (hgap : |subsetWeightSum w J - subsetWeightSum w J'| ≤ 1 / 4) :
    w.IImaj (5 / 8) := by
  obtain ⟨I, hIeq, hIJ, hIJ', hcover⟩ := complementPartition J J'
  have hsumI : subsetWeightSum w I =
      1 - (subsetWeightSum w J + subsetWeightSum w J') := by
    rw [hIeq, subsetWeightSum_compl,
      subsetWeightSum_union_disjoint w hJJ']
  refine ⟨I, J, J', hIJ, hIJ', hJJ', hcover, ?_, ?_, ?_⟩
  · rw [hsumI]
    norm_num
    linarith
  · rw [hsumI]
    norm_num
    linarith
  · norm_num at hgap ⊢
    exact hgap

/-- The minor grouping alternative for every `3/5 ≤ θ ≤ 1`. -/
theorem minorGrouping {k : ℕ} (w : GroupingPredicates k) (θ : ℝ)
    (hθlow : 3 / 5 ≤ θ) (hθhigh : θ ≤ 1) :
    w.I θ ∨ w.I2 θ ∨ w.IImin θ := by
  classical
  let sorted := sortedGroupingIndices w
  have hsorted : sorted.Pairwise (fun i j => w.weight j ≤ w.weight i) :=
    sortedGroupingIndices_sorted w
  have hnodup : sorted.Nodup := sortedGroupingIndices_nodup w
  have huniv : sorted.toFinset = (Finset.univ : Finset (Fin k)) :=
    sortedGroupingIndices_toFinset w
  have hsum : (sorted.map w.weight).sum = 1 := by
    calc
      (sorted.map w.weight).sum = subsetWeightSum w sorted.toFinset :=
        listWeightSum_eq_subsetWeightSum w sorted hnodup
      _ = subsetWeightSum w (Finset.univ : Finset (Fin k)) := by rw [huniv]
      _ = 1 := subsetWeightSum_univ w
  generalize hEq : sorted = sortedList
  cases sortedList with
  | nil =>
      rw [hEq] at hsum
      simp at hsum
  | cons i tail =>
      have hsortedCons : (i :: tail).Pairwise
          (fun i j => w.weight j ≤ w.weight i) := by
        rw [← hEq]
        exact hsorted
      have hnodupCons : (i :: tail).Nodup := by
        rw [← hEq]
        exact hnodup
      have hunivCons : (i :: tail).toFinset = (Finset.univ : Finset (Fin k)) := by
        rw [← hEq]
        exact huniv
      have hsumCons : ((i :: tail).map w.weight).sum = 1 := by
        rw [← hEq]
        exact hsum
      have hmax : ∀ j ∈ tail, w.weight j ≤ w.weight i := by
        exact (List.pairwise_cons.mp hsortedCons).1
      have hnotmem : i ∉ tail := (List.nodup_cons.mp hnodupCons).1
      have hsumTail : w.weight i + (tail.map w.weight).sum = 1 := by
        simpa using hsumCons
      by_cases hI : w.I θ
      · exact Or.inl hI
      · have hfirst : w.weight i < 1 - θ := by
          by_contra h
          apply hI
          exact ⟨i, le_of_not_gt h⟩
        by_cases hI2 : w.I2 θ
        · exact Or.inr (Or.inl hI2)
        · by_cases hpair : ∃ j l : Fin k, j ≠ l ∧
              1 - θ ≤ w.weight j + w.weight l
          · rcases hpair with ⟨j, l, hjl, hlo⟩
            have hpairhi : w.weight j + w.weight l <
                (3 / 2 : ℝ) * (1 - θ) := by
              by_contra h
              apply hI2
              exact ⟨j, l, hjl, le_of_not_gt h⟩
            have hthreehalves : (3 / 2 : ℝ) * (1 - θ) ≤ θ := by
              nlinarith [hθlow]
            let J : Finset (Fin k) := insert j (insert l ∅)
            let J' : Finset (Fin k) := Finset.univ \ J
            have hsumJ : subsetWeightSum w J = w.weight j + w.weight l := by
              simp [subsetWeightSum, J, hjl]
            have hsumJ' : subsetWeightSum w J' =
                1 - (w.weight j + w.weight l) := by
              rw [subsetWeightSum_compl, hsumJ]
            have hdisj : Disjoint J J' := by
              apply Finset.disjoint_left.mpr
              intro x hx hx'
              exact (Finset.mem_sdiff.mp hx').2 hx
            have hunion : J ∪ J' = Finset.univ := by
              dsimp [J']
              exact Finset.union_sdiff_of_subset (Finset.subset_univ J)
            have hIImin : w.IImin θ := by
              refine ⟨J, J', hdisj, hunion, ?_, ?_, ?_, ?_⟩
              · rw [hsumJ]
                exact hlo
              · rw [hsumJ]
                exact (lt_of_lt_of_le hpairhi hthreehalves).le
              · rw [hsumJ']
                linarith
              · rw [hsumJ']
                linarith [hθhigh]
            exact Or.inr (Or.inr hIImin)
          · have hpairlt {j l : Fin k} (hjl : j ≠ l) :
                w.weight j + w.weight l < 1 - θ := by
              by_contra h
              exact hpair ⟨j, l, hjl, le_of_not_gt h⟩
            have hdnonneg : 0 ≤ (2 * θ - 1 : ℝ) := by nlinarith [hθlow]
            have htailBound : ∀ j ∈ tail, w.weight j ≤ 2 * θ - 1 := by
              intro j hj
              have hne : i ≠ j := by
                intro heq
                subst j
                exact hnotmem hj
              have hsumij := hpairlt hne
              have hji := hmax j hj
              nlinarith [hθlow]
            let split := firstCrossingSplit (1 - θ) (w.weight i)
              (tail.map w.weight)
            have hsplit := firstCrossingSplit_spec (tail.map w.weight)
              (w.weight i) (1 - θ) (2 * θ - 1) hfirst
              (by rw [hsumTail]; linarith [hθhigh])
              (by
                intro z hz
                obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
                exact ⟨w.weight_nonneg j, htailBound j hj⟩)
            let pre := tail.take split.1.length
            let suffix := tail.drop split.1.length
            have hsplitMap : (tail.map w.weight).take split.1.length = split.1 := by
              rw [hsplit.1]
              calc
                (split.1 ++ split.2).take split.1.length =
                    split.1.take split.1.length :=
                  List.take_append_of_le_length (by exact le_rfl)
                _ = split.1 := List.take_length
            have htailDecomp : tail = pre ++ suffix := by
              simp [pre, suffix, List.take_append_drop]
            have hpreSum : (pre.map w.weight).sum = split.1.sum := by
              dsimp [pre]
              rw [List.map_take, hsplitMap]
            let leftItems := i :: pre
            let J : Finset (Fin k) := leftItems.toFinset
            let J' : Finset (Fin k) := suffix.toFinset
            have hpartsPerm : List.Perm (i :: tail) (leftItems ++ suffix) := by
              have heq : i :: tail = (i :: pre) ++ suffix := by
                calc
                  i :: tail = i :: (pre ++ suffix) := congrArg (List.cons i) htailDecomp
                  _ = (i :: pre) ++ suffix := by simp
              exact List.Perm.of_eq heq
            have hparts := listPartitionToFinset (i :: tail)
              (i :: pre) suffix hpartsPerm hnodupCons
            have hleftSum : subsetWeightSum w J =
                w.weight i + (pre.map w.weight).sum := by
              simpa [J, leftItems, List.map_cons, List.sum_cons] using
                (listWeightSum_eq_subsetWeightSum w (i :: pre) hparts.1).symm
            have hcover : J ∪ J' = Finset.univ := by
              rw [hparts.2.2.2, hunivCons]
            have hsumGroups : subsetWeightSum w J + subsetWeightSum w J' = 1 := by
              have h := subsetWeightSum_union_disjoint w hparts.2.2.1
              rw [hcover, subsetWeightSum_univ] at h
              exact h.symm
            have hJbounds : 1 - θ ≤ subsetWeightSum w J ∧
                subsetWeightSum w J ≤ θ := by
              constructor
              · rw [hleftSum, hpreSum]
                exact hsplit.2.1
              · rw [hleftSum, hpreSum]
                nlinarith [hsplit.2.2]
            have hJ'bounds : 1 - θ ≤ subsetWeightSum w J' ∧
                subsetWeightSum w J' ≤ θ := by
              constructor <;> linarith [hsumGroups, hJbounds.1, hJbounds.2, hθhigh]
            have hIImin : w.IImin θ := by
              exact ⟨J, J', hparts.2.2.1, hcover,
                hJbounds.1, hJbounds.2, hJ'bounds.1, hJ'bounds.2⟩
            exact Or.inr (Or.inr hIImin)

/-- At the endpoint `θ = 5/8`, either a type-I group exists or the major
type-II partition exists. -/
theorem majorGroupingFiveEighths {k : ℕ} (w : GroupingPredicates k) :
    w.I (5 / 8) ∨ w.IImaj (5 / 8) := by
  classical
  let sorted := sortedGroupingIndices w
  have hsorted : sorted.Pairwise (fun i j => w.weight j ≤ w.weight i) :=
    sortedGroupingIndices_sorted w
  have hnodup : sorted.Nodup := sortedGroupingIndices_nodup w
  have huniv : sorted.toFinset = (Finset.univ : Finset (Fin k)) :=
    sortedGroupingIndices_toFinset w
  have hsum : (sorted.map w.weight).sum = 1 := by
    calc
      (sorted.map w.weight).sum = subsetWeightSum w sorted.toFinset :=
        listWeightSum_eq_subsetWeightSum w sorted hnodup
      _ = subsetWeightSum w (Finset.univ : Finset (Fin k)) := by rw [huniv]
      _ = 1 := subsetWeightSum_univ w
  by_cases hI : w.I (5 / 8)
  · exact Or.inl hI
  · have hsmall : ∀ i : Fin k, w.weight i < 3 / 8 := by
      intro i
      by_contra hi
      apply hI
      refine ⟨i, ?_⟩
      norm_num at hi ⊢
      exact hi
    have hlen3 : 3 ≤ sorted.length := by
      by_contra h
      have hlen : sorted.length ≤ 2 := by omega
      generalize hEq : sorted = xs
      cases xs with
      | nil =>
          rw [hEq] at hsum
          simp at hsum
      | cons a rest =>
          cases rest with
          | nil =>
              rw [hEq] at hsum
              simp at hsum
              have ha := hsmall a
              linarith
          | cons b rest =>
              cases rest with
              | nil =>
                  rw [hEq] at hsum
                  simp at hsum
                  have ha := hsmall a
                  have hb := hsmall b
                  linarith
              | cons c rest =>
                  rw [hEq] at hlen
                  simp at hlen
    generalize hEq : sorted = xs
    cases xs with
    | nil =>
        rw [hEq] at hlen3
        simp at hlen3
    | cons i tail =>
        cases tail with
        | nil =>
            rw [hEq] at hlen3
            simp at hlen3
        | cons j tail =>
            cases tail with
            | nil =>
                rw [hEq] at hlen3
                simp at hlen3
            | cons z rest =>
                have hsortedCons : (i :: j :: z :: rest).Pairwise
                    (fun i j => w.weight j ≤ w.weight i) := by
                  rw [← hEq]
                  exact hsorted
                have hnodupCons : (i :: j :: z :: rest).Nodup := by
                  rw [← hEq]
                  exact hnodup
                have hsumCons : ((i :: j :: z :: rest).map w.weight).sum = 1 := by
                  rw [← hEq]
                  exact hsum
                have hsumTail : w.weight i + ((j :: z :: rest).map w.weight).sum = 1 := by
                  simpa [List.map_cons, List.sum_cons, add_assoc] using hsumCons
                have hfirstPair := List.pairwise_cons.mp hsortedCons
                have hsecondPair := List.pairwise_cons.mp hfirstPair.2
                have hthirdPair := List.pairwise_cons.mp hsecondPair.2
                have hij : w.weight j ≤ w.weight i := hfirstPair.1 j (by simp)
                have hjz : w.weight z ≤ w.weight j := hsecondPair.1 z (by simp)
                have hzrest : ∀ q ∈ rest, w.weight q ≤ w.weight z := hthirdPair.1
                have hnotmem : i ∉ j :: z :: rest :=
                  (List.nodup_cons.mp hnodupCons).1
                by_cases hz : 1 / 4 < w.weight z
                · have hsmallI := hsmall i
                  have hsmallJ := hsmall j
                  have hjlarge : 1 / 4 < w.weight j := lt_of_lt_of_le hz hjz
                  have hilarge : 1 / 4 < w.weight i := lt_of_lt_of_le hjlarge hij
                  let J : Finset (Fin k) := {i}
                  let J' : Finset (Fin k) := {j}
                  have hIJ : Disjoint J J' := by
                    apply Finset.disjoint_left.mpr
                    intro x hx hx'
                    simp only [J, J', Finset.mem_singleton] at hx hx'
                    subst x
                    exact hnotmem (by simp [hx'])
                  have hsumJ : subsetWeightSum w J = w.weight i := by
                    simp [subsetWeightSum, J]
                  have hsumJ' : subsetWeightSum w J' = w.weight j := by
                    simp [subsetWeightSum, J']
                  have htotalLow : (1 / 2 : ℝ) ≤
                      subsetWeightSum w J + subsetWeightSum w J' := by
                    rw [hsumJ, hsumJ']
                    linarith
                  have htotalHigh : subsetWeightSum w J + subsetWeightSum w J' ≤ 3 / 4 := by
                    rw [hsumJ, hsumJ']
                    linarith
                  have hgap : |subsetWeightSum w J - subsetWeightSum w J'| ≤ 1 / 4 := by
                    rw [hsumJ, hsumJ', abs_of_nonneg (sub_nonneg.mpr hij)]
                    linarith
                  exact Or.inr
                    (majorFromTwoGroups w J J' hIJ htotalLow htotalHigh hgap)
                · have hzle : w.weight z ≤ 1 / 4 := le_of_not_gt hz
                  let split := maximalPrefixBelow w.weight (w.weight i) 0
                    (j :: z :: rest)
                  let inner := maximalPrefixBelow w.weight (w.weight i)
                    (w.weight j) (z :: rest)
                  have hjfit : 0 + w.weight j ≤ w.weight i := by linarith [hij]
                  have hshape : split = (j :: inner.1, inner.2) := by
                    have h := maximalPrefixBelow_cons_of_fit w.weight
                      (w.weight i) 0 j (z :: rest) hjfit
                    simpa [split, inner, zero_add] using h
                  have hspecBase := maximalPrefixBelow_spec w.weight
                    (w.weight i) 0 (j :: z :: rest) (w.weight_nonneg i)
                  have hspec : (j :: z :: rest) = split.1 ++ split.2 ∧
                      0 + (split.1.map w.weight).sum ≤ w.weight i ∧
                      (split.2 = [] ∨
                        ∃ q qs, split.2 = q :: qs ∧
                          w.weight i < 0 + (split.1.map w.weight).sum + w.weight q) := by
                    simpa only [split] using hspecBase
                  have htailNodup : (j :: z :: rest).Nodup :=
                    (List.nodup_cons.mp hnodupCons).2
                  have hpreSuffixNodup : (split.1 ++ split.2).Nodup := by
                    rw [← hspec.1]
                    exact htailNodup
                  have hpreNodup : split.1.Nodup :=
                    (List.nodup_append'.mp hpreSuffixNodup).1
                  have hpreSuffixDisj : List.Disjoint split.1 split.2 :=
                    (List.nodup_append'.mp hpreSuffixNodup).2.2
                  have hprele : (split.1.map w.weight).sum ≤ w.weight i := by
                    simpa using hspec.2.1
                  have hsplitNonempty : split.2 ≠ [] := by
                    intro hnil
                    have hdecomp : (j :: z :: rest) = split.1 := by
                      simpa [hnil] using hspec.1
                    have hmapSum : ((j :: z :: rest).map w.weight).sum =
                        (split.1.map w.weight).sum := by
                      rw [hdecomp]
                    rw [hmapSum] at hsumTail
                    nlinarith [hprele, hsmall i]
                  have hzRestBound : ∀ q ∈ z :: rest, w.weight q ≤ 1 / 4 := by
                    intro q hq
                    rcases List.mem_cons.mp hq with hq | hq
                    · simpa [hq] using hzle
                    · exact le_trans (hzrest q hq) hzle
                  have hsufBound : ∀ q ∈ split.2, w.weight q ≤ 1 / 4 := by
                    intro q hq
                    have hqTail : q ∈ j :: z :: rest := by
                      rw [hspec.1]
                      exact List.mem_append_right _ hq
                    rcases List.mem_cons.mp hqTail with hqj | hqzr
                    · subst q
                      have hjpre : j ∈ split.1 := by rw [hshape]; simp
                      exact False.elim
                        ((List.disjoint_left.mp hpreSuffixDisj) hjpre hq)
                    · exact hzRestBound q hqzr
                  have hcrossData : ∃ q, q ∈ split.2 ∧
                      w.weight i < (split.1.map w.weight).sum + w.weight q := by
                    rcases hspec.2.2 with hnil | ⟨q, qs, hqeq, hcross⟩
                    · exact False.elim (hsplitNonempty hnil)
                    · refine ⟨q, ?_, ?_⟩
                      · rw [hqeq]
                        simp
                      · simpa using hcross
                  have hgap : |w.weight i - (split.1.map w.weight).sum| ≤ 1 / 4 := by
                    rcases hcrossData with ⟨q, hq, hcross⟩
                    rw [abs_of_nonneg (sub_nonneg.mpr hprele)]
                    nlinarith [hcross, hsufBound q hq]
                  let u := w.weight i
                  let v := (split.1.map w.weight).sum
                  have hvle : v ≤ u := by simpa [u, v] using hspec.2.1
                  have hprefixSum : subsetWeightSum w split.1.toFinset = v := by
                    simpa [v] using
                      (listWeightSum_eq_subsetWeightSum w split.1 hpreNodup).symm
                  by_cases hinitialLarge : (1 / 2 : ℝ) ≤ u + v
                  · let J : Finset (Fin k) := {i}
                    let J' : Finset (Fin k) := split.1.toFinset
                    have hIJ : Disjoint J J' := by
                      apply Finset.disjoint_left.mpr
                      intro x hx hx'
                      have hxi : x = i := by simpa [J] using hx
                      subst x
                      have hipre : i ∈ split.1 := List.mem_toFinset.mp hx'
                      have hitail : i ∈ j :: z :: rest := by
                        rw [hspec.1]
                        exact List.mem_append_left _ hipre
                      exact hnotmem hitail
                    have hsumJ : subsetWeightSum w J = u := by
                      simp [J, u, subsetWeightSum]
                    have hsumJ' : subsetWeightSum w J' = v := hprefixSum
                    have htotalHigh : subsetWeightSum w J + subsetWeightSum w J' ≤ 3 / 4 := by
                      rw [hsumJ, hsumJ']
                      dsimp [u]
                      nlinarith [hsmall i, hvle]
                    have hgap' : |subsetWeightSum w J - subsetWeightSum w J'| ≤ 1 / 4 := by
                      rw [hsumJ, hsumJ']
                      exact hgap
                    exact Or.inr (majorFromTwoGroups w J J' hIJ
                      (by simpa [hsumJ, hsumJ'] using hinitialLarge)
                      htotalHigh hgap')
                  · have hinitial : u + v < 1 / 2 := lt_of_not_ge hinitialLarge
                    have htotalAvailable : u + v + (split.2.map w.weight).sum = 1 := by
                      have htailSplit : ((j :: z :: rest).map w.weight).sum =
                          v + (split.2.map w.weight).sum := by
                        rw [hspec.1]
                        simp [v, List.map_append, List.sum_append]
                      have hsumTail' : w.weight i +
                          ((j :: z :: rest).map w.weight).sum = 1 := by
                        simpa [List.map_cons, List.sum_cons, add_assoc] using hsumCons
                      rw [htailSplit] at hsumTail'
                      simpa [u, add_assoc] using hsumTail'
                    have hweights : ∀ q ∈ split.2,
                        0 ≤ w.weight q ∧ w.weight q ≤ 1 / 4 := by
                      intro q hq
                      exact ⟨w.weight_nonneg q, hsufBound q hq⟩
                    have htotal : (1 / 2 : ℝ) ≤
                        u + v + (split.2.map w.weight).sum := by
                      rw [htotalAvailable]
                      norm_num
                    rcases balanceFiniteIndexedList w.weight u v (1 / 2) (1 / 4)
                        split.2 (by norm_num) hgap hweights hinitial htotal with
                      ⟨processed, unused, hsplit, hlow, hhigh, hbalgap⟩
                    let assignment := greedyAssignment w.weight processed (u, v)
                    let leftItems := i :: assignment.leftItems
                    let rightItems := split.1 ++ assignment.rightItems
                    let processedItems := (i :: split.1) ++ processed
                    have hfullSplit : (j :: z :: rest) =
                        split.1 ++ processed ++ unused := by
                      calc
                        j :: z :: rest = split.1 ++ split.2 := hspec.1
                        _ = split.1 ++ (processed ++ unused) :=
                          congrArg (List.append split.1) hsplit
                        _ = (split.1 ++ processed) ++ unused := by simp [List.append_assoc]
                    have hprocEq : (i :: j :: z :: rest) =
                        processedItems ++ unused := by
                      calc
                        i :: j :: z :: rest = i :: (split.1 ++ processed ++ unused) :=
                          congrArg (List.cons i) hfullSplit
                        _ = processedItems ++ unused := by
                          simp [processedItems, List.append_assoc]
                    have hprocNodup : processedItems.Nodup := by
                      have hfullNodup : (processedItems ++ unused).Nodup := by
                        rw [← hprocEq]
                        exact hnodupCons
                      exact List.Nodup.of_append_left hfullNodup
                    have hassignPerm := greedyAssignment_perm w.weight processed (u, v)
                    have hswap : List.Perm
                        (split.1 ++ assignment.leftItems)
                        (assignment.leftItems ++ split.1) := List.perm_append_comm
                    have hmove : List.Perm
                        ((i :: split.1) ++ assignment.leftItems)
                        ((i :: assignment.leftItems) ++ split.1) := by
                      have h := hswap.cons i
                      simpa only [List.cons_append] using h
                    have hprocPerm : List.Perm processedItems (leftItems ++ rightItems) := by
                      change List.Perm ((i :: split.1) ++ processed)
                        ((i :: assignment.leftItems) ++ (split.1 ++ assignment.rightItems))
                      have hstart := hassignPerm.append_left (i :: split.1)
                      have hassoc : List.Perm
                          ((i :: split.1) ++
                            (assignment.leftItems ++ assignment.rightItems))
                          (((i :: split.1) ++ assignment.leftItems) ++
                            assignment.rightItems) :=
                        List.Perm.of_eq (by simp [List.append_assoc])
                      have hmoveEnd := hmove.append_right assignment.rightItems
                      have hfinal : List.Perm
                          (((i :: assignment.leftItems) ++ split.1) ++
                            assignment.rightItems)
                          ((i :: assignment.leftItems) ++
                            (split.1 ++ assignment.rightItems)) :=
                        List.Perm.of_eq (by simp [List.append_assoc])
                      exact hstart.trans (hassoc.trans (hmoveEnd.trans hfinal))
                    have hgroups := listPartitionToFinset processedItems
                      leftItems rightItems hprocPerm hprocNodup
                    let J : Finset (Fin k) := leftItems.toFinset
                    let J' : Finset (Fin k) := rightItems.toFinset
                    have hassignTotals := greedyAssignment_item_weights
                      w.weight processed (u, v)
                    have hsumJ : subsetWeightSum w J = assignment.leftTotal := by
                      calc
                        subsetWeightSum w J = (leftItems.map w.weight).sum :=
                          (listWeightSum_eq_subsetWeightSum w leftItems hgroups.1).symm
                        _ = u + (assignment.leftItems.map w.weight).sum := by
                          simp [leftItems, u, List.map_cons, List.sum_cons]
                        _ = assignment.leftTotal := hassignTotals.1.symm
                    have hsumJ' : subsetWeightSum w J' = assignment.rightTotal := by
                      calc
                        subsetWeightSum w J' = (rightItems.map w.weight).sum :=
                          (listWeightSum_eq_subsetWeightSum w rightItems hgroups.2.1).symm
                        _ = v + (assignment.rightItems.map w.weight).sum := by
                          simp [rightItems, v, List.map_append, List.sum_append]
                        _ = assignment.rightTotal := hassignTotals.2.symm
                    have htotalLow : (1 / 2 : ℝ) ≤
                        subsetWeightSum w J + subsetWeightSum w J' := by
                      rw [hsumJ, hsumJ']
                      exact hlow
                    have htotalHigh : subsetWeightSum w J + subsetWeightSum w J' ≤ 3 / 4 := by
                      rw [hsumJ, hsumJ']
                      norm_num at hhigh ⊢
                      exact hhigh
                    have hgapGroups :
                        |subsetWeightSum w J - subsetWeightSum w J'| ≤ 1 / 4 := by
                      rw [hsumJ, hsumJ']
                      exact hbalgap
                    exact Or.inr (majorFromTwoGroups w J J' hgroups.2.2.1
                      htotalLow htotalHigh hgapGroups)

/-- The simultaneous minor and major grouping alternative at `5/8`. -/
theorem combinedGroupingFiveEighths {k : ℕ} (w : GroupingPredicates k) :
    w.I (5 / 8) ∨ w.I2 (5 / 8) ∨
      (w.IImin (5 / 8) ∧ w.IImaj (5 / 8)) := by
  classical
  by_cases hI : w.I (5 / 8)
  · exact Or.inl hI
  by_cases hI2 : w.I2 (5 / 8)
  · exact Or.inr (Or.inl hI2)
  have hmajor := majorGroupingFiveEighths w
  have hIImaj : w.IImaj (5 / 8) := by
    rcases hmajor with hI' | hIImaj
    · exact False.elim (hI hI')
    · exact hIImaj
  have hminor := minorGrouping w (5 / 8) (by norm_num) (by norm_num)
  rcases hminor with hI' | hI2' | hIImin
  · exact False.elim (hI hI')
  · exact False.elim (hI2 hI2')
  · exact Or.inr (Or.inr ⟨hIImin, hIImaj⟩)

#print axioms balanceFiniteList
#print axioms balanceFiniteIndexedList
#print axioms minorGrouping
#print axioms majorGroupingFiveEighths
#print axioms combinedGroupingFiveEighths

end

end FractionalPrimes.Literature.Uniformity.Combinatorics

end
