module

public import FractionalPrimes.Literature.JSW.DyadicMartingaleJump
public import FractionalPrimes.Literature.JSW.GreedyPrefixPredictability
public import FractionalPrimes.Literature.JSW.GreedyPrefixCellConstancy
public import FractionalPrimes.Literature.JSW.GreedyJumpSquareComparison

/-!
# Assembly of the finite dyadic martingale jump estimate

This downstream module combines the predictable-transform and finite-sign
estimates with the checked greedy-prefix interface.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open FractionalPrimes.Literature.Variation

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The integer scale of the increment after finite time `t`. -/
private def dyadicJumpScale (L : ℤ) {M : ℕ} (t : Fin M) : ℤ :=
  L + (t.val : ℤ) + 1

private theorem dyadicJumpScale_injective (L : ℤ) {M : ℕ} :
    Function.Injective (dyadicJumpScale L (M := M)) := by
  intro t s h
  apply Fin.ext
  dsimp [dyadicJumpScale] at h
  exact_mod_cast (by omega : (t.val : ℤ) = (s.val : ℤ))

private def dyadicJumpIndex (L : ℤ) (M : ℕ) (n : ℤ)
    (hn : n ∈ Finset.Ioc L (L + (M : ℤ))) : Fin M :=
  ⟨(n - L - 1).toNat, by
    have hLn := (Finset.mem_Ioc.mp hn).1
    have hnM := (Finset.mem_Ioc.mp hn).2
    have hq0 : 0 ≤ n - L - 1 := by omega
    have hqM : n - L - 1 < (M : ℤ) := by omega
    have hqMcast : ((n - L - 1).toNat : ℤ) < (M : ℤ) := by
      rw [Int.toNat_of_nonneg hq0]
      exact hqM
    exact_mod_cast hqMcast⟩

private theorem dyadicJumpIndex_val (L : ℤ) (M : ℕ) (n : ℤ)
    (hn : n ∈ Finset.Ioc L (L + (M : ℤ))) :
    (dyadicJumpIndex L M n hn).val = (n - L - 1).toNat := rfl

private theorem dyadicJumpScale_index (L : ℤ) (M : ℕ) (n : ℤ)
    (hn : n ∈ Finset.Ioc L (L + (M : ℤ))) :
    dyadicJumpScale L (dyadicJumpIndex L M n hn) = n := by
  rcases Finset.mem_Ioc.mp hn with ⟨hLn, hnM⟩
  have hq0 : 0 ≤ n - L - 1 := by omega
  change L + ((dyadicJumpIndex L M n hn).val : ℤ) + 1 = n
  rw [dyadicJumpIndex_val]
  change L + ((n - L - 1).toNat : ℤ) + 1 = n
  rw [Int.toNat_of_nonneg hq0]
  omega

private theorem dyadicJumpScale_mem {M : ℕ} (L : ℤ) (t : Fin M) :
    dyadicJumpScale L t ∈ Finset.Ioc L (L + (M : ℤ)) := by
  simp only [Finset.mem_Ioc]
  constructor
  · dsimp [dyadicJumpScale]
    omega
  · dsimp [dyadicJumpScale]
    have ht : (t.val : ℤ) < (M : ℤ) := by exact_mod_cast t.isLt
    omega

private theorem dyadicJumpIndex_scale {M : ℕ} (L : ℤ) (t : Fin M) :
    dyadicJumpIndex L M (dyadicJumpScale L t) (dyadicJumpScale_mem L t) = t := by
  apply dyadicJumpScale_injective L
  rw [dyadicJumpScale_index L M (dyadicJumpScale L t) (dyadicJumpScale_mem L t)]

/-- Reindex the increment scales `L+1,...,L+M` by `Fin M`. -/
private theorem sum_Ioc_eq_sum_fin {M : ℕ} (L : ℤ) (g : ℤ → ℂ) :
    ∑ n ∈ Finset.Ioc L (L + (M : ℤ)), g n =
      ∑ t : Fin M, g (dyadicJumpScale L t) := by
  have himage : Finset.Ioc L (L + (M : ℤ)) =
      (Finset.univ : Finset (Fin M)).image (dyadicJumpScale L) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hLn, hnN⟩
      let q : ℤ := n - L - 1
      have hq0 : 0 ≤ q := by dsimp [q]; omega
      have hqM : q < (M : ℤ) := by dsimp [q]; omega
      have hqM' : q.toNat < M := by
        have hqMcast : (q.toNat : ℤ) < (M : ℤ) := by
          rw [Int.toNat_of_nonneg hq0]
          exact hqM
        exact_mod_cast hqMcast
      refine ⟨⟨q.toNat, hqM'⟩, ?_⟩
      dsimp [dyadicJumpScale, q]
      have hqcast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq0
      rw [hqcast]
      dsimp [q]
      omega
    · rintro ⟨t, rfl⟩
      constructor
      · dsimp [dyadicJumpScale]
        have ht : (t.val : ℤ) ≥ 0 := Int.natCast_nonneg _
        omega
      · dsimp [dyadicJumpScale]
        have ht : (t.val : ℤ) < (M : ℤ) := by exact_mod_cast t.isLt
        omega
  calc
    ∑ n ∈ Finset.Ioc L (L + (M : ℤ)), g n =
        ∑ n ∈ (Finset.univ : Finset (Fin M)).image (dyadicJumpScale L), g n := by
          rw [himage]
    _ = ∑ t ∈ (Finset.univ : Finset (Fin M)), g (dyadicJumpScale L t) := by
          have hinj : Set.InjOn (dyadicJumpScale L (M := M))
              ↑(Finset.univ : Finset (Fin M)) := by
            intro a _ b _ hab
            exact dyadicJumpScale_injective L hab
          rw [Finset.sum_image (f := fun n => g n) hinj]
    _ = ∑ t : Fin M, g (dyadicJumpScale L t) := by simp

/-- The last stop of a greedy run that has occurred by time `t`. -/
private noncomputable def greedyLastStopIndex
    {M : ℕ} {u : Fin (M + 1) → ℂ} {threshold : ℝ} {G : ℕ}
    (run : GreedyStopRun u threshold G) (t : Fin (M + 1)) : Fin (G + 1) :=
  (Finset.univ.filter fun i : Fin (G + 1) => run.point i ≤ t).max'
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, run.least t⟩⟩

private theorem greedyLastStopIndex_mem
    {M : ℕ} {u : Fin (M + 1) → ℂ} {threshold : ℝ} {G : ℕ}
    (run : GreedyStopRun u threshold G) (t : Fin (M + 1)) :
    run.point (greedyLastStopIndex run t) ≤ t := by
  have hmem := Finset.max'_mem
    (Finset.univ.filter fun i : Fin (G + 1) => run.point i ≤ t)
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, run.least t⟩⟩
  exact (Finset.mem_filter.mp hmem).2

private theorem greedyLastStopIndex_maximal
    {M : ℕ} {u : Fin (M + 1) → ℂ} {threshold : ℝ} {G : ℕ}
    (run : GreedyStopRun u threshold G) (t : Fin (M + 1))
    {i : Fin (G + 1)} (hi : run.point i ≤ t) :
    i ≤ greedyLastStopIndex run t := by
  exact Finset.le_max' _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

private theorem greedyLastStopIndex_eq_iff
    {M : ℕ} {u : Fin (M + 1) → ℂ} {threshold : ℝ} {G : ℕ}
    (run : GreedyStopRun u threshold G) (t : Fin (M + 1))
    (i : Fin (G + 1)) :
    greedyLastStopIndex run t = i ↔
      run.point i ≤ t ∧ ∀ j : Fin (G + 1), run.point j ≤ t → j ≤ i := by
  classical
  unfold greedyLastStopIndex
  rw [Finset.max'_eq_iff
    (Finset.univ.filter fun j : Fin (G + 1) => run.point j ≤ t)
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, run.least t⟩⟩ i]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private theorem greedyLastStopIndex_eq_of_stop_interval
    {M : ℕ} {u : Fin (M + 1) → ℂ} {threshold : ℝ} {G : ℕ}
    (run : GreedyStopRun u threshold G) (t : Fin (M + 1))
    (i : Fin G) (hleft : run.point i.castSucc ≤ t)
    (hright : t < run.point i.succ) :
    greedyLastStopIndex run t = i.castSucc := by
  apply (greedyLastStopIndex_eq_iff run t i.castSucc).2
  constructor
  · exact hleft
  · intro j hj
    by_contra hnot
    have hij : i.castSucc < j := lt_of_not_ge hnot
    have hval : i.val < j.val := Fin.lt_iff_val_lt_val.mp hij
    have hsuccval : i.succ.val ≤ j.val := by
      change i.val + 1 ≤ j.val
      omega
    have hsucc : i.succ ≤ j := Fin.le_iff_val_le_val.mpr hsuccval
    have hpoint : run.point i.succ ≤ run.point j := run.strict.monotone hsucc
    exact (not_lt_of_ge (hpoint.trans hj)) hright

private theorem greedyLastStopIndex_stop_interval_of_eq
    {M : ℕ} {u : Fin (M + 1) → ℂ} {threshold : ℝ} {G : ℕ}
    (run : GreedyStopRun u threshold G) (t : Fin (M + 1))
    (i : Fin G) (hindex : greedyLastStopIndex run t = i.castSucc) :
    run.point i.castSucc ≤ t ∧ t < run.point i.succ := by
  have hchar := (greedyLastStopIndex_eq_iff run t i.castSucc).mp hindex
  refine ⟨hchar.1, ?_⟩
  by_contra hnot
  have hnext : run.point i.succ ≤ t := le_of_not_gt hnot
  have hle := hchar.2 i.succ hnext
  have hleval := Fin.le_iff_val_le_val.mp hle
  change i.val + 1 ≤ i.val at hleval
  omega

/-- A full greedy run restricts to a greedy run on every initial finite
prefix. -/
private def greedyRunPrefixRestriction
    {M : ℕ} {u : Fin (M + 1) → ℂ} {threshold : ℝ} {G : ℕ}
    (run : GreedyStopRun u threshold G) (t : Fin (M + 1)) :
    GreedyStopRun (fun i : Fin (t.val + 1) => u ⟨i.val, by omega⟩)
      threshold (greedyLastStopIndex run t).val := by
  classical
  let a := greedyLastStopIndex run t
  let runIndex (i : Fin (a.val + 1)) : Fin (G + 1) :=
    ⟨i.val, by omega⟩
  let prefixPoint (i : Fin (a.val + 1)) : Fin (t.val + 1) :=
    ⟨(run.point (runIndex i)).val, by
      have hi : runIndex i ≤ a := by
        exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ i.isLt)
      have hp := (run.strict.monotone hi).trans (greedyLastStopIndex_mem run t)
      have hpval := Fin.le_iff_val_le_val.mp hp
      omega⟩
  refine {
    point := prefixPoint
    strict := ?_
    least := ?_
    crosses := ?_
    first := ?_
    exhausted := ?_ }
  · intro i j hij
    apply Fin.lt_iff_val_lt_val.mpr
    have hrunIndex : runIndex i < runIndex j :=
      Fin.lt_iff_val_lt_val.mpr (Fin.lt_iff_val_lt_val.mp hij)
    have hrunPoint := run.strict hrunIndex
    exact Fin.lt_iff_val_lt_val.mp hrunPoint
  · intro x
    apply Fin.le_iff_val_le_val.mpr
    have hxle : x.val ≤ t.val := Nat.le_of_lt_succ x.isLt
    have hxltM : x.val < M + 1 := lt_of_le_of_lt hxle t.isLt
    have hleast := run.least (⟨x.val, by omega⟩ : Fin (M + 1))
    have hzero : runIndex 0 = 0 := by ext; rfl
    have hpt := Fin.le_iff_val_le_val.mp hleast
    simpa [prefixPoint, runIndex, hzero] using hpt
  · intro i
    let j : Fin G := ⟨i.val, by omega⟩
    have hi : runIndex i.castSucc = j.castSucc := by ext; rfl
    have hj : runIndex i.succ = j.succ := by ext; rfl
    change threshold / 2 < ‖u ⟨(prefixPoint i.succ).val, by omega⟩ -
      u ⟨(prefixPoint i.castSucc).val, by omega⟩‖
    simpa [prefixPoint, runIndex, hi, hj] using run.crosses j
  · intro i x hleft hright
    let j : Fin G := ⟨i.val, by omega⟩
    let x' : Fin (M + 1) := ⟨x.val, by omega⟩
    have hprev : runIndex i.castSucc = j.castSucc := by ext; rfl
    have hnext : runIndex i.succ = j.succ := by ext; rfl
    have hleft' : run.point j.castSucc ≤ x' := by
      apply Fin.le_iff_val_le_val.mpr
      exact Fin.le_iff_val_le_val.mp hleft
    have hright' : x' < run.point j.succ := by
      apply Fin.lt_iff_val_lt_val.mpr
      exact Fin.lt_iff_val_lt_val.mp hright
    have h := run.first j x' hleft' hright'
    simpa [prefixPoint, runIndex, hprev, hnext, x'] using h
  · intro x hafter
    let jlast : Fin (G + 1) := a
    let x' : Fin (M + 1) := ⟨x.val, by omega⟩
    have hlast : run.point jlast < x' := by
      apply Fin.lt_iff_val_lt_val.mpr
      exact Fin.lt_iff_val_lt_val.mp hafter
    by_cases hfinal : a.val = G
    · have ha : a = Fin.last G := by
        apply Fin.ext
        exact hfinal
      have h := run.exhausted x' (by simpa [jlast, ha] using hlast)
      have hlastPoint :
          (⟨(prefixPoint (Fin.last a.val)).val, by omega⟩ : Fin (M + 1)) =
            run.point a := by
        apply Fin.ext
        simp [prefixPoint, runIndex]
      change ‖u x' - u (⟨(prefixPoint (Fin.last a.val)).val, by omega⟩ : Fin (M + 1))‖ ≤
        threshold / 2
      rw [hlastPoint]
      rw [← ha] at h
      exact h
    · have hnextIndex : a.val < G := by omega
      let j : Fin G := ⟨a.val, hnextIndex⟩
      have hjcast : j.castSucc = a := by ext; rfl
      have hjnext : j.succ = (⟨a.val + 1, by omega⟩ : Fin (G + 1)) := by ext; rfl
      have hnextnot : ¬ run.point j.succ ≤ t := by
        intro hle
        have hmax := greedyLastStopIndex_maximal run t hle
        rw [hjnext] at hmax
        have hleval := Fin.le_iff_val_le_val.mp hmax
        change a.val + 1 ≤ a.val at hleval
        omega
      have htlt : t < run.point j.succ := lt_of_not_ge hnextnot
      have hx't : x' ≤ t := by
        apply Fin.le_iff_val_le_val.mpr
        exact Nat.le_of_lt_succ x.isLt
      have hright : x' < run.point j.succ := by
        exact lt_of_le_of_lt hx't htlt
      have hleft' : run.point j.castSucc ≤ x' := by
        have hja : run.point j.castSucc = run.point a := by rw [hjcast]
        rw [hja]
        exact hlast.le
      have h := run.first j x' hleft' hright
      simpa [prefixPoint, runIndex, hjcast, jlast, x'] using h

private def greedyPrefixValues {M : ℕ} (u : Fin (M + 1) → ℂ)
    (t : Fin (M + 1)) : ℕ → ℂ := fun k =>
  if hk : k ≤ t.val then u ⟨k, lt_of_le_of_lt hk t.isLt⟩ else 0

/-- The active block of a full greedy run is exactly the stop count selected
from the observed prefix. -/
private theorem greedyLastStopIndex_val_eq_prefixCount
    {M : ℕ} {u : Fin (M + 1) → ℂ} {threshold : ℝ} {G : ℕ}
    (run : GreedyStopRun u threshold G) (t : Fin (M + 1))
    (hthreshold : 0 < threshold) :
    (greedyLastStopIndex run t).val =
      greedyPrefixStopCount (greedyPrefixValues u t) threshold hthreshold t.val := by
  classical
  let preSeq : Fin (t.val + 1) → ℂ := fun i => u ⟨i.val, by omega⟩
  have hprefix : (fun i : Fin (t.val + 1) => greedyPrefixValues u t i.val) = preSeq := by
    funext i
    simp [greedyPrefixValues, preSeq, Nat.le_of_lt_succ i.isLt]
  let chosen := greedyStopRunChoice (I := Fin (t.val + 1)) preSeq threshold hthreshold
  have hcount := GreedyStopRun.count_eq
    (greedyRunPrefixRestriction run t) chosen.2
  unfold greedyPrefixStopCount
  rw [hprefix]
  exact hcount

private theorem greedyStopRun_length_le {M : ℕ} {u : Fin (M + 1) → ℂ}
    {threshold : ℝ} {G : ℕ} (run : GreedyStopRun u threshold G) : G ≤ M := by
  have hcard : Fintype.card (Fin (G + 1)) ≤ Fintype.card (Fin (M + 1)) :=
    Fintype.card_le_of_injective run.point run.strict.injective
  simpa using hcard

/-- Block label of the increment following time `t`; it is the most recent
greedy stop visible through time `t`. -/
private noncomputable def greedyRunActiveLabel {M : ℕ}
    {u : Fin (M + 1) → ℂ} {threshold : ℝ} {G : ℕ}
    (run : GreedyStopRun u threshold G) (t : Fin M) : Fin (M + 1) :=
  Fin.castLE (Nat.succ_le_succ (greedyStopRun_length_le run))
    (greedyLastStopIndex run t.castSucc)

/-- The full-run block label agrees with the selected run on the observed
prefix, including when the final active block is unfinished. -/
private theorem greedyRunActiveLabel_val_eq_prefixCount
    {M : ℕ} {u : Fin (M + 1) → ℂ} {uNat : ℕ → ℂ} {threshold : ℝ}
    {G : ℕ} (run : GreedyStopRun u threshold G) (t : Fin M)
    (hthreshold : 0 < threshold)
    (hprefix : ∀ (k : ℕ) (hkt : k ≤ t.val),
      u ⟨k, Nat.lt_succ_of_le (Nat.le_trans hkt t.isLt.le)⟩ = uNat k) :
    (greedyRunActiveLabel run t).val =
      greedyPrefixStopCount uNat threshold hthreshold t.val := by
  have hfull := greedyLastStopIndex_val_eq_prefixCount run t.castSucc hthreshold
  have hcongr := greedyPrefixStopCount_congr_prefix
    (greedyPrefixValues u t.castSucc) uNat threshold hthreshold t.val (by
      intro k hk
      change (if h : k ≤ t.castSucc.val then
        u ⟨k, Nat.lt_of_le_of_lt h t.castSucc.isLt⟩ else 0) = uNat k
      have hk' : k ≤ t.castSucc.val := by simpa using hk
      rw [dif_pos hk']
      exact hprefix k (by simpa using hk)
      )
  simpa [greedyRunActiveLabel] using hfull.trans hcongr

/-- The greedy prefix count of the dyadic averages at a point, through time
`t`. -/
private def dyadicJumpPrefixCount (L : ℤ) (threshold : ℝ)
    (hthreshold : 0 < threshold) (f : ℝ → ℂ) (t : ℕ) (x : ℝ) : ℕ :=
  greedyPrefixStopCount (fun k => dyadicAverage (-(L + (k : ℤ))) f x)
    threshold hthreshold t

/-- Indicator coefficient for the martingale increments belonging to one
greedy block. The coefficient is built from the observed prefix only. -/
private def dyadicJumpBlockMultiplier (L : ℤ) (M : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) (f : ℝ → ℂ) (i : Fin (M + 1))
    (n : ℤ) (x : ℝ) : ℝ :=
  if hn : n ∈ Finset.Ioc L (L + (M : ℤ)) then
    if dyadicJumpPrefixCount L threshold hthreshold f
        (dyadicJumpIndex L M n hn).val x = i.val then 1 else 0
  else 0

private theorem dyadicJumpBlockMultiplier_predictable (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold) (f : ℝ → ℂ)
    (i : Fin (M + 1)) (n : ℤ)
    (hn : n ∈ Finset.Ioc L (L + (M : ℤ))) (j : ℤ)
    {x y : ℝ} (hx : x ∈ dyadicInterval (1 - n) j)
    (hy : y ∈ dyadicInterval (1 - n) j) :
    dyadicJumpBlockMultiplier L M threshold hthreshold f i n x =
      dyadicJumpBlockMultiplier L M threshold hthreshold f i n y := by
  classical
  let t := dyadicJumpIndex L M n hn
  have hscale : L + ((t.val + 1 : ℕ) : ℤ) = n := by
    have h := dyadicJumpScale_index L M n hn
    dsimp [dyadicJumpScale] at h
    push_cast at h ⊢
    omega
  have hx' : x ∈ dyadicInterval (1 - (L + ((t.val + 1 : ℕ) : ℤ))) j := by
    rw [hscale]
    exact hx
  have hy' : y ∈ dyadicInterval (1 - (L + ((t.val + 1 : ℕ) : ℤ))) j := by
    rw [hscale]
    exact hy
  have hcount := greedyPrefixStopCount_eq_on_predictable_cell
    L t.val f threshold hthreshold j hx' hy'
  have hcount' : dyadicJumpPrefixCount L threshold hthreshold f
      (dyadicJumpIndex L M n hn).val x =
      dyadicJumpPrefixCount L threshold hthreshold f
        (dyadicJumpIndex L M n hn).val y := by
    simpa [dyadicJumpPrefixCount, t] using hcount
  simp only [dyadicJumpBlockMultiplier, dif_pos hn]
  rw [hcount']

private theorem dyadicJumpBlockMultiplier_bound (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold) (f : ℝ → ℂ)
    (i : Fin (M + 1)) (n : ℤ) (hn : n ∈ Finset.Ioc L (L + (M : ℤ)))
    (x : ℝ) :
    |dyadicJumpBlockMultiplier L M threshold hthreshold f i n x| ≤ 1 := by
  classical
  simp only [dyadicJumpBlockMultiplier, dif_pos hn]
  split_ifs <;> norm_num

/-- The signed coefficient attached to the active greedy block. -/
private def dyadicJumpSignedMultiplier (L : ℤ) (M : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) (f : ℝ → ℂ) (ω : jswSignSpace (M + 1))
    (n : ℤ) (x : ℝ) : ℝ :=
  if hn : n ∈ Finset.Ioc L (L + (M : ℤ)) then
    let t := dyadicJumpIndex L M n hn
    let c := dyadicJumpPrefixCount L threshold hthreshold f t.val x
    jswSignCoordinate (M + 1) ω ⟨c, by
      have hc := greedyPrefixStopCount_le
        (fun k => dyadicAverage (-(L + (k : ℤ))) f x)
        threshold hthreshold t.val
      exact Nat.lt_succ_of_le (Nat.le_trans hc (Nat.le_of_lt t.isLt))⟩
  else 0

private theorem dyadicJumpSignedMultiplier_predictable (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold) (f : ℝ → ℂ)
    (ω : jswSignSpace (M + 1)) (n : ℤ)
    (hn : n ∈ Finset.Ioc L (L + (M : ℤ))) (j : ℤ)
    {x y : ℝ} (hx : x ∈ dyadicInterval (1 - n) j)
    (hy : y ∈ dyadicInterval (1 - n) j) :
    dyadicJumpSignedMultiplier L M threshold hthreshold f ω n x =
      dyadicJumpSignedMultiplier L M threshold hthreshold f ω n y := by
  classical
  let t := dyadicJumpIndex L M n hn
  have hscale : L + ((t.val + 1 : ℕ) : ℤ) = n := by
    have h := dyadicJumpScale_index L M n hn
    dsimp [dyadicJumpScale] at h
    push_cast at h ⊢
    omega
  have hx' : x ∈ dyadicInterval (1 - (L + ((t.val + 1 : ℕ) : ℤ))) j := by
    rw [hscale]
    exact hx
  have hy' : y ∈ dyadicInterval (1 - (L + ((t.val + 1 : ℕ) : ℤ))) j := by
    rw [hscale]
    exact hy
  have hcount := greedyPrefixStopCount_eq_on_predictable_cell
    L t.val f threshold hthreshold j hx' hy'
  have hcount' : dyadicJumpPrefixCount L threshold hthreshold f
      (dyadicJumpIndex L M n hn).val x =
      dyadicJumpPrefixCount L threshold hthreshold f
        (dyadicJumpIndex L M n hn).val y := by
    simpa [dyadicJumpPrefixCount, t] using hcount
  simp only [dyadicJumpSignedMultiplier, dif_pos hn]
  apply congrArg (jswSignCoordinate (M + 1) ω)
  apply Fin.ext
  exact hcount'

private theorem dyadicJumpSignedMultiplier_bound (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold) (f : ℝ → ℂ)
    (ω : jswSignSpace (M + 1)) (n : ℤ)
    (hn : n ∈ Finset.Ioc L (L + (M : ℤ))) (x : ℝ) :
    |dyadicJumpSignedMultiplier L M threshold hthreshold f ω n x| ≤ 1 := by
  classical
  simp only [dyadicJumpSignedMultiplier, dif_pos hn]
  let t := dyadicJumpIndex L M n hn
  let c := dyadicJumpPrefixCount L threshold hthreshold f t.val x
  have hc : c ≤ t.val := by
    dsimp [c, dyadicJumpPrefixCount]
    exact greedyPrefixStopCount_le
      (fun k => dyadicAverage (-(L + (k : ℤ))) f x) threshold hthreshold t.val
  have hfin : c < M + 1 := Nat.lt_succ_of_le
    (Nat.le_trans hc (Nat.le_of_lt t.isLt))
  have hOne : |jswSignCoordinate (M + 1) ω (⟨c, hfin⟩ : Fin (M + 1))| = 1 :=
    jswSignCoordinate_abs_eq_one (M + 1) ω ⟨c, hfin⟩
  have hcoord : jswSignCoordinate (M + 1) ω
      (⟨dyadicJumpPrefixCount L threshold hthreshold f
        (dyadicJumpIndex L M n hn).val x, by
          have hc' := greedyPrefixStopCount_le
            (fun k => dyadicAverage (-(L + (k : ℤ))) f x)
            threshold hthreshold (dyadicJumpIndex L M n hn).val
          exact Nat.lt_succ_of_le (Nat.le_trans hc'
            (Nat.le_of_lt (dyadicJumpIndex L M n hn).isLt))⟩ : Fin (M + 1)) =
      jswSignCoordinate (M + 1) ω (⟨c, hfin⟩ : Fin (M + 1)) := by
    congr 1
  rw [hcoord, hOne]

private theorem dyadicJumpBlockMultiplier_at_scale {M : ℕ} (L : ℤ)
    (threshold : ℝ) (hthreshold : 0 < threshold) (f : ℝ → ℂ)
    (i : Fin (M + 1)) (t : Fin M) (x : ℝ) :
    dyadicJumpBlockMultiplier L M threshold hthreshold f i
      (dyadicJumpScale L t) x =
        if dyadicJumpPrefixCount L threshold hthreshold f t.val x = i.val
        then 1 else 0 := by
  classical
  unfold dyadicJumpBlockMultiplier
  rw [dif_pos (dyadicJumpScale_mem L t)]
  rw [dyadicJumpIndex_scale]

private theorem dyadicJumpSignedMultiplier_at_scale {M : ℕ} (L : ℤ)
    (threshold : ℝ) (hthreshold : 0 < threshold) (f : ℝ → ℂ)
    (ω : jswSignSpace (M + 1)) (t : Fin M) (x : ℝ) :
    dyadicJumpSignedMultiplier L M threshold hthreshold f ω
      (dyadicJumpScale L t) x =
        jswSignCoordinate (M + 1) ω
          ⟨dyadicJumpPrefixCount L threshold hthreshold f t.val x, by
            have hc := greedyPrefixStopCount_le
              (fun k => dyadicAverage (-(L + (k : ℤ))) f x)
              threshold hthreshold t.val
            exact Nat.lt_succ_of_le (Nat.le_trans hc (Nat.le_of_lt t.isLt))⟩ := by
  classical
  unfold dyadicJumpSignedMultiplier
  rw [dif_pos (dyadicJumpScale_mem L t)]
  change jswSignCoordinate (M + 1) ω
      (⟨dyadicJumpPrefixCount L threshold hthreshold f
        (dyadicJumpIndex L M (dyadicJumpScale L t)
          (dyadicJumpScale_mem L t)).val x, _⟩ : Fin (M + 1)) = _
  apply congrArg (jswSignCoordinate (M + 1) ω)
  apply Fin.ext
  simp [dyadicJumpIndex_scale]

private theorem dyadicJumpSignedMultiplier_eq_sum_blocks {M : ℕ}
    (L : ℤ) (threshold : ℝ) (hthreshold : 0 < threshold) (f : ℝ → ℂ)
    (ω : jswSignSpace (M + 1)) (n : ℤ)
    (hn : n ∈ Finset.Ioc L (L + (M : ℤ))) (x : ℝ) :
    (dyadicJumpSignedMultiplier L M threshold hthreshold f ω n x : ℂ) =
      ∑ i : Fin (M + 1),
        (jswSignCoordinate (M + 1) ω i : ℂ) *
          (dyadicJumpBlockMultiplier L M threshold hthreshold f i n x : ℂ) := by
  classical
  let t := dyadicJumpIndex L M n hn
  let c := dyadicJumpPrefixCount L threshold hthreshold f t.val x
  let k : Fin (M + 1) := ⟨c, by
    have hc := greedyPrefixStopCount_le
      (fun r => dyadicAverage (-(L + (r : ℤ))) f x) threshold hthreshold t.val
    exact Nat.lt_succ_of_le (Nat.le_trans hc (Nat.le_of_lt t.isLt))⟩
  have hscale : dyadicJumpScale L t = n := dyadicJumpScale_index L M n hn
  have hsign : dyadicJumpSignedMultiplier L M threshold hthreshold f ω n x =
      jswSignCoordinate (M + 1) ω k := by
    rw [← hscale]
    simpa [t, c, k] using
      (dyadicJumpSignedMultiplier_at_scale L threshold hthreshold f ω t x)
  rw [hsign]
  have hblock (i : Fin (M + 1)) :
      dyadicJumpBlockMultiplier L M threshold hthreshold f i n x =
        if i = k then 1 else 0 := by
    rw [← hscale]
    rw [dyadicJumpBlockMultiplier_at_scale]
    dsimp [c, k]
    by_cases h : dyadicJumpPrefixCount L threshold hthreshold f t.val x = i.val
    · have hi : i = k := Fin.ext h.symm
      rw [if_pos hi]
      simp [h]
    · have hi : i ≠ k := by
        intro heq
        apply h
        simpa [k] using (congrArg Fin.val heq).symm
      rw [if_neg hi]
      simp [h]
  calc
    (jswSignCoordinate (M + 1) ω k : ℂ) =
        ∑ i : Fin (M + 1), if i = k then
          (jswSignCoordinate (M + 1) ω i : ℂ) else 0 := by simp
    _ = ∑ i : Fin (M + 1),
        (jswSignCoordinate (M + 1) ω i : ℂ) *
          (dyadicJumpBlockMultiplier L M threshold hthreshold f i n x : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hblock i]
      split_ifs <;> simp

/-- The `Lᵖ` output assigned to one greedy block, with the input frozen in
the predictable coefficient. -/
private def dyadicJumpLpBlockOutput {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (i : Fin (M + 1)) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
  dyadicPredictableTransformLpCLM hp (Finset.Ioc L (L + (M : ℤ)))
    (dyadicJumpBlockMultiplier L M threshold hthreshold (f : ℝ → ℂ) i)
    (by
      intro n hn j x y hx hy
      exact dyadicJumpBlockMultiplier_predictable L M threshold hthreshold
        (f : ℝ → ℂ) i n hn j hx hy)
    (by
      intro n hn x
      exact dyadicJumpBlockMultiplier_bound L M threshold hthreshold
        (f : ℝ → ℂ) i n hn x)
    f

/-- The predictable transform with the sign of the active greedy block. -/
private def dyadicJumpSignedOutput {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (ω : jswSignSpace (M + 1)) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
  dyadicPredictableTransformLpCLM hp (Finset.Ioc L (L + (M : ℤ)))
    (dyadicJumpSignedMultiplier L M threshold hthreshold (f : ℝ → ℂ) ω)
    (by
      intro n hn j x y hx hy
      exact dyadicJumpSignedMultiplier_predictable L M threshold hthreshold
        (f : ℝ → ℂ) ω n hn j hx hy)
    (by
      intro n hn x
      exact dyadicJumpSignedMultiplier_bound L M threshold hthreshold
        (f : ℝ → ℂ) ω n hn x)
    f

private theorem dyadicJumpSignedOutput_bound {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hM : 0 < M) (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (ω : jswSignSpace (M + 1)) :
    ‖dyadicJumpSignedOutput hp L M threshold hthreshold f ω‖ ≤
      weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖ := by
  unfold dyadicJumpSignedOutput
  exact dyadicPredictableTransformLpCLM_interval_bound hp L
    (L + (M : ℤ)) (by
      have hM' : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
      omega)
    (dyadicJumpSignedMultiplier L M threshold hthreshold (f : ℝ → ℂ) ω)
    (by
      intro n hLn hnN j x y hx hy
      exact dyadicJumpSignedMultiplier_predictable L M threshold hthreshold
        (f : ℝ → ℂ) ω n (Finset.mem_Ioc.mpr ⟨hLn, hnN⟩) j hx hy)
    (by
      intro n hLn hnN x
      exact dyadicJumpSignedMultiplier_bound L M threshold hthreshold
        (f : ℝ → ℂ) ω n (Finset.mem_Ioc.mpr ⟨hLn, hnN⟩) x)
    f

private theorem dyadicJumpLpBlockOutput_ae {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (i : Fin (M + 1)) :
    (dyadicJumpLpBlockOutput hp L M threshold hthreshold f i : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ n ∈ Finset.Ioc L (L + (M : ℤ)),
        (dyadicJumpBlockMultiplier L M threshold hthreshold f i n x : ℂ) *
          dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
  unfold dyadicJumpLpBlockOutput
  exact dyadicPredictableTransformLpCLM_coeFn hp
    (Finset.Ioc L (L + (M : ℤ)))
    (dyadicJumpBlockMultiplier L M threshold hthreshold (f : ℝ → ℂ) i)
    (by
      intro n hn j x y hx hy
      exact dyadicJumpBlockMultiplier_predictable L M threshold hthreshold
        (f : ℝ → ℂ) i n hn j hx hy)
    (by
      intro n hn x
      exact dyadicJumpBlockMultiplier_bound L M threshold hthreshold
        (f : ℝ → ℂ) i n hn x)
    f

private theorem dyadicJumpSignedOutput_ae {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (ω : jswSignSpace (M + 1)) :
    (dyadicJumpSignedOutput hp L M threshold hthreshold f ω : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ n ∈ Finset.Ioc L (L + (M : ℤ)),
        (dyadicJumpSignedMultiplier L M threshold hthreshold
          (f : ℝ → ℂ) ω n x : ℂ) *
          dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
  unfold dyadicJumpSignedOutput
  exact dyadicPredictableTransformLpCLM_coeFn hp
    (Finset.Ioc L (L + (M : ℤ)))
    (dyadicJumpSignedMultiplier L M threshold hthreshold (f : ℝ → ℂ) ω)
    (by
      intro n hn j x y hx hy
      exact dyadicJumpSignedMultiplier_predictable L M threshold hthreshold
        (f : ℝ → ℂ) ω n hn j hx hy)
    (by
      intro n hn x
      exact dyadicJumpSignedMultiplier_bound L M threshold hthreshold
        (f : ℝ → ℂ) ω n hn x)
    f

private theorem dyadicJumpLpBlockOutput_ae_finSum {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (i : Fin (M + 1)) :
    (dyadicJumpLpBlockOutput hp L M threshold hthreshold f i : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ t : Fin M,
        if dyadicJumpPrefixCount L threshold hthreshold (f : ℝ → ℂ)
            t.val x = i.val then
          dyadicMartingaleDifference (dyadicJumpScale L t) (f : ℝ → ℂ) x
        else 0 := by
  filter_upwards [dyadicJumpLpBlockOutput_ae hp L M threshold hthreshold f i]
    with x hx
  calc
    (dyadicJumpLpBlockOutput hp L M threshold hthreshold f i : ℝ → ℂ) x =
        ∑ n ∈ Finset.Ioc L (L + (M : ℤ)),
          (dyadicJumpBlockMultiplier L M threshold hthreshold
            (f : ℝ → ℂ) i n x : ℂ) *
            dyadicMartingaleDifference n (f : ℝ → ℂ) x := hx
    _ = ∑ t : Fin M,
          (dyadicJumpBlockMultiplier L M threshold hthreshold
            (f : ℝ → ℂ) i (dyadicJumpScale L t) x : ℂ) *
            dyadicMartingaleDifference (dyadicJumpScale L t)
              (f : ℝ → ℂ) x := by
          rw [sum_Ioc_eq_sum_fin]
    _ = ∑ t : Fin M,
          if dyadicJumpPrefixCount L threshold hthreshold (f : ℝ → ℂ)
              t.val x = i.val then
            dyadicMartingaleDifference (dyadicJumpScale L t) (f : ℝ → ℂ) x
          else 0 := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [dyadicJumpBlockMultiplier_at_scale]
          split_ifs <;> simp

private theorem sum_fin_indicator_Ico {M a b : ℕ} (hb : b ≤ M)
    (g : ℕ → ℂ) :
    ∑ t : Fin M, (if a ≤ t.val ∧ t.val < b then g t.val else 0) =
      ∑ k ∈ Finset.Ico a b, g k := by
  classical
  let F : Finset (Fin M) := Finset.univ.filter
    (fun t => a ≤ t.val ∧ t.val < b)
  have himage : F.image (fun t : Fin M => t.val) = Finset.Ico a b := by
    ext k
    simp only [F, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨t, ⟨ha, htb⟩, rfl⟩
      exact ⟨ha, htb⟩
    · rintro ⟨ha, hkb⟩
      refine ⟨⟨k, ?_⟩, ⟨ha, hkb⟩, rfl⟩
      omega
  have hinj : Set.InjOn (fun t : Fin M => t.val) (↑F) := by
    intro s hs t ht hst
    exact Fin.ext hst
  calc
    ∑ t : Fin M, (if a ≤ t.val ∧ t.val < b then g t.val else 0) =
        ∑ t ∈ F, g t.val := by
          rw [← Finset.sum_filter]
    _ = ∑ k ∈ F.image (fun t : Fin M => t.val), g k :=
          (Finset.sum_image (f := g) hinj).symm
    _ = ∑ k ∈ Finset.Ico a b, g k := by rw [himage]

private theorem sum_Ico_telescope (u : ℕ → ℂ) (a b : ℕ) (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (u (k + 1) - u k) = u b - u a := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp
  | succ b ih =>
      by_cases hab' : a ≤ b
      · rw [Finset.sum_Ico_succ_top hab', ih a hab']
        ring
      · have ha : a = b + 1 := by omega
        subst a
        simp

/-- The increments assigned to a completed greedy block telescope between
its two stopping points. The prefix sequence may be any extension of the
finite input, since only indices through `M` occur. -/
private theorem greedyRun_block_sum_eq_increment
    {M : ℕ} {u : Fin (M + 1) → ℂ} {threshold : ℝ} {G : ℕ}
    (run : GreedyStopRun u threshold G) (uNat : ℕ → ℂ)
    (hthreshold : 0 < threshold)
    (hprefix : ∀ k (hk : k ≤ M),
      u ⟨k, by omega⟩ = uNat k)
    (d : Fin M → ℂ)
    (hd : ∀ t : Fin M, d t = uNat (t.val + 1) - uNat t.val)
    (i : Fin G) :
    (∑ t : Fin M,
      if greedyPrefixStopCount uNat threshold hthreshold t.val = i.val
      then d t else 0) =
        uNat (run.point i.succ).val - uNat (run.point i.castSucc).val := by
  let a := (run.point i.castSucc).val
  let b := (run.point i.succ).val
  have haM : a ≤ M := by
    dsimp [a]
    exact Nat.le_of_lt_succ (run.point i.castSucc).isLt
  have hbM : b ≤ M := by
    dsimp [b]
    exact Nat.le_of_lt_succ (run.point i.succ).isLt
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Nat.le_of_lt (Fin.lt_iff_val_lt_val.mp
      (run.strict i.castSucc_lt_succ))
  have hlabel (t : Fin M) :
      (greedyRunActiveLabel run t).val =
        greedyPrefixStopCount uNat threshold hthreshold t.val := by
    apply greedyRunActiveLabel_val_eq_prefixCount run t hthreshold
    intro k hkt
    exact hprefix k (by omega)
  have hinterval (t : Fin M) :
      greedyPrefixStopCount uNat threshold hthreshold t.val = i.val ↔
        a ≤ t.val ∧ t.val < b := by
    have hlastval :
        (greedyLastStopIndex run t.castSucc).val =
          greedyPrefixStopCount uNat threshold hthreshold t.val := by
      simpa [greedyRunActiveLabel] using (hlabel t)
    constructor
    · intro hcount
      have hlast : greedyLastStopIndex run t.castSucc = i.castSucc :=
        Fin.ext (by rw [hlastval]; exact hcount)
      have hstops :=
        greedyLastStopIndex_stop_interval_of_eq run t.castSucc i hlast
      constructor
      · have h := Fin.le_iff_val_le_val.mp hstops.1
        simpa [a] using h
      · have h := Fin.lt_iff_val_lt_val.mp hstops.2
        simpa [b] using h
    · rintro ⟨hleft, hright⟩
      have hleft' : run.point i.castSucc ≤ t.castSucc :=
        Fin.le_iff_val_le_val.mpr (by simpa [a] using hleft)
      have hright' : t.castSucc < run.point i.succ :=
        Fin.lt_iff_val_lt_val.mpr (by simpa [b] using hright)
      have hlast := greedyLastStopIndex_eq_of_stop_interval
        run t.castSucc i hleft' hright'
      rw [← hlastval]
      exact congrArg Fin.val hlast
  calc
    (∑ t : Fin M,
      if greedyPrefixStopCount uNat threshold hthreshold t.val = i.val
      then d t else 0) =
        ∑ t : Fin M,
          if a ≤ t.val ∧ t.val < b then
            uNat (t.val + 1) - uNat t.val else 0 := by
          apply Finset.sum_congr rfl
          intro t ht
          by_cases hc :
              greedyPrefixStopCount uNat threshold hthreshold t.val = i.val
          · have hi := (hinterval t).mp hc
            simp [hc, hi, hd t]
          · have hi : ¬ (a ≤ t.val ∧ t.val < b) := by
              intro h
              exact hc ((hinterval t).mpr h)
            simp [hc, hi, hd t]
    _ = ∑ k ∈ Finset.Ico a b, (uNat (k + 1) - uNat k) :=
          sum_fin_indicator_Ico hbM (fun k => uNat (k + 1) - uNat k)
    _ = uNat b - uNat a := sum_Ico_telescope uNat a b hab
    _ = uNat (run.point i.succ).val - uNat (run.point i.castSucc).val := by
          rfl

/-- Pointwise, the threshold jump count is controlled by the square function
of all grouped increments, including the unfinished last block. -/
private theorem dyadicJumpCount_le_blockSquare_ae {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    ∀ᵐ x ∂volume,
      threshold * Real.sqrt (finiteSeparatedJumpCount
        (fun i : Fin (M + 1) =>
          dyadicAverage (-(L + (i.val : ℤ))) (f : ℝ → ℂ) x)
        threshold : ℝ) ≤
        2 * Real.sqrt (∑ i : Fin (M + 1),
          ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f i x‖ ^ 2) := by
  have hblocks : ∀ᵐ x ∂volume, ∀ i : Fin (M + 1),
      (dyadicJumpLpBlockOutput hp L M threshold hthreshold f i : ℝ → ℂ) x =
        ∑ t : Fin M,
          if dyadicJumpPrefixCount L threshold hthreshold (f : ℝ → ℂ)
              t.val x = i.val then
            dyadicMartingaleDifference (dyadicJumpScale L t) (f : ℝ → ℂ) x
          else 0 := by
    rw [Filter.eventually_all]
    exact dyadicJumpLpBlockOutput_ae_finSum hp L M threshold hthreshold f
  filter_upwards [hblocks] with x hxblocks
  let uNat : ℕ → ℂ := fun k =>
    dyadicAverage (-(L + (k : ℤ))) (f : ℝ → ℂ) x
  let input : Fin (M + 1) → ℂ := fun i => uNat i.val
  let choice := greedyStopRunChoice (I := Fin (M + 1)) input threshold hthreshold
  let run := choice.2
  have hlen : choice.1 ≤ M := greedyStopRun_length_le run
  let embed : Fin choice.1 → Fin (M + 1) := fun i =>
    ⟨i.val, by omega⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    apply Fin.ext
    simpa [embed] using congrArg (fun k : Fin (M + 1) => k.val) hij
  have hinc (i : Fin choice.1) :
      (dyadicJumpLpBlockOutput hp L M threshold hthreshold f (embed i) :
        ℝ → ℂ) x =
        uNat (run.point i.succ).val - uNat (run.point i.castSucc).val := by
    have htel := greedyRun_block_sum_eq_increment run uNat hthreshold
      (by intro k hk; rfl)
      (fun t => dyadicMartingaleDifference (dyadicJumpScale L t)
        (f : ℝ → ℂ) x)
      (by
        intro t
        simp only [dyadicMartingaleDifference, dyadicIncreasingAverage,
          dyadicJumpScale, uNat]
        norm_num [Nat.cast_add, Nat.cast_one]
        congr 1 <;> ring) i
    calc
      (dyadicJumpLpBlockOutput hp L M threshold hthreshold f (embed i) :
          ℝ → ℂ) x =
          ∑ t : Fin M,
            if dyadicJumpPrefixCount L threshold hthreshold
                (f : ℝ → ℂ) t.val x = (embed i).val then
              dyadicMartingaleDifference (dyadicJumpScale L t)
                (f : ℝ → ℂ) x else 0 := hxblocks (embed i)
      _ = ∑ t : Fin M,
            if dyadicJumpPrefixCount L threshold hthreshold
                (f : ℝ → ℂ) t.val x = i.val then
              dyadicMartingaleDifference (dyadicJumpScale L t)
                (f : ℝ → ℂ) x else 0 := by simp [embed]
      _ = uNat (run.point i.succ).val - uNat (run.point i.castSucc).val := htel
  have hjump := greedyJumpCountSqrt_le_completedSquare input threshold
    hthreshold run
  let S : Finset (Fin (M + 1)) :=
    (Finset.univ : Finset (Fin choice.1)).image embed
  have hS :
      (∑ j ∈ S,
        ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f j x‖ ^ 2) =
      ∑ i : Fin choice.1,
        ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f (embed i) x‖ ^ 2 := by
    dsimp [S]
    have hinj : Set.InjOn embed
        ↑(Finset.univ : Finset (Fin choice.1)) := by
      intro i hi j hj hij
      exact hembed hij
    rw [Finset.sum_image (f := fun j =>
      ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f j x‖ ^ 2) hinj]
  have hsub : S ⊆ Finset.univ := by simp [S]
  have hsum :
      (∑ i : Fin choice.1,
        ‖uNat (run.point i.succ).val -
          uNat (run.point i.castSucc).val‖ ^ 2) ≤
      ∑ j : Fin (M + 1),
        ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f j x‖ ^ 2 := by
    calc
      ∑ i : Fin choice.1,
          ‖uNat (run.point i.succ).val -
            uNat (run.point i.castSucc).val‖ ^ 2 =
        ∑ j ∈ S,
          ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f j x‖ ^ 2 := by
            rw [hS]
            apply Finset.sum_congr rfl
            intro i hi
            rw [← hinc i]
      _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin (M + 1))),
          ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f j x‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (by
              intro j hj hnot
              positivity)
      _ = ∑ j : Fin (M + 1),
          ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f j x‖ ^ 2 := by simp
  have hroot := Real.sqrt_le_sqrt hsum
  calc
    threshold * Real.sqrt (finiteSeparatedJumpCount input threshold : ℝ) ≤
        2 * Real.sqrt (∑ i : Fin choice.1,
          ‖input (run.point i.succ) - input (run.point i.castSucc)‖ ^ 2) := hjump
    _ ≤ 2 * Real.sqrt (∑ i : Fin (M + 1),
          ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f i x‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hroot (by norm_num)
    _ = 2 * Real.sqrt (∑ i : Fin (M + 1),
          ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f i x‖ ^ 2) := rfl

private theorem lpFiniteComplexSmulSum_ae {q : ℝ≥0∞} {m : ℕ}
    (c : Fin m → ℂ) (V : Fin m → Lp ℂ q (volume : Measure ℝ)) :
    ((∑ i : Fin m, c i • V i : Lp ℂ q (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ i : Fin m, c i * (V i : ℝ → ℂ) x := by
  classical
  let F : Finset (Fin m) := Finset.univ
  have hcoe := Lp.coeFn_finsetSum F (fun i => c i • V i)
  have hsmul : ∀ᵐ x ∂volume, ∀ i ∈ F,
      ((c i • V i : Lp ℂ q volume) : ℝ → ℂ) x = c i * (V i : ℝ → ℂ) x := by
    rw [Finset.eventually_all]
    intro i hi
    filter_upwards [Lp.coeFn_smul (c i) (V i)] with x hx
    simpa [smul_eq_mul] using hx
  filter_upwards [hcoe, hsmul] with x hcoe hsmul
  have hcoe' :
      (((∑ i ∈ F, c i • V i : Lp ℂ q volume) : ℝ → ℂ) x) =
        ∑ i ∈ F, ((c i • V i : Lp ℂ q volume) : ℝ → ℂ) x := by
    simpa only [Finset.sum_apply] using hcoe
  calc
    ((∑ i : Fin m, c i • V i : Lp ℂ q volume) : ℝ → ℂ) x =
        ∑ i ∈ F, ((c i • V i : Lp ℂ q volume) : ℝ → ℂ) x := by
          simpa [F] using hcoe'
    _ = ∑ i : Fin m, c i * (V i : ℝ → ℂ) x := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hsmul i hi

private theorem dyadicJumpSignedOutput_eq_blockSum {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold) (hM : 0 < M)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (ω : jswSignSpace (M + 1)) :
    dyadicJumpSignedOutput hp L M threshold hthreshold f ω =
      ∑ i : Fin (M + 1),
        (jswSignCoordinate (M + 1) ω i : ℂ) •
          dyadicJumpLpBlockOutput hp L M threshold hthreshold f i := by
  classical
  apply Lp.ext
  have hsign := dyadicJumpSignedOutput_ae hp L M threshold hthreshold f ω
  have hblock (i : Fin (M + 1)) :=
    dyadicJumpLpBlockOutput_ae hp L M threshold hthreshold f i
  have hblockAll : ∀ᵐ x ∂volume, ∀ i : Fin (M + 1),
      (dyadicJumpLpBlockOutput hp L M threshold hthreshold f i : ℝ → ℂ) x =
        ∑ n ∈ Finset.Ioc L (L + (M : ℤ)),
          (dyadicJumpBlockMultiplier L M threshold hthreshold
            (f : ℝ → ℂ) i n x : ℂ) *
            dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
    rw [Filter.eventually_all]
    exact hblock
  let c : Fin (M + 1) → ℂ := fun i =>
    (jswSignCoordinate (M + 1) ω i : ℂ)
  let V : Fin (M + 1) → Lp ℂ (ENNReal.ofReal p) volume :=
    fun i => dyadicJumpLpBlockOutput hp L M threshold hthreshold f i
  have hsum := lpFiniteComplexSmulSum_ae c V
  filter_upwards [hsign, hblockAll, hsum] with x hs hb hv
  calc
    (dyadicJumpSignedOutput hp L M threshold hthreshold f ω : ℝ → ℂ) x =
        ∑ n ∈ Finset.Ioc L (L + (M : ℤ)),
          (dyadicJumpSignedMultiplier L M threshold hthreshold
            (f : ℝ → ℂ) ω n x : ℂ) *
            dyadicMartingaleDifference n (f : ℝ → ℂ) x := hs
    _ = ∑ n ∈ Finset.Ioc L (L + (M : ℤ)),
          ∑ i : Fin (M + 1),
            (jswSignCoordinate (M + 1) ω i : ℂ) *
              (dyadicJumpBlockMultiplier L M threshold hthreshold
                (f : ℝ → ℂ) i n x : ℂ) *
              dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [dyadicJumpSignedMultiplier_eq_sum_blocks
            L threshold hthreshold (f : ℝ → ℂ) ω n hn x]
          rw [Finset.sum_mul]
    _ = ∑ i : Fin (M + 1),
          (jswSignCoordinate (M + 1) ω i : ℂ) *
            ∑ n ∈ Finset.Ioc L (L + (M : ℤ)),
              (dyadicJumpBlockMultiplier L M threshold hthreshold
                (f : ℝ → ℂ) i n x : ℂ) *
                dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          calc
            ∑ n ∈ Finset.Ioc L (L + (M : ℤ)),
                (jswSignCoordinate (M + 1) ω i : ℂ) *
                  (dyadicJumpBlockMultiplier L M threshold hthreshold
                    (f : ℝ → ℂ) i n x : ℂ) *
                  dyadicMartingaleDifference n (f : ℝ → ℂ) x =
                ∑ n ∈ Finset.Ioc L (L + (M : ℤ)),
                  (jswSignCoordinate (M + 1) ω i : ℂ) *
                    ((dyadicJumpBlockMultiplier L M threshold hthreshold
                      (f : ℝ → ℂ) i n x : ℂ) *
                      dyadicMartingaleDifference n (f : ℝ → ℂ) x) := by
                    apply Finset.sum_congr rfl
                    intro n hn
                    ring
            _ = (jswSignCoordinate (M + 1) ω i : ℂ) *
                ∑ n ∈ Finset.Ioc L (L + (M : ℤ)),
                  (dyadicJumpBlockMultiplier L M threshold hthreshold
                    (f : ℝ → ℂ) i n x : ℂ) *
                    dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
                    rw [← Finset.mul_sum]
    _ = ∑ i : Fin (M + 1),
          (jswSignCoordinate (M + 1) ω i : ℂ) *
            (dyadicJumpLpBlockOutput hp L M threshold hthreshold f i : ℝ → ℂ) x := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← hb i]
    _ = (((∑ i : Fin (M + 1), c i • V i :
          Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) x) := by
          simpa [c, V, smul_eq_mul] using hv.symm

private theorem dyadicJumpBlockSquareLpBound {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold) (hM : 0 < M)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    lpNorm (fun x : ℝ => Real.sqrt (∑ i : Fin (M + 1),
        ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f i x‖ ^ 2))
      (ENNReal.ofReal p) volume ≤
        (littlewoodPaleyCp p)⁻¹ *
          (weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖) := by
  classical
  let V : Fin (M + 1) → Lp ℂ (ENNReal.ofReal p) volume :=
    fun i => dyadicJumpLpBlockOutput hp L M threshold hthreshold f i
  let S : jswSignSpace (M + 1) → Lp ℂ (ENNReal.ofReal p) volume :=
    fun ω => dyadicJumpSignedOutput hp L M threshold hthreshold f ω
  let R : ℝ := weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖
  have hS : ∀ ω : jswSignSpace (M + 1), (S ω : ℝ → ℂ) =ᵐ[volume]
      fun x => jswSignSum (M + 1) ω (fun i => V i x) := by
    intro ω
    have hEq := dyadicJumpSignedOutput_eq_blockSum hp L M threshold
      hthreshold hM f ω
    have hEqAE := Lp.ext_iff.mp hEq
    have hsum := lpFiniteComplexSmulSum_ae
      (fun i : Fin (M + 1) => (jswSignCoordinate (M + 1) ω i : ℂ)) V
    filter_upwards [hEqAE, hsum] with x hEq hx
    calc
      (S ω : ℝ → ℂ) x =
          ((∑ i : Fin (M + 1),
            (jswSignCoordinate (M + 1) ω i : ℂ) • V i :
            Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) x := by
              exact hEq
      _ = ∑ i : Fin (M + 1),
            (jswSignCoordinate (M + 1) ω i : ℂ) * (V i : ℝ → ℂ) x := hx
      _ = jswSignSum (M + 1) ω (fun i => V i x) := by
            rw [jswSignSum_eq_sum_signCoordinate]
  have hbound : ∀ ω : jswSignSpace (M + 1), ‖S ω‖ ≤ R := by
    intro ω
    exact dyadicJumpSignedOutput_bound hp L M threshold hthreshold hM f ω
  have hR : 0 ≤ R := by
    let ω : jswSignSpace (M + 1) := Classical.choice inferInstance
    have hnorm := norm_nonneg (S ω)
    have hboundω := hbound ω
    dsimp [R] at hboundω ⊢
    linarith
  simpa [V, R, S] using
    (finiteSignSquareLpBound hp (M + 1) V S hS hR hbound)

private theorem dyadicJumpBlockSquare_memLp {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (L : ℤ) (M : ℕ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    MemLp (fun x : ℝ => Real.sqrt (∑ i : Fin (M + 1),
      ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f i x‖ ^ 2))
      (ENNReal.ofReal p) volume := by
  let V : Fin (M + 1) → Lp ℂ (ENNReal.ofReal p) volume :=
    fun i => dyadicJumpLpBlockOutput hp L M threshold hthreshold f i
  let g : ℝ → ℝ := fun x => ∑ i : Fin (M + 1), ‖V i x‖
  have hg : MemLp g (ENNReal.ofReal p) volume := by
    apply memLp_finsetSum (Finset.univ : Finset (Fin (M + 1)))
    intro i hi
    exact (Lp.memLp (V i)).norm
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => Real.sqrt (∑ i : Fin (M + 1),
        ‖V i x‖ ^ 2)) volume := by
    fun_prop
  have hpoint (x : ℝ) :
      Real.sqrt (∑ i : Fin (M + 1), ‖V i x‖ ^ 2) ≤ g x := by
    have hsumsq := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset (Fin (M + 1))))
      (f := fun i => ‖V i x‖) (by intro i hi; positivity)
    have hsum0 : 0 ≤ ∑ i : Fin (M + 1), ‖V i x‖ := by positivity
    calc
      Real.sqrt (∑ i : Fin (M + 1), ‖V i x‖ ^ 2) ≤
          Real.sqrt ((∑ i : Fin (M + 1), ‖V i x‖) ^ 2) :=
            Real.sqrt_le_sqrt hsumsq
      _ = g x := by simp [g, Real.sqrt_sq_eq_abs, abs_of_nonneg hsum0]
  have hpoint' (x : ℝ) :
      ‖Real.sqrt (∑ i : Fin (M + 1), ‖V i x‖ ^ 2)‖ ≤ g x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hpoint x
  have hV := hg.mono' hmeas (Filter.Eventually.of_forall hpoint')
  simpa [V] using hV

/-- The exact finite-interval jump estimate for the increasing dyadic
averages `E_{-(L+k)}`. -/
theorem dyadicJumpIntervalLpBound {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (L : ℤ) (M : ℕ)
    (hM : 0 < M) (threshold : ℝ) (hthreshold : 0 < threshold)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    lpNorm (fun x : ℝ => threshold * Real.sqrt (finiteSeparatedJumpCount
      (fun i : Fin (M + 1) =>
        dyadicAverage (-(L + (i.val : ℤ))) (f : ℝ → ℂ) x)
      threshold : ℝ)) (ENNReal.ofReal p) volume ≤
        2 * (littlewoodPaleyCp p)⁻¹ *
          (weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖) := by
  let square : ℝ → ℝ := fun x => Real.sqrt (∑ i : Fin (M + 1),
    ‖dyadicJumpLpBlockOutput hp L M threshold hthreshold f i x‖ ^ 2)
  let jump : ℝ → ℝ := fun x => threshold * Real.sqrt
    (finiteSeparatedJumpCount
      (fun i : Fin (M + 1) =>
        dyadicAverage (-(L + (i.val : ℤ))) (f : ℝ → ℂ) x)
      threshold : ℝ)
  have hsquare : MemLp square (ENNReal.ofReal p) volume := by
    simpa [square] using
      dyadicJumpBlockSquare_memLp hp L M threshold hthreshold f
  have hgood : MemLp (fun x : ℝ => 2 * square x)
      (ENNReal.ofReal p) volume := hsquare.const_mul 2
  have hpoint := dyadicJumpCount_le_blockSquare_ae
    hp L M threshold hthreshold f
  have hdom : ∀ᵐ x ∂volume, ‖jump x‖ ≤ 2 * square x := by
    filter_upwards [hpoint] with x hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hthreshold.le (Real.sqrt_nonneg _))]
    simpa [jump, square] using hx
  have hmono : lpNorm jump (ENNReal.ofReal p) volume ≤
      lpNorm (fun x : ℝ => 2 * square x) (ENNReal.ofReal p) volume := by
    by_cases hjump : AEStronglyMeasurable jump volume
    · rw [← toReal_eLpNorm, ← toReal_eLpNorm]
      exact ENNReal.toNNReal_mono hgood.eLpNorm_ne_top
        (eLpNorm_mono_ae_real hjump hdom)
    · rw [lpNorm_of_not_aestronglyMeasurable hjump]
      exact lpNorm_nonneg (f := fun x : ℝ => 2 * square x)
  have hscale : lpNorm (fun x : ℝ => 2 * square x)
      (ENNReal.ofReal p) volume = 2 * lpNorm square
        (ENNReal.ofReal p) volume := by
    simpa [Pi.mul_def] using
      (lpNorm_natCast_mul (𝕜 := ℝ) 2 square (ENNReal.ofReal p) volume)
  have hsquareBound := dyadicJumpBlockSquareLpBound hp L M threshold
    hthreshold hM f
  calc
    lpNorm jump (ENNReal.ofReal p) volume ≤
        lpNorm (fun x : ℝ => 2 * square x) (ENNReal.ofReal p) volume := hmono
    _ = 2 * lpNorm square (ENNReal.ofReal p) volume := hscale
    _ ≤ 2 * ((littlewoodPaleyCp p)⁻¹ *
        (weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖)) :=
          mul_le_mul_of_nonneg_left hsquareBound (by norm_num)
    _ = 2 * (littlewoodPaleyCp p)⁻¹ *
        (weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖) := by ring

private theorem finiteSeparatedJumpCount_eq_zero_of_constant
    {I : Type*} [LinearOrder I] [Fintype I]
    (c : ℂ) (threshold : ℝ) (hthreshold : 0 < threshold) :
    finiteSeparatedJumpCount (fun _ : I => c) threshold = 0 := by
  classical
  by_contra hne
  have hpos : 0 < finiteSeparatedJumpCount (fun _ : I => c) threshold :=
    Nat.pos_of_ne_zero hne
  obtain ⟨s, t, hfamily⟩ :=
    finiteSeparatedJumpCount_isAttained (fun _ : I => c) threshold
  have hlarge := hfamily.2 ⟨0, hpos⟩
  have hnegative : threshold < 0 := by simpa using hlarge
  linarith

private theorem finiteSeparatedJumpCount_le_of_monotoneMap
    {I J : Type*} [LinearOrder I] [Fintype I]
    [LinearOrder J] [Fintype J]
    (u : I → ℂ) (v : J → ℂ) (threshold : ℝ)
    (φ : I → J) (hφ : Monotone φ)
    (hvalues : ∀ i, u i = v (φ i))
    (hstrict : ∀ i j, i < j → threshold < ‖u j - u i‖ → φ i < φ j) :
    finiteSeparatedJumpCount u threshold ≤
      finiteSeparatedJumpCount v threshold := by
  classical
  obtain ⟨s, t, hfamily⟩ := finiteSeparatedJumpCount_isAttained u threshold
  apply le_finiteSeparatedJumpCount_of_family
  refine ⟨fun i => φ (s i), fun i => φ (t i), ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    exact hstrict (s i) (t i) (hfamily.1.1 i) (hfamily.2 i)
  · intro i j hij
    exact hφ (hfamily.1.2 i j hij)
  · intro i
    change threshold < ‖v (φ (t i)) - v (φ (s i))‖
    rw [← hvalues (t i), ← hvalues (s i)]
    exact hfamily.2 i

/-- A monotone finite sequence of dyadic averages embeds into the complete
interval between its first and last filtration times. Repeated times are
allowed: a large jump forces its two endpoint times to be distinct. -/
private theorem dyadicFiniteJumpCount_le_interval
    {M : ℕ} (time : Fin (M + 1) → ℤ) (htime : Monotone time)
    (L : ℤ) (D : ℕ)
    (hfirst : time 0 = L)
    (hlast : time (Fin.last M) = L + (D : ℤ))
    (f : ℝ → ℂ) (x : ℝ) (threshold : ℝ) (hthreshold : 0 < threshold) :
    finiteSeparatedJumpCount
      (fun i : Fin (M + 1) => dyadicAverage (-time i) f x) threshold ≤
    finiteSeparatedJumpCount
      (fun i : Fin (D + 1) =>
        dyadicAverage (-(L + (i.val : ℤ))) f x) threshold := by
  let source : Fin (M + 1) → ℂ := fun i => dyadicAverage (-time i) f x
  let target : Fin (D + 1) → ℂ := fun i =>
    dyadicAverage (-(L + (i.val : ℤ))) f x
  have hbounds (i : Fin (M + 1)) : L ≤ time i ∧ time i ≤ L + (D : ℤ) := by
    constructor
    · rw [← hfirst]
      exact htime (Fin.zero_le i)
    · rw [← hlast]
      exact htime (Fin.le_last i)
  let embed : Fin (M + 1) → Fin (D + 1) := fun i =>
    ⟨(time i - L).toNat, by
      have hbound := hbounds i
      have hnonneg : 0 ≤ time i - L := by omega
      have hupper : time i - L ≤ (D : ℤ) := by omega
      have hcast : ((time i - L).toNat : ℤ) = time i - L :=
        Int.toNat_of_nonneg hnonneg
      have hnat : (time i - L).toNat ≤ D := by
        exact_mod_cast (show ((time i - L).toNat : ℤ) ≤ (D : ℤ) by
          rw [hcast]
          exact_mod_cast hupper)
      exact Nat.lt_succ_of_le hnat⟩
  have hembedVal (i : Fin (M + 1)) :
      ((embed i).val : ℤ) = time i - L := by
    dsimp [embed]
    exact Int.toNat_of_nonneg (by have hbound := hbounds i; omega)
  have hmono : Monotone embed := by
    intro i j hij
    apply Fin.le_iff_val_le_val.mpr
    have htimeij := htime hij
    have hcast : ((embed i).val : ℤ) ≤ ((embed j).val : ℤ) := by
      rw [hembedVal, hembedVal]
      omega
    exact_mod_cast hcast
  have hvalues (i : Fin (M + 1)) : source i = target (embed i) := by
    dsimp [source, target]
    congr 1
    rw [hembedVal]
    ring
  have hstrict (i j : Fin (M + 1)) (hij : i < j)
      (hlarge : threshold < ‖source j - source i‖) : embed i < embed j := by
    have htimeij : time i ≤ time j := htime hij.le
    by_contra hnot
    have hembed : embed i = embed j :=
      le_antisymm (hmono hij.le) (le_of_not_gt hnot)
    have htimeeq : time i = time j := by
      have h := congrArg (fun k : Fin (D + 1) => (k.val : ℤ)) hembed
      rw [hembedVal, hembedVal] at h
      linarith
    have hsourceeq : source i = source j := by
      dsimp [source]
      rw [htimeeq]
    have hzero : ‖source j - source i‖ = 0 := by rw [hsourceeq]; simp
    rw [hzero] at hlarge
    linarith
  exact finiteSeparatedJumpCount_le_of_monotoneMap source target threshold
    embed hmono hvalues hstrict

theorem weakTypeJumpConstant_nonneg {p : ℝ} (hp : 1 < p) :
    0 ≤ weakTypeFromOffSupportStrongConstant p 1 0 := by
  unfold weakTypeFromOffSupportStrongConstant
  by_cases hlt : p < 2
  · rw [if_pos hlt]
    have hpminus : 0 < p - 1 := by linarith
    have htwominus : 0 < 2 - p := by linarith
    have hI : 0 ≤ weakTypeInterpolationConstant 1 p 2 := by
      dsimp [weakTypeInterpolationConstant]
      positivity
    have hθ₀ : 0 ≤ weakTypeInterpolationTheta0 1 p 2 := by
      dsimp [weakTypeInterpolationTheta0]
      positivity
    have hθ₁ : 0 ≤ weakTypeInterpolationTheta1 1 p 2 := by
      dsimp [weakTypeInterpolationTheta1]
      positivity
    exact mul_nonneg (mul_nonneg hI (by positivity)) (by positivity)
  · by_cases heq : p = 2
    · rw [if_neg hlt, if_pos heq]
      norm_num
    · rw [if_neg hlt, if_neg heq]
      have hp₂ : 2 < p := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      let q : ℝ := p.conjExponent
      have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
      have hq₁ : 1 < q := hpq.symm.lt
      have hq₂ : q < 2 := by
        have hqpos : 0 < q := hpq.symm.pos
        have hprod : p = q * (p - 1) := by
          have hdiv := hpq.div_conj_eq_sub_one
          field_simp [ne_of_gt hqpos] at hdiv
          nlinarith
        by_contra hnot
        have htwoq : 2 ≤ q := le_of_not_gt hnot
        have hmul := mul_le_mul_of_nonneg_right htwoq (sub_nonneg.mpr hp.le)
        nlinarith
      have hI : 0 ≤ weakTypeInterpolationConstant 1 q 2 := by
        dsimp [weakTypeInterpolationConstant]
        positivity
      have hθ₀ : 0 ≤ weakTypeInterpolationTheta0 1 q 2 := by
        dsimp [weakTypeInterpolationTheta0]
        positivity
      have hθ₁ : 0 ≤ weakTypeInterpolationTheta1 1 q 2 := by
        dsimp [weakTypeInterpolationTheta1]
        positivity
      exact mul_nonneg (mul_nonneg hI (by positivity)) (by positivity)

/-- The exact `Lᵖ` jump estimate for every nondecreasing finite list of
integer filtration times. This includes repeated times. -/
theorem dyadicJumpMonotoneTimeLpBound {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) {M : ℕ}
    (time : Fin (M + 1) → ℤ) (htime : Monotone time)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    lpNorm (fun x : ℝ => threshold * Real.sqrt (finiteSeparatedJumpCount
      (fun i : Fin (M + 1) =>
        dyadicAverage (-time i) (f : ℝ → ℂ) x)
      threshold : ℝ)) (ENNReal.ofReal p) volume ≤
        2 * (littlewoodPaleyCp p)⁻¹ *
          (weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖) := by
  let L : ℤ := time 0
  let H : ℤ := time (Fin.last M)
  have hLH : L ≤ H := htime (Fin.zero_le (Fin.last M))
  let D : ℕ := (H - L).toNat
  have hfirst : time 0 = L := rfl
  have hlast : time (Fin.last M) = L + (D : ℤ) := by
    dsimp [H, L, D]
    rw [Int.toNat_of_nonneg (show 0 ≤ time (Fin.last M) - time 0 by omega)]
    ring
  by_cases hD : D = 0
  · have hlastEq : time (Fin.last M) = L := by
      rw [hlast, hD]
      simp
    have hconst (i : Fin (M + 1)) : time i = L := by
      have hleft := htime (Fin.zero_le i)
      have hright := htime (Fin.le_last i)
      rw [hfirst] at hleft
      rw [hlastEq] at hright
      omega
    have hcount (x : ℝ) :
        finiteSeparatedJumpCount
          (fun i : Fin (M + 1) => dyadicAverage (-time i) (f : ℝ → ℂ) x)
          threshold = 0 := by
      simpa [hconst] using
        (finiteSeparatedJumpCount_eq_zero_of_constant
          (dyadicAverage (-L) (f : ℝ → ℂ) x) threshold hthreshold)
    simp only [hcount, Nat.cast_zero, Real.sqrt_zero, mul_zero, lpNorm_fun_zero]
    have hK := weakTypeJumpConstant_nonneg hp
    have hcp : 0 ≤ littlewoodPaleyCp p := by
      unfold littlewoodPaleyCp
      exact mul_nonneg
        (Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _)
        (Real.rpow_nonneg (by norm_num : 0 ≤ (12 : ℝ)) _)
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hcp))
      (mul_nonneg hK (norm_nonneg f))
  · have hDpos : 0 < D := Nat.pos_of_ne_zero hD
    let square : ℝ → ℝ := fun x => Real.sqrt (∑ i : Fin (D + 1),
      ‖dyadicJumpLpBlockOutput hp L D threshold hthreshold f i x‖ ^ 2)
    let jump : ℝ → ℝ := fun x => threshold * Real.sqrt
      (finiteSeparatedJumpCount
        (fun i : Fin (M + 1) =>
          dyadicAverage (-time i) (f : ℝ → ℂ) x)
        threshold : ℝ)
    have hsquare : MemLp square (ENNReal.ofReal p) volume := by
      simpa [square] using
        dyadicJumpBlockSquare_memLp hp L D threshold hthreshold f
    have hgood : MemLp (fun x : ℝ => 2 * square x)
        (ENNReal.ofReal p) volume := hsquare.const_mul 2
    have hinterval := dyadicJumpCount_le_blockSquare_ae
      hp L D threshold hthreshold f
    have hdom : ∀ᵐ x ∂volume, ‖jump x‖ ≤ 2 * square x := by
      filter_upwards [hinterval] with x hx
      have hcount := dyadicFiniteJumpCount_le_interval time htime
        L D hfirst hlast (f : ℝ → ℂ) x threshold hthreshold
      have hcountReal :
          (finiteSeparatedJumpCount
            (fun i : Fin (M + 1) =>
              dyadicAverage (-time i) (f : ℝ → ℂ) x) threshold : ℝ) ≤
          finiteSeparatedJumpCount
            (fun i : Fin (D + 1) =>
              dyadicAverage (-(L + (i.val : ℤ))) (f : ℝ → ℂ) x)
            threshold := by exact_mod_cast hcount
      have hsqrt := Real.sqrt_le_sqrt hcountReal
      have hleft := mul_le_mul_of_nonneg_left hsqrt hthreshold.le
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hthreshold.le (Real.sqrt_nonneg _))]
      simpa [jump, square] using hleft.trans hx
    have hmono : lpNorm jump (ENNReal.ofReal p) volume ≤
        lpNorm (fun x : ℝ => 2 * square x) (ENNReal.ofReal p) volume := by
      by_cases hjump : AEStronglyMeasurable jump volume
      · rw [← toReal_eLpNorm, ← toReal_eLpNorm]
        exact ENNReal.toNNReal_mono hgood.eLpNorm_ne_top
          (eLpNorm_mono_ae_real hjump hdom)
      · rw [lpNorm_of_not_aestronglyMeasurable hjump]
        exact lpNorm_nonneg (f := fun x : ℝ => 2 * square x)
    have hscale : lpNorm (fun x : ℝ => 2 * square x)
        (ENNReal.ofReal p) volume = 2 * lpNorm square
          (ENNReal.ofReal p) volume := by
      simpa [Pi.mul_def] using
        (lpNorm_natCast_mul (𝕜 := ℝ) 2 square (ENNReal.ofReal p) volume)
    have hsquareBound := dyadicJumpBlockSquareLpBound hp L D threshold
      hthreshold hDpos f
    calc
      lpNorm jump (ENNReal.ofReal p) volume ≤
          lpNorm (fun x : ℝ => 2 * square x) (ENNReal.ofReal p) volume := hmono
      _ = 2 * lpNorm square (ENNReal.ofReal p) volume := hscale
      _ ≤ 2 * ((littlewoodPaleyCp p)⁻¹ *
          (weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖)) :=
            mul_le_mul_of_nonneg_left hsquareBound (by norm_num)
      _ = 2 * (littlewoodPaleyCp p)⁻¹ *
          (weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖) := by ring

private theorem finiteSeparatedJumpCount_rev_le {M : ℕ}
    (u : Fin (M + 1) → ℂ) (threshold : ℝ) :
    finiteSeparatedJumpCount (fun i : Fin (M + 1) => u i.rev) threshold ≤
      finiteSeparatedJumpCount u threshold := by
  classical
  obtain ⟨s, t, hfamily⟩ :=
    finiteSeparatedJumpCount_isAttained
      (fun i : Fin (M + 1) => u i.rev) threshold
  apply le_finiteSeparatedJumpCount_of_family
  refine ⟨fun i => (t i.rev).rev, fun i => (s i.rev).rev, ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    change (t i.rev).rev < (s i.rev).rev
    rw [Fin.rev_lt_iff]
    simpa using hfamily.1.1 i.rev
  · intro i j hij
    change (s i.rev).rev ≤ (t j.rev).rev
    rw [Fin.rev_le_iff]
    have hji : j.rev < i.rev := by
      rw [Fin.rev_lt_iff]
      simpa using hij
    simpa using hfamily.1.2 (j.rev) (i.rev) hji
  · intro i
    change threshold < ‖u ((s i.rev).rev) - u ((t i.rev).rev)‖
    simpa [norm_sub_rev] using hfamily.2 i.rev

private theorem finiteSeparatedJumpCount_rev_eq {M : ℕ}
    (u : Fin (M + 1) → ℂ) (threshold : ℝ) :
    finiteSeparatedJumpCount (fun i : Fin (M + 1) => u i.rev) threshold =
      finiteSeparatedJumpCount u threshold := by
  apply le_antisymm
  · exact finiteSeparatedJumpCount_rev_le u threshold
  · simpa using finiteSeparatedJumpCount_rev_le
      (fun i : Fin (M + 1) => u i.rev) threshold

/-- The exact jump estimate for any finite monotone list of dyadic scales,
in either order and with repetitions. -/
theorem dyadicJumpMonotoneScaleLpBound {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) {M : ℕ}
    (scale : Fin (M + 1) → ℤ)
    (hmono : Monotone scale ∨ Antitone scale)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    lpNorm (fun x : ℝ => threshold * Real.sqrt (finiteSeparatedJumpCount
      (fun i : Fin (M + 1) =>
        dyadicAverage (scale i) (f : ℝ → ℂ) x)
      threshold : ℝ)) (ENNReal.ofReal p) volume ≤
        2 * (littlewoodPaleyCp p)⁻¹ *
          (weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖) := by
  rcases hmono with hscale | hscale
  · let time : Fin (M + 1) → ℤ := fun i => -scale i.rev
    have htime : Monotone time := by
      intro i j hij
      have hrev : j.rev ≤ i.rev := by
        rw [Fin.rev_le_iff]
        simpa using hij
      dsimp [time]
      exact neg_le_neg (hscale hrev)
    have hbound := dyadicJumpMonotoneTimeLpBound hp time htime
      threshold hthreshold f
    have hcount (x : ℝ) :
        finiteSeparatedJumpCount
          (fun i : Fin (M + 1) =>
            dyadicAverage (scale i.rev) (f : ℝ → ℂ) x) threshold =
        finiteSeparatedJumpCount
          (fun i : Fin (M + 1) =>
            dyadicAverage (scale i) (f : ℝ → ℂ) x) threshold := by
      exact finiteSeparatedJumpCount_rev_eq
        (fun i => dyadicAverage (scale i) (f : ℝ → ℂ) x) threshold
    have hfun :
        (fun x : ℝ => threshold * Real.sqrt (finiteSeparatedJumpCount
          (fun i : Fin (M + 1) =>
            dyadicAverage (scale i) (f : ℝ → ℂ) x) threshold : ℝ)) =
        (fun x : ℝ => threshold * Real.sqrt (finiteSeparatedJumpCount
          (fun i : Fin (M + 1) =>
            dyadicAverage (scale i.rev) (f : ℝ → ℂ) x) threshold : ℝ)) := by
      funext x
      rw [hcount]
    rw [hfun]
    simpa [time] using hbound
  · let time : Fin (M + 1) → ℤ := fun i => -scale i
    have htime : Monotone time := by
      intro i j hij
      dsimp [time]
      exact neg_le_neg (hscale hij)
    simpa [time] using
      (dyadicJumpMonotoneTimeLpBound hp time htime threshold hthreshold f)

/-- The finite-list form of the dyadic martingale jump estimate. The
monotonicity may be in either direction, and repeated integer scales are
retained exactly as in the source statement. -/
private theorem dyadicJumpBound_withFact {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) {n : ℕ}
    (scale : Fin n → ℤ)
    (hmono : Monotone scale ∨ Antitone scale)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    lpNorm (fun x : ℝ => threshold * Real.sqrt (finiteSeparatedJumpCount
      (fun i : Fin n =>
        dyadicAverage (scale i) (f : ℝ → ℂ) x)
      threshold : ℝ)) (ENNReal.ofReal p) volume ≤
        2 * (littlewoodPaleyCp p)⁻¹ *
          (weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖) := by
  cases n with
  | zero =>
      have hcount (x : ℝ) :
          finiteSeparatedJumpCount
            (fun i : Fin 0 => dyadicAverage (scale i) (f : ℝ → ℂ) x)
            threshold = 0 := by
        have hle := finiteSeparatedJumpCount_le_card
          (fun i : Fin 0 => dyadicAverage (scale i) (f : ℝ → ℂ) x) threshold
        simpa using hle
      have hzero :
          (fun x : ℝ => threshold * Real.sqrt (finiteSeparatedJumpCount
            (fun i : Fin 0 => dyadicAverage (scale i) (f : ℝ → ℂ) x)
            threshold : ℝ)) = fun _ => 0 := by
        funext x
        simp [hcount]
      rw [hzero, lpNorm_fun_zero]
      have hK := weakTypeJumpConstant_nonneg hp
      have hcp : 0 ≤ littlewoodPaleyCp p := by
        unfold littlewoodPaleyCp
        exact mul_nonneg
          (Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _)
          (Real.rpow_nonneg (by norm_num : 0 ≤ (12 : ℝ)) _)
      exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hcp))
        (mul_nonneg hK (norm_nonneg f))
  | succ M =>
      exact dyadicJumpMonotoneScaleLpBound hp scale hmono
        threshold hthreshold f

/-- The finite-list dyadic martingale jump estimate with the exact
paper-facing hypotheses. The `MemLp` exponent fact is derived from `1<p`. -/
theorem dyadicJumpBound {p : ℝ} (hp : 1 < p) {n : ℕ}
    (scale : Fin n → ℤ)
    (hmono : Monotone scale ∨ Antitone scale)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    lpNorm (fun x : ℝ => threshold * Real.sqrt (finiteSeparatedJumpCount
      (fun i : Fin n =>
        dyadicAverage (scale i) (f : ℝ → ℂ) x)
      threshold : ℝ)) (ENNReal.ofReal p) volume ≤
        2 * (littlewoodPaleyCp p)⁻¹ *
          (weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  exact dyadicJumpBound_withFact hp scale hmono threshold hthreshold f

end

end FractionalPrimes.Literature.JSW

end
