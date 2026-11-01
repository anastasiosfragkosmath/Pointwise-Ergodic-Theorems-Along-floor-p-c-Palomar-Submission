module

public import FractionalPrimes.Literature.Variation.GreedyJumpBound
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find

/-!
# Existence of finite greedy stopping runs

For a finite nonempty ordered index set, this file constructs the greedy
stopping run used by `lv:greedy`.  The construction takes a longest prefix
whose successive points are the first strict `λ/2` crossings.  A further
crossing after its last point would extend the prefix, contradicting its
maximality.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

noncomputable section

/-- A finite prefix of the greedy stopping procedure. The `n+1` points
include the least anchor and the `n` new stops. -/
structure GreedyStopPrefix {I : Type*} [LinearOrder I]
    (u : I → ℂ) (threshold : ℝ) (n : ℕ) where
  point : Fin (n + 1) → I
  strict : StrictMono point
  least : ∀ x, point 0 ≤ x
  crosses : ∀ i : Fin n,
    threshold / 2 < ‖u (point i.succ) - u (point i.castSucc)‖
  first : ∀ (i : Fin n) (x : I),
    point i.castSucc ≤ x → x < point i.succ →
      ‖u x - u (point i.castSucc)‖ ≤ threshold / 2

/-- Appending the first crossing after the last point extends a greedy
prefix by one new stop. -/
private def extendGreedyStopPrefix
    {I : Type*} [LinearOrder I] {u : I → ℂ} {threshold : ℝ} {n : ℕ}
    (runPrefix : GreedyStopPrefix u threshold n) (y : I)
    (hy : runPrefix.point (Fin.last n) < y)
    (hcross : threshold / 2 < ‖u y - u (runPrefix.point (Fin.last n))‖)
    (hfirst : ∀ x : I, runPrefix.point (Fin.last n) ≤ x → x < y →
      ‖u x - u (runPrefix.point (Fin.last n))‖ ≤ threshold / 2) :
    GreedyStopPrefix u threshold (n + 1) := by
  let extended : Fin (n + 1 + 1) → I := Fin.snoc runPrefix.point y
  refine ⟨extended, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    cases i using Fin.lastCases with
    | cast i =>
      cases j using Fin.lastCases with
      | cast j =>
        have hij' : i < j := Fin.castSucc_lt_castSucc_iff.mp hij
        simpa [extended] using runPrefix.strict hij'
      | last =>
        have hle : runPrefix.point i ≤ runPrefix.point (Fin.last n) :=
          runPrefix.strict.monotone (Fin.le_last i)
        simpa [extended] using hle.trans_lt hy
    | last =>
      exact False.elim ((not_lt_of_ge (Fin.le_last j)) hij)
  · intro x
    have hzero : (0 : Fin (n + 1 + 1)) = (0 : Fin (n + 1)).castSucc := by
      apply Fin.ext
      rfl
    calc
      extended 0 = runPrefix.point 0 := by
        rw [hzero]
        simp only [extended, Fin.snoc_castSucc]
      _ ≤ x := runPrefix.least x
  · intro i
    cases i using Fin.lastCases with
    | cast i =>
      have hsucc : i.castSucc.succ = i.succ.castSucc := by
        apply Fin.ext
        simp
      simpa only [extended, hsucc, Fin.snoc_castSucc] using runPrefix.crosses i
    | last =>
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        rfl
      simpa only [extended, hlast, Fin.snoc_last, Fin.snoc_castSucc] using hcross
  · intro i x hprev hnext
    cases i using Fin.lastCases with
    | cast i =>
      have hsucc : i.castSucc.succ = i.succ.castSucc := by
        apply Fin.ext
        simp
      have hprev' : runPrefix.point i.castSucc ≤ x := by
        simpa only [extended, Fin.snoc_castSucc] using hprev
      have hnext' : x < runPrefix.point i.succ := by
        simpa only [extended, hsucc, Fin.snoc_castSucc] using hnext
      simpa only [extended, Fin.snoc_castSucc] using
        runPrefix.first i x hprev' hnext'
    | last =>
      have hprev' : runPrefix.point (Fin.last n) ≤ x := by
        simpa only [extended, Fin.snoc_castSucc] using hprev
      have hnext' : x < y := by
        have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
          apply Fin.ext
          rfl
        simpa only [extended, hlast, Fin.snoc_last] using hnext
      simpa only [extended, Fin.snoc_castSucc] using hfirst x hprev' hnext'

/-- There is a greedy prefix with zero new stops: its sole point is the
least element of the finite ordered index set. -/
private theorem exists_greedyStopPrefix_zero
    {I : Type*} [LinearOrder I] [Fintype I] [Nonempty I]
    (u : I → ℂ) (threshold : ℝ) : Nonempty (GreedyStopPrefix u threshold 0) := by
  classical
  let hI : (Finset.univ : Finset I).Nonempty := Finset.univ_nonempty
  let a : I := Finset.univ.min' hI
  refine ⟨{ point := fun _ => a
           , strict := ?_
           , least := ?_
           , crosses := ?_
           , first := ?_ }⟩
  · intro i j hij
    have hij' : i.val < j.val := Fin.lt_iff_val_lt_val.mp hij
    have hi := i.isLt
    have hj := j.isLt
    omega
  · intro x
    exact Finset.min'_le Finset.univ x (Finset.mem_univ x)
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

/-- Every finite greedy prefix contains at most one point per index. -/
private theorem greedyStopPrefix_card_le
    {I : Type*} [LinearOrder I] [Fintype I] {u : I → ℂ} {threshold : ℝ} {n : ℕ}
    (runPrefix : GreedyStopPrefix u threshold n) : n + 1 ≤ Fintype.card I := by
  have hcard := Fintype.card_le_of_injective runPrefix.point runPrefix.strict.injective
  simpa using hcard

/-- A finite nonempty ordered sequence has a finite greedy stopping run.
Its anchor is the least index; every new stop is the first later point whose
value differs from the preceding stop by more than `λ/2`. -/
theorem exists_greedyStopRun
    {I : Type*} [LinearOrder I] [Fintype I] [Nonempty I]
    (u : I → ℂ) (threshold : ℝ) (hthreshold : 0 < threshold) :
    ∃ G : ℕ, Nonempty (GreedyStopRun u threshold G) := by
  classical
  let P : ℕ → Prop := fun n => Nonempty (GreedyStopPrefix u threshold n)
  let G : ℕ := Nat.findGreatest P (Fintype.card I)
  have hPzero : P 0 := exists_greedyStopPrefix_zero u threshold
  have hPG : P G := by
    dsimp [G]
    exact Nat.findGreatest_spec (P := P) (Nat.zero_le _) hPzero
  obtain ⟨runPrefix⟩ := hPG
  have hlen : G + 1 ≤ Fintype.card I := greedyStopPrefix_card_le runPrefix
  have hexhausted : ∀ x : I,
      runPrefix.point (Fin.last G) < x →
        ‖u x - u (runPrefix.point (Fin.last G))‖ ≤ threshold / 2 := by
    intro x hx
    by_contra hnot
    have hcross : threshold / 2 < ‖u x - u (runPrefix.point (Fin.last G))‖ :=
      lt_of_not_ge hnot
    let candidates : Finset I := Finset.univ.filter fun z =>
      runPrefix.point (Fin.last G) < z ∧
        threshold / 2 < ‖u z - u (runPrefix.point (Fin.last G))‖
    have hcandidates : candidates.Nonempty := by
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hcross⟩⟩
    let y : I := candidates.min' hcandidates
    have hy : runPrefix.point (Fin.last G) < y ∧
        threshold / 2 < ‖u y - u (runPrefix.point (Fin.last G))‖ :=
      (Finset.mem_filter.mp (Finset.min'_mem candidates hcandidates)).2
    have hyfirst : ∀ z : I, runPrefix.point (Fin.last G) ≤ z → z < y →
        ‖u z - u (runPrefix.point (Fin.last G))‖ ≤ threshold / 2 := by
      intro z hle hzy
      by_cases hEq : z = runPrefix.point (Fin.last G)
      · subst z
        have hhalf : 0 ≤ threshold / 2 := by positivity
        simpa using hhalf
      · have hz : runPrefix.point (Fin.last G) < z :=
          lt_of_le_of_ne hle (Ne.symm hEq)
        by_contra hnot'
        have hlarge : threshold / 2 < ‖u z - u (runPrefix.point (Fin.last G))‖ :=
          lt_of_not_ge hnot'
        have hmin : y ≤ z :=
          Finset.min'_le candidates z
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz, hlarge⟩)
        exact (not_lt_of_ge hmin) hzy
    let longer : GreedyStopPrefix u threshold (G + 1) :=
      extendGreedyStopPrefix runPrefix y hy.1 hy.2 hyfirst
    have hnotLonger : ¬ P (G + 1) := by
      have hlt : Nat.findGreatest P (Fintype.card I) < G + 1 := by
        simpa [G] using Nat.lt_succ_self (Nat.findGreatest P (Fintype.card I))
      exact Nat.findGreatest_is_greatest hlt hlen
    exact hnotLonger ⟨longer⟩
  refine ⟨G, ⟨{ point := runPrefix.point
               , strict := runPrefix.strict
               , least := runPrefix.least
               , crosses := runPrefix.crosses
               , first := runPrefix.first
               , exhausted := hexhausted }⟩⟩

end

end FractionalPrimes.Literature.Variation
