module

public import FractionalPrimes.Literature.Variation.FiniteJumpCount
import Mathlib.Data.Finset.Max

/-!
# Greedy stopping controls separated jumps

This file formalizes the finite combinatorial core of blueprint item
`lv:greedy`. A `GreedyStopRun` records the least starting point, successive
first threshold crossings, and exhaustion after the final stop. The theorem
assigns a distinct stop to each interval in a separated jump family.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

noncomputable section

/-- The finite stopping sequence produced by starting at the least index
and repeatedly taking the first later threshold crossing. `point 0` is the
initial anchor, and the `G` successors are the new stops. -/
structure GreedyStopRun {I : Type*} [LinearOrder I]
    (u : I → ℂ) (threshold : ℝ) (G : ℕ) where
  point : Fin (G + 1) → I
  strict : StrictMono point
  least : ∀ x, point 0 ≤ x
  crosses : ∀ i : Fin G,
    threshold / 2 < ‖u (point i.succ) - u (point i.castSucc)‖
  first : ∀ (i : Fin G) (x : I),
    point i.castSucc ≤ x → x < point i.succ →
      ‖u x - u (point i.castSucc)‖ ≤ threshold / 2
  exhausted : ∀ x : I,
    point (Fin.last G) < x → ‖u x - u (point (Fin.last G))‖ ≤ threshold / 2

namespace GreedyStopRun

/-- Every interval whose endpoint values differ by more than `λ` contains
one of the newly chosen greedy stops. -/
theorem exists_stop_between
    {I : Type*} [LinearOrder I] {u : I → ℂ} {threshold : ℝ} {G : ℕ}
    (run : GreedyStopRun u threshold G) {s t : I} (hst : s < t)
    (hlarge : threshold < ‖u t - u s‖) :
    ∃ i : Fin G, s < run.point i.succ ∧ run.point i.succ ≤ t := by
  classical
  let S : Finset (Fin (G + 1)) := Finset.univ.filter fun j => run.point j ≤ s
  have hS : S.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, run.least s⟩⟩
  let j : Fin (G + 1) := S.max' hS
  have hjmem : j ∈ S := Finset.max'_mem S hS
  have hjle : run.point j ≤ s := (Finset.mem_filter.mp hjmem).2
  by_cases hjG : j.val < G
  · let i : Fin G := ⟨j.val, hjG⟩
    have hprev : i.castSucc = j := by
      apply Fin.ext
      rfl
    let jnext : Fin (G + 1) := ⟨j.val + 1, by omega⟩
    have hnext : i.succ = jnext := by
      apply Fin.ext
      simp [i, jnext]
    have hsnext : s < run.point jnext := by
      by_contra hnot
      have hjnextle : run.point jnext ≤ s := le_of_not_gt hnot
      have hnextmem : jnext ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjnextle⟩
      have hmax : jnext ≤ j := Finset.le_max' S jnext hnextmem
      have hmaxval : jnext.val ≤ j.val := Fin.le_iff_val_le_val.mp hmax
      change j.val + 1 ≤ j.val at hmaxval
      omega
    by_cases htNext : run.point jnext ≤ t
    · exact ⟨i, by simpa [hnext] using hsnext, by simpa [hnext] using htNext⟩
    · have htlt : t < run.point jnext := lt_of_not_ge htNext
      have hprevS : run.point i.castSucc ≤ s := by simpa [hprev] using hjle
      have hprevT : run.point i.castSucc ≤ t := hprevS.trans hst.le
      have hsclose : ‖u s - u (run.point i.castSucc)‖ ≤ threshold / 2 := by
        exact run.first i s hprevS (by simpa [hnext] using hsnext)
      have htclose : ‖u t - u (run.point i.castSucc)‖ ≤ threshold / 2 := by
        exact run.first i t hprevT (by simpa [hnext] using htlt)
      have htriangle : ‖u t - u s‖ ≤ threshold := by
        calc
          ‖u t - u s‖ =
              ‖(u t - u (run.point i.castSucc)) +
                (u (run.point i.castSucc) - u s)‖ := by congr 1 <;> abel
          _ ≤ ‖u t - u (run.point i.castSucc)‖ +
                ‖u (run.point i.castSucc) - u s‖ := norm_add_le _ _
          _ ≤ threshold / 2 + threshold / 2 :=
            add_le_add htclose (by simpa [norm_sub_rev] using hsclose)
          _ = threshold := by ring
      exact False.elim ((not_lt_of_ge htriangle) hlarge)
  · have hjlast : j = Fin.last G := by
      apply Fin.ext
      have hjbound : j.val ≤ G := by omega
      have hjbound' : G ≤ j.val := by omega
      simpa using (Nat.le_antisymm hjbound hjbound')
    have htlast : run.point (Fin.last G) < t := by
      have hlt : run.point j < t := lt_of_le_of_lt hjle hst
      simpa [hjlast] using hlt
    have htcloseLast :
        ‖u t - u (run.point (Fin.last G))‖ ≤ threshold / 2 :=
      run.exhausted t htlast
    have hhalf : 0 ≤ threshold / 2 := (norm_nonneg _).trans htcloseLast
    have hsclose : ‖u s - u (run.point j)‖ ≤ threshold / 2 := by
      by_cases hse : s = run.point j
      · rw [hse]
        simpa using hhalf
      · have hlt : run.point j < s := lt_of_le_of_ne hjle (Ne.symm hse)
        have hltlast : run.point (Fin.last G) < s := by
          simpa [hjlast] using hlt
        simpa [hjlast] using run.exhausted s hltlast
    have htclose : ‖u t - u (run.point j)‖ ≤ threshold / 2 := by
      simpa [hjlast] using htcloseLast
    have htriangle : ‖u t - u s‖ ≤ threshold := by
      calc
        ‖u t - u s‖ = ‖(u t - u (run.point j)) + (u (run.point j) - u s)‖ := by
          congr 1 <;> abel
        _ ≤ ‖u t - u (run.point j)‖ + ‖u (run.point j) - u s‖ := norm_add_le _ _
        _ ≤ threshold / 2 + threshold / 2 :=
          add_le_add htclose (by simpa [norm_sub_rev] using hsclose)
        _ = threshold := by ring
    exact False.elim ((not_lt_of_ge htriangle) hlarge)

end GreedyStopRun

/-- The number of separated `λ`-jumps is at most the number of new stops
chosen by the greedy threshold-`λ/2` procedure. -/
theorem jumpCountLeGreedy
    {I : Type*} [LinearOrder I] [Fintype I]
    (u : I → ℂ) (threshold : ℝ) (hthreshold : 0 < threshold) {G : ℕ}
    (run : GreedyStopRun u threshold G) :
    finiteSeparatedJumpCount u threshold ≤ G := by
  classical
  letI : Nonempty I := ⟨run.point 0⟩
  obtain ⟨s, t, hfamily⟩ := finiteSeparatedJumpCount_isAttained u threshold
  let chosen : Fin (finiteSeparatedJumpCount u threshold) → Fin G := fun i =>
    Classical.choose (run.exists_stop_between (hfamily.1.1 i) (hfamily.2 i))
  have hchosen (i : Fin (finiteSeparatedJumpCount u threshold)) :
      s i < run.point (chosen i).succ ∧ run.point (chosen i).succ ≤ t i :=
    Classical.choose_spec (run.exists_stop_between (hfamily.1.1 i) (hfamily.2 i))
  have hinj : Function.Injective chosen := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstrict : run.point (chosen i).succ < run.point (chosen j).succ := by
        calc
          run.point (chosen i).succ ≤ t i := (hchosen i).2
          _ ≤ s j := hfamily.1.2 i j hlt
          _ < run.point (chosen j).succ := (hchosen j).1
      rw [hij] at hstrict
      exact (lt_irrefl _ hstrict).elim
    · have hstrict : run.point (chosen j).succ < run.point (chosen i).succ := by
        calc
          run.point (chosen j).succ ≤ t j := (hchosen j).2
          _ ≤ s i := hfamily.1.2 j i hgt
          _ < run.point (chosen i).succ := (hchosen i).1
      rw [hij] at hstrict
      exact (lt_irrefl _ hstrict).elim
  simpa using Fintype.card_le_of_injective chosen hinj

end

end FractionalPrimes.Literature.Variation
