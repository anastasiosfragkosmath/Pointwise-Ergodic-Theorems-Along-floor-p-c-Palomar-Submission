module

public import FractionalPrimes.Literature.JSW.DyadicMartingaleJump

/-!
# Prefix predictability for finite greedy stopping

The active block at a step is chosen by running the finite greedy
algorithm on the input prefix through that step. Equality of prefixes
therefore gives equality of stop counts without comparing full runs
whose later inputs may differ.
-/

@[expose] public section

namespace FractionalPrimes.Literature.JSW

open FractionalPrimes.Literature.Variation

noncomputable section

/-- The greedy stop count through time `t` depends only on the values
through time `t`. This is the pure finite predictability interface. -/
theorem greedyPrefixStopCount_congr_prefix
    (u v : ℕ → ℂ) (threshold : ℝ) (hthreshold : 0 < threshold)
    (t : ℕ) (hprefix : ∀ i ≤ t, u i = v i) :
    greedyPrefixStopCount u threshold hthreshold t =
      greedyPrefixStopCount v threshold hthreshold t := by
  have hrestricted :
      (fun i : Fin (t + 1) => u i.val) =
        (fun i : Fin (t + 1) => v i.val) := by
    funext i
    exact hprefix i.val (Nat.le_of_lt_succ i.isLt)
  unfold greedyPrefixStopCount
  rw [hrestricted]

/-- First threshold crossings are unique once their anchor is fixed.
This uses precisely `first` and `crosses` from the approved greedy run. -/
theorem GreedyStopRun.next_eq_of_anchor_eq
    {I : Type*} [LinearOrder I] {u : I → ℂ} {threshold : ℝ}
    {G H : ℕ} (r : GreedyStopRun u threshold G)
    (s : GreedyStopRun u threshold H) (i : Fin G) (j : Fin H)
    (hanchor : r.point i.castSucc = s.point j.castSucc) :
    r.point i.succ = s.point j.succ := by
  rcases lt_trichotomy (r.point i.succ) (s.point j.succ) with hlt | heq | hgt
  · have hclose := s.first j (r.point i.succ)
      (by rw [← hanchor]; exact (r.strict i.castSucc_lt_succ).le) hlt
    rw [← hanchor] at hclose
    exact False.elim ((not_lt_of_ge hclose) (r.crosses i))
  · exact heq
  · have hclose := r.first i (s.point j.succ)
      (by rw [hanchor]; exact (s.strict j.castSucc_lt_succ).le) hgt
    rw [hanchor] at hclose
    exact False.elim ((not_lt_of_ge hclose) (s.crosses j))

/-- Two greedy runs on the same finite input have identical stop points
for every index present in both runs. -/
theorem GreedyStopRun.point_eq_of_le
    {I : Type*} [LinearOrder I] {u : I → ℂ} {threshold : ℝ}
    {G H : ℕ} (r : GreedyStopRun u threshold G)
    (s : GreedyStopRun u threshold H) (n : ℕ)
    (hnG : n ≤ G) (hnH : n ≤ H) :
    r.point ⟨n, Nat.lt_succ_of_le hnG⟩ =
      s.point ⟨n, Nat.lt_succ_of_le hnH⟩ := by
  induction n with
  | zero =>
      exact le_antisymm (r.least _) (s.least _)
  | succ n ih =>
      let i : Fin G := ⟨n, by omega⟩
      let j : Fin H := ⟨n, by omega⟩
      have hanchor : r.point i.castSucc = s.point j.castSucc := by
        simpa [i, j] using ih (by omega) (by omega)
      have hnext := GreedyStopRun.next_eq_of_anchor_eq r s i j hanchor
      simpa [i, j] using hnext

/-- A finite input and threshold determine the number of greedy stops. -/
theorem GreedyStopRun.count_eq
    {I : Type*} [LinearOrder I] {u : I → ℂ} {threshold : ℝ}
    {G H : ℕ} (r : GreedyStopRun u threshold G)
    (s : GreedyStopRun u threshold H) : G = H := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hGH | hHG
  · let j : Fin H := ⟨G, hGH⟩
    have hanchor : r.point (Fin.last G) = s.point j.castSucc := by
      simpa [Fin.last, j] using GreedyStopRun.point_eq_of_le r s G le_rfl hGH.le
    have hnext : r.point (Fin.last G) < s.point j.succ := by
      rw [hanchor]
      exact s.strict j.castSucc_lt_succ
    have hclose := r.exhausted (s.point j.succ) hnext
    have hcross := s.crosses j
    rw [← hanchor] at hcross
    exact (not_lt_of_ge hclose) hcross
  · let i : Fin G := ⟨H, hHG⟩
    have hanchor : r.point i.castSucc = s.point (Fin.last H) := by
      simpa [Fin.last, i] using GreedyStopRun.point_eq_of_le r s H hHG.le le_rfl
    have hnext : s.point (Fin.last H) < r.point i.succ := by
      rw [← hanchor]
      exact r.strict i.castSucc_lt_succ
    have hclose := s.exhausted (r.point i.succ) hnext
    have hcross := r.crosses i
    rw [hanchor] at hcross
    exact (not_lt_of_ge hclose) hcross

end

end FractionalPrimes.Literature.JSW

end
