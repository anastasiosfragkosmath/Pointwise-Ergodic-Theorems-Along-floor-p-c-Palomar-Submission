module

public import FractionalPrimes.Literature.Hyperbola.OccupiedSliceCount
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Field.GeomSum

set_option maxHeartbeats 1000000

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

open Set HyperbolaGeometricData

private theorem cellPointCoordinateBounds (g : HyperbolaGeometricData)
    (a q : ℕ) (hidx : positiveRationalCellIndexEligible g a q)
    (p : ℤ × ℤ) (hp : p ∈ cellLinearSlice g a q) :
    let u : ℝ := (a : ℝ) * (q : ℝ)
    let t : ℝ := 2 * Real.sqrt (u * g.X)
    let c : ℝ := (cellLinearCoordinate a q p : ℝ)
    let z : ℝ := (cellTransverseCoordinate a q p : ℝ)
    c > t ∧ 0 < t ∧ |z| ≤ 2 * D g.K₀ * g.M / (g.Q : ℝ) ∧
      c ^ 2 - z ^ 2 = 4 * u * (p.1 : ℝ) * (p.2 : ℝ) ∧
      g.r * (q : ℝ) ^ 2 / 8 ≤ u ∧
      u ≤ E g.K₀ * g.r * (q : ℝ) ^ 2 ∧
      g.X < (p.1 : ℝ) * (p.2 : ℝ) ∧
      (p.1 : ℝ) * (p.2 : ℝ) ≤ g.X + g.H := by
  let cInt : ℤ := cellLinearCoordinate a q p
  have hline := cellLinearSlices g a q hidx cInt
  rcases hline with ⟨hpoint, _, _, _⟩
  have hb := hpoint p ⟨hp, rfl⟩
  change
    (cellLinearCoordinate a q p : ℝ) >
        2 * Real.sqrt ((a : ℝ) * (q : ℝ) * g.X) ∧
      0 < 2 * Real.sqrt ((a : ℝ) * (q : ℝ) * g.X) ∧
      |(cellTransverseCoordinate a q p : ℝ)| ≤
        2 * D g.K₀ * g.M / (g.Q : ℝ) ∧
      (cellLinearCoordinate a q p : ℝ) ^ 2 -
          (cellTransverseCoordinate a q p : ℝ) ^ 2 =
        4 * ((a : ℝ) * (q : ℝ)) * (p.1 : ℝ) * (p.2 : ℝ) ∧
      (g.r * (q : ℝ) ^ 2 / 8 ≤ (a : ℝ) * (q : ℝ) ∧
        (a : ℝ) * (q : ℝ) ≤ E g.K₀ * g.r * (q : ℝ) ^ 2) at hb
  rcases hb with ⟨hcgt, htpos, hzbound, hid, huLower, huUpper⟩
  have hpstrip :
      g.X < (p.1 : ℝ) * (p.2 : ℝ) ∧
        (p.1 : ℝ) * (p.2 : ℝ) ≤ g.X + g.H := by
    have hpL := hp.1
    change (p.1 : ℝ) ∈ g.J ∧ g.X < (p.1 : ℝ) * (p.2 : ℝ) ∧
      (p.1 : ℝ) * (p.2 : ℝ) ≤ g.X + g.H at hpL
    exact ⟨hpL.2.1, hpL.2.2⟩
  exact ⟨hcgt, htpos, hzbound, hid, huLower, huUpper,
    hpstrip.1, hpstrip.2⟩

private theorem cellPointSquareWindow (g : HyperbolaGeometricData)
    (a q : ℕ) (hidx : positiveRationalCellIndexEligible g a q)
    (p : ℤ × ℤ) (hp : p ∈ cellLinearSlice g a q) :
    let u : ℝ := (a : ℝ) * (q : ℝ)
    let c : ℝ := (cellLinearCoordinate a q p : ℝ)
    let z : ℝ := (cellTransverseCoordinate a q p : ℝ)
    let lo : ℝ := max 0 (c ^ 2 - 4 * u * (g.X + g.H))
    let hi : ℝ := c ^ 2 - 4 * u * g.X
    0 ≤ hi ∧ lo ≤ hi ∧ hi - lo ≤ 4 * u * g.H ∧
      z ^ 2 ∈ Set.Icc lo hi := by
  let u : ℝ := (a : ℝ) * (q : ℝ)
  let c : ℝ := (cellLinearCoordinate a q p : ℝ)
  let z : ℝ := (cellTransverseCoordinate a q p : ℝ)
  let rawLo : ℝ := c ^ 2 - 4 * u * (g.X + g.H)
  let lo : ℝ := max 0 rawLo
  let hi : ℝ := c ^ 2 - 4 * u * g.X
  have hdata := cellPointCoordinateBounds g a q hidx p hp
  change c > 2 * Real.sqrt (u * g.X) ∧ 0 < 2 * Real.sqrt (u * g.X) ∧
    |z| ≤ 2 * D g.K₀ * g.M / (g.Q : ℝ) ∧
    c ^ 2 - z ^ 2 = 4 * u * (p.1 : ℝ) * (p.2 : ℝ) ∧
    g.r * (q : ℝ) ^ 2 / 8 ≤ u ∧
    u ≤ E g.K₀ * g.r * (q : ℝ) ^ 2 ∧
    g.X < (p.1 : ℝ) * (p.2 : ℝ) ∧
    (p.1 : ℝ) * (p.2 : ℝ) ≤ g.X + g.H at hdata
  rcases hdata with ⟨_, _, _, hid, _, _, hprodLo, hprodHi⟩
  have hXpos : 0 < g.X := by linarith [g.X_ge_one]
  have hHpos : 0 < g.H := by linarith [g.H_ge_one]
  have huPos : 0 < u := by
    dsimp [u]
    have ha : 1 ≤ a := hidx.1.2.2.2.1
    have hq : 1 ≤ q := hidx.1.2.1
    have ha' : 0 < a := by omega
    have hq' : 0 < q := by omega
    exact mul_pos (by exact_mod_cast ha') (by exact_mod_cast hq')
  have huHpos : 0 < u * g.H := mul_pos huPos hHpos
  have hzSq : z ^ 2 = c ^ 2 - 4 * u * ((p.1 : ℝ) * (p.2 : ℝ)) := by
    dsimp [z, c, u] at hid ⊢
    nlinarith [hid]
  have hzLower : rawLo ≤ z ^ 2 := by
    dsimp [rawLo, hi, c, u]
    have hmul := mul_le_mul_of_nonneg_left hprodHi (by positivity : 0 ≤ 4 * ((a : ℝ) * (q : ℝ)))
    nlinarith [hzSq, hmul]
  have hzUpper : z ^ 2 ≤ hi := by
    dsimp [hi, c, u]
    have hmul := mul_le_mul_of_nonneg_left hprodLo.le
      (by positivity : 0 ≤ 4 * ((a : ℝ) * (q : ℝ)))
    nlinarith [hzSq, hmul]
  have hhiNonneg : 0 ≤ hi := le_trans (sq_nonneg z) hzUpper
  have hrawLeHi : rawLo ≤ hi := by
    dsimp [rawLo, hi]
    nlinarith [huHpos]
  have hloLeHi : lo ≤ hi := by
    dsimp [lo]
    exact max_le_iff.mpr ⟨hhiNonneg, hrawLeHi⟩
  have hwidth : hi - lo ≤ 4 * u * g.H := by
    by_cases hraw : 0 ≤ rawLo
    · rw [show lo = rawLo by dsimp [lo]; exact max_eq_right hraw]
      dsimp [rawLo, hi]
      ring_nf
      exact le_rfl
    · have hrawLt : rawLo < 0 := lt_of_not_ge hraw
      rw [show lo = 0 by dsimp [lo]; exact max_eq_left hrawLt.le]
      have hhiBound : hi ≤ 4 * u * g.H := by
        dsimp [hi, rawLo] at hrawLt ⊢
        nlinarith [hrawLt]
      linarith
  have hzIn : lo ≤ z ^ 2 ∧ z ^ 2 ≤ hi := by
    constructor
    · dsimp [lo]
      exact max_le_iff.mpr ⟨sq_nonneg z, hzLower⟩
    · exact hzUpper
  dsimp [lo, hi]
  exact ⟨hhiNonneg, hloLeHi, hwidth, hzIn⟩

private theorem residueSquaresIccCount
    (S : Finset ℤ) (residue : ℤ) (u : ℕ)
    (lo hi W : ℝ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hlohi : lo ≤ hi) (hwidth : hi - lo ≤ W) (_hW : 0 ≤ W)
    (hu : 0 < u)
    (hSq : ∀ z ∈ S, (z : ℝ) ^ 2 ∈ Set.Icc lo hi)
    (hres : ∀ z ∈ S, z ≡ residue [ZMOD (u : ℤ)]) :
    (S.card : ℝ) ≤ 2 * Real.sqrt W / (u : ℝ) + 2 := by
  classical
  let Spos := S.filter fun z : ℤ => 0 ≤ (z : ℝ)
  let Sneg := S.filter fun z : ℤ => (z : ℝ) ≤ 0
  have hsubset : S ⊆ Spos ∪ Sneg := by
    intro z hz
    by_cases hz0 : 0 ≤ (z : ℝ)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hz, hz0⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨hz, le_of_lt (lt_of_not_ge hz0)⟩))
  have hcardSplit : S.card ≤ Spos.card + Sneg.card := by
    calc
      S.card ≤ (Spos ∪ Sneg).card := Finset.card_le_card hsubset
      _ ≤ Spos.card + Sneg.card := Finset.card_union_le _ _
  have hrootWidth : Real.sqrt hi - Real.sqrt lo ≤ Real.sqrt W := by
    exact (sqrtDifference_le_sqrtSub lo hi hlo hlohi).trans
      (Real.sqrt_le_sqrt hwidth)
  have hposI : ∀ z ∈ Spos,
      (z : ℝ) ∈ Set.Icc (Real.sqrt lo) (Real.sqrt hi) := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzS, hz0⟩
    have hsq := hSq z hzS
    have hlowSq : (Real.sqrt lo) ^ 2 ≤ (z : ℝ) ^ 2 := by
      rw [Real.sq_sqrt hlo]
      exact hsq.1
    have hhighSq : (z : ℝ) ^ 2 ≤ (Real.sqrt hi) ^ 2 := by
      rw [Real.sq_sqrt hhi]
      exact hsq.2
    have hzLo : Real.sqrt lo ≤ (z : ℝ) :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) hz0).mp hlowSq
    have hzHi : (z : ℝ) ≤ Real.sqrt hi :=
      (sq_le_sq₀ hz0 (Real.sqrt_nonneg _)).mp hhighSq
    exact ⟨hzLo, hzHi⟩
  have hnegI : ∀ z ∈ Sneg,
      (z : ℝ) ∈ Set.Icc (-Real.sqrt hi) (-Real.sqrt lo) := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzS, hz0⟩
    have hsq := hSq z hzS
    have hnegNonneg : 0 ≤ -(z : ℝ) := by linarith
    have hlowSq : (Real.sqrt lo) ^ 2 ≤ (-(z : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt hlo]
      nlinarith [hsq.1]
    have hhighSq : (-(z : ℝ)) ^ 2 ≤ (Real.sqrt hi) ^ 2 := by
      rw [Real.sq_sqrt hhi]
      nlinarith [hsq.2]
    have hzLo : Real.sqrt lo ≤ -(z : ℝ) :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) hnegNonneg).mp hlowSq
    have hzHi : -(z : ℝ) ≤ Real.sqrt hi :=
      (sq_le_sq₀ hnegNonneg (Real.sqrt_nonneg _)).mp hhighSq
    exact ⟨by linarith, by linarith⟩
  have hposCount := residueClassIntervalCount
    (Set.Icc (Real.sqrt lo) (Real.sqrt hi)) Set.ordConnected_Icc
    Spos residue u (Real.sqrt lo) (Real.sqrt hi) (Real.sqrt W)
    (Real.sqrt_le_sqrt hlohi) (Real.sqrt_nonneg W) hrootWidth
    (by intro x hx; exact hx) hposI hu
    (by
      intro z hz
      exact hres z (Finset.mem_filter.mp hz).1)
  have hnegCount := residueClassIntervalCount
    (Set.Icc (-Real.sqrt hi) (-Real.sqrt lo)) Set.ordConnected_Icc
    Sneg residue u (-Real.sqrt hi) (-Real.sqrt lo) (Real.sqrt W)
    (neg_le_neg (Real.sqrt_le_sqrt hlohi)) (Real.sqrt_nonneg W)
    (by linarith) (by intro x hx; exact hx) hnegI hu
    (by
      intro z hz
      exact hres z (Finset.mem_filter.mp hz).1)
  have hsum := add_le_add hposCount hnegCount
  have hcardReal : (S.card : ℝ) ≤ (Spos.card : ℝ) + (Sneg.card : ℝ) := by
    exact_mod_cast hcardSplit
  calc
    (S.card : ℝ) ≤ (Spos.card : ℝ) + (Sneg.card : ℝ) := hcardReal
    _ ≤ (Real.sqrt W / (u : ℝ) + 1) +
        (Real.sqrt W / (u : ℝ) + 1) := hsum
    _ = 2 * Real.sqrt W / (u : ℝ) + 2 := by ring

private theorem positiveSeparatedSquareCount
    (S : Finset ℤ) (residue : ℤ) (u : ℕ)
    (A H lo hi : ℝ) (hA : 0 < A) (hH : 0 ≤ H) (hu : 0 < u)
    (hhi : lo ≤ hi) (hwidth : hi - lo ≤ 4 * (u : ℝ) * H)
    (hSq : ∀ z ∈ S, (z : ℝ) ^ 2 ∈ Set.Icc lo hi)
    (hAlo : ∀ z ∈ S, A ≤ (z : ℝ))
    (hres : ∀ z ∈ S, z ≡ residue [ZMOD (u : ℤ)]) :
    (S.card : ℝ) ≤ 2 * H / A + 1 := by
  classical
  let f : ℤ → ℝ := fun z => (z : ℝ) ^ 2
  have hf_inj : Set.InjOn f S := by
    intro z hz w hw hzw
    have hzA := hAlo z hz
    have hwA := hAlo w hw
    have hsum : 0 < (z : ℝ) + (w : ℝ) := by linarith [hA]
    have hfactor : ((z : ℝ) - (w : ℝ)) * ((z : ℝ) + (w : ℝ)) = 0 := by
      dsimp [f] at hzw
      nlinarith [hzw]
    have hcast : (z : ℝ) = (w : ℝ) := by
      rcases mul_eq_zero.mp hfactor with hdiff | hsumzero
      · linarith
      · linarith
    exact Int.cast_injective hcast
  let T : Finset ℝ := S.image f
  have hcardT : T.card = S.card := by
    simp [T, Finset.card_image_of_injOn hf_inj]
  have hTI : ∀ x ∈ T, x ∈ Set.Icc lo hi := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    exact hSq z hz
  have hTsep :
      ∀ ⦃x y : ℝ⦄, x ∈ T → y ∈ T → x ≠ y →
        2 * A * (u : ℝ) ≤ |x - y| := by
    intro x y hx hy hxy
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨w, hw, rfl⟩
    have hzw : z ≠ w := by
      intro h
      subst w
      exact hxy rfl
    have hmod : z ≡ w [ZMOD (u : ℤ)] :=
      (hres z hz).trans (hres w hw).symm
    have hdiv : (u : ℤ) ∣ w - z := Int.ModEq.dvd hmod
    have hdiff : w - z ≠ 0 := by omega
    have hspacingInt : (u : ℤ) ≤ |w - z| := Int.le_abs_of_dvd hdiff hdiv
    have hspacing : (u : ℝ) ≤ |(w : ℝ) - (z : ℝ)| := by
      exact_mod_cast hspacingInt
    have hsum : 2 * A ≤ (z : ℝ) + (w : ℝ) := by
      linarith [hAlo z hz, hAlo w hw]
    have hsumNonneg : 0 ≤ (z : ℝ) + (w : ℝ) := le_of_lt (by linarith [hA])
    have hmul₁ := mul_le_mul_of_nonneg_right hspacing (by positivity : 0 ≤ 2 * A)
    have hmul₂ := mul_le_mul_of_nonneg_left hsum
      (abs_nonneg ((w : ℝ) - (z : ℝ)))
    have hmul : (u : ℝ) * (2 * A) ≤
        |(w : ℝ) - (z : ℝ)| * ((z : ℝ) + (w : ℝ)) := by
      calc
        (u : ℝ) * (2 * A) ≤ |(w : ℝ) - (z : ℝ)| * (2 * A) := hmul₁
        _ ≤ |(w : ℝ) - (z : ℝ)| * ((z : ℝ) + (w : ℝ)) := hmul₂
    have habs :
        |(z : ℝ) ^ 2 - (w : ℝ) ^ 2| =
          |(w : ℝ) - (z : ℝ)| * ((z : ℝ) + (w : ℝ)) := by
      rw [show (z : ℝ) ^ 2 - (w : ℝ) ^ 2 =
          ((z : ℝ) - (w : ℝ)) * ((z : ℝ) + (w : ℝ)) by ring,
        abs_mul, abs_of_nonneg hsumNonneg]
      congr 1
      exact abs_sub_comm _ _
    rw [habs]
    nlinarith [hmul]
  have hcount := separatedIntervalCount
    (Set.Icc lo hi) Set.ordConnected_Icc T lo hi (4 * (u : ℝ) * H)
    (2 * A * (u : ℝ)) hhi (by positivity) hwidth
    (by intro x hx; exact hx) hTI (by positivity) hTsep
  rw [hcardT] at hcount
  have huReal : 0 < (u : ℝ) := by exact_mod_cast hu
  have hquot : (4 * (u : ℝ) * H) / (2 * A * (u : ℝ)) = 2 * H / A := by
    field_simp [ne_of_gt hA, ne_of_gt huReal]
    ring
  rw [hquot] at hcount
  exact hcount

private theorem negativeSeparatedSquareCount
    (S : Finset ℤ) (residue : ℤ) (u : ℕ)
    (A H lo hi : ℝ) (hA : 0 < A) (hH : 0 ≤ H) (hu : 0 < u)
    (hhi : lo ≤ hi) (hwidth : hi - lo ≤ 4 * (u : ℝ) * H)
    (hSq : ∀ z ∈ S, (z : ℝ) ^ 2 ∈ Set.Icc lo hi)
    (hAlo : ∀ z ∈ S, (z : ℝ) ≤ -A)
    (hres : ∀ z ∈ S, z ≡ residue [ZMOD (u : ℤ)]) :
    (S.card : ℝ) ≤ 2 * H / A + 1 := by
  classical
  let T : Finset ℤ := S.image fun z => -z
  have hneg_inj : Set.InjOn (fun z : ℤ => -z) S := by
    intro z hz w hw hzw
    exact neg_injective hzw
  have hcardT : T.card = S.card := by
    simp [T, Finset.card_image_of_injOn hneg_inj]
  have hTcount := positiveSeparatedSquareCount T (-residue) u A H lo hi
    hA hH hu hhi hwidth
    (by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      simpa using hSq w hw)
    (by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      have hwA := hAlo w hw
      simpa using neg_le_neg hwA)
    (by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact Int.ModEq.neg (hres w hw))
  rw [hcardT] at hTcount
  exact hTcount

private theorem card_le_fiber_bound {α β : Type*} [DecidableEq β]
    (P : Finset α) (C : Finset β) (f : α → β)
    (hmap : ∀ p ∈ P, f p ∈ C) (B : ℝ)
    (hbound : ∀ c ∈ C, ((P.filter fun p => f p = c).card : ℝ) ≤ B) :
    (P.card : ℝ) ≤ (C.card : ℝ) * B := by
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  have hcardReal : (P.card : ℝ) =
      ∑ c ∈ C, ((P.filter fun p => f p = c).card : ℝ) := by
    exact_mod_cast hcard
  calc
    (P.card : ℝ) =
        ∑ c ∈ C, ((P.filter fun p => f p = c).card : ℝ) := hcardReal
    _ ≤ ∑ c ∈ C, B := by
      apply Finset.sum_le_sum
      intro c hc
      exact hbound c hc
    _ = (C.card : ℝ) * B := by simp [mul_comm]

private theorem card_le_weighted_fiber_bound {α β : Type*} [DecidableEq β]
    (P : Finset α) (C : Finset β) (f : α → β)
    (hmap : ∀ p ∈ P, f p ∈ C) (B : β → ℝ)
    (hbound : ∀ c ∈ C, ((P.filter fun p => f p = c).card : ℝ) ≤ B c) :
    (P.card : ℝ) ≤ ∑ c ∈ C, B c := by
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  have hcardReal : (P.card : ℝ) =
      ∑ c ∈ C, ((P.filter fun p => f p = c).card : ℝ) := by
    exact_mod_cast hcard
  calc
    (P.card : ℝ) =
        ∑ c ∈ C, ((P.filter fun p => f p = c).card : ℝ) := hcardReal
    _ ≤ ∑ c ∈ C, B c := by
      apply Finset.sum_le_sum
      intro c hc
      exact hbound c hc

private theorem cellLineFiberRootCount (g : HyperbolaGeometricData)
    (a q : ℕ) (hidx : positiveRationalCellIndexEligible g a q)
    (c : ℤ) (F : Finset (ℤ × ℤ))
    (hF : ∀ p ∈ F, p ∈ cellLinearSliceOnLine g a q c) :
    (F.card : ℝ) ≤
      4 * Real.sqrt (g.H / ((a : ℝ) * (q : ℝ))) + 2 := by
  classical
  let u : ℝ := (a : ℝ) * (q : ℝ)
  let un : ℕ := a * q
  let cR : ℝ := (c : ℝ)
  let lo : ℝ := max 0 (cR ^ 2 - 4 * u * (g.X + g.H))
  let hi : ℝ := cR ^ 2 - 4 * u * g.X
  let zcoord : ℤ × ℤ → ℤ := cellTransverseCoordinate a q
  let Zset : Finset ℤ := F.image zcoord
  have ha : 1 ≤ a := hidx.1.2.2.2.1
  have hq : 1 ≤ q := hidx.1.2.1
  have huNat : 0 < un := by
    dsimp [un]
    exact Nat.mul_pos (by omega) (by omega)
  have huCast : (un : ℝ) = u := by
    simp [un, u, Nat.cast_mul]
  have huPos : 0 < u := by
    dsimp [u]
    have ha' : 0 < a := by omega
    have hq' : 0 < q := by omega
    exact mul_pos (by exact_mod_cast ha') (by exact_mod_cast hq')
  have hHpos : 0 < g.H := by linarith [g.H_ge_one]
  have hdata := cellLinearSlices g a q hidx c
  rcases hdata with ⟨_, hinj, hmod, _⟩
  have hF_inj : Set.InjOn zcoord F := by
    intro p hp p' hp' hzz
    exact hinj (hF p hp) (hF p' hp') hzz
  have hZcard : Zset.card = F.card := by
    simp [Zset, Finset.card_image_of_injOn hF_inj]
  by_cases hFne : F.Nonempty
  · rcases hFne with ⟨p₀, hp₀⟩
    have hp₀Line := hF p₀ hp₀
    change p₀ ∈ cellLinearSlice g a q ∧
      cellLinearCoordinate a q p₀ = c at hp₀Line
    have hc₀ : (cellLinearCoordinate a q p₀ : ℝ) = cR := by
      dsimp [cR]
      exact_mod_cast hp₀Line.2
    have hwin₀ := cellPointSquareWindow g a q hidx p₀ hp₀Line.1
    have hwindow₀ :
        0 ≤ hi ∧ lo ≤ hi ∧ hi - lo ≤ 4 * u * g.H := by
      rcases hwin₀ with ⟨hhi₀, hlohi₀, hwidth₀, _⟩
      rw [hc₀] at hhi₀ hlohi₀ hwidth₀
      have hhi' : 0 ≤ hi := by
        dsimp [hi, cR, u]
        linarith [hhi₀]
      have hlohi' : lo ≤ hi := by
        dsimp [lo, hi, cR, u]
        exact hlohi₀
      have hwidth' : hi - lo ≤ 4 * u * g.H := by
        dsimp [hi, lo, cR, u]
        exact hwidth₀
      exact ⟨hhi', hlohi', hwidth'⟩
    have hwindow : ∀ z ∈ Zset,
        (z : ℝ) ^ 2 ∈ Set.Icc lo hi := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
      have hpLine := hF p hp
      change p ∈ cellLinearSlice g a q ∧
        cellLinearCoordinate a q p = c at hpLine
      have hcp : (cellLinearCoordinate a q p : ℝ) = cR := by
        dsimp [cR]
        exact_mod_cast hpLine.2
      have hwin := cellPointSquareWindow g a q hidx p hpLine.1
      simpa [u, lo, hi, cR, zcoord, hcp] using hwin.2.2.2
    have hres : ∀ z ∈ Zset, z ≡ zcoord p₀ [ZMOD (un : ℤ)] := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
      exact hmod (hF p hp) hp₀Line
    have hcount := residueSquaresIccCount Zset (zcoord p₀) un lo hi
      (4 * u * g.H) (le_max_left 0 _) hwindow₀.1
      hwindow₀.2.1 hwindow₀.2.2 (by positivity) huNat hwindow hres
    have hZcardReal : (Zset.card : ℝ) = (F.card : ℝ) := by
      exact_mod_cast hZcard
    rw [hZcardReal] at hcount
    have hrootFour : Real.sqrt (4 * u * g.H) =
        2 * Real.sqrt (u * g.H) := by
      rw [show 4 * u * g.H = 4 * (u * g.H) by ring,
        Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
      rw [show Real.sqrt (4 : ℝ) = 2 by
        apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
        norm_num]
    have hrootRatio : Real.sqrt (u * g.H) / u = Real.sqrt (g.H / u) := by
      rw [Real.sqrt_mul huPos.le, Real.sqrt_div (le_of_lt hHpos)]
      have huRootPos : 0 < Real.sqrt u := Real.sqrt_pos.mpr huPos
      have huRootSq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt huPos.le
      field_simp [ne_of_gt huPos, ne_of_gt huRootPos]
      rw [huRootSq]
    have hrootBudget :
        2 * Real.sqrt (4 * u * g.H) / (un : ℝ) =
          4 * Real.sqrt (g.H / u) := by
      rw [huCast, hrootFour]
      calc
        2 * (2 * Real.sqrt (u * g.H)) / u =
            4 * (Real.sqrt (u * g.H) / u) := by ring
        _ = 4 * Real.sqrt (g.H / u) := by rw [hrootRatio]
    rw [hrootBudget] at hcount
    exact hcount
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hFne
    simp [hFempty]
    positivity

private theorem nearCellBudget (g : HyperbolaGeometricData)
    (a q : ℕ) (hidx : positiveRationalCellIndexEligible g a q) :
    let u : ℝ := (a : ℝ) * (q : ℝ)
    (2 * Real.sqrt u * g.H / Real.sqrt g.X + 3) *
        (4 * Real.sqrt (g.H / u) + 2) ≤
      64 * (1 + E g.K₀) * S_q g q := by
  let u : ℝ := (a : ℝ) * (q : ℝ)
  have hXpos : 0 < g.X := by linarith [g.X_ge_one]
  have hHpos : 0 < g.H := by linarith [g.H_ge_one]
  have hMpos : 0 < g.M := by linarith [g.M_ge_one]
  have hXnonneg : 0 ≤ g.X := hXpos.le
  have hHnonneg : 0 ≤ g.H := hHpos.le
  have hMnonneg : 0 ≤ g.M := hMpos.le
  have hqlo : 1 ≤ q := hidx.1.2.1
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqnonneg : 0 ≤ (q : ℝ) := hqpos.le
  have hapos : 0 < (a : ℝ) := by
    have ha : 1 ≤ a := hidx.1.2.2.2.1
    exact_mod_cast (show 0 < a by omega)
  have huPos : 0 < u := by dsimp [u]; positivity
  have hrPos : 0 < g.r := by
    dsimp [HyperbolaGeometricData.r]
    exact div_pos hXpos (sq_pos_of_pos hMpos)
  have hrNonneg : 0 ≤ g.r := hrPos.le
  have hEge : 1 ≤ E g.K₀ := by
    dsimp [E]
    nlinarith [g.K₀_ge_one]
  have hEnonneg : 0 ≤ E g.K₀ := le_trans (by norm_num) hEge
  have hSlo : 1 ≤ S_q g q :=
    (admissibleParameterBounds g q hqlo hidx.1.2.2.1).S_lower
  have hSnonneg : 0 ≤ S_q g q := le_trans (by norm_num) hSlo
  have huLower : g.r * (q : ℝ) ^ 2 / 8 ≤ u := by
    rcases hidx.1 with ⟨_, _, _, _, hamin, _⟩
    dsimp [u]
    calc
      g.r * (q : ℝ) ^ 2 / 8 = (g.r / 8 * (q : ℝ)) * (q : ℝ) := by ring
      _ ≤ (a : ℝ) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hamin hqnonneg
  have huUpper : u ≤ E g.K₀ * g.r * (q : ℝ) ^ 2 := by
    rcases hidx.1 with ⟨_, _, _, _, _, hamax⟩
    dsimp [u]
    calc
      (a : ℝ) * (q : ℝ) ≤
          (E g.K₀ * g.r * (q : ℝ)) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hamax hqnonneg
      _ = E g.K₀ * g.r * (q : ℝ) ^ 2 := by ring
  have hrootE : Real.sqrt (E g.K₀) ≤ E g.K₀ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hEnonneg).mp
    rw [Real.sq_sqrt hEnonneg]
    nlinarith [hEge]
  have hroot8 : Real.sqrt (8 : ℝ) ≤ 3 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : 0 ≤ (3 : ℝ))).mp
    rw [Real.sq_sqrt (by norm_num : 0 ≤ (8 : ℝ))]
    norm_num
  have hrSqrt : Real.sqrt g.r = Real.sqrt g.X / g.M := by
    dsimp [HyperbolaGeometricData.r]
    rw [Real.sqrt_div hXnonneg, Real.sqrt_sq hMnonneg]
  have huRoot : Real.sqrt u ≤
      Real.sqrt (E g.K₀) * Real.sqrt g.r * (q : ℝ) := by
    calc
      Real.sqrt u ≤
          Real.sqrt (E g.K₀ * g.r * (q : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt huUpper
      _ = Real.sqrt (E g.K₀) * Real.sqrt g.r * (q : ℝ) := by
        rw [Real.sqrt_mul (mul_nonneg hEnonneg hrNonneg),
          Real.sqrt_mul hEnonneg, Real.sqrt_sq hqnonneg]
  have htermTwoBase : Real.sqrt u * g.H / Real.sqrt g.X ≤
      Real.sqrt (E g.K₀) * ((q : ℝ) * g.H / g.M) := by
    have hmul := mul_le_mul_of_nonneg_right huRoot
      (div_nonneg hHnonneg (Real.sqrt_nonneg g.X))
    calc
      Real.sqrt u * g.H / Real.sqrt g.X =
          Real.sqrt u * (g.H / Real.sqrt g.X) := by ring
      _ ≤ (Real.sqrt (E g.K₀) * Real.sqrt g.r * (q : ℝ)) *
          (g.H / Real.sqrt g.X) := hmul
      _ = Real.sqrt (E g.K₀) * ((q : ℝ) * g.H / g.M) := by
        rw [hrSqrt]
        have hrootXpos : 0 < Real.sqrt g.X := Real.sqrt_pos.mpr hXpos
        field_simp [ne_of_gt hMpos, ne_of_gt hrootXpos]
  have htermTwo :
      4 * (Real.sqrt u * g.H / Real.sqrt g.X) ≤
        4 * E g.K₀ * S_q g q := by
    calc
      4 * (Real.sqrt u * g.H / Real.sqrt g.X) ≤
          4 * (Real.sqrt (E g.K₀) * ((q : ℝ) * g.H / g.M)) :=
        mul_le_mul_of_nonneg_left htermTwoBase (by norm_num)
      _ ≤ 4 * E g.K₀ * S_q g q := by
        have hqH := (admissibleParameterBounds g q hqlo
          hidx.1.2.2.1).qH_div_M_le_S
        have hterm₁ := mul_le_mul_of_nonneg_left hqH (Real.sqrt_nonneg (E g.K₀))
        have hterm₂ := mul_le_mul_of_nonneg_right hrootE hSnonneg
        calc
          4 * (Real.sqrt (E g.K₀) * ((q : ℝ) * g.H / g.M)) ≤
              4 * (Real.sqrt (E g.K₀) * S_q g q) :=
            mul_le_mul_of_nonneg_left hterm₁ (by norm_num)
          _ ≤ 4 * E g.K₀ * S_q g q := by
            nlinarith [hterm₂]
  have htermThreeBase :
      Real.sqrt (g.H / u) ≤
        Real.sqrt (8 : ℝ) *
          (Real.sqrt g.H * g.M / ((q : ℝ) * Real.sqrt g.X)) := by
    have hdenPos : 0 < g.r * (q : ℝ) ^ 2 :=
      mul_pos hrPos (sq_pos_of_pos hqpos)
    have hcross : g.r * (q : ℝ) ^ 2 ≤ 8 * u := by
      nlinarith [huLower]
    have hdiv : g.H / u ≤ 8 * g.H / (g.r * (q : ℝ) ^ 2) := by
      apply (div_le_div_iff₀ huPos hdenPos).2
      nlinarith [mul_le_mul_of_nonneg_left hcross hHnonneg]
    have hrootdiv := Real.sqrt_le_sqrt hdiv
    have hdenSqrt : Real.sqrt (g.r * (q : ℝ) ^ 2) =
        Real.sqrt g.r * (q : ℝ) := by
      rw [Real.sqrt_mul hrNonneg, Real.sqrt_sq hqnonneg]
    have hnumerSqrt : Real.sqrt (8 * g.H) =
        Real.sqrt (8 : ℝ) * Real.sqrt g.H := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (8 : ℝ))]
    rw [Real.sqrt_div (by positivity : 0 ≤ 8 * g.H),
      hnumerSqrt, hdenSqrt, hrSqrt] at hrootdiv
    have hrootXpos : 0 < Real.sqrt g.X := Real.sqrt_pos.mpr hXpos
    have hrootqpos : 0 < (q : ℝ) := hqpos
    have hrootRhs :
        Real.sqrt (8 : ℝ) * Real.sqrt g.H /
            ((Real.sqrt g.X / g.M) * (q : ℝ)) =
          Real.sqrt (8 : ℝ) *
            (Real.sqrt g.H * g.M / ((q : ℝ) * Real.sqrt g.X)) := by
      field_simp [ne_of_gt hMpos, ne_of_gt hrootXpos, ne_of_gt hrootqpos]
    rw [hrootRhs] at hrootdiv
    exact hrootdiv
  have htermThree :
      12 * Real.sqrt (g.H / u) ≤ 36 * S_q g q := by
    calc
      12 * Real.sqrt (g.H / u) ≤
          12 * (Real.sqrt (8 : ℝ) *
            (Real.sqrt g.H * g.M / ((q : ℝ) * Real.sqrt g.X))) :=
        mul_le_mul_of_nonneg_left htermThreeBase (by norm_num)
      _ ≤ 36 * S_q g q := by
        have hscale := (admissibleParameterBounds g q hqlo
          hidx.1.2.2.1).sqrtH_M_div_q_sqrtX_le_S
        let V : ℝ := Real.sqrt g.H * g.M / ((q : ℝ) * Real.sqrt g.X)
        have hVnonneg : 0 ≤ V := by dsimp [V]; positivity
        have hrootScale : 12 * Real.sqrt (8 : ℝ) ≤ 36 := by nlinarith [hroot8]
        calc
          12 * (Real.sqrt (8 : ℝ) * V) =
              (12 * Real.sqrt (8 : ℝ)) * V := by ring
          _ ≤ 36 * V := mul_le_mul_of_nonneg_right hrootScale hVnonneg
          _ ≤ 36 * S_q g q := mul_le_mul_of_nonneg_left hscale (by norm_num)
  have htermOne :
      8 * (g.H ^ (3 / 2 : ℝ) / Real.sqrt g.X) ≤ 8 * S_q g q := by
    have hscale := (admissibleParameterBounds g q hqlo
      hidx.1.2.2.1).H_three_halves_le_S
    exact mul_le_mul_of_nonneg_left hscale (by norm_num)
  have htermFour : 6 ≤ 6 * S_q g q := by nlinarith [hSlo]
  have hcoefficient :
      8 + 4 * E g.K₀ + 36 + 6 ≤ 64 * (1 + E g.K₀) := by
    nlinarith [hEge]
  have hsum :
      8 * (g.H ^ (3 / 2 : ℝ) / Real.sqrt g.X) +
        4 * (Real.sqrt u * g.H / Real.sqrt g.X) +
        12 * Real.sqrt (g.H / u) + 6 ≤
      64 * (1 + E g.K₀) * S_q g q := by
    have hcoeffS := mul_le_mul_of_nonneg_right hcoefficient hSnonneg
    nlinarith [htermOne, htermTwo, htermThree, htermFour, hcoeffS]
  have hsqrtHpow : g.H ^ (3 / 2 : ℝ) = g.H * Real.sqrt g.H := by
    calc
      g.H ^ (3 / 2 : ℝ) = g.H ^ (1 + (1 / 2 : ℝ)) := by
        congr 1
        norm_num
      _ = g.H ^ (1 : ℝ) * g.H ^ (1 / 2 : ℝ) := Real.rpow_add hHpos _ _
      _ = g.H * Real.sqrt g.H := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hrootCancel : Real.sqrt u * Real.sqrt (g.H / u) =
      Real.sqrt g.H := by
    rw [← Real.sqrt_mul huPos.le]
    congr 1
    field_simp [ne_of_gt huPos]
  have hproduct :
      (2 * Real.sqrt u * g.H / Real.sqrt g.X + 3) *
          (4 * Real.sqrt (g.H / u) + 2) =
        8 * (g.H ^ (3 / 2 : ℝ) / Real.sqrt g.X) +
          4 * (Real.sqrt u * g.H / Real.sqrt g.X) +
          12 * Real.sqrt (g.H / u) + 6 := by
    calc
      (2 * Real.sqrt u * g.H / Real.sqrt g.X + 3) *
          (4 * Real.sqrt (g.H / u) + 2) =
        8 * (Real.sqrt u * g.H / Real.sqrt g.X *
            Real.sqrt (g.H / u)) +
          4 * (Real.sqrt u * g.H / Real.sqrt g.X) +
          12 * Real.sqrt (g.H / u) + 6 := by ring
      _ = 8 * (g.H * Real.sqrt g.H / Real.sqrt g.X) +
          4 * (Real.sqrt u * g.H / Real.sqrt g.X) +
          12 * Real.sqrt (g.H / u) + 6 := by
            rw [show Real.sqrt u * g.H / Real.sqrt g.X *
                Real.sqrt (g.H / u) =
                  g.H * (Real.sqrt u * Real.sqrt (g.H / u)) /
                    Real.sqrt g.X by ring,
              hrootCancel]
      _ = 8 * (g.H ^ (3 / 2 : ℝ) / Real.sqrt g.X) +
          4 * (Real.sqrt u * g.H / Real.sqrt g.X) +
          12 * Real.sqrt (g.H / u) + 6 := by rw [← hsqrtHpow]
  change (2 * Real.sqrt u * g.H / Real.sqrt g.X + 3) *
      (4 * Real.sqrt (g.H / u) + 2) ≤
      64 * (1 + E g.K₀) * S_q g q
  rw [hproduct]
  exact hsum

private def cellDyadicIndex (z : ℤ) : ℕ := Nat.log 2 z.natAbs

private def cellDyadicScale (z : ℤ) : ℕ := 2 ^ cellDyadicIndex z

private theorem cellDyadicBounds (z : ℤ) (hz : z ≠ 0) :
    (cellDyadicScale z : ℝ) ≤ |(z : ℝ)| ∧
      |(z : ℝ)| < 2 * (cellDyadicScale z : ℝ) := by
  have hnz : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hlow : 2 ^ Nat.log 2 z.natAbs ≤ z.natAbs :=
    Nat.pow_log_le_self 2 hnz
  have hhigh : z.natAbs < 2 ^ (Nat.log 2 z.natAbs + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) z.natAbs
  have hhigh' : z.natAbs < 2 ^ Nat.log 2 z.natAbs * 2 := by
    calc
      z.natAbs < 2 ^ (Nat.log 2 z.natAbs + 1) := hhigh
      _ = 2 ^ Nat.log 2 z.natAbs * 2 := by rw [Nat.pow_succ]
  have habs : |(z : ℝ)| = (z.natAbs : ℝ) := by
    calc
      |(z : ℝ)| = ((|z| : ℤ) : ℝ) := by rw [← Int.cast_abs]
      _ = ((z.natAbs : ℤ) : ℝ) := by
        exact congrArg (fun w : ℤ => (w : ℝ))
          (Int.natCast_natAbs z).symm
      _ = (z.natAbs : ℝ) := by simp
  constructor
  · rw [cellDyadicScale, cellDyadicIndex, habs]
    exact_mod_cast hlow
  · rw [cellDyadicScale, cellDyadicIndex, habs]
    have hhighReal : (z.natAbs : ℝ) <
        2 * ((2 ^ Nat.log 2 z.natAbs : ℕ) : ℝ) := by
      have h' : (z.natAbs : ℝ) <
          (((2 ^ Nat.log 2 z.natAbs * 2 : ℕ) : ℝ)) := by
        exact_mod_cast hhigh'
      simpa [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using h'
    exact hhighReal

private theorem integerIocCount (S : Finset ℤ) (a B : ℝ)
    (hB : 0 ≤ B)
    (hS : ∀ c ∈ S, (c : ℝ) ∈ Set.Ioc a (a + B)) :
    (S.card : ℝ) ≤ B + 1 := by
  have hcount := residueClassIntervalCount
    (Set.Ioc a (a + B)) Set.ordConnected_Ioc S 0 1 a (a + B) B
    (by linarith) hB (by linarith)
    (by
      intro x hx
      rcases Set.mem_Ioc.mp hx with ⟨hlt, hle⟩
      exact ⟨hlt.le, hle⟩)
    hS (by norm_num)
    (by intro c hc; norm_num [Int.ModEq])
  simpa using hcount

private theorem cellFarPointFacts (g : HyperbolaGeometricData)
    (a q : ℕ) (hidx : positiveRationalCellIndexEligible g a q)
    (p : ℤ × ℤ) (hp : p ∈ cellLinearSlice g a q)
    (hfar : ¬ ((cellLinearCoordinate a q p : ℝ) -
      2 * Real.sqrt ((a : ℝ) * (q : ℝ) * g.X) ≤
        4 * ((a : ℝ) * (q : ℝ)) * g.H /
          (2 * Real.sqrt ((a : ℝ) * (q : ℝ) * g.X)) + 2)) :
    let u : ℝ := (a : ℝ) * (q : ℝ)
    let t : ℝ := 2 * Real.sqrt (u * g.X)
    let c : ℝ := (cellLinearCoordinate a q p : ℝ)
    let z : ℝ := (cellTransverseCoordinate a q p : ℝ)
    2 < c - t ∧ c ^ 2 - t ^ 2 > 8 * u * g.H + 4 * t ∧
      z ^ 2 > (c ^ 2 - t ^ 2) / 2 ∧ c - t ≤ z ^ 2 / t ∧
      cellTransverseCoordinate a q p ≠ 0 := by
  let u : ℝ := (a : ℝ) * (q : ℝ)
  let t : ℝ := 2 * Real.sqrt (u * g.X)
  let c : ℝ := (cellLinearCoordinate a q p : ℝ)
  let z : ℝ := (cellTransverseCoordinate a q p : ℝ)
  let delta : ℝ := c ^ 2 - t ^ 2
  have hdata := cellPointCoordinateBounds g a q hidx p hp
  change c > t ∧ 0 < t ∧ |z| ≤ 2 * D g.K₀ * g.M / (g.Q : ℝ) ∧
    c ^ 2 - z ^ 2 = 4 * u * (p.1 : ℝ) * (p.2 : ℝ) ∧
    g.r * (q : ℝ) ^ 2 / 8 ≤ u ∧
    u ≤ E g.K₀ * g.r * (q : ℝ) ^ 2 ∧
    g.X < (p.1 : ℝ) * (p.2 : ℝ) ∧
    (p.1 : ℝ) * (p.2 : ℝ) ≤ g.X + g.H at hdata
  rcases hdata with ⟨hcgt, htpos, _, hid, _, _, hprodLo, hprodHi⟩
  have hXpos : 0 < g.X := by linarith [g.X_ge_one]
  have hHpos : 0 < g.H := by linarith [g.H_ge_one]
  have huPos : 0 < u := by
    dsimp [u]
    have ha : 0 < a := by have h := hidx.1.2.2.2.1; omega
    have hq : 0 < q := by have h := hidx.1.2.1; omega
    positivity
  have htSq : t ^ 2 = 4 * u * g.X := by
    dsimp [t]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hdeltaFactor : delta = (c - t) * (c + t) := by
    dsimp [delta]
    ring
  have hnearLt : 4 * u * g.H / t + 2 < c - t := by
    dsimp [u, t, c] at hfar ⊢
    exact lt_of_not_ge hfar
  have hct : 2 * t ≤ c + t := by linarith [hcgt]
  have hdelta : 8 * u * g.H + 4 * t < delta := by
    have hmul := mul_lt_mul_of_pos_right hnearLt
      (show 0 < 2 * t by positivity)
    have hleft : (4 * u * g.H / t + 2) * (2 * t) =
        8 * u * g.H + 4 * t := by
      field_simp [ne_of_gt htpos]
      ring
    rw [hleft] at hmul
    have hthresholdPos : 0 < 4 * u * g.H / t + 2 := by positivity
    have hcmtnonneg : 0 ≤ c - t := le_of_lt (lt_trans hthresholdPos hnearLt)
    have hmul' := mul_le_mul_of_nonneg_left hct hcmtnonneg
    rw [← hdeltaFactor] at hmul'
    exact lt_of_lt_of_le hmul hmul'
  have hproductExcess : 0 < (p.1 : ℝ) * (p.2 : ℝ) - g.X := by
    linarith [hprodLo]
  have hproductExcessUpper : (p.1 : ℝ) * (p.2 : ℝ) - g.X ≤ g.H := by
    linarith [hprodHi]
  have hsubBound := mul_le_mul_of_nonneg_left hproductExcessUpper
    (show 0 ≤ 4 * u by positivity)
  have hzSq : z ^ 2 = delta -
      4 * u * ((p.1 : ℝ) * (p.2 : ℝ) - g.X) := by
    calc
      z ^ 2 = c ^ 2 - 4 * u * ((p.1 : ℝ) * (p.2 : ℝ)) := by
        nlinarith [hid]
      _ = (c ^ 2 - t ^ 2) -
          4 * u * ((p.1 : ℝ) * (p.2 : ℝ) - g.X) := by
        rw [htSq]
        ring
      _ = delta - 4 * u * ((p.1 : ℝ) * (p.2 : ℝ) - g.X) := by
        rfl
  have hdeltaHalf : 4 * u * g.H < delta / 2 := by
    nlinarith [hdelta]
  have hzFar : z ^ 2 > delta / 2 := by
    calc
      z ^ 2 = delta - 4 * u * ((p.1 : ℝ) * (p.2 : ℝ) - g.X) := hzSq
      _ ≥ delta - 4 * u * g.H := by nlinarith [hsubBound]
      _ > delta / 2 := by nlinarith [hdeltaHalf]
  have hctLower : 2 < c - t := by
    have hfour : 0 < 4 * u * g.H / t := by positivity
    linarith [hnearLt, hfour]
  have hdeltaBase : 0 < 8 * u * g.H + 4 * t := by positivity
  have hdeltaPos : 0 < delta := lt_trans hdeltaBase hdelta
  have hzSqPos : 0 < z ^ 2 := lt_trans (by linarith [hdeltaPos]) hzFar
  have hzNonzero : cellTransverseCoordinate a q p ≠ 0 := by
    intro hzero
    have : z = 0 := by simp [z, hzero]
    rw [this] at hzSqPos
    norm_num at hzSqPos
  have hctPos : 0 < c + t := by linarith [hcgt, htpos]
  have hfrac : c - t = delta / (c + t) := by
    rw [hdeltaFactor]
    field_simp [ne_of_gt hctPos]
  have hdeltaSmall : delta < 2 * z ^ 2 := by linarith [hzFar]
  have hprodDen := mul_le_mul_of_nonneg_left hct
    (div_nonneg (sq_nonneg z) htpos.le)
  have htwoSq : 2 * z ^ 2 ≤ (z ^ 2 / t) * (c + t) := by
    calc
      2 * z ^ 2 = (z ^ 2 / t) * (2 * t) := by field_simp [ne_of_gt htpos]
      _ ≤ (z ^ 2 / t) * (c + t) := hprodDen
  have hfracLe : delta / (c + t) ≤ z ^ 2 / t := by
    apply (div_le_iff₀ hctPos).2
    exact le_trans hdeltaSmall.le htwoSq
  have hquot : c - t ≤ z ^ 2 / t := by rw [hfrac]; exact hfracLe
  change 2 < c - t ∧ delta > 8 * u * g.H + 4 * t ∧
    z ^ 2 > delta / 2 ∧ c - t ≤ z ^ 2 / t ∧
      cellTransverseCoordinate a q p ≠ 0
  exact ⟨hctLower, hdelta, hzFar, hquot, hzNonzero⟩

private theorem dyadicPowerSumBound (J : Finset ℕ) (Z : ℝ)
    (hZ : 1 ≤ Z)
    (hJ : ∀ j ∈ J, (2 ^ j : ℕ) ≤ Nat.floor Z) :
    (∑ j ∈ J, (2 ^ j : ℕ) : ℝ) ≤ 2 * Z := by
  have hn : Nat.floor Z ≠ 0 := by
    have hZreal : (1 : ℕ) ≤ Z := by exact_mod_cast hZ
    have hfloor : 1 ≤ Nat.floor Z := Nat.le_floor hZreal
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hfloor)
  let N : ℕ := Nat.log 2 (Nat.floor Z)
  have hJrange : ∀ j ∈ J, j < N + 1 := by
    intro j hj
    have hlog := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (hJ j hj)
    dsimp [N]
    omega
  have hsumNat :
      (∑ j ∈ J, (2 ^ j : ℕ)) < 2 ^ (N + 1) :=
    Nat.geomSum_lt (by norm_num : 2 ≤ 2) (fun j hj => hJrange j hj)
  have hpowlog : 2 ^ N ≤ Nat.floor Z := by
    dsimp [N]
    exact Nat.pow_log_le_self 2 hn
  have hpow : 2 ^ (N + 1) ≤ 2 * Nat.floor Z := by
    calc
      2 ^ (N + 1) = 2 ^ N * 2 := by rw [Nat.pow_succ]
      _ ≤ Nat.floor Z * 2 := Nat.mul_le_mul_right 2 hpowlog
      _ = 2 * Nat.floor Z := by omega
  have hfloor : (Nat.floor Z : ℝ) ≤ Z := Nat.floor_le (by linarith)
  have hsumReal :
      (∑ j ∈ J, (2 ^ j : ℕ) : ℝ) ≤ (2 ^ (N + 1) : ℝ) := by
    exact_mod_cast hsumNat.le
  have hpowReal : (2 ^ (N + 1) : ℝ) ≤ 2 * Z := by
    calc
      (2 ^ (N + 1) : ℝ) ≤ 2 * (Nat.floor Z : ℝ) := by exact_mod_cast hpow
      _ ≤ 2 * Z := mul_le_mul_of_nonneg_left hfloor (by norm_num)
  exact hsumReal.trans hpowReal

private theorem cellLineDyadicFiberCount (g : HyperbolaGeometricData)
    (a q : ℕ) (hidx : positiveRationalCellIndexEligible g a q)
    (c : ℤ) (F : Finset (ℤ × ℤ))
    (hF : ∀ p ∈ F, p ∈ cellLinearSliceOnLine g a q c)
    (A : ℝ) (hA : 0 < A)
    (hbin : ∀ p ∈ F,
      A ≤ |(cellTransverseCoordinate a q p : ℝ)| ∧
        |(cellTransverseCoordinate a q p : ℝ)| < 2 * A)
    (hAZ : A ≤ 2 * D g.K₀ * g.H) :
    (F.card : ℝ) ≤ 4 * (1 + D g.K₀) * g.H / A := by
  classical
  let u : ℝ := (a : ℝ) * (q : ℝ)
  let un : ℕ := a * q
  let cR : ℝ := (c : ℝ)
  let lo : ℝ := max 0 (cR ^ 2 - 4 * u * (g.X + g.H))
  let hi : ℝ := cR ^ 2 - 4 * u * g.X
  let zcoord : ℤ × ℤ → ℤ := cellTransverseCoordinate a q
  let Zset : Finset ℤ := F.image zcoord
  let Zpos : Finset ℤ := Zset.filter fun z => A ≤ (z : ℝ)
  let Zneg : Finset ℤ := Zset.filter fun z => (z : ℝ) ≤ -A
  have haNat : 0 < a := by
    have h := hidx.1.2.2.2.1
    omega
  have hqNat : 0 < q := by
    have h := hidx.1.2.1
    omega
  have huNat : 0 < un := by
    dsimp [un]
    exact Nat.mul_pos haNat hqNat
  have huCast : (un : ℝ) = u := by simp [un, u, Nat.cast_mul]
  have huPos : 0 < u := by
    dsimp [u]
    exact mul_pos (by exact_mod_cast haNat) (by exact_mod_cast hqNat)
  have hHpos : 0 < g.H := by linarith [g.H_ge_one]
  have hHnonneg : 0 ≤ g.H := hHpos.le
  have hDnonneg : 0 ≤ D g.K₀ := by dsimp [D]; positivity
  have hdata := cellLinearSlices g a q hidx c
  rcases hdata with ⟨_, hinj, hmod, _⟩
  have hFinj : Set.InjOn zcoord F := by
    intro p hp p' hp' hzz
    exact hinj (hF p hp) (hF p' hp') hzz
  have hZcard : Zset.card = F.card := by
    simp [Zset, Finset.card_image_of_injOn hFinj]
  by_cases hFne : F.Nonempty
  · rcases hFne with ⟨p₀, hp₀⟩
    have hp₀line := hF p₀ hp₀
    change p₀ ∈ cellLinearSlice g a q ∧
      cellLinearCoordinate a q p₀ = c at hp₀line
    have hc₀ : (cellLinearCoordinate a q p₀ : ℝ) = cR := by
      dsimp [cR]
      exact_mod_cast hp₀line.2
    have hwindow₀ := cellPointSquareWindow g a q hidx p₀ hp₀line.1
    have hwindow :
        0 ≤ hi ∧ lo ≤ hi ∧ hi - lo ≤ 4 * u * g.H := by
      rcases hwindow₀ with ⟨hhi₀, hlohi₀, hwidth₀, _⟩
      rw [hc₀] at hhi₀ hlohi₀ hwidth₀
      have hhi' : 0 ≤ hi := by
        dsimp [hi, cR, u]
        exact hhi₀
      have hlohi' : lo ≤ hi := by
        dsimp [lo, hi, cR, u]
        exact hlohi₀
      have hwidth' : hi - lo ≤ 4 * u * g.H := by
        dsimp [hi, lo, cR, u]
        exact hwidth₀
      exact ⟨hhi', hlohi', hwidth'⟩
    have hsq : ∀ z ∈ Zset, (z : ℝ) ^ 2 ∈ Set.Icc lo hi := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
      have hpline := hF p hp
      change p ∈ cellLinearSlice g a q ∧
        cellLinearCoordinate a q p = c at hpline
      have hcp : (cellLinearCoordinate a q p : ℝ) = cR := by
        dsimp [cR]
        exact_mod_cast hpline.2
      have hwp := cellPointSquareWindow g a q hidx p hpline.1
      simpa [u, lo, hi, cR, zcoord, hcp] using hwp.2.2.2
    have hres : ∀ z ∈ Zset, z ≡ zcoord p₀ [ZMOD (un : ℤ)] := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
      exact hmod (hF p hp) hp₀line
    have hsplit : Zset ⊆ Zpos ∪ Zneg := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
      have habs := (hbin p hp).1
      by_cases hzpos : 0 ≤ (zcoord p : ℝ)
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
        rw [abs_of_nonneg hzpos] at habs
        exact habs
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
        have hzneg : (zcoord p : ℝ) ≤ 0 := le_of_lt (lt_of_not_ge hzpos)
        rw [abs_of_nonpos hzneg] at habs
        linarith
    have hcardSplit : Zset.card ≤ Zpos.card + Zneg.card := by
      calc
        Zset.card ≤ (Zpos ∪ Zneg).card := Finset.card_le_card hsplit
        _ ≤ Zpos.card + Zneg.card := Finset.card_union_le _ _
    have hwidthNat : hi - lo ≤ 4 * (un : ℝ) * g.H := by
      rw [huCast]
      exact hwindow.2.2
    have hposCount := positiveSeparatedSquareCount Zpos (zcoord p₀) un A g.H
      lo hi hA hHnonneg huNat hwindow.2.1 hwidthNat
      (by
        intro z hz
        exact hsq z (Finset.mem_filter.mp hz).1)
      (by
        intro z hz
        exact (Finset.mem_filter.mp hz).2)
      (by
        intro z hz
        exact hres z (Finset.mem_filter.mp hz).1)
    have hnegCount := negativeSeparatedSquareCount Zneg (zcoord p₀) un A g.H
      lo hi hA hHnonneg huNat hwindow.2.1 hwidthNat
      (by
        intro z hz
        exact hsq z (Finset.mem_filter.mp hz).1)
      (by
        intro z hz
        exact (Finset.mem_filter.mp hz).2)
      (by
        intro z hz
        exact hres z (Finset.mem_filter.mp hz).1)
    have hcardReal : (Zset.card : ℝ) ≤
        (Zpos.card : ℝ) + (Zneg.card : ℝ) := by exact_mod_cast hcardSplit
    have hZreal : (Zset.card : ℝ) = (F.card : ℝ) := by exact_mod_cast hZcard
    have hpre : (F.card : ℝ) ≤ 4 * g.H / A + 2 := by
      rw [← hZreal]
      calc
        (Zset.card : ℝ) ≤ (Zpos.card : ℝ) + (Zneg.card : ℝ) := hcardReal
        _ ≤ (2 * g.H / A + 1) + (2 * g.H / A + 1) := add_le_add hposCount hnegCount
        _ = 4 * g.H / A + 2 := by ring
    have hAbsorb : 2 ≤ 4 * D g.K₀ * g.H / A := by
      apply (le_div_iff₀ hA).2
      nlinarith [hAZ]
    have hsumAbsorb : 4 * g.H / A + 2 ≤
        4 * g.H / A + 4 * D g.K₀ * g.H / A := by
      linarith [hAbsorb]
    calc
      (F.card : ℝ) ≤ 4 * g.H / A + 2 := hpre
      _ ≤ 4 * g.H / A + 4 * D g.K₀ * g.H / A := hsumAbsorb
      _ = 4 * (1 + D g.K₀) * g.H / A := by ring
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hFne
    simp [hFempty]
    positivity

theorem rationalCellPointCount (g : HyperbolaGeometricData)
    (a q : ℕ) (hidx : positiveRationalCellIndexEligible g a q) :
    ((cellLinearSlice g a q).ncard : ℝ) ≤ C_point g.K₀ * S_q g q := by
  classical
  let u : ℝ := (a : ℝ) * (q : ℝ)
  let t : ℝ := 2 * Real.sqrt (u * g.X)
  let Bnear : ℝ := 4 * u * g.H / t + 2
  let nearPred : (ℤ × ℤ) → Prop := fun p =>
    (cellLinearCoordinate a q p : ℝ) - t ≤ Bnear
  have hqlo : 1 ≤ q := hidx.1.2.1
  have hqhi : q ≤ g.Q := hidx.1.2.2.1
  have hparams := admissibleParameterBounds g q hqlo hqhi
  have hXpos : 0 < g.X := by linarith [g.X_ge_one]
  have hHpos : 0 < g.H := by linarith [g.H_ge_one]
  have hMpos : 0 < g.M := by linarith [g.M_ge_one]
  have hQpos : 0 < (g.Q : ℝ) := by exact_mod_cast g.Q_pos
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqnonneg : 0 ≤ (q : ℝ) := hqpos.le
  have huPos : 0 < u := by
    dsimp [u]
    have ha : 0 < a := by have h := hidx.1.2.2.2.1; omega
    have hq : 0 < q := by have h := hidx.1.2.1; omega
    exact mul_pos (by exact_mod_cast ha) (by exact_mod_cast hq)
  have hTpos : 0 < t := by dsimp [t]; positivity
  have hrPos : 0 < g.r := by
    dsimp [HyperbolaGeometricData.r]
    exact div_pos hXpos (sq_pos_of_pos hMpos)
  have huLower : g.r * (q : ℝ) ^ 2 / 8 ≤ u := by
    rcases hidx.1 with ⟨_, _, _, _, hamin, _⟩
    dsimp [u]
    calc
      g.r * (q : ℝ) ^ 2 / 8 =
          (g.r / 8 * (q : ℝ)) * (q : ℝ) := by ring
      _ ≤ (a : ℝ) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hamin hqnonneg
  have huUpper : u ≤ E g.K₀ * g.r * (q : ℝ) ^ 2 := by
    rcases hidx.1 with ⟨_, _, _, _, _, hamax⟩
    dsimp [u]
    calc
      (a : ℝ) * (q : ℝ) ≤
          (E g.K₀ * g.r * (q : ℝ)) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hamax hqnonneg
      _ = E g.K₀ * g.r * (q : ℝ) ^ 2 := by ring
  have hSliceFinite : (cellLinearSlice g a q).Finite := by
    apply hparams.lattice_finite.subset
    intro p hp
    exact hp.1
  obtain ⟨S, hSmem, _, hcoverage, _, _⟩ :=
    occupiedSliceCount g a q hidx
  let P : Finset (ℤ × ℤ) := hSliceFinite.toFinset
  have hPmem : ∀ p, p ∈ P ↔ p ∈ cellLinearSlice g a q := by
    intro p
    simp [P]
  have hcoordS : ∀ p ∈ P, cellLinearCoordinate a q p ∈ S := by
    intro p hp
    rcases (hcoverage p).mp ((hPmem p).mp hp) with ⟨c, hc, hline⟩
    have hline' : p ∈ cellLinearSlice g a q ∧
        cellLinearCoordinate a q p = c := by
      simpa [cellLinearSliceOnLine, cellLinearCoordinate] using hline
    rw [hline'.2]
    exact hc
  let Pnear : Finset (ℤ × ℤ) := P.filter nearPred
  let Pfar : Finset (ℤ × ℤ) := P.filter fun p => ¬ nearPred p
  have hsplitNat : Pnear.card + Pfar.card = P.card :=
    Finset.card_filter_add_card_filter_not (s := P) nearPred
  have hsplitReal : (P.card : ℝ) =
      (Pnear.card : ℝ) + (Pfar.card : ℝ) := by exact_mod_cast hsplitNat.symm
  let Cnear : Finset ℤ := S.filter fun c => (c : ℝ) - t ≤ Bnear
  have hnearMap : ∀ p ∈ Pnear, cellLinearCoordinate a q p ∈ Cnear := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpP, hpnear⟩
    apply Finset.mem_filter.mpr
    refine ⟨hcoordS p hpP, ?_⟩
    simpa [nearPred] using hpnear
  have hnearInterval : ∀ c ∈ Cnear,
      (c : ℝ) ∈ Set.Ioc t (t + Bnear) := by
    intro c hc
    rcases Finset.mem_filter.mp hc with ⟨hcS, hcnear⟩
    have hcOcc := (hSmem c).mp hcS
    have hcIoc := occupiedSliceValue_mem_Ioc g a q hidx hcOcc
    change (c : ℝ) ∈ Set.Ioc t (t + occupiedSliceWindowWidth g q) at hcIoc
    refine ⟨hcIoc.1, ?_⟩
    linarith [hcnear]
  have hnearLines : (Cnear.card : ℝ) ≤ Bnear + 1 := by
    exact integerIocCount Cnear t Bnear (by positivity) hnearInterval
  let rootBudget : ℝ := 4 * Real.sqrt (g.H / u) + 2
  have hnearFiber : ∀ c ∈ Cnear,
      ((Pnear.filter fun p => cellLinearCoordinate a q p = c).card : ℝ) ≤
        rootBudget := by
    intro c hc
    let F := Pnear.filter fun p => cellLinearCoordinate a q p = c
    have hFline : ∀ p ∈ F, p ∈ cellLinearSliceOnLine g a q c := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpnear, hEq⟩
      have hpP := (Finset.mem_filter.mp hpnear).1
      change p ∈ cellLinearSlice g a q ∧
        cellLinearCoordinate a q p = c
      exact ⟨(hPmem p).mp hpP, hEq⟩
    have hroot := cellLineFiberRootCount g a q hidx c F hFline
    simpa [F, rootBudget, u] using hroot
  have hnearPointCount : (Pnear.card : ℝ) ≤
      (Cnear.card : ℝ) * rootBudget := by
    exact card_le_fiber_bound Pnear Cnear (cellLinearCoordinate a q)
      hnearMap rootBudget hnearFiber
  have hXroot : 0 < Real.sqrt g.X := Real.sqrt_pos.mpr hXpos
  have huRoot : 0 < Real.sqrt u := Real.sqrt_pos.mpr huPos
  have htEq : t = 2 * Real.sqrt u * Real.sqrt g.X := by
    dsimp [t]
    rw [Real.sqrt_mul huPos.le]
    ring
  have hnearWidthEq : Bnear + 1 =
      2 * Real.sqrt u * g.H / Real.sqrt g.X + 3 := by
    dsimp [Bnear]
    rw [htEq]
    have hcancel : 4 * u * g.H / (2 * Real.sqrt u * Real.sqrt g.X) =
        2 * Real.sqrt u * g.H / Real.sqrt g.X := by
      field_simp [ne_of_gt huRoot, ne_of_gt hXroot]
      rw [Real.sq_sqrt huPos.le]
      ring
    rw [hcancel]
    ring
  have hnearBudget := nearCellBudget g a q hidx
  have hnearTotal : (Pnear.card : ℝ) ≤
      64 * (1 + E g.K₀) * S_q g q := by
    calc
      (Pnear.card : ℝ) ≤ (Cnear.card : ℝ) * rootBudget := hnearPointCount
      _ ≤ (Bnear + 1) * rootBudget := by
        exact mul_le_mul_of_nonneg_right hnearLines (by positivity)
      _ = (2 * Real.sqrt u * g.H / Real.sqrt g.X + 3) *
          (4 * Real.sqrt (g.H / u) + 2) := by
        simp [hnearWidthEq, rootBudget]
      _ ≤ 64 * (1 + E g.K₀) * S_q g q := by
        simpa [u] using hnearBudget
  have hMleQH : g.M ≤ (g.Q : ℝ) * g.H := by
    exact (div_le_iff₀ hHpos).mp g.M_div_H_le_Q
  have hDpos : 0 < D g.K₀ := by
    dsimp [D]
    nlinarith [g.K₀_ge_one]
  let Z : ℝ := 2 * D g.K₀ * g.M / (g.Q : ℝ)
  have hZle : Z ≤ 2 * D g.K₀ * g.H := by
    dsimp [Z]
    apply (div_le_iff₀ hQpos).2
    calc
      2 * D g.K₀ * g.M ≤ 2 * D g.K₀ * ((g.Q : ℝ) * g.H) :=
        mul_le_mul_of_nonneg_left hMleQH (by positivity)
      _ = (2 * D g.K₀ * g.H) * (g.Q : ℝ) := by ring
  have hZge : 1 ≤ Z := by
    have hMdivQ : 1 ≤ g.M / (g.Q : ℝ) :=
      (le_div_iff₀ hQpos).2 (by simpa using hparams.Q_le_M)
    have htwoD : 1 ≤ 2 * D g.K₀ := by
      dsimp [D]
      nlinarith [g.K₀_ge_one]
    have hprod := mul_le_mul_of_nonneg_left hMdivQ (by positivity : 0 ≤ 2 * D g.K₀)
    dsimp [Z]
    calc
      1 ≤ 2 * D g.K₀ := htwoD
      _ ≤ 2 * D g.K₀ * (g.M / (g.Q : ℝ)) := by simpa using hprod
      _ = 2 * D g.K₀ * g.M / (g.Q : ℝ) := by ring
  let zcoord : ℤ × ℤ → ℤ := cellTransverseCoordinate a q
  let binIndex : (ℤ × ℤ) → ℕ := fun p => cellDyadicIndex (zcoord p)
  let Jset : Finset ℕ := Pfar.image binIndex
  have hJmap : ∀ p ∈ Pfar, binIndex p ∈ Jset := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hJfloor : ∀ j ∈ Jset, (2 ^ j : ℕ) ≤ Nat.floor Z := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨p, hp, hjEq⟩
    have hpP := (Finset.mem_filter.mp hp).1
    have hnotNear := (Finset.mem_filter.mp hp).2
    have hpSlice := (hPmem p).mp hpP
    have hfarFacts := cellFarPointFacts g a q hidx p hpSlice (by
      simpa [nearPred, u, t] using hnotNear)
    have hzne := hfarFacts.2.2.2.2
    have hzBounds := cellDyadicBounds (zcoord p) hzne
    have hidxEq : cellDyadicIndex (zcoord p) = j := by
      simpa [binIndex] using hjEq
    have hscale : ((2 ^ j : ℕ) : ℝ) ≤ |(zcoord p : ℝ)| := by
      have hidxEq' : Nat.log 2 (zcoord p).natAbs = j := by
        simpa [cellDyadicIndex] using hidxEq
      simpa [cellDyadicScale, cellDyadicIndex, hidxEq'] using hzBounds.1
    have hpointBounds := cellPointCoordinateBounds g a q hidx p hpSlice
    have hzUpper : |(zcoord p : ℝ)| ≤ Z := by
      simpa [zcoord, Z] using hpointBounds.2.2.1
    have hpowZ : ((2 ^ j : ℕ) : ℝ) ≤ Z := hscale.trans hzUpper
    exact Nat.le_floor hpowZ
  have hbinBudget : ∀ j ∈ Jset,
      ((Pfar.filter fun p => binIndex p = j).card : ℝ) ≤
        24 * (1 + D g.K₀) * g.H * (2 ^ j : ℕ) / t := by
    intro j hj
    let A : ℝ := (2 ^ j : ℕ)
    let Pbin : Finset (ℤ × ℤ) := Pfar.filter fun p => binIndex p = j
    let Cbin : Finset ℤ := Pbin.image (cellLinearCoordinate a q)
    have hApos : 0 < A := by dsimp [A]; positivity
    have hAjZ : ((2 ^ j : ℕ) : ℝ) ≤ Z := by
      calc
        ((2 ^ j : ℕ) : ℝ) ≤ (Nat.floor Z : ℝ) := by exact_mod_cast hJfloor j hj
        _ ≤ Z := Nat.floor_le (by linarith [hZge])
    have hAupper : A ≤ 2 * D g.K₀ * g.H := by
      dsimp [A]
      exact hAjZ.trans hZle
    have hbin : ∀ p ∈ Pbin,
        A ≤ |(zcoord p : ℝ)| ∧ |(zcoord p : ℝ)| < 2 * A := by
      intro p hp
      have hpFar := (Finset.mem_filter.mp hp).1
      have hjp := (Finset.mem_filter.mp hp).2
      have hpP := (Finset.mem_filter.mp hpFar).1
      have hnotNear := (Finset.mem_filter.mp hpFar).2
      have hpSlice := (hPmem p).mp hpP
      have hfarFacts := cellFarPointFacts g a q hidx p hpSlice (by
        simpa [nearPred, u, t] using hnotNear)
      have hd := cellDyadicBounds (zcoord p) hfarFacts.2.2.2.2
      have hidxEq : cellDyadicIndex (zcoord p) = j := by
        simpa [binIndex] using hjp
      have hidxEq' : Nat.log 2 (zcoord p).natAbs = j := by
        simpa [cellDyadicIndex] using hidxEq
      constructor
      · simpa [A, cellDyadicScale, cellDyadicIndex, hidxEq'] using hd.1
      · simpa [A, cellDyadicScale, cellDyadicIndex, hidxEq'] using hd.2
    have hA2over : (1 / 2 : ℝ) < A ^ 2 / t := by
      rcases Finset.mem_image.mp hj with ⟨p₀, hp₀, hjEq⟩
      have hnotNear := (Finset.mem_filter.mp hp₀).2
      have hpSlice := (hPmem p₀).mp ((Finset.mem_filter.mp hp₀).1)
      have hfarFacts := cellFarPointFacts g a q hidx p₀ hpSlice (by
        simpa [nearPred, u, t] using hnotNear)
      have hzFacts := cellDyadicBounds (zcoord p₀) hfarFacts.2.2.2.2
      have hdeltaLarge : 4 * t <
          (cellLinearCoordinate a q p₀ : ℝ) ^ 2 - t ^ 2 := by
        have h8uh : 0 ≤ 8 * u * g.H := by positivity
        linarith [hfarFacts.2.1]
      have hzSquareLarge : 2 * t < (zcoord p₀ : ℝ) ^ 2 := by
        have h := hfarFacts.2.2.1
        linarith [hdeltaLarge]
      have hidxEq : cellDyadicIndex (zcoord p₀) = j := by
        simpa [binIndex] using hjEq
      have hidxEq' : Nat.log 2 (zcoord p₀).natAbs = j := by
        simpa [cellDyadicIndex] using hidxEq
      have hbinAbs : |(zcoord p₀ : ℝ)| < 2 * A := by
        simpa [A, cellDyadicScale, cellDyadicIndex, hidxEq'] using hzFacts.2
      have hzSquareSmall : (zcoord p₀ : ℝ) ^ 2 < 4 * A ^ 2 := by
        have hsq := (sq_lt_sq₀ (abs_nonneg (zcoord p₀ : ℝ))
          (by positivity : 0 ≤ 2 * A)).2 hbinAbs
        calc
          (zcoord p₀ : ℝ) ^ 2 < (2 * A) ^ 2 := by simpa [sq_abs] using hsq
          _ = 4 * A ^ 2 := by ring
      apply (lt_div_iff₀ hTpos).2
      dsimp [A]
      nlinarith [hzSquareLarge, hzSquareSmall]
    have hCbinInterval : ∀ c ∈ Cbin,
        (c : ℝ) ∈ Set.Ioc t (t + 4 * A ^ 2 / t) := by
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨p, hp, rfl⟩
      have hpFar := (Finset.mem_filter.mp hp).1
      have hpP := (Finset.mem_filter.mp hpFar).1
      have hnotNear := (Finset.mem_filter.mp hpFar).2
      have hpSlice := (hPmem p).mp hpP
      have hpointFacts := cellFarPointFacts g a q hidx p hpSlice (by
        simpa [nearPred, u, t] using hnotNear)
      have hcgt : t < (cellLinearCoordinate a q p : ℝ) := by
        linarith [hpointFacts.1]
      have hbinp : A ≤ |(zcoord p : ℝ)| ∧
          |(zcoord p : ℝ)| < 2 * A := hbin p hp
      have hzSquareSmall : (zcoord p : ℝ) ^ 2 < 4 * A ^ 2 := by
        have hsq := (sq_lt_sq₀ (abs_nonneg (zcoord p : ℝ))
          (by positivity : 0 ≤ 2 * A)).2 hbinp.2
        calc
          (zcoord p : ℝ) ^ 2 < (2 * A) ^ 2 := by simpa [sq_abs] using hsq
          _ = 4 * A ^ 2 := by ring
      have hquotUpper := div_lt_div_of_pos_right hzSquareSmall hTpos
      have hcoordUpper : (cellLinearCoordinate a q p : ℝ) - t ≤
          (zcoord p : ℝ) ^ 2 / t := by
        simpa [zcoord] using hpointFacts.2.2.2.1
      have hdiffUpper : (cellLinearCoordinate a q p : ℝ) - t <
          4 * A ^ 2 / t := lt_of_le_of_lt hcoordUpper hquotUpper
      exact ⟨hcgt, by linarith⟩
    have hCbinCount : (Cbin.card : ℝ) ≤ 6 * A ^ 2 / t := by
      have hcount := integerIocCount Cbin t (4 * A ^ 2 / t)
        (by positivity) hCbinInterval
      calc
        (Cbin.card : ℝ) ≤ 4 * A ^ 2 / t + 1 := hcount
        _ ≤ 6 * A ^ 2 / t := by
          have hscale : 1 ≤ 2 * (A ^ 2 / t) := by linarith [hA2over]
          calc
            4 * A ^ 2 / t + 1 = 4 * (A ^ 2 / t) + 1 := by ring
            _ ≤ 4 * (A ^ 2 / t) + 2 * (A ^ 2 / t) := by linarith [hscale]
            _ = 6 * A ^ 2 / t := by ring
    have hbinMap : ∀ p ∈ Pbin, cellLinearCoordinate a q p ∈ Cbin := by
      intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hbinFiber : ∀ c ∈ Cbin,
        ((Pbin.filter fun p => cellLinearCoordinate a q p = c).card : ℝ) ≤
          4 * (1 + D g.K₀) * g.H / A := by
      intro c hc
      let F := Pbin.filter fun p => cellLinearCoordinate a q p = c
      have hFline : ∀ p ∈ F, p ∈ cellLinearSliceOnLine g a q c := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpbin, hEq⟩
        have hpFar := (Finset.mem_filter.mp hpbin).1
        have hpP := (Finset.mem_filter.mp hpFar).1
        change p ∈ cellLinearSlice g a q ∧
          cellLinearCoordinate a q p = c
        exact ⟨(hPmem p).mp hpP, hEq⟩
      have hFbin : ∀ p ∈ F,
          A ≤ |(zcoord p : ℝ)| ∧ |(zcoord p : ℝ)| < 2 * A := by
        intro p hp
        have hpbin : p ∈ Pbin := (Finset.mem_filter.mp hp).1
        exact hbin p hpbin
      have hcount := cellLineDyadicFiberCount g a q hidx c F hFline
        A hApos hFbin hAupper
      simpa [F] using hcount
    have hweighted := card_le_fiber_bound Pbin Cbin
      (cellLinearCoordinate a q) hbinMap
      (4 * (1 + D g.K₀) * g.H / A) hbinFiber
    have hbinTotal : (Pbin.card : ℝ) ≤
        24 * (1 + D g.K₀) * g.H * A / t := by
      calc
        (Pbin.card : ℝ) ≤ (Cbin.card : ℝ) *
            (4 * (1 + D g.K₀) * g.H / A) := hweighted
        _ ≤ (6 * A ^ 2 / t) *
            (4 * (1 + D g.K₀) * g.H / A) :=
          mul_le_mul_of_nonneg_right hCbinCount (by positivity)
        _ = 24 * (1 + D g.K₀) * g.H * A / t := by
          field_simp [ne_of_gt hApos, ne_of_gt hTpos]
          ring
    simpa [Pbin, A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbinTotal
  have hfarWeighted := card_le_weighted_fiber_bound Pfar Jset binIndex hJmap
    (fun j => 24 * (1 + D g.K₀) * g.H * (2 ^ j : ℕ) / t) hbinBudget
  have hdyadic := dyadicPowerSumBound Jset Z hZge hJfloor
  have hsumFactor :
      (∑ j ∈ Jset,
        24 * (1 + D g.K₀) * g.H * (2 ^ j : ℕ) / t) =
        (24 * (1 + D g.K₀) * g.H / t) *
          (∑ j ∈ Jset, (2 ^ j : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hfarTotal : (Pfar.card : ℝ) ≤
      48 * (1 + D g.K₀) * g.H * Z / t := by
    calc
      (Pfar.card : ℝ) ≤
          ∑ j ∈ Jset,
            24 * (1 + D g.K₀) * g.H * (2 ^ j : ℕ) / t := hfarWeighted
      _ = (24 * (1 + D g.K₀) * g.H / t) *
          (∑ j ∈ Jset, (2 ^ j : ℕ) : ℝ) := hsumFactor
      _ ≤ (24 * (1 + D g.K₀) * g.H / t) * (2 * Z) :=
        mul_le_mul_of_nonneg_left hdyadic (by positivity)
      _ = 48 * (1 + D g.K₀) * g.H * Z / t := by ring
  have hfarRewrite : 48 * (1 + D g.K₀) * g.H * Z / t =
      48 * D g.K₀ * (1 + D g.K₀) * g.H * g.M /
        ((g.Q : ℝ) * Real.sqrt (u * g.X)) := by
    dsimp [Z, t]
    field_simp [ne_of_gt hQpos, ne_of_gt hTpos]
  have huLowerX : g.X * (q : ℝ) ^ 2 / (8 * g.M ^ 2) ≤ u := by
    have hrew : g.r * (q : ℝ) ^ 2 / 8 =
        g.X * (q : ℝ) ^ 2 / (8 * g.M ^ 2) := by
      dsimp [HyperbolaGeometricData.r]
      field_simp [ne_of_gt hMpos]
    rw [hrew] at huLower
    exact huLower
  have hdenRootLower :
      g.X * (q : ℝ) / (Real.sqrt 8 * g.M) ≤ Real.sqrt (u * g.X) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (mul_nonneg huPos.le (le_of_lt hXpos))]
    have hleftSq :
        (g.X * (q : ℝ) / (Real.sqrt 8 * g.M)) ^ 2 =
          g.X ^ 2 * (q : ℝ) ^ 2 / (8 * g.M ^ 2) := by
      have hsqrt8sq : Real.sqrt (8 : ℝ) ^ 2 = 8 :=
        Real.sq_sqrt (by norm_num : 0 ≤ (8 : ℝ))
      have hdenSq : (Real.sqrt 8 * g.M) ^ 2 = 8 * g.M ^ 2 := by
        rw [mul_pow, hsqrt8sq]
      rw [div_pow, hdenSq, mul_pow]
    rw [hleftSq]
    have hmul := mul_le_mul_of_nonneg_right huLowerX (le_of_lt hXpos)
    convert hmul using 1
    ring
  have hroot8 : Real.sqrt (8 : ℝ) ≤ 3 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : 0 ≤ (3 : ℝ))).mp
    rw [Real.sq_sqrt (by norm_num : 0 ≤ (8 : ℝ))]
    norm_num
  have hcrossLo : g.X * (q : ℝ) ≤
      Real.sqrt 8 * g.M * Real.sqrt (u * g.X) := by
    have hmul := mul_le_mul_of_nonneg_right hdenRootLower
      (mul_nonneg (Real.sqrt_nonneg 8) (le_of_lt hMpos))
    have hcancel :
        g.X * (q : ℝ) / (Real.sqrt 8 * g.M) *
            (Real.sqrt 8 * g.M) = g.X * (q : ℝ) := by
      field_simp [ne_of_gt hMpos,
        ne_of_gt (Real.sqrt_pos.mpr (by norm_num : 0 < (8 : ℝ)))]
    rw [hcancel] at hmul
    calc
      g.X * (q : ℝ) ≤ Real.sqrt (u * g.X) * (Real.sqrt 8 * g.M) := hmul
      _ = Real.sqrt 8 * g.M * Real.sqrt (u * g.X) := by ring
  have hcross : g.X * (q : ℝ) ≤
      3 * g.M * Real.sqrt (u * g.X) := by
    calc
      g.X * (q : ℝ) ≤
          Real.sqrt 8 * g.M * Real.sqrt (u * g.X) := hcrossLo
      _ ≤ 3 * g.M * Real.sqrt (u * g.X) := by
        calc
          Real.sqrt 8 * g.M * Real.sqrt (u * g.X) ≤
              (3 * g.M) * Real.sqrt (u * g.X) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hroot8 (le_of_lt hMpos))
              (Real.sqrt_nonneg _)
          _ = 3 * g.M * Real.sqrt (u * g.X) := by ring
  have hratioS :
      g.H * g.M / ((g.Q : ℝ) * Real.sqrt (u * g.X)) ≤ 3 * S_q g q := by
    rw [S_q, ← mul_div_assoc]
    have hmain : g.H * g.M / ((g.Q : ℝ) * Real.sqrt (u * g.X)) ≤
        (3 * (g.H * g.M ^ 2)) /
          (g.X * ((g.Q : ℝ) * (q : ℝ))) := by
      apply (div_le_div_iff₀
        (mul_pos hQpos (Real.sqrt_pos.mpr (mul_pos huPos hXpos)))
        (mul_pos hXpos (mul_pos hQpos hqpos))).2
      field_simp [ne_of_gt hHpos, ne_of_gt hMpos, ne_of_gt hQpos,
        ne_of_gt hqpos, ne_of_gt (Real.sqrt_pos.mpr (mul_pos huPos hXpos))]
      have hcross' : g.X * (q : ℝ) ≤
          3 * g.M * Real.sqrt (g.X * u) := by
        simpa [mul_comm] using hcross
      linarith [hcross']
    simpa [mul_assoc] using hmain
  have hfarBudget : (Pfar.card : ℝ) ≤
      144 * D g.K₀ * (1 + D g.K₀) * S_q g q := by
    rw [hfarRewrite] at hfarTotal
    calc
      (Pfar.card : ℝ) ≤
          48 * D g.K₀ * (1 + D g.K₀) * g.H * g.M /
            ((g.Q : ℝ) * Real.sqrt (u * g.X)) := hfarTotal
      _ ≤ (48 * D g.K₀ * (1 + D g.K₀)) *
          (3 * S_q g q) := by
        have hcoeff : 0 ≤ 48 * D g.K₀ * (1 + D g.K₀) := by positivity
        have hscaled := mul_le_mul_of_nonneg_left hratioS hcoeff
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
      _ = 144 * D g.K₀ * (1 + D g.K₀) * S_q g q := by ring
  have hPcard : (P.card : ℝ) ≤
      (64 * (1 + E g.K₀) +
        144 * D g.K₀ * (1 + D g.K₀)) * S_q g q := by
    rw [hsplitReal]
    have hsum := add_le_add hnearTotal hfarBudget
    calc
      (Pnear.card : ℝ) + (Pfar.card : ℝ) ≤
          64 * (1 + E g.K₀) * S_q g q +
            144 * D g.K₀ * (1 + D g.K₀) * S_q g q := hsum
      _ = (64 * (1 + E g.K₀) +
          144 * D g.K₀ * (1 + D g.K₀)) * S_q g q := by ring
  have hncard : (cellLinearSlice g a q).ncard = P.card := by
    rw [Set.ncard_eq_toFinset_card _ hSliceFinite]
  rw [hncard]
  simpa [C_point] using hPcard

end FractionalPrimes.Literature.Hyperbola
