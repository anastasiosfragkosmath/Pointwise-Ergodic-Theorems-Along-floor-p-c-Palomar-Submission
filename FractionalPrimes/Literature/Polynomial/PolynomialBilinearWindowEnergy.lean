module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearUnweightedEnergy

/-!
# Averaging bilinear energy over short windows

This file formalizes blueprint item `lbi:window-energy`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The integer length `R = ceil (4r)` of the short bilinear windows. -/
def bilinearWindowRadius (r : ℝ) : ℕ := Nat.ceil (4 * r)

/-- The integer centers in the exact source interval `[M/2,2M]`. -/
def bilinearWindowCenters (M : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor (2 * M))).filter (fun u => M / 2 ≤ (u : ℝ))

/-- The exact source window `(u,u+R] ∩ (M,2M] ∩ ℕ_{>0}`. -/
def bilinearWindow (M r : ℝ) (u : ℕ) : Finset ℕ :=
  (bilinearRightSet M).filter
    (fun m => u < m ∧ m ≤ u + bilinearWindowRadius r)

/-- The squared correlation energy in one short window. -/
def bilinearWindowSquaredEnergy (M r : ℝ) (C : ℕ → ℕ → ℂ) (u : ℕ) : ℝ :=
  ∑ m ∈ bilinearWindow M r u, ∑ m' ∈ bilinearWindow M r u, ‖C m m'‖ ^ 2

@[simp]
theorem mem_bilinearWindowCenters (M : ℝ) (u : ℕ) :
    u ∈ bilinearWindowCenters M ↔
      1 ≤ u ∧ M / 2 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * M := by
  simp only [bilinearWindowCenters, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hu, hufloor⟩, hlower⟩
    exact ⟨hu, hlower,
      (Nat.le_floor_iff' (Nat.ne_of_gt hu)).mp hufloor⟩
  · rintro ⟨hu, hlower, hupper⟩
    exact ⟨⟨hu, Nat.le_floor hupper⟩, hlower⟩

@[simp]
theorem mem_bilinearWindow (M r : ℝ) (u m : ℕ) :
    m ∈ bilinearWindow M r u ↔
      m ∈ bilinearRightSet M ∧ u < m ∧
        m ≤ u + bilinearWindowRadius r := by
  simp [bilinearWindow]

private theorem bilinearWindowRadius_bounds
    (r : ℝ) (hr : 1 ≤ r) :
    4 * r ≤ (bilinearWindowRadius r : ℝ) ∧
      (bilinearWindowRadius r : ℝ) ≤ 5 * r := by
  constructor
  · exact Nat.le_ceil (4 * r)
  · have hpos : 0 ≤ 4 * r := by positivity
    have hlt : (bilinearWindowRadius r : ℝ) < 4 * r + 1 := by
      exact Nat.ceil_lt_add_one hpos
    dsimp [bilinearWindowRadius] at hlt ⊢
    linarith

private theorem bilinearWindow_card_le
    (M r : ℝ) (u : ℕ) :
    (bilinearWindow M r u).card ≤ bilinearWindowRadius r := by
  classical
  have hsub : bilinearWindow M r u ⊆
      Finset.Ioc u (u + bilinearWindowRadius r) := by
    intro m hm
    exact Finset.mem_Ioc.mpr ((mem_bilinearWindow M r u m).mp hm |>.2)
  calc
    (bilinearWindow M r u).card ≤
        (Finset.Ioc u (u + bilinearWindowRadius r)).card :=
      Finset.card_le_card hsub
    _ = bilinearWindowRadius r := by simp

private theorem real_nat_min_near_left
    (m m' : ℕ) (r : ℝ)
    (hband : |(m : ℝ) - (m' : ℝ)| ≤ 2 * r) :
    (m : ℝ) ≤ (min m m' : ℕ) + 2 * r := by
  have hr0 : 0 ≤ r := by
    nlinarith [abs_nonneg ((m : ℝ) - (m' : ℝ))]
  by_cases hmm' : m ≤ m'
  · rw [min_eq_left hmm']
    norm_num
    linarith
  · have hm'm : m' ≤ m := Nat.le_of_not_ge hmm'
    have hcast : (m' : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm'm
    have hnonneg : 0 ≤ (m : ℝ) - (m' : ℝ) := by linarith
    rw [abs_of_nonneg hnonneg] at hband
    rw [min_eq_right hm'm]
    norm_num at hband ⊢
    linarith

private theorem real_nat_min_near_right
    (m m' : ℕ) (r : ℝ)
    (hband : |(m : ℝ) - (m' : ℝ)| ≤ 2 * r) :
    (m' : ℝ) ≤ (min m m' : ℕ) + 2 * r := by
  have hr0 : 0 ≤ r := by
    nlinarith [abs_nonneg ((m : ℝ) - (m' : ℝ))]
  by_cases hmm' : m ≤ m'
  · have hcast : (m : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hmm'
    have hnonpos : (m : ℝ) - (m' : ℝ) ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos] at hband
    rw [min_eq_left hmm']
    norm_num at hband ⊢
    linarith
  · have hm'm : m' ≤ m := Nat.le_of_not_ge hmm'
    rw [min_eq_right hm'm]
    norm_num
    linarith

/-- Every pair in the source `2r` band occurs in at least `r/4` of the
short windows.  The proof injects `1 ≤ k ≤ ceil(r/4)` into the admissible
centers by `k ↦ min(m,m')-k`. -/
private theorem bilinearWindow_cover_count
    (M r : ℝ) (hM : 2 ≤ M) (hr : 8 ≤ r) (hrM : r ≤ M)
    (m m' : ℕ) (hm : m ∈ bilinearRightSet M)
    (hm' : m' ∈ bilinearRightSet M)
    (hband : |(m : ℝ) - (m' : ℝ)| ≤ 2 * r) :
    r / 4 ≤ (((bilinearWindowCenters M).filter (fun u =>
      m ∈ bilinearWindow M r u ∧ m' ∈ bilinearWindow M r u)).card : ℝ) := by
  classical
  let K : ℕ := Nat.ceil (r / 4)
  let D : Finset ℕ := Finset.Icc 1 K
  let f : ℕ → ℕ := fun k => min m m' - k
  have hr0 : 0 ≤ r := by linarith
  have hKlower : r / 4 ≤ (K : ℝ) := by
    exact Nat.le_ceil (r / 4)
  have hKupper : (K : ℝ) < r / 4 + 1 := by
    exact Nat.ceil_lt_add_one (by positivity : 0 ≤ r / 4)
  have hmData := (mem_bilinearRightSet M m).mp hm
  have hm'Data := (mem_bilinearRightSet M m').mp hm'
  have hKltm : K < m := by
    exact_mod_cast (show (K : ℝ) < (m : ℝ) by linarith)
  have hKltm' : K < m' := by
    exact_mod_cast (show (K : ℝ) < (m' : ℝ) by linarith)
  have hKltmin : K < min m m' := lt_min hKltm hKltm'
  have hR := bilinearWindowRadius_bounds r (by linarith)
  have hmap : Set.MapsTo f (D : Set ℕ)
      (((bilinearWindowCenters M).filter (fun u =>
        m ∈ bilinearWindow M r u ∧ m' ∈ bilinearWindow M r u)) : Set ℕ) := by
    intro k hk
    have hkData : 1 ≤ k ∧ k ≤ K := Finset.mem_Icc.mp hk
    have hkmin : k ≤ min m m' := le_trans hkData.2 hKltmin.le
    have hkltmin : k < min m m' := lt_of_le_of_lt hkData.2 hKltmin
    have hfcast : (f k : ℝ) = (min m m' : ℕ) - (k : ℝ) := by
      dsimp [f]
      rw [Nat.cast_sub hkmin]
    have hkcast : (k : ℝ) < r / 4 + 1 := by
      exact (show (k : ℝ) ≤ (K : ℝ) by exact_mod_cast hkData.2) |>.trans_lt hKupper
    have hminM : M < (min m m' : ℕ) := by
      rw [Nat.cast_min]
      exact lt_min hmData.2.1 hm'Data.2.1
    have hflower : M / 2 ≤ (f k : ℝ) := by
      rw [hfcast]
      linarith
    have hfpos : 1 ≤ f k := by
      dsimp [f]
      omega
    have hfupper : (f k : ℝ) ≤ 2 * M := by
      have hfle : f k ≤ m := by
        exact (Nat.sub_le _ _).trans (min_le_left _ _)
      exact (show (f k : ℝ) ≤ (m : ℝ) by exact_mod_cast hfle) |>.trans hmData.2.2
    have hfcenter : f k ∈ bilinearWindowCenters M :=
      (mem_bilinearWindowCenters M (f k)).mpr ⟨hfpos, hflower, hfupper⟩
    have hmnear := real_nat_min_near_left m m' r hband
    have hm'near := real_nat_min_near_right m m' r hband
    have hmargin : (k : ℝ) + 2 * r ≤ (bilinearWindowRadius r : ℝ) := by
      linarith [hR.1]
    have hminsplit : (min m m' : ℕ) = (f k : ℝ) + (k : ℝ) := by
      linarith [hfcast]
    have hmupperReal : (m : ℝ) ≤ (f k : ℝ) + bilinearWindowRadius r := by
      calc
        (m : ℝ) ≤ (min m m' : ℕ) + 2 * r := hmnear
        _ = (f k : ℝ) + (k : ℝ) + 2 * r := by rw [hminsplit]
        _ ≤ (f k : ℝ) + bilinearWindowRadius r := by norm_num; linarith
    have hm'upperReal : (m' : ℝ) ≤ (f k : ℝ) + bilinearWindowRadius r := by
      calc
        (m' : ℝ) ≤ (min m m' : ℕ) + 2 * r := hm'near
        _ = (f k : ℝ) + (k : ℝ) + 2 * r := by rw [hminsplit]
        _ ≤ (f k : ℝ) + bilinearWindowRadius r := by norm_num; linarith
    have hflt_m : f k < m := by
      exact (Nat.sub_lt (by omega) hkData.1).trans_le (min_le_left _ _)
    have hflt_m' : f k < m' := by
      exact (Nat.sub_lt (by omega) hkData.1).trans_le (min_le_right _ _)
    have hmupper : m ≤ f k + bilinearWindowRadius r := by
      exact_mod_cast hmupperReal
    have hm'upper : m' ≤ f k + bilinearWindowRadius r := by
      exact_mod_cast hm'upperReal
    change f k ∈ (bilinearWindowCenters M).filter (fun u =>
      m ∈ bilinearWindow M r u ∧ m' ∈ bilinearWindow M r u)
    exact Finset.mem_filter.mpr ⟨hfcenter,
      (mem_bilinearWindow M r (f k) m).mpr ⟨hm, hflt_m, hmupper⟩,
      (mem_bilinearWindow M r (f k) m').mpr ⟨hm', hflt_m', hm'upper⟩⟩
  have hinj : (D : Set ℕ).InjOn f := by
    intro a ha b hb hab
    have haData : 1 ≤ a ∧ a ≤ K := Finset.mem_Icc.mp ha
    have hbData : 1 ≤ b ∧ b ≤ K := Finset.mem_Icc.mp hb
    exact (tsub_right_inj
      (haData.2.trans hKltmin.le) (hbData.2.trans hKltmin.le)).mp hab
  have hcardNat : D.card ≤
      ((bilinearWindowCenters M).filter (fun u =>
        m ∈ bilinearWindow M r u ∧ m' ∈ bilinearWindow M r u)).card :=
    Finset.card_le_card_of_injOn f hmap hinj
  have hDcard : D.card = K := by simp [D]
  calc
    r / 4 ≤ (K : ℝ) := hKlower
    _ = (D.card : ℝ) := by rw [hDcard]
    _ ≤ (((bilinearWindowCenters M).filter (fun u =>
        m ∈ bilinearWindow M r u ∧ m' ∈ bilinearWindow M r u)).card : ℝ) := by
      exact_mod_cast hcardNat

private theorem many_large_window_energies
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (F : ι → ℝ) (M r s ρ : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hs : 0 < s) (hρ : 0 < ρ)
    (hcard : (S.card : ℝ) ≤ 3 * M)
    (hupper : ∀ i ∈ S, F i ≤ 100 * r ^ 2 * s ^ 2)
    (hsum : ρ ^ 4 * M * r ^ 2 * s ^ 2 / 20 ≤ ∑ i ∈ S, F i) :
    ρ ^ 4 * M / 4000 ≤
      ((S.filter (fun i => ρ ^ 4 * r ^ 2 * s ^ 2 / 120 ≤ F i)).card : ℝ) := by
  classical
  let threshold : ℝ := ρ ^ 4 * r ^ 2 * s ^ 2 / 120
  let G : Finset ι := S.filter (fun i => threshold ≤ F i)
  let B : Finset ι := S.filter (fun i => F i < threshold)
  let upper : ℝ := 100 * r ^ 2 * s ^ 2
  have hthreshold0 : 0 ≤ threshold := by
    dsimp [threshold]
    positivity
  have hupperPos : 0 < upper := by
    dsimp [upper]
    positivity
  have hBcard : (B.card : ℝ) ≤ 3 * M := by
    calc
      (B.card : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ 3 * M := hcard
  have hBsum : (∑ i ∈ B, F i) ≤ ρ ^ 4 * M * r ^ 2 * s ^ 2 / 40 := by
    calc
      (∑ i ∈ B, F i) ≤ ∑ _i ∈ B, threshold := by
        apply Finset.sum_le_sum
        intro i hi
        exact ((Finset.mem_filter.mp hi).2).le
      _ = (B.card : ℝ) * threshold := by simp [Finset.sum_const]
      _ ≤ (3 * M) * threshold :=
        mul_le_mul_of_nonneg_right hBcard hthreshold0
      _ = ρ ^ 4 * M * r ^ 2 * s ^ 2 / 40 := by
        dsimp [threshold]
        ring
  have hsplit : (∑ i ∈ S, F i) = (∑ i ∈ G, F i) + ∑ i ∈ B, F i := by
    simpa only [G, B, threshold, not_le] using
      (Finset.sum_filter_add_sum_filter_not S
        (fun i => threshold ≤ F i) F).symm
  have hGsumLower : ρ ^ 4 * M * r ^ 2 * s ^ 2 / 40 ≤ ∑ i ∈ G, F i := by
    rw [hsplit] at hsum
    linarith
  have hGsumUpper : (∑ i ∈ G, F i) ≤ (G.card : ℝ) * upper := by
    calc
      (∑ i ∈ G, F i) ≤ ∑ _i ∈ G, upper := by
        apply Finset.sum_le_sum
        intro i hi
        exact hupper i (Finset.mem_filter.mp hi).1
      _ = (G.card : ℝ) * upper := by simp [Finset.sum_const]
  have htargetMul :
      (ρ ^ 4 * M / 4000) * upper = ρ ^ 4 * M * r ^ 2 * s ^ 2 / 40 := by
    dsimp [upper]
    ring
  have hmul : (ρ ^ 4 * M / 4000) * upper ≤ (G.card : ℝ) * upper := by
    rw [htargetMul]
    exact hGsumLower.trans hGsumUpper
  have hmul' : upper * (ρ ^ 4 * M / 4000) ≤ upper * (G.card : ℝ) := by
    simpa [mul_comm] using hmul
  have hcount : ρ ^ 4 * M / 4000 ≤ (G.card : ℝ) :=
    (mul_le_mul_iff_right₀ hupperPos).mp hmul'
  simpa [G, threshold] using hcount

private theorem many_large_pairs_of_window_energy
    (J : Finset ℕ) (C : ℕ → ℕ → ℂ) (r s ρ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hρ : 0 < ρ)
    (hcard : (J.card : ℝ) ≤ 5 * r)
    (hbound : ∀ m ∈ J, ∀ m' ∈ J, ‖C m m'‖ ≤ 2 * s)
    (henergy : ρ ^ 4 * r ^ 2 * s ^ 2 / 120 ≤
      ∑ m ∈ J, ∑ m' ∈ J, ‖C m m'‖ ^ 2) :
    ρ ^ 4 * r ^ 2 / 800 ≤
      (((J.product J).filter (fun p =>
        ρ ^ 2 * s / 100 ≤ ‖C p.1 p.2‖)).card : ℝ) := by
  classical
  let P : Finset (ℕ × ℕ) := J.product J
  let e : ℕ × ℕ → ℝ := fun p => ‖C p.1 p.2‖ ^ 2
  let threshold : ℝ := ρ ^ 2 * s / 100
  let G : Finset (ℕ × ℕ) := P.filter (fun p => threshold ≤ ‖C p.1 p.2‖)
  let B : Finset (ℕ × ℕ) := P.filter (fun p => ‖C p.1 p.2‖ < threshold)
  let upper : ℝ := 4 * s ^ 2
  have hthresholdPos : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hupperPos : 0 < upper := by
    dsimp [upper]
    positivity
  have hPcard : (P.card : ℝ) ≤ 25 * r ^ 2 := by
    have hcard0 : 0 ≤ (J.card : ℝ) := by positivity
    have h5r0 : 0 ≤ 5 * r := by positivity
    calc
      (P.card : ℝ) = (J.card : ℝ) * (J.card : ℝ) := by
        simp [P]
      _ ≤ (5 * r) * (5 * r) :=
        mul_le_mul hcard hcard hcard0 h5r0
      _ = 25 * r ^ 2 := by ring
  have hBsum : (∑ p ∈ B, e p) ≤ ρ ^ 4 * r ^ 2 * s ^ 2 / 400 := by
    have hBcard : (B.card : ℝ) ≤ 25 * r ^ 2 := by
      calc
        (B.card : ℝ) ≤ (P.card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ ≤ 25 * r ^ 2 := hPcard
    have hthresholdSq0 : 0 ≤ threshold ^ 2 := sq_nonneg threshold
    calc
      (∑ p ∈ B, e p) ≤ ∑ _p ∈ B, threshold ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        have hlt := (Finset.mem_filter.mp hp).2
        exact (sq_le_sq₀ (norm_nonneg _) hthresholdPos.le).2 hlt.le
      _ = (B.card : ℝ) * threshold ^ 2 := by simp [Finset.sum_const]
      _ ≤ (25 * r ^ 2) * threshold ^ 2 :=
        mul_le_mul_of_nonneg_right hBcard hthresholdSq0
      _ = ρ ^ 4 * r ^ 2 * s ^ 2 / 400 := by
        dsimp [threshold]
        ring
  have hsumProduct : (∑ p ∈ P, e p) =
      ∑ m ∈ J, ∑ m' ∈ J, ‖C m m'‖ ^ 2 := by
    exact Finset.sum_product' J J (fun m m' => ‖C m m'‖ ^ 2)
  have hsplit : (∑ p ∈ P, e p) = (∑ p ∈ G, e p) + ∑ p ∈ B, e p := by
    simpa only [G, B, P, threshold, e, not_le] using
      (Finset.sum_filter_add_sum_filter_not P
        (fun p => threshold ≤ ‖C p.1 p.2‖) e).symm
  have hGsumLower : ρ ^ 4 * r ^ 2 * s ^ 2 / 200 ≤ ∑ p ∈ G, e p := by
    have henergyP : ρ ^ 4 * r ^ 2 * s ^ 2 / 120 ≤ ∑ p ∈ P, e p := by
      rw [hsumProduct]
      exact henergy
    rw [hsplit] at henergyP
    have hscale0 : 0 ≤ ρ ^ 4 * r ^ 2 * s ^ 2 := by positivity
    linarith
  have hGsumUpper : (∑ p ∈ G, e p) ≤ (G.card : ℝ) * upper := by
    calc
      (∑ p ∈ G, e p) ≤ ∑ _p ∈ G, upper := by
        apply Finset.sum_le_sum
        intro p hp
        have hpP := (Finset.mem_filter.mp hp).1
        have hpJ := Finset.mem_product.mp hpP
        have hnorm := hbound p.1 hpJ.1 p.2 hpJ.2
        have hs2 : 0 ≤ 2 * s := by positivity
        have hsq : ‖C p.1 p.2‖ ^ 2 ≤ (2 * s) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hs2).2 hnorm
        dsimp [e, upper]
        nlinarith
      _ = (G.card : ℝ) * upper := by simp [Finset.sum_const]
  have htargetMul :
      (ρ ^ 4 * r ^ 2 / 800) * upper = ρ ^ 4 * r ^ 2 * s ^ 2 / 200 := by
    dsimp [upper]
    ring
  have hmul : (ρ ^ 4 * r ^ 2 / 800) * upper ≤ (G.card : ℝ) * upper := by
    rw [htargetMul]
    exact hGsumLower.trans hGsumUpper
  have hmul' : upper * (ρ ^ 4 * r ^ 2 / 800) ≤ upper * (G.card : ℝ) := by
    simpa [mul_comm] using hmul
  have hcount : ρ ^ 4 * r ^ 2 / 800 ≤ (G.card : ℝ) :=
    (mul_le_mul_iff_right₀ hupperPos).mp hmul'
  simpa [G, P, threshold] using hcount

private theorem bilinearWindowCenters_card_le
    (M : ℝ) (hM : 0 < M) :
    ((bilinearWindowCenters M).card : ℝ) ≤ 3 * M := by
  have hsub : bilinearWindowCenters M ⊆
      Finset.Icc 1 (Nat.floor (2 * M)) := Finset.filter_subset _ _
  have hcardNat : (bilinearWindowCenters M).card ≤
      (Finset.Icc 1 (Nat.floor (2 * M))).card := Finset.card_le_card hsub
  calc
    ((bilinearWindowCenters M).card : ℝ) ≤
        ((Finset.Icc 1 (Nat.floor (2 * M))).card : ℝ) := by
      exact_mod_cast hcardNat
    _ = (Nat.floor (2 * M) : ℝ) := by simp [Nat.card_Icc]
    _ ≤ 2 * M := Nat.floor_le (by positivity)
    _ ≤ 3 * M := by linarith

private theorem bilinearWindow_energy_upper
    (M r s : ℝ) (hr : 1 ≤ r) (hs : 0 < s)
    (C : ℕ → ℕ → ℂ)
    (hbound : ∀ m ∈ bilinearRightSet M, ∀ m' ∈ bilinearRightSet M,
      ‖C m m'‖ ≤ 2 * s)
    (u : ℕ) :
    bilinearWindowSquaredEnergy M r C u ≤ 100 * r ^ 2 * s ^ 2 := by
  classical
  let J := bilinearWindow M r u
  have hJcardNat : J.card ≤ bilinearWindowRadius r :=
    bilinearWindow_card_le M r u
  have hJcard : (J.card : ℝ) ≤ 5 * r := by
    calc
      (J.card : ℝ) ≤ (bilinearWindowRadius r : ℝ) := by
        exact_mod_cast hJcardNat
      _ ≤ 5 * r := (bilinearWindowRadius_bounds r hr).2
  have hterm : ∀ m ∈ J, ∀ m' ∈ J, ‖C m m'‖ ^ 2 ≤ 4 * s ^ 2 := by
    intro m hm m' hm'
    have hmS := (mem_bilinearWindow M r u m).mp hm |>.1
    have hm'S := (mem_bilinearWindow M r u m').mp hm' |>.1
    have hn := hbound m hmS m' hm'S
    have hs2 : 0 ≤ 2 * s := by positivity
    have hsq := (sq_le_sq₀ (norm_nonneg _) hs2).2 hn
    nlinarith
  have hsum : (∑ m ∈ J, ∑ m' ∈ J, ‖C m m'‖ ^ 2) ≤
      (J.card : ℝ) ^ 2 * (4 * s ^ 2) := by
    calc
      (∑ m ∈ J, ∑ m' ∈ J, ‖C m m'‖ ^ 2) ≤
          ∑ _m ∈ J, ∑ _m' ∈ J, 4 * s ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro m' hm'
        exact hterm m hm m' hm'
      _ = (J.card : ℝ) ^ 2 * (4 * s ^ 2) := by
        simp [Finset.sum_const]
        ring
  have hcardSq : (J.card : ℝ) ^ 2 ≤ (5 * r) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hJcard
  calc
    bilinearWindowSquaredEnergy M r C u =
        ∑ m ∈ J, ∑ m' ∈ J, ‖C m m'‖ ^ 2 := by rfl
    _ ≤ (J.card : ℝ) ^ 2 * (4 * s ^ 2) := hsum
    _ ≤ (5 * r) ^ 2 * (4 * s ^ 2) :=
      mul_le_mul_of_nonneg_right hcardSq (by positivity)
    _ = 100 * r ^ 2 * s ^ 2 := by ring

private theorem bilinearWindowEnergy_eq_masked_product
    (M r : ℝ) (C : ℕ → ℕ → ℂ) (u : ℕ) :
    bilinearWindowSquaredEnergy M r C u =
      ∑ p ∈ (bilinearRightSet M).product (bilinearRightSet M),
        if p.1 ∈ bilinearWindow M r u ∧ p.2 ∈ bilinearWindow M r u then
          ‖C p.1 p.2‖ ^ 2
        else 0 := by
  classical
  let S := bilinearRightSet M
  let J := bilinearWindow M r u
  have hprod : J.product J = (S.product S).filter
      (fun p => p.1 ∈ J ∧ p.2 ∈ J) := by
    apply Finset.ext
    rintro ⟨m, m'⟩
    simp [J, S, bilinearWindow, and_assoc, and_left_comm, and_comm]
  calc
    bilinearWindowSquaredEnergy M r C u =
        ∑ p ∈ J.product J, ‖C p.1 p.2‖ ^ 2 := by
      unfold bilinearWindowSquaredEnergy
      exact (Finset.sum_product' J J (fun m m' => ‖C m m'‖ ^ 2)).symm
    _ = ∑ p ∈ (S.product S).filter (fun p => p.1 ∈ J ∧ p.2 ∈ J),
          ‖C p.1 p.2‖ ^ 2 := by rw [hprod]
    _ = ∑ p ∈ S.product S,
        if p.1 ∈ J ∧ p.2 ∈ J then ‖C p.1 p.2‖ ^ 2 else 0 := by
      rw [Finset.sum_filter]
    _ = _ := by rfl

private theorem sum_bilinearWindowEnergy_eq_counted
    (M r : ℝ) (C : ℕ → ℕ → ℂ) :
    (∑ u ∈ bilinearWindowCenters M, bilinearWindowSquaredEnergy M r C u) =
      ∑ p ∈ (bilinearRightSet M).product (bilinearRightSet M),
        (((bilinearWindowCenters M).filter (fun u =>
          p.1 ∈ bilinearWindow M r u ∧
            p.2 ∈ bilinearWindow M r u)).card : ℝ) * ‖C p.1 p.2‖ ^ 2 := by
  classical
  let U := bilinearWindowCenters M
  let P := (bilinearRightSet M).product (bilinearRightSet M)
  calc
    (∑ u ∈ U, bilinearWindowSquaredEnergy M r C u) =
        ∑ u ∈ U, ∑ p ∈ P,
          if p.1 ∈ bilinearWindow M r u ∧ p.2 ∈ bilinearWindow M r u then
            ‖C p.1 p.2‖ ^ 2
          else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      exact bilinearWindowEnergy_eq_masked_product M r C u
    _ = ∑ p ∈ P, ∑ u ∈ U,
          if p.1 ∈ bilinearWindow M r u ∧ p.2 ∈ bilinearWindow M r u then
            ‖C p.1 p.2‖ ^ 2
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ P,
        ((U.filter (fun u => p.1 ∈ bilinearWindow M r u ∧
          p.2 ∈ bilinearWindow M r u)).card : ℝ) * ‖C p.1 p.2‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter]
      simp [Finset.sum_const]
    _ = _ := by rfl

private theorem sum_bilinearWindowEnergy_lower
    (M r s ρ : ℝ) (hM : 2 ≤ M) (hr : 8 ≤ r) (hrM : r ≤ M)
    (C : ℕ → ℕ → ℂ)
    (hzero : ∀ m ∈ bilinearRightSet M, ∀ m' ∈ bilinearRightSet M,
      2 * r < |(m : ℝ) - (m' : ℝ)| → C m m' = 0)
    (henergy : ρ ^ 4 / 5 * M * r * s ^ 2 ≤
      ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        ‖C m m'‖ ^ 2) :
    ρ ^ 4 * M * r ^ 2 * s ^ 2 / 20 ≤
      ∑ u ∈ bilinearWindowCenters M, bilinearWindowSquaredEnergy M r C u := by
  classical
  let S := bilinearRightSet M
  let P := S.product S
  let count : ℕ × ℕ → ℝ := fun p =>
    (((bilinearWindowCenters M).filter (fun u =>
      p.1 ∈ bilinearWindow M r u ∧ p.2 ∈ bilinearWindow M r u)).card : ℝ)
  let e : ℕ × ℕ → ℝ := fun p => ‖C p.1 p.2‖ ^ 2
  have hr0 : 0 ≤ r / 4 := by linarith
  have hterm : ∀ p ∈ P, (r / 4) * e p ≤ count p * e p := by
    intro p hp
    have hpS := Finset.mem_product.mp hp
    by_cases hband : |(p.1 : ℝ) - (p.2 : ℝ)| ≤ 2 * r
    · have hcount := bilinearWindow_cover_count M r hM hr hrM
        p.1 p.2 hpS.1 hpS.2 hband
      exact mul_le_mul_of_nonneg_right hcount (by dsimp [e]; positivity)
    · have hz := hzero p.1 hpS.1 p.2 hpS.2 (lt_of_not_ge hband)
      simp [e, hz]
  have hsumTerm : ∑ p ∈ P, (r / 4) * e p ≤ ∑ p ∈ P, count p * e p := by
    exact Finset.sum_le_sum hterm
  have hproductSum : (∑ p ∈ P, e p) =
      ∑ m ∈ S, ∑ m' ∈ S, ‖C m m'‖ ^ 2 := by
    exact Finset.sum_product' S S (fun m m' => ‖C m m'‖ ^ 2)
  have hscaled : (r / 4) * (ρ ^ 4 / 5 * M * r * s ^ 2) ≤
      (r / 4) * ∑ p ∈ P, e p := by
    apply mul_le_mul_of_nonneg_left _ hr0
    rw [hproductSum]
    exact henergy
  calc
    ρ ^ 4 * M * r ^ 2 * s ^ 2 / 20 =
        (r / 4) * (ρ ^ 4 / 5 * M * r * s ^ 2) := by ring
    _ ≤ (r / 4) * ∑ p ∈ P, e p := hscaled
    _ = ∑ p ∈ P, (r / 4) * e p := by rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ P, count p * e p := hsumTerm
    _ = ∑ u ∈ bilinearWindowCenters M, bilinearWindowSquaredEnergy M r C u := by
      symm
      simpa [S, P, count, e] using sum_bilinearWindowEnergy_eq_counted M r C

/-- **Averaging over short windows** (`lbi:window-energy`).

For an array supported in the `2r` diagonal band, the exact source energy
lower bound forces at least `ρ⁴ M / 4000` integer centers in `[M/2,2M]` to
contain at least `ρ⁴ r² / 800` pairs whose correlation has size at least
`ρ² s / 100`. -/
theorem bilinearWindowEnergy
    (M r s ρ : ℝ) (hM : 2 ≤ M) (hr : 8 ≤ r) (hrM : r ≤ M)
    (hs : 1 ≤ s) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (C : ℕ → ℕ → ℂ)
    (hzero : ∀ m ∈ bilinearRightSet M, ∀ m' ∈ bilinearRightSet M,
      2 * r < |(m : ℝ) - (m' : ℝ)| → C m m' = 0)
    (hbound : ∀ m ∈ bilinearRightSet M, ∀ m' ∈ bilinearRightSet M,
      ‖C m m'‖ ≤ 2 * s)
    (henergy : ρ ^ 4 / 5 * M * r * s ^ 2 ≤
      ∑ m ∈ bilinearRightSet M, ∑ m' ∈ bilinearRightSet M,
        ‖C m m'‖ ^ 2) :
    ρ ^ 4 * M / 4000 ≤
      (((bilinearWindowCenters M).filter (fun u =>
        ρ ^ 4 * r ^ 2 / 800 ≤
          ((((bilinearWindow M r u).product (bilinearWindow M r u)).filter
            (fun p => ρ ^ 2 * s / 100 ≤ ‖C p.1 p.2‖)).card : ℝ))).card : ℝ) := by
  classical
  have hMpos : 0 < M := by linarith
  have hrpos : 0 < r := by linarith
  have hspos : 0 < s := by linarith
  have hcenterCard := bilinearWindowCenters_card_le M hMpos
  have hwindowUpper : ∀ u ∈ bilinearWindowCenters M,
      bilinearWindowSquaredEnergy M r C u ≤ 100 * r ^ 2 * s ^ 2 := by
    intro u hu
    exact bilinearWindow_energy_upper M r s (by linarith) hspos C hbound u
  have hwindowSum := sum_bilinearWindowEnergy_lower M r s ρ hM hr hrM C
    hzero henergy
  have hmanyEnergy := many_large_window_energies
    (bilinearWindowCenters M) (bilinearWindowSquaredEnergy M r C)
    M r s ρ hMpos hrpos hspos hρ hcenterCard hwindowUpper hwindowSum
  let energyGood := (bilinearWindowCenters M).filter (fun u =>
    ρ ^ 4 * r ^ 2 * s ^ 2 / 120 ≤ bilinearWindowSquaredEnergy M r C u)
  let pairGood := (bilinearWindowCenters M).filter (fun u =>
    ρ ^ 4 * r ^ 2 / 800 ≤
      ((((bilinearWindow M r u).product (bilinearWindow M r u)).filter
        (fun p => ρ ^ 2 * s / 100 ≤ ‖C p.1 p.2‖)).card : ℝ))
  have hsubset : energyGood ⊆ pairGood := by
    intro u hu
    have huData := Finset.mem_filter.mp hu
    have hJcardNat := bilinearWindow_card_le M r u
    have hJcard : (((bilinearWindow M r u).card : ℕ) : ℝ) ≤ 5 * r := by
      calc
        ((bilinearWindow M r u).card : ℝ) ≤
            (bilinearWindowRadius r : ℝ) := by exact_mod_cast hJcardNat
        _ ≤ 5 * r := (bilinearWindowRadius_bounds r (by linarith)).2
    have hJbound : ∀ m ∈ bilinearWindow M r u,
        ∀ m' ∈ bilinearWindow M r u, ‖C m m'‖ ≤ 2 * s := by
      intro m hm m' hm'
      exact hbound m ((mem_bilinearWindow M r u m).mp hm).1
        m' ((mem_bilinearWindow M r u m').mp hm').1
    have hpairs := many_large_pairs_of_window_energy
      (bilinearWindow M r u) C r s ρ hrpos hspos hρ hJcard hJbound
        (by simpa [bilinearWindowSquaredEnergy] using huData.2)
    exact Finset.mem_filter.mpr ⟨huData.1, hpairs⟩
  have hcard : (energyGood.card : ℝ) ≤ (pairGood.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  calc
    ρ ^ 4 * M / 4000 ≤ (energyGood.card : ℝ) := by
      simpa [energyGood] using hmanyEnergy
    _ ≤ (pairGood.card : ℝ) := hcard
    _ = _ := by rfl

end

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.bilinearWindowEnergy

