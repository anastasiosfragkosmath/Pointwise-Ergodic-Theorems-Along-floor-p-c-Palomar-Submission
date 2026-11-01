module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearInverseInterval
public import Mathlib.Combinatorics.Pigeonhole

/-!
# The first two pigeonholes in the bilinear inverse theorem

This file isolates the common-denominator and common-second-coordinate
selection used after scalar Weyl inversion in blueprint item
`lbi:inverse-theorem`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

noncomputable section

/-- A finite set of pairs, each carrying a positive denominator bounded by a
real budget `B`, has one denominator and one second coordinate whose first-
coordinate fiber has the expected `1/(B*R)` density. -/
theorem finitePair_denominator_base_pigeonhole
    (S : Finset (ℕ × ℕ)) (W : Finset ℕ)
    (B R η : ℝ) (hB : 1 ≤ B) (hR : 0 < R) (hη : 0 < η)
    (hSsub : S ⊆ W.product W)
    (hWcard : (W.card : ℝ) ≤ R)
    (hcount : η ≤ (S.card : ℝ))
    (P : ℕ → ℕ → ℕ → Prop)
    (hden : ∀ p ∈ S, ∃ q : ℕ,
      1 ≤ q ∧ (q : ℝ) ≤ B ∧ P q p.1 p.2) :
    ∃ q : ℕ, ∃ mstar : ℕ, ∃ T : Finset ℕ,
      1 ≤ q ∧ (q : ℝ) ≤ B ∧
      mstar ∈ W ∧ T ⊆ W ∧
      η / (B * R) ≤ (T.card : ℝ) ∧
      ∀ m ∈ T, (m, mstar) ∈ S ∧ P q m mstar := by
  classical
  let K : ℕ := Nat.floor B
  let Q : Finset ℕ := Finset.Icc 1 K
  let den : ℕ × ℕ → ℕ := fun p =>
    if hp : p ∈ S then Classical.choose (hden p hp) else 0
  let target : Finset (ℕ × ℕ) := Q.product W
  let pairMap : ℕ × ℕ → ℕ × ℕ := fun p => (den p, p.2)
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hKpos : 1 ≤ K := by
    dsimp [K]
    exact Nat.le_floor (by simpa using hB)
  have hKleB : (K : ℝ) ≤ B := by
    dsimp [K]
    exact Nat.floor_le (by linarith)
  have hScardPos : 0 < (S.card : ℝ) := hη.trans_le hcount
  have hSnonempty : S.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hScardPos
  obtain ⟨p0, hp0⟩ := hSnonempty
  have hp0W := Finset.mem_product.mp (hSsub hp0)
  have hQnonempty : Q.Nonempty := by
    exact ⟨1, Finset.mem_Icc.mpr ⟨by omega, hKpos⟩⟩
  have htargetNonempty : target.Nonempty := by
    exact ⟨(1, p0.2), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hKpos⟩, hp0W.2⟩⟩
  have hdenSpec (p : ℕ × ℕ) (hp : p ∈ S) :
      1 ≤ den p ∧ (den p : ℝ) ≤ B ∧ P (den p) p.1 p.2 := by
    simp only [den, dite_eq_left hp]
    exact Classical.choose_spec (hden p hp)
  have hmap : ∀ p ∈ S, pairMap p ∈ target := by
    intro p hp
    have hspec := hdenSpec p hp
    have hqK : den p ≤ K := by
      dsimp [K]
      exact Nat.le_floor hspec.2.1
    have hpW := Finset.mem_product.mp (hSsub hp)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hspec.1, hqK⟩, hpW.2⟩
  have hQcard : Q.card = K := by
    simp [Q, Nat.card_Icc]
  have htargetCard : (target.card : ℝ) ≤ B * R := by
    rw [show target.card = Q.card * W.card by simp [target]]
    push_cast
    rw [hQcard]
    exact mul_le_mul hKleB hWcard (by positivity) hBpos.le
  have hBRpos : 0 < B * R := mul_pos hBpos hR
  have hthreshold : 0 ≤ η / (B * R) := by positivity
  have hsum : target.card • (η / (B * R)) ≤
      ∑ _p ∈ S, (1 : ℝ) := by
    rw [nsmul_eq_mul]
    calc
      (target.card : ℝ) * (η / (B * R)) ≤
          (B * R) * (η / (B * R)) :=
        mul_le_mul_of_nonneg_right htargetCard hthreshold
      _ = η := by field_simp [ne_of_gt hBRpos]
      _ ≤ (S.card : ℝ) := hcount
      _ = ∑ _p ∈ S, (1 : ℝ) := by simp
  obtain ⟨y, hyTarget, hyLarge⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (s := S) (t := target) (f := pairMap) (w := fun _ => (1 : ℝ))
      hmap htargetNonempty hsum
  rcases y with ⟨q, mstar⟩
  have hyData := Finset.mem_product.mp hyTarget
  let F : Finset (ℕ × ℕ) := S.filter (fun p => pairMap p = (q, mstar))
  let T : Finset ℕ := F.image Prod.fst
  have hFlarge : η / (B * R) ≤ (F.card : ℝ) := by
    simpa [F] using hyLarge
  have hinj : Set.InjOn Prod.fst (F : Set (ℕ × ℕ)) := by
    intro p hp p' hp' heq
    have hpFilter := Finset.mem_filter.mp hp
    have hp'Filter := Finset.mem_filter.mp hp'
    have hpSnd : p.2 = mstar := by
      have := congrArg Prod.snd hpFilter.2
      simpa [pairMap] using this
    have hp'Snd : p'.2 = mstar := by
      have := congrArg Prod.snd hp'Filter.2
      simpa [pairMap] using this
    exact Prod.ext heq (hpSnd.trans hp'Snd.symm)
  have hTcard : T.card = F.card := by
    dsimp [T]
    exact Finset.card_image_of_injOn hinj
  have hTsub : T ⊆ W := by
    intro m hm
    obtain ⟨p, hpF, hpEq⟩ := Finset.mem_image.mp hm
    have hpS := (Finset.mem_filter.mp hpF).1
    have hpW := Finset.mem_product.mp (hSsub hpS)
    simpa [hpEq] using hpW.1
  refine ⟨q, mstar, T, (Finset.mem_Icc.mp hyData.1).1, ?_, hyData.2,
    hTsub, ?_, ?_⟩
  · have hqK := (Finset.mem_Icc.mp hyData.1).2
    exact (Nat.cast_le.mpr hqK).trans hKleB
  · rw [hTcard]
    exact hFlarge
  · intro m hm
    obtain ⟨p, hpF, hpEq⟩ := Finset.mem_image.mp hm
    have hpFilter := Finset.mem_filter.mp hpF
    have hpS := hpFilter.1
    have hpairEq := hpFilter.2
    have hpSnd : p.2 = mstar := by
      have := congrArg Prod.snd hpairEq
      simpa [pairMap] using this
    have hdenEq : den p = q := by
      have := congrArg Prod.fst hpairEq
      simpa [pairMap] using this
    have hpEq' : p = (m, mstar) := by
      apply Prod.ext
      · simpa using hpEq
      · exact hpSnd
    have hspec := hdenSpec p hpS
    rw [hdenEq] at hspec
    simpa [hpEq'] using And.intro hpS hspec.2.2

/-- The good pairs in one bilinear window at the exact source threshold. -/
def bilinearGoodPairSet
    (X H L M ρ : ℝ) (d : ℕ) (ν : ℕ → ℝ) (u : ℕ) :
    Finset (ℕ × ℕ) :=
  ((bilinearWindow M (H / L) u).product
      (bilinearWindow M (H / L) u)).filter fun p =>
    ρ ^ 2 * (H / M) / 100 ≤
      ‖bilinearC X H L (bilinearCenteredPhase X d ν) p.1 p.2‖

/-- The exact natural window-cardinality bound, exposed for the bilinear
inverse pigeonhole. -/
theorem bilinearWindow_card_le_radius_public
    (M r : ℝ) (u : ℕ) :
    (bilinearWindow M r u).card ≤ bilinearWindowRadius r := by
  have hsub : bilinearWindow M r u ⊆
      Finset.Ioc u (u + bilinearWindowRadius r) := by
    intro m hm
    exact Finset.mem_Ioc.mpr ((mem_bilinearWindow M r u m).mp hm |>.2)
  calc
    (bilinearWindow M r u).card ≤
        (Finset.Ioc u (u + bilinearWindowRadius r)).card :=
      Finset.card_le_card hsub
    _ = bilinearWindowRadius r := by simp

/-- Pigeonholing the Weyl denominators and then the second coordinate gives
one base point and many first coordinates, with the exact pre-simplification
density from the source proof. -/
theorem bilinearGoodPairDenominatorSelection
    (d : ℕ) (hd : 1 ≤ d)
    (X H L M ρ : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (hr : 1 ≤ H / L) (hs : 1 ≤ H / M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (u : ℕ) (hu : u ∈ bilinearWindowCenters M)
    (ν : ℕ → ℝ)
    (hgoodCount : ρ ^ 4 * (H / L) ^ 2 / 800 ≤
      ((bilinearGoodPairSet X H L M ρ d ν u).card : ℝ)) :
    ∃ q : ℕ, ∃ mstar : ℕ, ∃ T : Finset ℕ,
      1 ≤ q ∧ (q : ℝ) ≤ bilinearInverseB d ρ⁻¹ ∧
      mstar ∈ bilinearWindow M (H / L) u ∧
      T ⊆ bilinearWindow M (H / L) u ∧
      (ρ ^ 4 * (H / L) ^ 2 / 800) /
          (bilinearInverseB d ρ⁻¹ *
            (bilinearWindowRadius (H / L) : ℝ)) ≤ (T.card : ℝ) ∧
      ∀ m ∈ T,
        (m, mstar) ∈ bilinearGoodPairSet X H L M ρ d ν u ∧
        ∀ j, 1 ≤ j → j ≤ d →
          realDistanceToIntegers
              ((q : ℝ) *
                ((bilinearGammaPolynomial X
                    (bilinearCommonLeftBase X (H / M) u) d j ν).eval (m : ℝ) -
                  (bilinearGammaPolynomial X
                    (bilinearCommonLeftBase X (H / M) u) d j ν).eval
                      (mstar : ℝ))) ≤
            bilinearInverseB d ρ⁻¹ / (H / M) ^ j := by
  let W := bilinearWindow M (H / L) u
  let S := bilinearGoodPairSet X H L M ρ d ν u
  let B := bilinearInverseB d ρ⁻¹
  let R : ℝ := bilinearWindowRadius (H / L)
  let η : ℝ := ρ ^ 4 * (H / L) ^ 2 / 800
  have hρinv : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  have hB : 1 ≤ B := by
    simpa [B] using (bilinearInverseBudget_values d hd ρ⁻¹ hρinv).1
  have hR : 0 < R := by
    have hceil : 4 * (H / L) ≤ R := by
      dsimp [R, bilinearWindowRadius]
      exact Nat.le_ceil _
    have : 0 < H / L := by linarith
    linarith
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hSsub : S ⊆ W.product W := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hWcard : (W.card : ℝ) ≤ R := by
    dsimp [W, R]
    exact_mod_cast bilinearWindow_card_le_radius_public M (H / L) u
  have hcount : η ≤ (S.card : ℝ) := by
    simpa [η, S] using hgoodCount
  let P : ℕ → ℕ → ℕ → Prop := fun q m m' =>
    ∀ j, 1 ≤ j → j ≤ d →
      realDistanceToIntegers
          ((q : ℝ) *
            ((bilinearGammaPolynomial X
                (bilinearCommonLeftBase X (H / M) u) d j ν).eval (m : ℝ) -
              (bilinearGammaPolynomial X
                (bilinearCommonLeftBase X (H / M) u) d j ν).eval (m' : ℝ))) ≤
        B / (H / M) ^ j
  have hden : ∀ p ∈ S, ∃ q : ℕ,
      1 ≤ q ∧ (q : ℝ) ≤ B ∧ P q p.1 p.2 := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpWindow := Finset.mem_product.mp hpData.1
    simpa [B, P] using bilinearGoodPairWeyl_scaled
      d hd X H L M ρ hL hM hX hHX hr hs hρ hρhalf
        u hu p.1 p.2 hpWindow.1 hpWindow.2 ν hpData.2
  obtain ⟨q, mstar, T, hq, hqB, hmstar, hTsub, hTcard, hT⟩ :=
    finitePair_denominator_base_pigeonhole S W B R η hB hR hη
      hSsub hWcard hcount P hden
  refine ⟨q, mstar, T, hq, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [B] using hqB
  · simpa [W] using hmstar
  · simpa [W] using hTsub
  · simpa [η, B, R] using hTcard
  · intro m hm
    have h := hT m hm
    simpa [S, P, B] using h

/-- The explicit budgets and `R≤5r` turn the raw two-pigeonhole density into
the source density `2*δ₁*R`. -/
theorem bilinearFirstPigeonhole_density
    (d : ℕ) (hd : 1 ≤ d) (ρ r : ℝ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hr : 1 ≤ r) :
    2 * (bilinearInverseZOne d ρ⁻¹)⁻¹ *
        (bilinearWindowRadius r : ℝ) ≤
      (ρ ^ 4 * r ^ 2 / 800) /
        (bilinearInverseB d ρ⁻¹ * (bilinearWindowRadius r : ℝ)) := by
  have hρinv : 2 ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hρ).2
    nlinarith
  have hB : 1 ≤ bilinearInverseB d ρ⁻¹ :=
    (bilinearInverseBudget_values d hd ρ⁻¹ hρinv).1
  have hBpos : 0 < bilinearInverseB d ρ⁻¹ := lt_of_lt_of_le zero_lt_one hB
  have hRlower : 4 * r ≤ (bilinearWindowRadius r : ℝ) := by
    dsimp [bilinearWindowRadius]
    exact Nat.le_ceil _
  have hRupper : (bilinearWindowRadius r : ℝ) ≤ 5 * r := by
    have hceil : (bilinearWindowRadius r : ℝ) < 4 * r + 1 := by
      dsimp [bilinearWindowRadius]
      exact Nat.ceil_lt_add_one (by positivity)
    linarith
  have hRpos : 0 < (bilinearWindowRadius r : ℝ) := by linarith
  have h5rpos : 0 < 5 * r := by positivity
  have hRsq : (bilinearWindowRadius r : ℝ) ^ 2 ≤ 25 * r ^ 2 := by
    have h := (sq_le_sq₀ hRpos.le h5rpos.le).2 hRupper
    nlinarith
  have hleft :
      2 * (bilinearInverseZOne d ρ⁻¹)⁻¹ *
          (bilinearWindowRadius r : ℝ) =
        ρ ^ 4 * (bilinearWindowRadius r : ℝ) /
          (20000 * bilinearInverseB d ρ⁻¹) := by
    rw [bilinearInverseZOne_eval]
    field_simp [ne_of_gt hρ, ne_of_gt hBpos]
    ring
  rw [hleft]
  have hright :
      (ρ ^ 4 * r ^ 2 / 800) /
          (bilinearInverseB d ρ⁻¹ * (bilinearWindowRadius r : ℝ)) =
        ρ ^ 4 * r ^ 2 /
          (800 * bilinearInverseB d ρ⁻¹ *
            (bilinearWindowRadius r : ℝ)) := by
    ring
  rw [hright]
  apply (div_le_div_iff₀
      (mul_pos (by norm_num) hBpos)
      (mul_pos (mul_pos (by norm_num) hBpos) hRpos)).2
  have hcore :
      800 * (bilinearWindowRadius r : ℝ) ^ 2 ≤
        20000 * r ^ 2 := by
    nlinarith
  have hscale :
      0 ≤ ρ ^ 4 * bilinearInverseB d ρ⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hcore hscale
  convert hscaled using 1 <;> ring

/-- The first two source pigeonholes in their final normalized form. -/
theorem bilinearGoodPairCommonDenominator
    (d : ℕ) (hd : 1 ≤ d)
    (X H L M ρ : ℝ) (hL : 0 < L) (hM : 0 < M)
    (hX : X = L * M) (hHX : H ≤ X)
    (hr : 1 ≤ H / L) (hs : 1 ≤ H / M)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (u : ℕ) (hu : u ∈ bilinearWindowCenters M)
    (ν : ℕ → ℝ)
    (hgoodCount : ρ ^ 4 * (H / L) ^ 2 / 800 ≤
      ((bilinearGoodPairSet X H L M ρ d ν u).card : ℝ)) :
    ∃ q : ℕ, ∃ mstar : ℕ, ∃ T : Finset ℕ,
      1 ≤ q ∧ (q : ℝ) ≤ bilinearInverseB d ρ⁻¹ ∧
      mstar ∈ bilinearWindow M (H / L) u ∧
      T ⊆ bilinearWindow M (H / L) u ∧
      2 * (bilinearInverseZOne d ρ⁻¹)⁻¹ *
          (bilinearWindowRadius (H / L) : ℝ) ≤ (T.card : ℝ) ∧
      ∀ m ∈ T,
        (m, mstar) ∈ bilinearGoodPairSet X H L M ρ d ν u ∧
        ∀ j, 1 ≤ j → j ≤ d →
          realDistanceToIntegers
              ((q : ℝ) *
                ((bilinearGammaPolynomial X
                    (bilinearCommonLeftBase X (H / M) u) d j ν).eval (m : ℝ) -
                  (bilinearGammaPolynomial X
                    (bilinearCommonLeftBase X (H / M) u) d j ν).eval
                      (mstar : ℝ))) ≤
            bilinearInverseB d ρ⁻¹ / (H / M) ^ j := by
  obtain ⟨q, mstar, T, hq, hqB, hmstar, hTsub, hTcard, hT⟩ :=
    bilinearGoodPairDenominatorSelection d hd X H L M ρ hL hM hX hHX
      hr hs hρ hρhalf u hu ν hgoodCount
  refine ⟨q, mstar, T, hq, hqB, hmstar, hTsub, ?_, hT⟩
  exact (bilinearFirstPigeonhole_density d hd ρ (H / L) hρ hρhalf hr).trans
    hTcard

#print axioms finitePair_denominator_base_pigeonhole
#print axioms bilinearGoodPairDenominatorSelection
#print axioms bilinearFirstPigeonhole_density
#print axioms bilinearGoodPairCommonDenominator

end

end FractionalPrimes.Literature.Polynomial
