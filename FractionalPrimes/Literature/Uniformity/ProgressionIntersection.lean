module

public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalAndTV
public import Mathlib.Data.Int.CardIntervalMod

/-!
# Finite progression membership characterization

This helper identifies a positive-length arithmetic progression with the
integer interval between its endpoints, filtered to its residue class.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open Int

/-- A positive-length progression consists exactly of the integers from its
initial point through its final point in the same residue class. -/
theorem arithmeticProgressionPoints_eq_Ioc_filter_modEq
    (a : ℤ) (d : ℕ) (hd : 0 < d) (L : ℕ) (hL : 0 < L) :
    arithmeticProgressionPoints a d hd L =
      {x ∈ Finset.Ioc (a - 1) (a + ((L - 1 : ℕ) : ℤ) * (d : ℤ)) |
        x ≡ a [ZMOD (d : ℤ)]} := by
  classical
  have hdZ : 0 < (d : ℤ) := by exact_mod_cast hd
  have hL' : 1 ≤ L := Nat.succ_le_iff.mpr hL
  ext x
  simp only [arithmeticProgressionPoints, Finset.mem_image, Finset.mem_range,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨j, hj, hx⟩
    subst x
    have hjle : j ≤ L - 1 := Nat.le_pred_of_lt hj
    have hjleZ : (j : ℤ) ≤ ((L - 1 : ℕ) : ℤ) := by exact_mod_cast hjle
    have hmul := mul_le_mul_of_nonneg_right hjleZ (le_of_lt hdZ)
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · have hjnonneg : 0 ≤ (j : ℤ) * (d : ℤ) :=
          mul_nonneg (Int.natCast_nonneg _) (le_of_lt hdZ)
        linarith
      · simpa [add_comm] using add_le_add_left hmul a
    · apply Int.modEq_iff_dvd.mpr
      refine ⟨-(j : ℤ), ?_⟩
      ring
  · rintro ⟨⟨hlo, hhi⟩, hmod⟩
    have ha_le : a ≤ x := by omega
    have hdiv : (d : ℤ) ∣ x - a := Int.modEq_iff_dvd.mp hmod.symm
    rcases hdiv with ⟨t, ht⟩
    have hx : x = a + (d : ℤ) * t := by linarith
    have hmul_nonneg : 0 ≤ (d : ℤ) * t := by linarith
    have ht_nonneg : 0 ≤ t := by
      by_contra h
      have ht_neg : t < 0 := lt_of_not_ge h
      have hmul_neg : (d : ℤ) * t < 0 := mul_neg_of_pos_of_neg hdZ ht_neg
      linarith
    have hmul_le : (d : ℤ) * t ≤ (d : ℤ) * ((L - 1 : ℕ) : ℤ) := by
      nlinarith [hx, hhi]
    have ht_le : t ≤ ((L - 1 : ℕ) : ℤ) :=
      (mul_le_mul_iff_of_pos_left hdZ).mp hmul_le
    have ht_lt : t < (L : ℤ) := by
      have hsub : ((L - 1 : ℕ) : ℤ) + 1 = (L : ℤ) := by
        exact_mod_cast Nat.sub_add_cancel hL'
      linarith
    let j : ℕ := t.toNat
    have hjcast : (j : ℤ) = t := by
      exact Int.toNat_of_nonneg ht_nonneg
    have hjltZ : (j : ℤ) < (L : ℤ) := by simpa [j, hjcast] using ht_lt
    have hj : j < L := by exact_mod_cast hjltZ
    refine ⟨j, hj, ?_⟩
    rw [← hjcast] at hx
    calc
      a + (j : ℤ) * (d : ℤ) = a + (d : ℤ) * (j : ℤ) := by ring
      _ = x := hx.symm

private theorem filtered_Ioc_modEq_isFiniteArithmeticProgression
    (lo hi c : ℤ) (q : ℕ) (hq : 0 < q) :
    isFiniteArithmeticProgression
      {x ∈ Finset.Ioc lo hi | x ≡ c [ZMOD (q : ℤ)]} := by
  classical
  have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
  let lo' : ℤ := ⌊((lo - c : ℤ) : ℚ) / (q : ℚ)⌋
  let hi' : ℤ := ⌊((hi - c : ℤ) : ℚ) / (q : ℚ)⌋
  let L : ℕ := (hi' - lo').toNat
  let a : ℤ := c + (lo' + 1) * (q : ℤ)
  let emul : ℤ ↪ ℤ := ⟨fun z => z * (q : ℤ), mul_left_injective₀ hqZ.ne'⟩
  let eadd : ℤ ↪ ℤ := ⟨fun z => z + c, add_left_injective c⟩
  have hfilter :
      {x ∈ Finset.Ioc lo hi | x ≡ c [ZMOD (q : ℤ)]} =
        (Finset.Ioc lo' hi').map (emul.trans eadd) := by
    rw [Int.Ioc_filter_modEq_eq lo hi c]
    rw [Int.Ioc_filter_dvd_eq (lo - c) (hi - c) hqZ]
    rw [Finset.map_map]
    rfl
  have hIoc :
      Finset.Ioc lo' hi' =
        (Finset.range L).map
          (Nat.castEmbedding.trans (addLeftEmbedding (lo' + 1))) := by
    simpa [L] using (Int.Ioc_eq_finset_map lo' hi')
  refine ⟨a, q, hq, L, ?_⟩
  rw [hfilter, hIoc, Finset.map_map]
  simp only [arithmeticProgressionPoints, Finset.map_eq_image]
  apply Finset.image_congr
  intro j hj
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]
  dsimp [a, lo', emul, eadd]
  ring

/-- The intersection of two finite arithmetic progressions is either empty or
is itself a finite arithmetic progression. -/
theorem arithmeticProgressionPoints_inter_eq_empty_or_isFiniteArithmeticProgression
    (a b : ℤ) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (L M : ℕ) :
    arithmeticProgressionPoints a d hd L ∩ arithmeticProgressionPoints b e he M = ∅ ∨
      isFiniteArithmeticProgression
        (arithmeticProgressionPoints a d hd L ∩ arithmeticProgressionPoints b e he M) := by
  classical
  let A := arithmeticProgressionPoints a d hd L
  let B := arithmeticProgressionPoints b e he M
  let P := A ∩ B
  change P = ∅ ∨ isFiniteArithmeticProgression P
  by_cases hL0 : L = 0
  · left
    simp [P, A, arithmeticProgressionPoints, hL0]
  by_cases hM0 : M = 0
  · left
    simp [P, B, arithmeticProgressionPoints, hM0]
  have hL : 0 < L := Nat.pos_of_ne_zero hL0
  have hM : 0 < M := Nat.pos_of_ne_zero hM0
  by_cases hPempty : P = ∅
  · exact Or.inl hPempty
  right
  let loA : ℤ := a - 1
  let hiA : ℤ := a + ((L - 1 : ℕ) : ℤ) * (d : ℤ)
  let loB : ℤ := b - 1
  let hiB : ℤ := b + ((M - 1 : ℕ) : ℤ) * (e : ℤ)
  let lo : ℤ := max loA loB
  let hi : ℤ := min hiA hiB
  let q : ℕ := Nat.lcm d e
  have hA : A = {x ∈ Finset.Ioc loA hiA | x ≡ a [ZMOD (d : ℤ)]} := by
    simpa [A, loA, hiA] using
      (arithmeticProgressionPoints_eq_Ioc_filter_modEq a d hd L hL)
  have hB : B = {x ∈ Finset.Ioc loB hiB | x ≡ b [ZMOD (e : ℤ)]} := by
    simpa [B, loB, hiB] using
      (arithmeticProgressionPoints_eq_Ioc_filter_modEq b e he M hM)
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Nat.ne_of_gt hd) (Nat.ne_of_gt he))
  have hqd : (d : ℤ) ∣ (q : ℤ) := by
    dsimp [q]
    exact_mod_cast (Nat.dvd_lcm_left d e)
  have hqe : (e : ℤ) ∣ (q : ℤ) := by
    dsimp [q]
    exact_mod_cast (Nat.dvd_lcm_right d e)
  have hPne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hPempty
  obtain ⟨c, hcP⟩ := hPne
  rcases Finset.mem_inter.mp hcP with ⟨hcA, hcB⟩
  have hcAFilter : c ∈ {x ∈ Finset.Ioc loA hiA | x ≡ a [ZMOD (d : ℤ)]} := by
    rw [← hA]
    exact hcA
  have hcBFilter : c ∈ {x ∈ Finset.Ioc loB hiB | x ≡ b [ZMOD (e : ℤ)]} := by
    rw [← hB]
    exact hcB
  have hca : c ≡ a [ZMOD (d : ℤ)] :=
    (Finset.mem_filter.mp hcAFilter).2
  have hcb : c ≡ b [ZMOD (e : ℤ)] :=
    (Finset.mem_filter.mp hcBFilter).2
  have hP_eq :
      P = {x ∈ Finset.Ioc lo hi | x ≡ c [ZMOD (q : ℤ)]} := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxA, hxB⟩
      have hxAFilter :
          x ∈ {x ∈ Finset.Ioc loA hiA | x ≡ a [ZMOD (d : ℤ)]} := by
        rw [← hA]
        exact hxA
      have hxBFilter :
          x ∈ {x ∈ Finset.Ioc loB hiB | x ≡ b [ZMOD (e : ℤ)]} := by
        rw [← hB]
        exact hxB
      rcases Finset.mem_filter.mp hxAFilter with ⟨hxAIoc, hxa⟩
      rcases Finset.mem_Ioc.mp hxAIoc with ⟨hloA, hhiA⟩
      rcases Finset.mem_filter.mp hxBFilter with ⟨hxBIoc, hxb⟩
      rcases Finset.mem_Ioc.mp hxBIoc with ⟨hloB, hhiB⟩
      have hxd : x ≡ c [ZMOD (d : ℤ)] := hxa.trans hca.symm
      have hxe : x ≡ c [ZMOD (e : ℤ)] := hxb.trans hcb.symm
      have hxqLcm : x ≡ c [ZMOD (d : ℤ).lcm (e : ℤ)] :=
        (Int.modEq_and_modEq_iff_modEq_lcm).mp ⟨hxd, hxe⟩
      have hxq : x ≡ c [ZMOD (q : ℤ)] := by
        simpa [q, Int.lcm_def] using hxqLcm
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hxq⟩
      · exact (max_lt_iff).2 ⟨hloA, hloB⟩
      · exact (le_min_iff).2 ⟨hhiA, hhiB⟩
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxIoc, hxcq⟩
      rcases Finset.mem_Ioc.mp hxIoc with ⟨hlo, hhi⟩
      have hloA : loA < x := lt_of_le_of_lt (le_max_left _ _) hlo
      have hloB : loB < x := lt_of_le_of_lt (le_max_right _ _) hlo
      have hhiA : x ≤ hiA := le_trans hhi (min_le_left _ _)
      have hhiB : x ≤ hiB := le_trans hhi (min_le_right _ _)
      have hxcD : x ≡ c [ZMOD (d : ℤ)] := Int.ModEq.of_dvd hqd hxcq
      have hxcE : x ≡ c [ZMOD (e : ℤ)] := Int.ModEq.of_dvd hqe hxcq
      have hxa : x ≡ a [ZMOD (d : ℤ)] := hxcD.trans hca
      have hxb : x ≡ b [ZMOD (e : ℤ)] := hxcE.trans hcb
      have hxAFilter : x ∈ {x ∈ Finset.Ioc loA hiA | x ≡ a [ZMOD (d : ℤ)]} :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hloA, hhiA⟩, hxa⟩
      have hxBFilter : x ∈ {x ∈ Finset.Ioc loB hiB | x ≡ b [ZMOD (e : ℤ)]} :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hloB, hhiB⟩, hxb⟩
      have hxA : x ∈ A := by rw [hA]; exact hxAFilter
      have hxB : x ∈ B := by rw [hB]; exact hxBFilter
      exact Finset.mem_inter.mpr ⟨hxA, hxB⟩
  have hFiltered :
      isFiniteArithmeticProgression
        {x ∈ Finset.Ioc lo hi | x ≡ c [ZMOD (q : ℤ)]} :=
    filtered_Ioc_modEq_isFiniteArithmeticProgression lo hi c q hq
  rw [← hP_eq] at hFiltered
  exact hFiltered

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.arithmeticProgressionPoints_eq_Ioc_filter_modEq
#print axioms FractionalPrimes.Literature.Uniformity.arithmeticProgressionPoints_inter_eq_empty_or_isFiniteArithmeticProgression
