module

public import FractionalPrimes.Literature.MSZ.LocalizedGridFiniteVariationBootstrap
public import FractionalPrimes.Literature.Variation.OrderedVariationExhaustion
public import FractionalPrimes.Literature.MSZ.LocalizedGridCountableFatouCore
public import Mathlib.MeasureTheory.Function.LpSeminorm.Count

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open FractionalPrimes.Literature.Variation
open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

private theorem mszRationalDyadic_to_numerator_denominator
    (n : ℕ) (e : ℤ) :
    ∃ L a : ℕ, (n : ℚ) * (2 : ℚ) ^ e =
      (a : ℚ) / (2 ^ L : ℚ) := by
  by_cases he : 0 ≤ e
  · refine ⟨0, n * 2 ^ e.toNat, ?_⟩
    have he' : (e.toNat : ℤ) = e := Int.toNat_of_nonneg he
    rw [← he', zpow_natCast]
    norm_cast
    simp [he]
  · have he' : e < 0 := lt_of_not_ge he
    let L : ℕ := (-e).toNat
    have hL : (L : ℤ) = -e := by
      dsimp [L]
      exact Int.toNat_of_nonneg (neg_nonneg.mpr he'.le)
    refine ⟨L, n, ?_⟩
    have hExp : e = -(L : ℤ) := by omega
    rw [hExp, zpow_neg, zpow_natCast]
    simp [div_eq_mul_inv]

/-- Every source time in a closed dyadic short block belongs to one of its
normalized finite grids. -/
theorem mszShortBlockTime_mem_some_grid
    (k : ℤ) (t : MSZTime)
    (ht : (2 : ℚ) ^ k ≤ t.val ∧ t.val ≤ (2 : ℚ) ^ (k + 1)) :
    ∃ L m, m ≤ 2 ^ L ∧ mszGridTime k L m = t := by
  rcases (positiveDyadicRationals_iff_powerRationals t.val).1 t.property with
    ⟨n, hn, v, ht_repr⟩
  let e : ℤ := v - k
  obtain ⟨L, a, hratio⟩ :=
    mszRationalDyadic_to_numerator_denominator n e
  have hratio' : t.val / (2 : ℚ) ^ k =
      (a : ℚ) / (2 ^ L : ℚ) := by
    rw [ht_repr]
    have hpow : (2 : ℚ) ^ v / (2 : ℚ) ^ k = (2 : ℚ) ^ e := by
      rw [← zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
    calc
      (n : ℚ) * (2 : ℚ) ^ v / (2 : ℚ) ^ k =
          (n : ℚ) * ((2 : ℚ) ^ v / (2 : ℚ) ^ k) := by ring
      _ = (n : ℚ) * (2 : ℚ) ^ e := by rw [hpow]
      _ = (a : ℚ) / (2 ^ L : ℚ) := hratio
  have hbasepos : 0 < (2 ^ L : ℚ) := by positivity
  have hbase_le_a : (2 ^ L : ℚ) ≤ (a : ℚ) := by
    have hlow : 1 ≤ (a : ℚ) / (2 ^ L : ℚ) := by
      calc
        1 ≤ t.val / (2 : ℚ) ^ k :=
          (le_div_iff₀ (zpow_pos (by norm_num : (0 : ℚ) < 2) k)).2
            (by simpa using ht.1)
        _ = _ := hratio'
    simpa using (le_div_iff₀ hbasepos).1 hlow
  have ha_le_two_base : (a : ℚ) ≤ 2 * (2 ^ L : ℚ) := by
    have hhigh : (a : ℚ) / (2 ^ L : ℚ) ≤ 2 := by
      have hpow : (2 : ℚ) ^ (k + 1) = 2 * (2 : ℚ) ^ k := by
        rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        ring
      have hbound : t.val ≤ 2 * (2 : ℚ) ^ k := by
        calc
          t.val ≤ (2 : ℚ) ^ (k + 1) := ht.2
          _ = 2 * (2 : ℚ) ^ k := hpow
      have hdivbound : t.val / (2 : ℚ) ^ k ≤ 2 :=
        (div_le_iff₀ (zpow_pos (by norm_num : (0 : ℚ) < 2) k)).2
          (by simpa [mul_comm] using hbound)
      calc
        (a : ℚ) / (2 ^ L : ℚ) = t.val / (2 : ℚ) ^ k := hratio'.symm
        _ ≤ 2 := hdivbound
    exact (div_le_iff₀ hbasepos).1 hhigh
  have hbase_le_a_nat : 2 ^ L ≤ a := by exact_mod_cast hbase_le_a
  have ha_le_two_base_nat : a ≤ 2 * 2 ^ L := by exact_mod_cast ha_le_two_base
  let m : ℕ := a - 2 ^ L
  have hm : m ≤ 2 ^ L := by dsimp [m]; omega
  have hsum : 2 ^ L + m = a := by
    dsimp [m]
    exact Nat.add_sub_of_le hbase_le_a_nat
  have hratio'' : t.val = (2 : ℚ) ^ k *
      (1 + (m : ℚ) / (2 ^ L : ℚ)) := by
    have htdiv : t.val = (2 : ℚ) ^ k *
        ((a : ℚ) / (2 ^ L : ℚ)) := by
      calc
        t.val = t.val / (2 : ℚ) ^ k * (2 : ℚ) ^ k := by
          field_simp [ne_of_gt (zpow_pos (by norm_num : (0 : ℚ) < 2) k)]
        _ = _ := by rw [hratio']; ring
    rw [htdiv, ← hsum]
    push_cast
    field_simp
    <;> ring
  have hpow : (2 : ℚ) ^ (-(L : ℤ)) = 1 / (2 ^ L : ℚ) := by
    rw [zpow_neg, zpow_natCast]
    simp
  have htime : t.val = (mszGridTime k L m).val := by
    rw [mszGridTime_eq_blueprint, hpow]
    simpa [div_eq_mul_inv] using hratio''
  refine ⟨L, m, hm, ?_⟩
  exact Subtype.ext htime.symm

private theorem mszGridTime_normalized (k : ℤ) (L m : ℕ) :
    ((mszGridTime k L m).val / (2 : ℚ) ^ k) - 1 =
      dyadicGridPoint L m := by
  rw [mszGridTime_eq_affine_dyadicGridPoint]
  have hpow : (2 : ℚ) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
  field_simp
  ring

/-- The literal source time set in the closed short block
`[2^k,2^(k+1)] ∩ 𝒰`. -/
abbrev MSZShortBlockTime (k : ℤ) :=
  {t : MSZTime // (2 : ℚ) ^ k ≤ t.val ∧ t.val ≤ (2 : ℚ) ^ (k + 1)}

/-- The source average restricted to one closed short block. -/
noncomputable def mszShortBlockValue (A : AdmissibleData) (k : ℤ)
    (f : ℤ → ℂ) (x : ℤ) (t : MSZShortBlockTime k) : ℂ :=
  mszKernelAverage (A.kernel t.1) f x

/-- The unrestricted ordered `2`-variation on a closed source short block. -/
noncomputable def mszSourceShortBlockVariation (A : AdmissibleData) (k : ℤ)
    (f : ℤ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  orderedRVariation 2 (mszShortBlockValue A k f x)

private theorem dyadicGridPoint_bounds {L m : ℕ} (hm : m ≤ 2 ^ L) :
    0 ≤ dyadicGridPoint L m ∧ dyadicGridPoint L m ≤ 1 := by
  constructor
  · unfold dyadicGridPoint
    positivity
  · unfold dyadicGridPoint
    apply (div_le_one₀ (by positivity : (0 : ℚ) < (2 ^ L : ℚ))).2
    exact_mod_cast hm

/-- The time corresponding to a normalized point of the finite grid, viewed
as a point of the exact source block. -/
private noncomputable def mszShortBlockGridTime
    (k : ℤ) (L : ℕ)
    (t : {t : ℚ // t ∈ dyadicGridTimes L}) : MSZShortBlockTime k := by
  refine ⟨mszGridTimeAffine k L t, ?_⟩
  rcases mszDyadicGridPointIndex_spec L t with ⟨hm, hpoint⟩
  have ht01 := dyadicGridPoint_bounds hm
  rw [hpoint] at ht01
  have hscale : 0 < (2 : ℚ) ^ k := zpow_pos (by norm_num) k
  have hupper : (2 : ℚ) ^ (k + 1) = 2 * (2 : ℚ) ^ k := by
    rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    ring
  rw [mszGridTimeAffine_val]
  constructor
  · have hbase : (1 : ℚ) ≤ 1 + t.1 := by linarith [ht01.1]
    simpa using mul_le_mul_of_nonneg_left hbase hscale.le
  · calc
      (2 : ℚ) ^ k * (1 + t.1) ≤ (2 : ℚ) ^ k * 2 :=
        mul_le_mul_of_nonneg_left (by linarith [ht01.2]) hscale.le
      _ = 2 * (2 : ℚ) ^ k := by ring
      _ = (2 : ℚ) ^ (k + 1) := hupper.symm

private theorem mszShortBlockGridTime_val
    (k : ℤ) (L : ℕ) (t : {t : ℚ // t ∈ dyadicGridTimes L}) :
    (mszShortBlockGridTime k L t).1 = mszGridTimeAffine k L t := by
  simp [mszShortBlockGridTime]

private theorem mszShortBlockGridTime_strictMono (k : ℤ) (L : ℕ) :
    StrictMono (mszShortBlockGridTime k L) := by
  intro a b hab
  change a.1 < b.1 at hab
  change ((mszShortBlockGridTime k L a).1).val <
    ((mszShortBlockGridTime k L b).1).val
  rw [mszShortBlockGridTime_val, mszGridTimeAffine_val,
    mszShortBlockGridTime_val, mszGridTimeAffine_val]
  exact mul_lt_mul_of_pos_left (add_lt_add_right hab (1 : ℚ))
    (zpow_pos (by norm_num) k)

private theorem mszShortBlockGridTime_value
    (A : AdmissibleData) (k : ℤ) (L : ℕ) (f : ℤ → ℂ) (x : ℤ)
    (t : {t : ℚ // t ∈ dyadicGridTimes L}) :
    mszShortBlockValue A k f x (mszShortBlockGridTime k L t) =
      mszFiniteShortBlockValues A k L f x t := by
  rw [mszShortBlockValue, mszShortBlockGridTime_val,
    mszFiniteShortBlockValues]

private theorem dyadicGridTimes_finite (L : ℕ) :
    (dyadicGridTimes L).Finite := by
  refine (Set.finite_range
    (fun m : Fin (2 ^ L + 1) => dyadicGridPoint L m.1)).subset ?_
  intro t ht
  rcases ht with ⟨m, hm, rfl⟩
  exact ⟨⟨m, by omega⟩, rfl⟩

private def mszShortBlockGridSet (k : ℤ) (L : ℕ) :
    Set (MSZShortBlockTime k) := Set.range (mszShortBlockGridTime k L)

private theorem mszDyadicGridPoint_refine (L m : ℕ) :
    dyadicGridPoint L m = dyadicGridPoint (L + 1) (2 * m) := by
  unfold dyadicGridPoint
  push_cast
  rw [pow_succ]
  field_simp

private theorem mszShortBlockGridSet_mono (k : ℤ) (L : ℕ) :
    mszShortBlockGridSet k L ⊆ mszShortBlockGridSet k (L + 1) := by
  rintro y ⟨t, hty⟩
  let m := mszDyadicGridPointIndex L t
  have hm : m ≤ 2 ^ L := (mszDyadicGridPointIndex_spec L t).1
  have hpoint : dyadicGridPoint L m = t.1 :=
    (mszDyadicGridPointIndex_spec L t).2
  have hhm : 2 * m ≤ 2 ^ (L + 1) := by
    calc
      2 * m ≤ 2 * 2 ^ L := Nat.mul_le_mul_left 2 hm
      _ = 2 ^ (L + 1) := by rw [pow_succ]; ring
  let t' : {t : ℚ // t ∈ dyadicGridTimes (L + 1)} :=
    ⟨dyadicGridPoint (L + 1) (2 * m), ⟨2 * m, hhm, rfl⟩⟩
  have hnorm : t.1 = t'.1 := by
    calc
      t.1 = dyadicGridPoint L m := hpoint.symm
      _ = dyadicGridPoint (L + 1) (2 * m) := mszDyadicGridPoint_refine L m
      _ = t'.1 := rfl
  have htime : mszGridTimeAffine k L t =
      mszGridTimeAffine k (L + 1) t' := by
    apply Subtype.ext
    rw [mszGridTimeAffine_val, mszGridTimeAffine_val, hnorm]
  have hgrid : mszShortBlockGridTime k L t =
      mszShortBlockGridTime k (L + 1) t' := by
    apply Subtype.ext
    rw [mszShortBlockGridTime_val, mszShortBlockGridTime_val]
    exact htime
  rw [← hty, hgrid]
  exact ⟨t', rfl⟩

private noncomputable def mszShortBlockGridExhaustion (k : ℤ) :
    Set.FiniteExhaustion (Set.univ : Set (MSZShortBlockTime k)) where
  toFun := mszShortBlockGridSet k
  finite' L := by
    haveI : Finite {t : ℚ // t ∈ dyadicGridTimes L} :=
      (dyadicGridTimes_finite L).to_subtype
    exact Set.finite_range (mszShortBlockGridTime k L)
  subset_succ' := mszShortBlockGridSet_mono k
  iUnion_eq' := by
    ext t
    constructor
    · intro ht
      exact Set.mem_univ t
    · intro ht
      rcases mszShortBlockTime_mem_some_grid k t.1 t.2 with
        ⟨L, m, hm, htime⟩
      let u : {t : ℚ // t ∈ dyadicGridTimes L} :=
        ⟨dyadicGridPoint L m, ⟨m, hm, rfl⟩⟩
      have hgrid : mszShortBlockGridTime k L u = t := by
        apply Subtype.ext
        rw [mszShortBlockGridTime_val]
        exact (mszGridTimeAffine_eq_gridTime k L m hm).trans htime
      exact Set.mem_iUnion.mpr ⟨L, ⟨u, hgrid⟩⟩

private noncomputable def mszShortBlockGridTimeOrderIso
    (k : ℤ) (L : ℕ) :
    {t : ℚ // t ∈ dyadicGridTimes L} ≃o
      {t : MSZShortBlockTime k // t ∈ mszShortBlockGridSet k L} := by
  let f : {t : ℚ // t ∈ dyadicGridTimes L} →
      {t : MSZShortBlockTime k // t ∈ mszShortBlockGridSet k L} :=
    fun t => ⟨mszShortBlockGridTime k L t, ⟨t, rfl⟩⟩
  have hf : StrictMono f := by
    intro a b hab
    exact mszShortBlockGridTime_strictMono k L hab
  have hsurj : Function.Surjective f := by
    intro y
    rcases y.2 with ⟨t, hty⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    exact hty
  exact hf.orderIsoOfSurjective f hsurj

private theorem finiteChainVariation_two_eq_sqrt
    {I : Type*} [LinearOrder I] {n : ℕ} (u : I → ℂ)
    (chain : StrictOrderedChain I n) :
    finiteChainVariation 2 u chain =
      ENNReal.ofReal (Real.sqrt (∑ i : Fin n,
        ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ^ 2)) := by
  unfold finiteChainVariation
  have hterm (i : Fin n) :
      (ENNReal.ofReal ‖u (chain.point i.succ) -
        u (chain.point i.castSucc)‖).rpow 2 =
        ENNReal.ofReal (‖u (chain.point i.succ) -
          u (chain.point i.castSucc)‖ ^ 2) := by
    rw [ENNReal.rpow_eq_pow,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
        (by norm_num : 0 ≤ (2 : ℝ))]
    congr 1
    simpa using (Real.rpow_natCast
      (‖u (chain.point i.succ) - u (chain.point i.castSucc)‖) 2)
  have hsum :
      (∑ i : Fin n,
        (ENNReal.ofReal ‖u (chain.point i.succ) -
          u (chain.point i.castSucc)‖).rpow 2) =
        ENNReal.ofReal (∑ i : Fin n,
          ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := fun i : Fin n =>
      ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ^ 2)
      (fun i hi => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i
  have henergy : 0 ≤ ∑ i : Fin n,
      ‖u (chain.point i.succ) - u (chain.point i.castSucc)‖ ^ 2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  rw [hsum, show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num,
    ENNReal.rpow_eq_pow,
    ENNReal.ofReal_rpow_of_nonneg henergy (by norm_num : 0 ≤ (1 / 2 : ℝ)),
    Real.sqrt_eq_rpow]

private theorem orderedRVariation_orderIso_congr
    {I J : Type*} [LinearOrder I] [LinearOrder J]
    (e : I ≃o J) (r : ℝ) (u : I → ℂ) :
    orderedRVariation r u = orderedRVariation r (fun j => u (e.symm j)) := by
  apply le_antisymm
  · unfold orderedRVariation
    apply iSup_le
    intro n
    apply iSup_le
    intro chain
    let chain' : StrictOrderedChain J n :=
      ⟨fun i => e (chain.point i), fun i j hij => e.strictMono (chain.strictMono hij)⟩
    have hvalue : finiteChainVariation r u chain =
        finiteChainVariation r (fun j => u (e.symm j)) chain' := by
      simp [finiteChainVariation, chain']
    rw [hvalue]
    exact le_iSup_of_le n (le_iSup_of_le chain' le_rfl)
  · unfold orderedRVariation
    apply iSup_le
    intro n
    apply iSup_le
    intro chain
    let chain' : StrictOrderedChain I n :=
      ⟨fun i => e.symm (chain.point i),
        fun i j hij => e.symm.strictMono (chain.strictMono hij)⟩
    have hvalue : finiteChainVariation r (fun j => u (e.symm j)) chain =
        finiteChainVariation r u chain' := by
      simp [finiteChainVariation, chain']
    rw [hvalue]
    exact le_iSup_of_le n (le_iSup_of_le chain' le_rfl)

private theorem dyadicGridVariationTwoSubtype_eq_ordered
    (L : ℕ) (g : {t : ℚ // t ∈ dyadicGridTimes L} → ℂ) :
    dyadicGridVariationTwoSubtype L g = orderedRVariation 2 g := by
  classical
  change dyadicGridVariationTwo L (dyadicGridExtend L g) = orderedRVariation 2 g
  unfold dyadicGridVariationTwo orderedRVariation
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro t
    by_cases ht : 0 < n ∧ StrictMono t ∧ ∀ i, t i ∈ dyadicGridTimes L
    · let chain : StrictOrderedChain {t : ℚ // t ∈ dyadicGridTimes L} n :=
        ⟨fun i => ⟨t i, ht.2.2 i⟩,
          fun i j hij => ht.2.1 hij⟩
      rw [dif_pos ht]
      have hvalue : ENNReal.ofReal (Real.sqrt (∑ i : Fin n,
          ‖dyadicGridExtend L g (t i.succ) -
            dyadicGridExtend L g (t i.castSucc)‖ ^ 2)) =
          finiteChainVariation 2 g chain := by
        rw [finiteChainVariation_two_eq_sqrt]
        congr 1
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [dyadicGridExtend_of_mem L g (ht.2.2 i.succ),
          dyadicGridExtend_of_mem L g (ht.2.2 i.castSucc)]
      rw [hvalue]
      exact le_iSup_of_le n (le_iSup_of_le chain le_rfl)
    · simp [ht]
  · apply iSup_le
    intro n
    apply iSup_le
    intro chain
    by_cases hn : 0 < n
    · let t : Fin (n + 1) → ℚ := fun i => (chain.point i).1
      have ht : StrictMono t ∧ ∀ i, t i ∈ dyadicGridTimes L := by
        refine ⟨?_, ?_⟩
        · intro i j hij
          exact chain.strictMono hij
        · intro i
          exact (chain.point i).2
      let h : 0 < n ∧ StrictMono t ∧ ∀ i, t i ∈ dyadicGridTimes L :=
        ⟨hn, ht.1, ht.2⟩
      apply le_iSup_of_le n
      apply le_iSup_of_le t
      rw [dif_pos h]
      have hvalue : finiteChainVariation 2 g chain =
          ENNReal.ofReal (Real.sqrt (∑ i : Fin n,
            ‖dyadicGridExtend L g (t i.succ) -
              dyadicGridExtend L g (t i.castSucc)‖ ^ 2)) := by
        rw [finiteChainVariation_two_eq_sqrt]
        congr 1
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [dyadicGridExtend_of_mem L g (ht.2 i.succ),
          dyadicGridExtend_of_mem L g (ht.2 i.castSucc)]
      rw [hvalue]
    · have hzero : finiteChainVariation 2 g chain = 0 := by
        have hn0 : n = 0 := by omega
        subst n
        simp [finiteChainVariation]
      rw [hzero]
      exact bot_le

private theorem mszSourceShortBlockVariation_eq_iSup_finite
    (A : AdmissibleData) (k : ℤ) (f : ℤ → ℂ) (x : ℤ) :
    mszSourceShortBlockVariation A k f x =
      ⨆ L : ℕ, mszFiniteShortBlockVariation A k L f x := by
  classical
  let K := mszShortBlockGridExhaustion k
  have hfull := orderedRVariation_eq_iSup_trunc K 2
    (mszShortBlockValue A k f x)
  change orderedRVariation 2 (mszShortBlockValue A k f x) = _
  rw [hfull]
  apply iSup_congr
  intro L
  rw [orderedRVariationTrunc_eq_subtype K 2
    (mszShortBlockValue A k f x) L]
  let e := mszShortBlockGridTimeOrderIso k L
  let v : {t : MSZShortBlockTime k // t ∈ mszShortBlockGridSet k L} → ℂ :=
    fun t => mszShortBlockValue A k f x t.1
  have heval : (fun t : {t : ℚ // t ∈ dyadicGridTimes L} => v (e t)) =
      mszFiniteShortBlockValues A k L f x := by
    funext t
    change mszShortBlockValue A k f x (mszShortBlockGridTime k L t) = _
    exact mszShortBlockGridTime_value A k L f x t
  have hiso := orderedRVariation_orderIso_congr e.symm 2 v
  calc
    orderedRVariation 2 v =
        orderedRVariation 2 (fun t : {t : ℚ // t ∈ dyadicGridTimes L} =>
          v (e t)) := by simpa [e] using hiso
    _ = orderedRVariation 2 (mszFiniteShortBlockValues A k L f x) := by
          rw [heval]
    _ = mszFiniteShortBlockVariation A k L f x :=
          (dyadicGridVariationTwoSubtype_eq_ordered L
            (mszFiniteShortBlockValues A k L f x)).symm

private theorem mszFiniteShortBlockVariation_refine
    (A : AdmissibleData) (k : ℤ) (L : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    mszFiniteShortBlockVariation A k L f x ≤
      mszFiniteShortBlockVariation A k (L + 1) f x := by
  let g : ℚ → ℂ := dyadicGridExtend L (mszFiniteShortBlockValues A k L f x)
  let g' : ℚ → ℂ :=
    dyadicGridExtend (L + 1) (mszFiniteShortBlockValues A k (L + 1) f x)
  have heval (m : ℕ) (hm : m ≤ 2 ^ L) :
      g (dyadicGridPoint L m) =
        g' (dyadicGridPoint (L + 1) (2 * m)) := by
    have hhm : 2 * m ≤ 2 ^ (L + 1) := by
      calc
        2 * m ≤ 2 * 2 ^ L := Nat.mul_le_mul_left 2 hm
        _ = 2 ^ (L + 1) := by rw [pow_succ]; ring
    have hpoint : dyadicGridPoint L m =
        dyadicGridPoint (L + 1) (2 * m) := by
      unfold dyadicGridPoint
      push_cast
      rw [pow_succ]
      field_simp
    have htime : mszGridTime k L m =
        mszGridTime k (L + 1) (2 * m) := by
      simpa [Nat.mul_comm] using (mszGridTime_refine_start k L m 1).symm
    have hmem : dyadicGridPoint L m ∈ dyadicGridTimes L := ⟨m, hm, rfl⟩
    have hmem' : dyadicGridPoint (L + 1) (2 * m) ∈
        dyadicGridTimes (L + 1) := ⟨2 * m, hhm, rfl⟩
    change dyadicGridExtend L (mszFiniteShortBlockValues A k L f x)
        (dyadicGridPoint L m) =
      dyadicGridExtend (L + 1)
        (mszFiniteShortBlockValues A k (L + 1) f x)
        (dyadicGridPoint (L + 1) (2 * m))
    rw [dyadicGridExtend_of_mem L _ hmem,
      dyadicGridExtend_of_mem (L + 1) _ hmem',
      mszFiniteShortBlockValues_gridPoint A k L m f x hm,
      mszFiniteShortBlockValues_gridPoint A k (L + 1) (2 * m) f x hhm,
      htime]
  have hindex :
      dyadicGridVariationTwoIndex L g ≤
        dyadicGridVariationTwoIndex (L + 1) g' := by
    unfold dyadicGridVariationTwoIndex
    apply iSup_le
    intro N
    apply iSup_le
    intro u
    by_cases h : 0 < N ∧ StrictMono u ∧ ∀ i, u i ≤ 2 ^ L
    · let v : Fin (N + 1) → ℕ := fun i => 2 * u i
      have hvStrict : StrictMono v := by
        intro i j hij
        exact Nat.mul_lt_mul_of_pos_left (h.2.1 hij) (by norm_num)
      have hvBound : ∀ i, v i ≤ 2 ^ (L + 1) := by
        intro i
        dsimp [v]
        calc
          2 * u i ≤ 2 * 2 ^ L := Nat.mul_le_mul_left 2 (h.2.2 i)
          _ = 2 ^ (L + 1) := by rw [pow_succ]; ring
      have hv : 0 < N ∧ StrictMono v ∧ ∀ i, v i ≤ 2 ^ (L + 1) :=
        ⟨h.1, hvStrict, hvBound⟩
      apply le_iSup_of_le N
      apply le_iSup_of_le v
      rw [dif_pos h, dif_pos hv]
      apply ENNReal.ofReal_le_ofReal
      have hsum :
          (∑ i : Fin N,
            ‖g (dyadicGridPoint L (u i.succ)) -
              g (dyadicGridPoint L (u i.castSucc))‖ ^ 2) =
          ∑ i : Fin N,
            ‖g' (dyadicGridPoint (L + 1) (v i.succ)) -
              g' (dyadicGridPoint (L + 1) (v i.castSucc))‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [show g' (dyadicGridPoint (L + 1) (v i.succ)) =
            g (dyadicGridPoint L (u i.succ)) by
              simpa [v] using (heval (u i.succ) (h.2.2 i.succ)).symm,
          show g' (dyadicGridPoint (L + 1) (v i.castSucc)) =
            g (dyadicGridPoint L (u i.castSucc)) by
              simpa [v] using (heval (u i.castSucc) (h.2.2 i.castSucc)).symm]
      rw [hsum]
    · have hzero :
        (if h : 0 < N ∧ StrictMono u ∧ ∀ i, u i ≤ 2 ^ L then
          ENNReal.ofReal (Real.sqrt (∑ i : Fin N,
            ‖g (dyadicGridPoint L (u i.succ)) -
              g (dyadicGridPoint L (u i.castSucc))‖ ^ 2)) else 0) = 0 := by
          simp [h]
      rw [hzero]
      exact bot_le
  change dyadicGridVariationTwo L g ≤ dyadicGridVariationTwo (L + 1) g'
  rw [dyadicGridVariationTwo_eq_index, dyadicGridVariationTwo_eq_index]
  exact hindex

private theorem mszFiniteShortVariation_mono_K
    (A : AdmissibleData) (K K' L : ℕ) (f : ℤ → ℂ) (x : ℤ)
    (hKK' : K ≤ K') :
    mszFiniteShortVariation A K L f x ≤ mszFiniteShortVariation A K' L f x := by
  have hset : Finset.Icc (-(K : ℤ)) (K : ℤ) ⊆
      Finset.Icc (-(K' : ℤ)) (K' : ℤ) := by
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hlo, hhi⟩
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum :
      (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (mszFiniteShortBlockVariation A k L f x).toReal ^ 2) ≤
      ∑ k ∈ Finset.Icc (-(K' : ℤ)) (K' : ℤ),
        (mszFiniteShortBlockVariation A k L f x).toReal ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hset
    intro k hk hnot
    exact sq_nonneg _
  unfold mszFiniteShortVariation
  exact Real.sqrt_le_sqrt hsum

private theorem mszFiniteShortVariation_mono_L
    (A : AdmissibleData) (K L L' : ℕ) (f : ℤ → ℂ) (x : ℤ)
    (hLL' : L ≤ L') :
    mszFiniteShortVariation A K L f x ≤ mszFiniteShortVariation A K L' f x := by
  have hblock (k : ℤ) :
      (mszFiniteShortBlockVariation A k L f x).toReal ≤
        (mszFiniteShortBlockVariation A k L' f x).toReal := by
    have hiter (n : ℕ) :
        (mszFiniteShortBlockVariation A k L f x).toReal ≤
          (mszFiniteShortBlockVariation A k (L + n) f x).toReal := by
      induction n with
      | zero => exact le_rfl
      | succ n ih =>
        apply ih.trans
        exact ENNReal.toReal_mono
          (mszFiniteShortBlockVariation_ne_top A k (L + n + 1) f x)
          (by simpa [Nat.add_assoc] using
            mszFiniteShortBlockVariation_refine A k (L + n) f x)
    have hsumNat : L + (L' - L) = L' := Nat.add_sub_of_le hLL'
    simpa [hsumNat] using hiter (L' - L)
  have hterm (k : ℤ) (hk : k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)) :
      (mszFiniteShortBlockVariation A k L f x).toReal ^ 2 ≤
        (mszFiniteShortBlockVariation A k L' f x).toReal ^ 2 := by
    have hleft : 0 ≤ (mszFiniteShortBlockVariation A k L f x).toReal :=
      ENNReal.toReal_nonneg
    have hright : 0 ≤ (mszFiniteShortBlockVariation A k L' f x).toReal :=
      ENNReal.toReal_nonneg
    exact (sq_le_sq₀ hleft hright).2 (hblock k)
  have hsum :
      (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (mszFiniteShortBlockVariation A k L f x).toReal ^ 2) ≤
      ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (mszFiniteShortBlockVariation A k L' f x).toReal ^ 2 := by
    apply Finset.sum_le_sum
    intro k hk
    exact hterm k hk
  unfold mszFiniteShortVariation
  exact Real.sqrt_le_sqrt hsum

private theorem mszFiniteShortVariation_mono_diagonal
    (A : AdmissibleData) (n m : ℕ) (f : ℤ → ℂ) (x : ℤ)
    (hnm : n ≤ m) :
    mszFiniteShortVariation A n n f x ≤
      mszFiniteShortVariation A m m f x := by
  exact (mszFiniteShortVariation_mono_K A n m n f x hnm).trans
    (mszFiniteShortVariation_mono_L A m n m f x hnm)

private theorem mszFiniteShortBlockVariation_mono_L
    (A : AdmissibleData) (k : ℤ) (L L' : ℕ) (f : ℤ → ℂ) (x : ℤ)
    (hLL' : L ≤ L') :
    mszFiniteShortBlockVariation A k L f x ≤
      mszFiniteShortBlockVariation A k L' f x := by
  have hiter (n : ℕ) :
      mszFiniteShortBlockVariation A k L f x ≤
        mszFiniteShortBlockVariation A k (L + n) f x := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      apply ih.trans
      simpa [Nat.add_assoc] using
        mszFiniteShortBlockVariation_refine A k (L + n) f x
  have hsum : L + (L' - L) = L' := Nat.add_sub_of_le hLL'
  simpa [hsum] using hiter (L' - L)

/-- The exact source short-variation square function, first truncated to the
blocks `-K ≤ k ≤ K`, with each block carrying its full ordered variation on
the closed MSZ time interval `[2^k,2^(k+1)]`.  The outer supremum exhausts all
integer blocks; the inner block variations already range over every finite
chain of source times. -/
noncomputable def mszSourceShortVariation
    (A : AdmissibleData) (f : ℤ → ℂ) : ℤ → ℝ≥0∞ :=
  fun x => ⨆ K : ℕ,
    (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (mszSourceShortBlockVariation A k f x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

private noncomputable def mszSourceFiniteShortVariation
    (A : AdmissibleData) (K : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
    (mszSourceShortBlockVariation A k f x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

private theorem mszFiniteShortVariation_ofReal
    (A : AdmissibleData) (K L : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    ENNReal.ofReal (mszFiniteShortVariation A K L f x) =
      (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (mszFiniteShortBlockVariation A k L f x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  classical
  let s := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let energy : ℝ := ∑ k ∈ s,
    (mszFiniteShortBlockVariation A k L f x).toReal ^ 2
  have henergy : 0 ≤ energy := by
    dsimp [energy]
    exact Finset.sum_nonneg fun k hk => sq_nonneg _
  have hterm (k : ℤ) (hk : k ∈ s) :
      ENNReal.ofReal ((mszFiniteShortBlockVariation A k L f x).toReal ^ 2) =
        (mszFiniteShortBlockVariation A k L f x) ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg 2,
      ENNReal.ofReal_toReal
        (mszFiniteShortBlockVariation_ne_top A k L f x)]
    exact (ENNReal.rpow_natCast _ 2).symm
  have hsum : ENNReal.ofReal energy =
      ∑ k ∈ s, (mszFiniteShortBlockVariation A k L f x) ^ (2 : ℝ) := by
    dsimp [energy]
    rw [ENNReal.ofReal_sum_of_nonneg (s := s)
      (f := fun k : ℤ => (mszFiniteShortBlockVariation A k L f x).toReal ^ 2)
      (fun k hk => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k hk
  change ENNReal.ofReal (Real.sqrt energy) = _
  rw [Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg henergy
      (by norm_num : 0 ≤ (1 / 2 : ℝ)),
    hsum]

private theorem mszSourceShortBlockVariation_rpow_two_eq_iSup_finite
    (A : AdmissibleData) (k : ℤ) (f : ℤ → ℂ) (x : ℤ) :
    (mszSourceShortBlockVariation A k f x) ^ (2 : ℝ) =
      ⨆ L : ℕ, (mszFiniteShortBlockVariation A k L f x) ^ (2 : ℝ) := by
  rw [mszSourceShortBlockVariation_eq_iSup_finite]
  change ENNReal.orderIsoRpow 2 (by norm_num : 0 < (2 : ℝ))
      (⨆ L : ℕ, mszFiniteShortBlockVariation A k L f x) = _
  rw [OrderIso.map_iSup]
  simp only [ENNReal.orderIsoRpow_apply]

private theorem mszSourceFiniteShortVariation_eq_iSup_grid
    (A : AdmissibleData) (K : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    mszSourceFiniteShortVariation A K f x =
      ⨆ L : ℕ, ENNReal.ofReal (mszFiniteShortVariation A K L f x) := by
  classical
  let s := Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hblock_mono (k : ℤ) : Monotone fun L : ℕ =>
      (mszFiniteShortBlockVariation A k L f x) ^ (2 : ℝ) := by
    intro L L' hLL'
    have h := ENNReal.rpow_le_rpow
      (mszFiniteShortBlockVariation_mono_L A k L L' f x hLL')
      (by norm_num : 0 ≤ (2 : ℝ))
    exact h
  calc
    mszSourceFiniteShortVariation A K f x =
        (∑ k ∈ s,
          ⨆ L : ℕ, (mszFiniteShortBlockVariation A k L f x) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := by
            unfold mszSourceFiniteShortVariation
            congr 1
            apply Finset.sum_congr rfl
            intro k hk
            exact mszSourceShortBlockVariation_rpow_two_eq_iSup_finite A k f x
    _ = (⨆ L : ℕ, ∑ k ∈ s,
          (mszFiniteShortBlockVariation A k L f x) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := by
            congr 2
            exact ENNReal.finsetSum_iSup_of_monotone (s := s)
              (f := fun k L => (mszFiniteShortBlockVariation A k L f x) ^ (2 : ℝ))
              hblock_mono
    _ = ⨆ L : ℕ,
          (∑ k ∈ s,
            (mszFiniteShortBlockVariation A k L f x) ^ (2 : ℝ)) ^
            (1 / 2 : ℝ) := by
            change ENNReal.orderIsoRpow (1 / 2 : ℝ)
                (by norm_num : 0 < (1 / 2 : ℝ))
                (⨆ L : ℕ, ∑ k ∈ s,
                  (mszFiniteShortBlockVariation A k L f x) ^ (2 : ℝ)) = _
            rw [OrderIso.map_iSup]
            simp only [ENNReal.orderIsoRpow_apply]
    _ = ⨆ L : ℕ, ENNReal.ofReal (mszFiniteShortVariation A K L f x) := by
          apply iSup_congr
          intro L
          symm
          exact mszFiniteShortVariation_ofReal A K L f x

theorem mszSourceShortVariation_eq_iSup_diagonal
    (A : AdmissibleData) (f : ℤ → ℂ) (x : ℤ) :
    mszSourceShortVariation A f x =
      ⨆ n : ℕ, ENNReal.ofReal (mszFiniteShortVariation A n n f x) := by
  classical
  change (⨆ K : ℕ, mszSourceFiniteShortVariation A K f x) = _
  simp_rw [mszSourceFiniteShortVariation_eq_iSup_grid]
  apply le_antisymm
  · apply iSup_le
    intro K
    apply iSup_le
    intro L
    let N := max K L
    have hKN : K ≤ N := Nat.le_max_left _ _
    have hLN : L ≤ N := Nat.le_max_right _ _
    calc
      ENNReal.ofReal (mszFiniteShortVariation A K L f x) ≤
          ENNReal.ofReal (mszFiniteShortVariation A N L f x) :=
            ENNReal.ofReal_mono
              (mszFiniteShortVariation_mono_K A K N L f x hKN)
      _ ≤ ENNReal.ofReal (mszFiniteShortVariation A N N f x) :=
            ENNReal.ofReal_mono
              (mszFiniteShortVariation_mono_L A N L N f x hLN)
      _ ≤ ⨆ n : ℕ, ENNReal.ofReal (mszFiniteShortVariation A n n f x) :=
            le_iSup_of_le N le_rfl
  · apply iSup_le
    intro n
    exact le_iSup_of_le n (le_iSup_of_le n le_rfl)

/-- The increasing simultaneous finite-grid limit used in the proof of
`lm:main`. The chain-capture lemma below identifies it with the source
short-variation square function over all blocks and all positive dyadic times. -/
noncomputable def mszShortVariationEndpointLimit
    (A : AdmissibleData) (f : ℤ → ℂ) : ℤ → ℝ :=
  fun x => ⨆ n : ℕ, mszFiniteShortVariation A n n f x

/-- For the `ℓ^p` passage, the exact source square function has the same
real-valued coordinates as the simultaneous finite-grid/block limit.  The
block exhaustion theorem captures every finite ordered chain, and the max
index synchronizes the two increasing truncation parameters. -/
theorem mszSourceShortVariation_toReal_eq_endpointLimit
    (A : AdmissibleData) (f : ℤ → ℂ) (x : ℤ) :
    (mszSourceShortVariation A f x).toReal =
      mszShortVariationEndpointLimit A f x := by
  rw [mszSourceShortVariation_eq_iSup_diagonal]
  unfold mszShortVariationEndpointLimit
  rw [ENNReal.toReal_iSup (fun n => ENNReal.ofReal_ne_top)]
  apply iSup_congr
  intro n
  exact ENNReal.toReal_ofReal (Real.sqrt_nonneg _)

private theorem mszShortVariationEndpointLimit_tendsto
    (A : AdmissibleData) (p : ℝ)
    (hp : p = A.q ∨ p = A.q / (A.q - 1))
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) (x : ℤ) :
    Tendsto (fun n : ℕ => mszFiniteShortVariation A n n (f : ℤ → ℂ) x)
      atTop (𝓝 (mszShortVariationEndpointLimit A (f : ℤ → ℂ) x)) := by
  let pENN : ℝ≥0∞ := ENNReal.ofReal p
  let Cvar : ℝ := (Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A) *
      (max (2 * (1 + A.Mq))
        ((2 * (Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A)) ^
          (2 / A.q))) ^ ((2 - A.q) / 2)
  let CENN : ℝ≥0∞ := ENNReal.ofReal Cvar *
      eLpNorm (fun y : ℤ => f y) pENN Measure.count
  have hp0 : pENN ≠ 0 := by
    dsimp [pENN]
    rcases hp with hpq | hpq'
    · rw [hpq]
      exact ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one A.q_gt_one)
    · rw [hpq']
      have hq' : 1 < A.q / (A.q - 1) := by
        rw [lt_div_iff₀ (sub_pos.mpr A.q_gt_one)]
        linarith
      exact ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one hq')
  have hCENN : CENN ≠ ∞ := by
    dsimp [CENN]
    have hpTop : pENN ≠ ∞ := by
      dsimp [pENN]
      exact ENNReal.ofReal_ne_top
    haveI : Fact (1 ≤ pENN) := by
      constructor
      dsimp [pENN]
      rw [← ENNReal.ofReal_one]
      rcases hp with hpq | hpq
      · have hpReal : 1 ≤ p := by
          rw [hpq]
          exact le_of_lt A.q_gt_one
        exact ENNReal.ofReal_le_ofReal hpReal
      · rw [hpq]
        have hq' : 1 < A.q / (A.q - 1) := by
          rw [lt_div_iff₀ (sub_pos.mpr A.q_gt_one)]
          linarith
        exact ENNReal.ofReal_le_ofReal (le_of_lt hq')
    have hmem := memLp_count_of_memlp_seq_finite hp0 hpTop f
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmem.eLpNorm_ne_top
  have hbound (n : ℕ) :
      eLpNorm
          (fun y : ℤ => mszFiniteShortVariation A n n (f : ℤ → ℂ) y)
          pENN Measure.count ≤ CENN := by
    have h := mszFiniteShortVariation_uniform A n n p hp f
    simpa [CENN, Cvar, pENN] using h
  have hpoint (n : ℕ) :
      mszFiniteShortVariation A n n (f : ℤ → ℂ) x ≤ CENN.toReal := by
    have hnonneg :
        0 ≤ mszFiniteShortVariation A n n (f : ℤ → ℂ) x :=
      Real.sqrt_nonneg _
    have hcoord := MeasureTheory.enorm_le_eLpNorm_count
      (fun y : ℤ => mszFiniteShortVariation A n n (f : ℤ → ℂ) y) x hp0
    have hcoord' : ‖mszFiniteShortVariation A n n (f : ℤ → ℂ) x‖ₑ ≤
        eLpNorm
          (fun y : ℤ => mszFiniteShortVariation A n n (f : ℤ → ℂ) y)
          pENN Measure.count := by
      simpa only [enorm_eq_nnnorm] using hcoord
    rw [← ofReal_norm, Real.norm_of_nonneg hnonneg] at hcoord'
    exact (ENNReal.ofReal_le_iff_le_toReal hCENN).mp (hcoord'.trans (hbound n))
  let u : ℕ → ℝ := fun n => mszFiniteShortVariation A n n (f : ℤ → ℂ) x
  have hu_mono : Monotone u := by
    intro n m hnm
    exact mszFiniteShortVariation_mono_diagonal A n m (f : ℤ → ℂ) x hnm
  have hu_bdd : BddAbove (Set.range u) := by
    refine ⟨CENN.toReal, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hpoint n
  have hu_lub : IsLUB (Set.range u) (⨆ n : ℕ, u n) :=
    isLUB_csSup (Set.range_nonempty u) hu_bdd
  have hu_tendsto : Tendsto u atTop (𝓝 (⨆ n : ℕ, u n)) :=
    tendsto_atTop_isLUB hu_mono hu_lub
  simpa [u, mszShortVariationEndpointLimit] using hu_tendsto

/-- The source short-variation endpoint theorem `lm:main`, with each block
using the unrestricted ordered `2`-variation over its exact MSZ time interval.
It uses finite-chain exhaustion and the simultaneous monotone/Fatou limit. -/
theorem shortVariationEndpoints
    (A : AdmissibleData) (p : ℝ)
    (hp : p = A.q ∨ p = A.q / (A.q - 1))
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) :
    eLpNorm
        (fun x : ℤ => (mszSourceShortVariation A (f : ℤ → ℂ) x).toReal)
        (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal
          (1 + (Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A) *
            (max (2 * (1 + A.Mq))
              ((2 * (Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A)) ^
                (2 / A.q))) ^ ((2 - A.q) / 2)) *
        eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count := by
  let pENN : ℝ≥0∞ := ENNReal.ofReal p
  let Cvar : ℝ := (Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A) *
      (max (2 * (1 + A.Mq))
        ((2 * (Real.sqrt 2 * mszLocalizedGridKq A * mszSigmaQ A)) ^
          (2 / A.q))) ^ ((2 - A.q) / 2)
  let CENN : ℝ≥0∞ := ENNReal.ofReal Cvar *
      eLpNorm (fun y : ℤ => f y) pENN Measure.count
  have hbound (n : ℕ) :
      eLpNorm
          (fun y : ℤ => mszFiniteShortVariation A n n (f : ℤ → ℂ) y)
          pENN Measure.count ≤ CENN := by
    have h := mszFiniteShortVariation_uniform A n n p hp f
    simpa [CENN, Cvar, pENN] using h
  have hpoint (x : ℤ) :=
    mszShortVariationEndpointLimit_tendsto A p hp f x
  have hlimit := msz_counting_eLpNorm_le_of_pointwise_limit_core
    (approximant := fun n y =>
      mszFiniteShortVariation A n n (f : ℤ → ℂ) y)
    (limit := mszShortVariationEndpointLimit A (f : ℤ → ℂ))
    CENN hbound hpoint
  have hsource :
      (fun x : ℤ => (mszSourceShortVariation A (f : ℤ → ℂ) x).toReal) =
        mszShortVariationEndpointLimit A (f : ℤ → ℂ) := by
    funext x
    exact mszSourceShortVariation_toReal_eq_endpointLimit A
      (f : ℤ → ℂ) x
  have hsourcebound :
      eLpNorm
          (fun x : ℤ => (mszSourceShortVariation A (f : ℤ → ℂ) x).toReal)
          pENN Measure.count ≤ CENN := by
    rw [hsource]
    exact hlimit
  have hCvar : Cvar ≤ 1 + Cvar := by linarith
  have hcoef : ENNReal.ofReal Cvar ≤ ENNReal.ofReal (1 + Cvar) :=
    ENNReal.ofReal_le_ofReal hCvar
  calc
    _ ≤ CENN := by simpa [CENN, pENN] using hsourcebound
    _ ≤ ENNReal.ofReal (1 + Cvar) *
          eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count := by
            exact mul_le_mul_of_nonneg_right hcoef bot_le
    _ = _ := by rfl

end

end FractionalPrimes.Literature.MSZ

end
