module

public import FractionalPrimes.ScalePartitions
public import FractionalPrimes.VariationBlocks

/-!
# Long/short variation: finite-chain classification

This module begins the blueprint's finite-chain decomposition by assigning
each chain point to a unique sparse block and classifying adjacent edges.
-/

@[expose] public section

namespace FractionalPrimes

open Filter
open scoped ENNReal

noncomputable section

/-- Reindex a finite sum along an injective map by summing over its image. -/
theorem finiteSum_injective_eq_image {n : ℕ} {α : Type*} [DecidableEq α]
    (e : Fin n → α) (he : Function.Injective e) (f : α → ℝ≥0∞) :
    (∑ i : Fin n, f (e i)) =
      ∑ j ∈ (Finset.univ : Finset (Fin n)).image e, f j := by
  classical
  have hinj : Set.InjOn e (↑(Finset.univ : Finset (Fin n))) := by
    intro i _ j _ hij
    exact he hij
  exact (Finset.sum_image (f := f) hinj).symm

/-- Sum over a finite ordered set by its canonical `Fin card` enumeration. -/
theorem finiteSet_sum_eq_fin_card {α : Type*} [LinearOrder α]
    (E : Finset α) (f : α → ℝ≥0∞) :
    (∑ i ∈ E, f i) = ∑ j : Fin E.card, f (E.orderEmbOfFin rfl j) := by
  classical
  have hrange : Set.range (E.orderEmbOfFin (k := E.card) rfl) = E :=
    Finset.range_orderEmbOfFin E rfl
  symm
  apply Finset.sum_bij (fun j _ => E.orderEmbOfFin rfl j)
  · intro j _
    exact Finset.orderEmbOfFin_mem E rfl j
  · intro i _ j _ hij
    exact (E.orderEmbOfFin rfl).injective hij
  · intro x hx
    have hxrange : x ∈ Set.range (E.orderEmbOfFin (k := E.card) rfl) := by
      rw [hrange]
      exact hx
    obtain ⟨j, hj⟩ := Set.mem_range.mp hxrange
    exact ⟨j, by simp [hj]⟩
  · intro j _
    rfl

/-- A pointwise bound passes to powered sums over the image of an injective
finite index map. -/
theorem finiteSum_rpow_le_image {n : ℕ} (e : Fin n → ℕ)
    (he : Function.Injective e) (f : Fin n → ℝ≥0∞) (g : ℕ → ℝ≥0∞)
    (r : ℝ) (hr : 0 ≤ r) (hfg : ∀ i, f i ≤ g (e i)) :
    (∑ i : Fin n, (f i).rpow r) ≤
      ∑ k ∈ (Finset.univ : Finset (Fin n)).image e, (g k).rpow r := by
  calc
    (∑ i : Fin n, (f i).rpow r) ≤
        ∑ i : Fin n, (g (e i)).rpow r :=
      Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hfg i) hr
    _ = ∑ k ∈ (Finset.univ : Finset (Fin n)).image e, (g k).rpow r :=
      finiteSum_injective_eq_image e he (fun k => (g k).rpow r)

/-- For `r ≥ 2`, a finite `ℓ^r` norm of restricted block variations is at
most their `ℓ^2` norm. -/
theorem finiteSparseBlockVariation_rpow_le_two {s : ℕ → Scale}
    (u : Scale → ℂ) {r : ℝ} (hr2 : 2 ≤ r) (t : Finset ℕ) :
    (∑ k ∈ t,
      (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r).rpow r⁻¹ ≤
    (∑ k ∈ t,
      (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) := by
  classical
  let V : ℕ → ℝ≥0∞ := fun k => rVariationOn r u (Set.Icc (s k) (s (k + 1)))
  let W : ℕ → ℝ≥0∞ := fun k => rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))
  have hfirst := finiteENNReal_rpow_sum_mono_exponent (t := t) V
    (by norm_num : 0 < (2 : ℝ)) hr2
  have hmono (k : ℕ) : V k ≤ W k :=
    rVariationOn_mono_exponent (by linarith) hr2 u _
  have hsum : (∑ k ∈ t, (V k).rpow 2) ≤ ∑ k ∈ t, (W k).rpow 2 :=
    Finset.sum_le_sum fun k _ => ENNReal.rpow_le_rpow (hmono k) (by norm_num)
  have hroot := ENNReal.rpow_le_rpow hsum
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
  calc
    (∑ k ∈ t, (V k).rpow r).rpow r⁻¹ ≤
        (∑ k ∈ t, (V k).rpow 2).rpow (1 / 2 : ℝ) := by
          simpa only [ENNReal.rpow_eq_pow, one_div] using hfirst
    _ ≤ (∑ k ∈ t, (W k).rpow 2).rpow (1 / 2 : ℝ) := by
          simpa only [ENNReal.rpow_eq_pow] using hroot

/-- A finite sparse-block square sum is bounded by the full square sum. -/
theorem finiteSparseBlockSquare_le_tsum {s : ℕ → Scale} (u : Scale → ℂ)
    (t : Finset ℕ) :
    (∑ k ∈ t,
      (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow
        (1 / 2 : ℝ) ≤
      (∑' k : ℕ,
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow
        (1 / 2 : ℝ) := by
  have hfinite :
      (∑ k ∈ t,
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2) ≤
      ∑' k : ℕ,
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2 :=
    ENNReal.sum_le_tsum t
  exact ENNReal.rpow_le_rpow hfinite
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))

/-- Minkowski for the finite `ℓʳ` norm of ENNReal-valued vectors. -/
theorem finiteENNReal_rpow_sum_add_le {n : ℕ} {r : ℝ} (hr : 1 ≤ r)
    (f g : Fin n → ℝ≥0∞) :
    (∑ i : Fin n, (f i + g i).rpow r).rpow r⁻¹ ≤
      (∑ i : Fin n, (f i).rpow r).rpow r⁻¹ +
        (∑ i : Fin n, (g i).rpow r).rpow r⁻¹ := by
  simpa only [ENNReal.rpow_eq_pow, one_div] using
    ENNReal.Lp_add_le (Finset.univ : Finset (Fin n)) f g hr

/-- The three-vector form of finite `ℓʳ` Minkowski. -/
theorem finiteENNReal_rpow_sum_add_three_le {n : ℕ} {r : ℝ} (hr : 1 ≤ r)
    (f g h : Fin n → ℝ≥0∞) :
    (∑ i : Fin n, (f i + g i + h i).rpow r).rpow r⁻¹ ≤
      (∑ i : Fin n, (f i).rpow r).rpow r⁻¹ +
        (∑ i : Fin n, (g i).rpow r).rpow r⁻¹ +
          (∑ i : Fin n, (h i).rpow r).rpow r⁻¹ := by
  calc
    (∑ i : Fin n, (f i + g i + h i).rpow r).rpow r⁻¹ ≤
        (∑ i : Fin n, ((f i + g i) + h i).rpow r).rpow r⁻¹ := by
          exact le_rfl
    _ ≤ (∑ i : Fin n, (f i + g i).rpow r).rpow r⁻¹ +
        (∑ i : Fin n, (h i).rpow r).rpow r⁻¹ :=
      finiteENNReal_rpow_sum_add_le hr (fun i => f i + g i) h
    _ ≤ ((∑ i : Fin n, (f i).rpow r).rpow r⁻¹ +
        (∑ i : Fin n, (g i).rpow r).rpow r⁻¹) +
          (∑ i : Fin n, (h i).rpow r).rpow r⁻¹ := by
      gcongr
      exact finiteENNReal_rpow_sum_add_le hr f g

/-- Pointwise three-piece control of the increments of a fixed chain gives
the corresponding finite variation bound. -/
theorem chainVariation_le_three_increment_families {length : ℕ}
    (chain : StrictScaleChain length) (u : Scale → ℂ) {r : ℝ}
    (hr : 1 ≤ r) (A B C : Fin length → ℝ≥0∞)
    (hterm : ∀ i : Fin length,
      ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖ ≤
        A i + B i + C i) :
    chainVariation r u chain ≤
      (∑ i : Fin length, (A i).rpow r).rpow r⁻¹ +
        (∑ i : Fin length, (B i).rpow r).rpow r⁻¹ +
          (∑ i : Fin length, (C i).rpow r).rpow r⁻¹ := by
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hr
  have hsum :
      (∑ i : Fin length,
        (ENNReal.ofReal ‖u (chain.index i.succ) -
          u (chain.index i.castSucc)‖).rpow r) ≤
      ∑ i : Fin length, (A i + B i + C i).rpow r :=
    Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hterm i) (by linarith)
  have hroot := ENNReal.rpow_le_rpow hsum (inv_nonneg.mpr hrpos.le)
  calc
    chainVariation r u chain =
        (∑ i : Fin length,
          (ENNReal.ofReal ‖u (chain.index i.succ) -
            u (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ := rfl
    _ ≤ (∑ i : Fin length, (A i + B i + C i).rpow r).rpow r⁻¹ := hroot
    _ ≤ (∑ i : Fin length, (A i).rpow r).rpow r⁻¹ +
        (∑ i : Fin length, (B i).rpow r).rpow r⁻¹ +
          (∑ i : Fin length, (C i).rpow r).rpow r⁻¹ :=
      finiteENNReal_rpow_sum_add_three_le hr A B C

/-- The sparse block containing a point of a finite scale chain. -/
def chainScaleBlockIndex {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (i : Fin (length + 1)) : ℕ :=
  scaleBlockIndex hs hUnbounded (chain.index i)

/-- Sparse block labels increase weakly along every strict scale chain. -/
theorem chainScaleBlockIndex_monotone {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) :
    Monotone (chainScaleBlockIndex hs hUnbounded chain) := by
  intro i j hij
  exact scaleBlockIndex_monotone hs0 hs hUnbounded
    (chain.strictMono.monotone hij)

/-- Every chain point lies in its assigned half-open sparse block. -/
theorem chainScaleBlockIndex_spec {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (i : Fin (length + 1)) :
    s (chainScaleBlockIndex hs hUnbounded chain i) ≤ chain.index i ∧
      chain.index i < s (chainScaleBlockIndex hs hUnbounded chain i + 1) := by
  exact ⟨scaleBlockIndex_lower hs0 hs hUnbounded (chain.index i),
    scaleBlockIndex_upper hs hUnbounded (chain.index i)⟩

/-- In a crossing between two different blocks, both chain points lie in
their respective closed blocks, and the inserted boundaries are ordered. -/
theorem chainCrossing_bounds {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (i : Fin length)
    {k l : ℕ}
    (hk : chainScaleBlockIndex hs hUnbounded chain i.castSucc = k)
    (hl : chainScaleBlockIndex hs hUnbounded chain i.succ = l)
    (hcross : k < l) :
    s k ≤ chain.index i.castSucc ∧ chain.index i.castSucc ≤ s (k + 1) ∧
      s l ≤ chain.index i.succ ∧ chain.index i.succ ≤ s (l + 1) ∧
        s (k + 1) ≤ s l := by
  have ha := chainScaleBlockIndex_spec hs0 hs hUnbounded chain i.castSucc
  have hb := chainScaleBlockIndex_spec hs0 hs hUnbounded chain i.succ
  rw [hk] at ha
  rw [hl] at hb
  have hboundary : s (k + 1) ≤ s l := hs (Nat.succ_le_of_lt hcross)
  exact ⟨ha.1, le_of_lt ha.2, hb.1, le_of_lt hb.2, hboundary⟩

/-- The first endpoint piece of a crossing increment is controlled by the
variation inside its starting closed sparse block. -/
theorem chainCrossing_leftPiece_le_blockVariation {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (i : Fin length)
    {k l : ℕ}
    (hk : chainScaleBlockIndex hs hUnbounded chain i.castSucc = k)
    (hl : chainScaleBlockIndex hs hUnbounded chain i.succ = l)
    (hcross : k < l) {r : ℝ} (hr : 0 < r) (u : Scale → ℂ) :
    ENNReal.ofReal ‖u (s (k + 1)) - u (chain.index i.castSucc)‖ ≤
      rVariationOn r u (Set.Icc (s k) (s (k + 1))) := by
  have hb := chainCrossing_bounds hs0 hs hUnbounded chain i hk hl hcross
  by_cases hlt : chain.index i.castSucc < s (k + 1)
  · exact enorm_sub_le_rVariationOn hr u (Set.Icc (s k) (s (k + 1))) hlt
      ⟨hb.1, hb.2.1⟩ ⟨hs (Nat.le_succ k), le_rfl⟩
  · have heq : chain.index i.castSucc = s (k + 1) :=
      le_antisymm hb.2.1 (le_of_not_gt hlt)
    simp [heq]

/-- The last endpoint piece of a crossing increment is controlled by the
variation inside its ending closed sparse block. -/
theorem chainCrossing_rightPiece_le_blockVariation {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (i : Fin length)
    {k l : ℕ}
    (hk : chainScaleBlockIndex hs hUnbounded chain i.castSucc = k)
    (hl : chainScaleBlockIndex hs hUnbounded chain i.succ = l)
    (hcross : k < l) {r : ℝ} (hr : 0 < r) (u : Scale → ℂ) :
    ENNReal.ofReal ‖u (chain.index i.succ) - u (s l)‖ ≤
      rVariationOn r u (Set.Icc (s l) (s (l + 1))) := by
  have hb := chainCrossing_bounds hs0 hs hUnbounded chain i hk hl hcross
  by_cases hlt : s l < chain.index i.succ
  · exact enorm_sub_le_rVariationOn hr u (Set.Icc (s l) (s (l + 1))) hlt
      ⟨le_rfl, hs (Nat.le_succ l)⟩ ⟨hb.2.2.1, hb.2.2.2.1⟩
  · have heq : chain.index i.succ = s l :=
      le_antisymm (le_of_not_gt hlt) hb.2.2.1
    simp [heq]

/-- The block interval of an earlier crossing ends no later than the
starting block of a later crossing. -/
theorem chainCrossings_block_order {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    {i j : Fin length} (hij : i < j) {l k' : ℕ}
    (hli : chainScaleBlockIndex hs hUnbounded chain i.succ = l)
    (hkj : chainScaleBlockIndex hs hUnbounded chain j.castSucc = k') :
    l ≤ k' := by
  have hidx : i.succ ≤ j.castSucc := by
    apply Fin.mk_le_mk.mpr
    exact Nat.succ_le_of_lt (Fin.mk_lt_mk.mp hij)
  have hlabels := chainScaleBlockIndex_monotone hs0 hs hUnbounded chain hidx
  rw [hli, hkj] at hlabels
  exact hlabels

/-- The finite set of every edge that moves between sparse blocks. This
includes crossings with coincident inserted boundary scales. -/
noncomputable def chainAllCrossingSet {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) : Finset (Fin length) := by
  classical
  exact Finset.univ.filter (fun i =>
    chainScaleBlockIndex hs hUnbounded chain i.castSucc <
      chainScaleBlockIndex hs hUnbounded chain i.succ)

/-- Membership in the all-crossings family is exactly strict block crossing. -/
theorem mem_chainAllCrossingSet {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (i : Fin length) :
    i ∈ chainAllCrossingSet hs hUnbounded chain ↔
      chainScaleBlockIndex hs hUnbounded chain i.castSucc <
        chainScaleBlockIndex hs hUnbounded chain i.succ := by
  classical
  simp [chainAllCrossingSet]

/-- Starting block indices of all crossings increase strictly. -/
noncomputable def chainAllCrossingStartBlock {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (i : Fin (chainAllCrossingSet hs hUnbounded chain).card) : ℕ :=
  chainScaleBlockIndex hs hUnbounded chain
    ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin rfl i).castSucc

/-- Ending block indices of all crossings increase strictly. -/
noncomputable def chainAllCrossingEndBlock {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (i : Fin (chainAllCrossingSet hs hUnbounded chain).card) : ℕ :=
  chainScaleBlockIndex hs hUnbounded chain
    ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin rfl i).succ

/-- The starting blocks of enumerated all-crossings increase strictly. -/
theorem chainAllCrossingStartBlock_strictMono {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) :
    StrictMono (chainAllCrossingStartBlock hs hUnbounded chain) := by
  classical
  intro i j hij
  let E := chainAllCrossingSet hs hUnbounded chain
  have hi : E.orderEmbOfFin rfl i ∈ E := Finset.orderEmbOfFin_mem E rfl i
  have hj : E.orderEmbOfFin rfl j ∈ E := Finset.orderEmbOfFin_mem E rfl j
  have hcrossi := (mem_chainAllCrossingSet hs hUnbounded chain
    (E.orderEmbOfFin rfl i)).mp hi
  have horder : E.orderEmbOfFin rfl i < E.orderEmbOfFin rfl j :=
    (E.orderEmbOfFin rfl).strictMono hij
  have hblocks := chainCrossings_block_order hs0 hs hUnbounded chain horder rfl rfl
  change chainScaleBlockIndex hs hUnbounded chain
      (E.orderEmbOfFin rfl i).castSucc <
    chainScaleBlockIndex hs hUnbounded chain
      (E.orderEmbOfFin rfl j).castSucc
  exact hcrossi.trans_le hblocks

/-- The ending blocks of enumerated all-crossings increase strictly. -/
theorem chainAllCrossingEndBlock_strictMono {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) :
    StrictMono (chainAllCrossingEndBlock hs hUnbounded chain) := by
  classical
  intro i j hij
  let E := chainAllCrossingSet hs hUnbounded chain
  have hj : E.orderEmbOfFin rfl j ∈ E := Finset.orderEmbOfFin_mem E rfl j
  have hcrossj := (mem_chainAllCrossingSet hs hUnbounded chain
    (E.orderEmbOfFin rfl j)).mp hj
  have horder : E.orderEmbOfFin rfl i < E.orderEmbOfFin rfl j :=
    (E.orderEmbOfFin rfl).strictMono hij
  have hblocks := chainCrossings_block_order hs0 hs hUnbounded chain horder rfl rfl
  change chainScaleBlockIndex hs hUnbounded chain
      (E.orderEmbOfFin rfl i).succ <
    chainScaleBlockIndex hs hUnbounded chain
      (E.orderEmbOfFin rfl j).succ
  exact hblocks.trans_lt hcrossj

/-- Each starting endpoint piece in the all-crossing enumeration is
controlled by the variation of its starting block. -/
theorem chainAllCrossing_leftPiece_blockBound {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (i : Fin (chainAllCrossingSet hs hUnbounded chain).card)
    (u : Scale → ℂ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ‖u (s (chainAllCrossingStartBlock hs hUnbounded chain i + 1)) -
      u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
        rfl i).castSucc)‖ ≤
      rVariationOn r u (Set.Icc
        (s (chainAllCrossingStartBlock hs hUnbounded chain i))
        (s (chainAllCrossingStartBlock hs hUnbounded chain i + 1))) := by
  classical
  let e := (chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin rfl i
  have he : e ∈ chainAllCrossingSet hs hUnbounded chain :=
    Finset.orderEmbOfFin_mem _ _ _
  have hcross := (mem_chainAllCrossingSet hs hUnbounded chain e).mp he
  have hk : chainScaleBlockIndex hs hUnbounded chain e.castSucc =
      chainAllCrossingStartBlock hs hUnbounded chain i := rfl
  have hl : chainScaleBlockIndex hs hUnbounded chain e.succ =
      chainAllCrossingEndBlock hs hUnbounded chain i := rfl
  have hbound := chainCrossing_leftPiece_le_blockVariation hs0 hs hUnbounded
    chain e hk hl hcross hr u
  simpa [e, chainAllCrossingStartBlock] using hbound

/-- Each ending endpoint piece in the all-crossing enumeration is controlled
by the variation of its ending block. -/
theorem chainAllCrossing_rightPiece_blockBound {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (i : Fin (chainAllCrossingSet hs hUnbounded chain).card)
    (u : Scale → ℂ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ‖u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
        rfl i).succ) -
      u (s (chainAllCrossingEndBlock hs hUnbounded chain i))‖ ≤
      rVariationOn r u (Set.Icc
        (s (chainAllCrossingEndBlock hs hUnbounded chain i))
        (s (chainAllCrossingEndBlock hs hUnbounded chain i + 1))) := by
  classical
  let e := (chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin rfl i
  have he : e ∈ chainAllCrossingSet hs hUnbounded chain :=
    Finset.orderEmbOfFin_mem _ _ _
  have hcross := (mem_chainAllCrossingSet hs hUnbounded chain e).mp he
  have hk : chainScaleBlockIndex hs hUnbounded chain e.castSucc =
      chainAllCrossingStartBlock hs hUnbounded chain i := rfl
  have hl : chainScaleBlockIndex hs hUnbounded chain e.succ =
      chainAllCrossingEndBlock hs hUnbounded chain i := rfl
  have hbound := chainCrossing_rightPiece_le_blockVariation hs0 hs hUnbounded
    chain e hk hl hcross hr u
  simpa [e, chainAllCrossingEndBlock] using hbound

/-- The powered sum of starting endpoint pieces is bounded by the powered
block variations over the finite set of starting blocks. -/
theorem chainAllCrossing_leftPiece_sum_le_blockImage {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr : 0 < r) :
    (∑ i : Fin (chainAllCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (s (chainAllCrossingStartBlock hs hUnbounded chain i + 1)) -
        u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).castSucc)‖).rpow r) ≤
      ∑ k ∈ (Finset.univ : Finset
        (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
          (chainAllCrossingStartBlock hs hUnbounded chain),
        (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r := by
  classical
  let e := chainAllCrossingStartBlock hs hUnbounded chain
  let f : Fin (chainAllCrossingSet hs hUnbounded chain).card → ℝ≥0∞ := fun i =>
    ENNReal.ofReal ‖u (s (e i + 1)) - u (chain.index
      ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin rfl i).castSucc)‖
  let g : ℕ → ℝ≥0∞ := fun k => rVariationOn r u (Set.Icc (s k) (s (k + 1)))
  have he : Function.Injective e :=
    (chainAllCrossingStartBlock_strictMono hs0 hs hUnbounded chain).injective
  have hpoint (i : Fin (chainAllCrossingSet hs hUnbounded chain).card) :
      f i ≤ g (e i) := by
    exact chainAllCrossing_leftPiece_blockBound hs0 hs hUnbounded chain i u hr
  have hsum := finiteSum_rpow_le_image e he f g r hr.le hpoint
  simpa [e, f, g] using hsum

/-- The powered sum of ending endpoint pieces is bounded by the powered
block variations over the finite set of ending blocks. -/
theorem chainAllCrossing_rightPiece_sum_le_blockImage {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr : 0 < r) :
    (∑ i : Fin (chainAllCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).succ) -
        u (s (chainAllCrossingEndBlock hs hUnbounded chain i))‖).rpow r) ≤
      ∑ k ∈ (Finset.univ : Finset
        (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
          (chainAllCrossingEndBlock hs hUnbounded chain),
        (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r := by
  classical
  let e := chainAllCrossingEndBlock hs hUnbounded chain
  let f : Fin (chainAllCrossingSet hs hUnbounded chain).card → ℝ≥0∞ := fun i =>
    ENNReal.ofReal ‖u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
      rfl i).succ) - u (s (e i))‖
  let g : ℕ → ℝ≥0∞ := fun k => rVariationOn r u (Set.Icc (s k) (s (k + 1)))
  have he : Function.Injective e :=
    (chainAllCrossingEndBlock_strictMono hs0 hs hUnbounded chain).injective
  have hpoint (i : Fin (chainAllCrossingSet hs hUnbounded chain).card) :
      f i ≤ g (e i) := by
    exact chainAllCrossing_rightPiece_blockBound hs0 hs hUnbounded chain i u hr
  have hsum := finiteSum_rpow_le_image e he f g r hr.le hpoint
  simpa [e, f, g] using hsum

/-- The starting endpoint pieces are bounded in `ℓ^r` by the block
square-function over their starting-block image, for `r ≥ 2`. -/
theorem chainAllCrossing_leftPiece_le_blockSquare {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr2 : 2 ≤ r) :
    (∑ i : Fin (chainAllCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (s (chainAllCrossingStartBlock hs hUnbounded chain i + 1)) -
        u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).castSucc)‖).rpow r).rpow r⁻¹ ≤
      (∑ k ∈ (Finset.univ : Finset
        (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
          (chainAllCrossingStartBlock hs hUnbounded chain),
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) := by
  have hsum := chainAllCrossing_leftPiece_sum_le_blockImage hs0 hs hUnbounded
    chain u r (by linarith)
  have hroot := ENNReal.rpow_le_rpow hsum
    (one_div_nonneg.mpr (by linarith : 0 < r).le)
  have hblocks := finiteSparseBlockVariation_rpow_le_two (s := s) u hr2
    ((Finset.univ : Finset
      (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
        (chainAllCrossingStartBlock hs hUnbounded chain))
  calc
    (∑ i : Fin (chainAllCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (s (chainAllCrossingStartBlock hs hUnbounded chain i + 1)) -
        u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).castSucc)‖).rpow r).rpow r⁻¹ ≤
        (∑ k ∈ (Finset.univ : Finset
          (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
            (chainAllCrossingStartBlock hs hUnbounded chain),
          (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r).rpow r⁻¹ := by
              simpa only [ENNReal.rpow_eq_pow, one_div] using hroot
    _ ≤ (∑ k ∈ (Finset.univ : Finset
          (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
            (chainAllCrossingStartBlock hs hUnbounded chain),
          (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) :=
      hblocks

/-- The ending endpoint pieces are bounded in `ℓ^r` by the block
square-function over their ending-block image, for `r ≥ 2`. -/
theorem chainAllCrossing_rightPiece_le_blockSquare {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr2 : 2 ≤ r) :
    (∑ i : Fin (chainAllCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).succ) -
        u (s (chainAllCrossingEndBlock hs hUnbounded chain i))‖).rpow r).rpow r⁻¹ ≤
      (∑ k ∈ (Finset.univ : Finset
        (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
          (chainAllCrossingEndBlock hs hUnbounded chain),
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) := by
  have hsum := chainAllCrossing_rightPiece_sum_le_blockImage hs0 hs hUnbounded
    chain u r (by linarith)
  have hroot := ENNReal.rpow_le_rpow hsum
    (one_div_nonneg.mpr (by linarith : 0 < r).le)
  have hblocks := finiteSparseBlockVariation_rpow_le_two (s := s) u hr2
    ((Finset.univ : Finset
      (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
        (chainAllCrossingEndBlock hs hUnbounded chain))
  calc
    (∑ i : Fin (chainAllCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).succ) -
        u (s (chainAllCrossingEndBlock hs hUnbounded chain i))‖).rpow r).rpow r⁻¹ ≤
        (∑ k ∈ (Finset.univ : Finset
          (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
            (chainAllCrossingEndBlock hs hUnbounded chain),
          (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r).rpow r⁻¹ := by
              simpa only [ENNReal.rpow_eq_pow, one_div] using hroot
    _ ≤ (∑ k ∈ (Finset.univ : Finset
          (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
            (chainAllCrossingEndBlock hs hUnbounded chain),
          (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) :=
      hblocks

/-- All crossing start pieces are bounded by the global sparse-block square
function. -/
theorem chainAllCrossing_leftPiece_le_globalBlockSquare {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr2 : 2 ≤ r) :
    (∑ i : Fin (chainAllCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (s (chainAllCrossingStartBlock hs hUnbounded chain i + 1)) -
        u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).castSucc)‖).rpow r).rpow r⁻¹ ≤
      (∑' k : ℕ,
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow
        (1 / 2 : ℝ) := by
  let blocks := (Finset.univ : Finset
    (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
      (chainAllCrossingStartBlock hs hUnbounded chain)
  calc
    _ ≤ (∑ k ∈ blocks,
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow
          (1 / 2 : ℝ) := by
            simpa [blocks] using
              chainAllCrossing_leftPiece_le_blockSquare hs0 hs hUnbounded
                chain u r hr2
    _ ≤ _ := finiteSparseBlockSquare_le_tsum u blocks

/-- All crossing end pieces are bounded by the global sparse-block square
function. -/
theorem chainAllCrossing_rightPiece_le_globalBlockSquare {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr2 : 2 ≤ r) :
    (∑ i : Fin (chainAllCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).succ) -
        u (s (chainAllCrossingEndBlock hs hUnbounded chain i))‖).rpow r).rpow r⁻¹ ≤
      (∑' k : ℕ,
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow
        (1 / 2 : ℝ) := by
  let blocks := (Finset.univ : Finset
    (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
      (chainAllCrossingEndBlock hs hUnbounded chain)
  calc
    _ ≤ (∑ k ∈ blocks,
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow
          (1 / 2 : ℝ) := by
            simpa [blocks] using
              chainAllCrossing_rightPiece_le_blockSquare hs0 hs hUnbounded
                chain u r hr2
    _ ≤ _ := finiteSparseBlockSquare_le_tsum u blocks

/-- The two endpoint-piece norms are jointly bounded by twice the block
square function over the union of their starting and ending block images. -/
theorem chainAllCrossing_endpointPieces_le_unionBlockSquare {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr2 : 2 ≤ r) :
    (∑ i : Fin (chainAllCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (s (chainAllCrossingStartBlock hs hUnbounded chain i + 1)) -
        u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).castSucc)‖).rpow r).rpow r⁻¹ +
    (∑ i : Fin (chainAllCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (chain.index ((chainAllCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).succ) -
        u (s (chainAllCrossingEndBlock hs hUnbounded chain i))‖).rpow r).rpow r⁻¹ ≤
      (∑ k ∈ ((Finset.univ : Finset
        (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
          (chainAllCrossingStartBlock hs hUnbounded chain) ∪
        (Finset.univ : Finset
          (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
            (chainAllCrossingEndBlock hs hUnbounded chain)),
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) +
      (∑ k ∈ ((Finset.univ : Finset
        (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
          (chainAllCrossingStartBlock hs hUnbounded chain) ∪
        (Finset.univ : Finset
          (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
            (chainAllCrossingEndBlock hs hUnbounded chain)),
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) := by
  classical
  let startBlocks := (Finset.univ : Finset
    (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
      (chainAllCrossingStartBlock hs hUnbounded chain)
  let endBlocks := (Finset.univ : Finset
    (Fin (chainAllCrossingSet hs hUnbounded chain).card)).image
      (chainAllCrossingEndBlock hs hUnbounded chain)
  let allBlocks := startBlocks ∪ endBlocks
  let V : ℕ → ℝ≥0∞ := fun k =>
    rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))
  have hstartSum : (∑ k ∈ startBlocks, (V k).rpow 2) ≤
      ∑ k ∈ allBlocks, (V k).rpow 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (by intro k _ _; exact bot_le)
  have hendSum : (∑ k ∈ endBlocks, (V k).rpow 2) ≤
      ∑ k ∈ allBlocks, (V k).rpow 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      (by intro k _ _; exact bot_le)
  have hstartRoot := ENNReal.rpow_le_rpow hstartSum
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
  have hendRoot := ENNReal.rpow_le_rpow hendSum
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
  have hleft := chainAllCrossing_leftPiece_le_blockSquare hs0 hs hUnbounded
    chain u r hr2
  have hright := chainAllCrossing_rightPiece_le_blockSquare hs0 hs hUnbounded
    chain u r hr2
  apply add_le_add
  · exact hleft.trans (by simpa [startBlocks, allBlocks, V] using hstartRoot)
  · exact hright.trans (by simpa [endBlocks, allBlocks, V] using hendRoot)

/-- If two entries in the increasing enumeration of a finite set have no
member strictly between them, their indices are consecutive. -/
theorem orderEmbOfFin_succ_of_no_between {α : Type*} [LinearOrder α]
    (t : Finset α) {n : ℕ} (hcard : t.card = n) (i j : Fin n)
    (hij : i < j)
    (hno : ∀ x ∈ t, ¬ (t.orderEmbOfFin hcard i < x ∧
      x < t.orderEmbOfFin hcard j)) :
    j.1 = i.1 + 1 := by
  by_contra hnot
  have hgap : i.1 + 1 < j.1 := by omega
  let m : Fin n := ⟨i.1 + 1, by omega⟩
  have him : i < m := by
    change i.1 < i.1 + 1
    omega
  have hmj : m < j := by
    change i.1 + 1 < j.1
    exact hgap
  have hmem : t.orderEmbOfFin hcard m ∈ t :=
    Finset.orderEmbOfFin_mem t hcard m
  exact hno (t.orderEmbOfFin hcard m) hmem
    ⟨(t.orderEmbOfFin hcard).strictMono him,
      (t.orderEmbOfFin hcard).strictMono hmj⟩

/-- Chain positions assigned to a fixed sparse block. -/
def chainBlockPointSet {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (k : ℕ) :
    Finset (Fin (length + 1)) := by
  classical
  exact Finset.univ.filter (fun j =>
    chainScaleBlockIndex hs hUnbounded chain j = k)

theorem mem_chainBlockPointSet {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (k : ℕ)
    (j : Fin (length + 1)) :
    j ∈ chainBlockPointSet hs hUnbounded chain k ↔
      chainScaleBlockIndex hs hUnbounded chain j = k := by
  classical
  simp [chainBlockPointSet]

/-- Enumerate the chain points assigned to one block as a strict chain. -/
noncomputable def chainBlockPointChain {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (k : ℕ)
    (ht : (chainBlockPointSet hs hUnbounded chain k).Nonempty) :
    StrictScaleChain ((chainBlockPointSet hs hUnbounded chain k).card - 1) := by
  classical
  let t := chainBlockPointSet hs hUnbounded chain k
  have hcard : 1 ≤ t.card := Nat.one_le_iff_ne_zero.mpr
    (Finset.card_ne_zero.mpr ht)
  have hsize : t.card - 1 + 1 = t.card := Nat.sub_add_cancel hcard
  refine ⟨fun i => chain.index (t.orderEmbOfFin rfl (Fin.cast hsize i)), ?_⟩
  intro i j hij
  exact chain.strictMono ((t.orderEmbOfFin rfl).strictMono
    ((Fin.cast_lt_cast hsize).2 hij))

/-- Every point of the block subchain lies in its closed sparse block. -/
theorem chainBlockPointChain_mem_interval {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (k : ℕ)
    (ht : (chainBlockPointSet hs hUnbounded chain k).Nonempty)
    (j : Fin ((chainBlockPointSet hs hUnbounded chain k).card - 1 + 1)) :
    (chainBlockPointChain hs hUnbounded chain k ht).index j ∈
      Set.Icc (s k) (s (k + 1)) := by
  classical
  let t := chainBlockPointSet hs hUnbounded chain k
  have hcard : 1 ≤ t.card := Nat.one_le_iff_ne_zero.mpr
    (Finset.card_ne_zero.mpr ht)
  have hsize : t.card - 1 + 1 = t.card := Nat.sub_add_cancel hcard
  have hmem : t.orderEmbOfFin rfl (Fin.cast hsize j) ∈ t :=
    Finset.orderEmbOfFin_mem t rfl (Fin.cast hsize j)
  have hlabel : chainScaleBlockIndex hs hUnbounded chain
      (t.orderEmbOfFin rfl (Fin.cast hsize j)) = k :=
    (mem_chainBlockPointSet hs hUnbounded chain k _).mp hmem
  have hblock := chainScaleBlockIndex_spec hs0 hs hUnbounded chain
    (t.orderEmbOfFin rfl (Fin.cast hsize j))
  change s k ≤ chain.index (t.orderEmbOfFin rfl (Fin.cast hsize j)) ∧
      chain.index (t.orderEmbOfFin rfl (Fin.cast hsize j)) ≤ s (k + 1)
  rw [← hlabel]
  exact ⟨hblock.1, le_of_lt hblock.2⟩

/-- Adjacent chain edges whose two endpoints lie in the same sparse block. -/
def chainBlockEdgeSet {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (k : ℕ) :
    Finset (Fin length) := by
  classical
  exact Finset.univ.filter (fun i =>
    chainScaleBlockIndex hs hUnbounded chain i.castSucc = k ∧
      chainScaleBlockIndex hs hUnbounded chain i.succ = k)

theorem mem_chainBlockEdgeSet {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (k : ℕ)
    (i : Fin length) :
    i ∈ chainBlockEdgeSet hs hUnbounded chain k ↔
      chainScaleBlockIndex hs hUnbounded chain i.castSucc = k ∧
        chainScaleBlockIndex hs hUnbounded chain i.succ = k := by
  classical
  simp [chainBlockEdgeSet]

/-- The rank of a chain position in the ordered finite set of points assigned
to a block. -/
noncomputable def chainBlockPointRank {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (k : ℕ)
    (j : Fin (length + 1))
    (hj : j ∈ chainBlockPointSet hs hUnbounded chain k) :
    Fin (chainBlockPointSet hs hUnbounded chain k).card :=
  ((chainBlockPointSet hs hUnbounded chain k).orderIsoOfFin rfl).symm ⟨j, hj⟩

theorem chainBlockPointRank_value {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (k : ℕ)
    (j : Fin (length + 1))
    (hj : j ∈ chainBlockPointSet hs hUnbounded chain k) :
    (chainBlockPointSet hs hUnbounded chain k).orderEmbOfFin rfl
      (chainBlockPointRank hs hUnbounded chain k j hj) = j := by
  simp [chainBlockPointRank, Finset.orderEmbOfFin]

/-- The two endpoints of a same-block edge are consecutive in the ordered
enumeration of that block's chain points. -/
theorem chainBlockEdge_ranks_succ {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (k : ℕ)
    (i : Fin length) (hi : i ∈ chainBlockEdgeSet hs hUnbounded chain k) :
    (chainBlockPointRank hs hUnbounded chain k i.succ
      ((mem_chainBlockPointSet hs hUnbounded chain k i.succ).2
        ((mem_chainBlockEdgeSet hs hUnbounded chain k i).mp hi).2)).1 =
      (chainBlockPointRank hs hUnbounded chain k i.castSucc
        ((mem_chainBlockPointSet hs hUnbounded chain k i.castSucc).2
          ((mem_chainBlockEdgeSet hs hUnbounded chain k i).mp hi).1)).1 + 1 := by
  classical
  let t := chainBlockPointSet hs hUnbounded chain k
  have hlabels := (mem_chainBlockEdgeSet hs hUnbounded chain k i).mp hi
  have hleftMem : i.castSucc ∈ t :=
    (mem_chainBlockPointSet hs hUnbounded chain k i.castSucc).2 hlabels.1
  have hrightMem : i.succ ∈ t :=
    (mem_chainBlockPointSet hs hUnbounded chain k i.succ).2 hlabels.2
  let leftRank := chainBlockPointRank hs hUnbounded chain k i.castSucc
    hleftMem
  let rightRank := chainBlockPointRank hs hUnbounded chain k i.succ
    hrightMem
  have hleft := chainBlockPointRank_value hs hUnbounded chain k i.castSucc
    hleftMem
  have hright := chainBlockPointRank_value hs hUnbounded chain k i.succ
    hrightMem
  have hpos : i.castSucc < i.succ := Fin.castSucc_lt_succ
  have hlt : leftRank < rightRank := by
    by_contra hnot
    have hle : rightRank ≤ leftRank := le_of_not_gt hnot
    have hlePos := (t.orderEmbOfFin rfl).monotone hle
    rw [hright, hleft] at hlePos
    exact (not_le_of_gt hpos) hlePos
  have hno : ∀ x ∈ t, ¬ (t.orderEmbOfFin rfl leftRank < x ∧
      x < t.orderEmbOfFin rfl rightRank) := by
    intro x hx hbetween
    rw [hleft, hright] at hbetween
    change i.1 < x.1 ∧ x.1 < i.1 + 1 at hbetween
    omega
  exact orderEmbOfFin_succ_of_no_between t rfl leftRank rightRank hlt hno

/-- The local-chain edge corresponding to a same-block edge. -/
noncomputable def chainBlockLocalEdgeIndex {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (k : ℕ)
    (i : Fin length) (hi : i ∈ chainBlockEdgeSet hs hUnbounded chain k) :
    Fin ((chainBlockPointSet hs hUnbounded chain k).card - 1) := by
  classical
  let hlabels := (mem_chainBlockEdgeSet hs hUnbounded chain k i).mp hi
  let hleftMem :=
    (mem_chainBlockPointSet hs hUnbounded chain k i.castSucc).2 hlabels.1
  let hrightMem :=
    (mem_chainBlockPointSet hs hUnbounded chain k i.succ).2 hlabels.2
  let leftRank := chainBlockPointRank hs hUnbounded chain k i.castSucc hleftMem
  let rightRank := chainBlockPointRank hs hUnbounded chain k i.succ hrightMem
  have hsucc := chainBlockEdge_ranks_succ hs hUnbounded chain k i hi
  have hright := rightRank.isLt
  rw [hsucc] at hright
  exact ⟨leftRank.1, by omega⟩

/-- A same-block edge is the corresponding consecutive increment in the
enumerated local chain. -/
theorem chainBlockLocalEdgeIndex_endpoints {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (k : ℕ)
    (ht : (chainBlockPointSet hs hUnbounded chain k).Nonempty)
    (i : Fin length) (hi : i ∈ chainBlockEdgeSet hs hUnbounded chain k) :
    (chainBlockPointChain hs hUnbounded chain k
      ht).index
        (chainBlockLocalEdgeIndex hs hUnbounded chain k i hi).castSucc =
        chain.index i.castSucc ∧
      (chainBlockPointChain hs hUnbounded chain k
        ht).index
        (chainBlockLocalEdgeIndex hs hUnbounded chain k i hi).succ =
        chain.index i.succ := by
  classical
  let t := chainBlockPointSet hs hUnbounded chain k
  let hlabels := (mem_chainBlockEdgeSet hs hUnbounded chain k i).mp hi
  have hleftMem : i.castSucc ∈ t :=
    (mem_chainBlockPointSet hs hUnbounded chain k i.castSucc).2 hlabels.1
  have hrightMem : i.succ ∈ t :=
    (mem_chainBlockPointSet hs hUnbounded chain k i.succ).2 hlabels.2
  have hcard : 1 ≤ t.card := Nat.one_le_iff_ne_zero.mpr
    (Finset.card_ne_zero.mpr ht)
  have hsize : t.card - 1 + 1 = t.card := Nat.sub_add_cancel hcard
  let leftRank := chainBlockPointRank hs hUnbounded chain k i.castSucc hleftMem
  let rightRank := chainBlockPointRank hs hUnbounded chain k i.succ hrightMem
  let e := chainBlockLocalEdgeIndex hs hUnbounded chain k i hi
  have hstep : rightRank.1 = leftRank.1 + 1 := by
    exact chainBlockEdge_ranks_succ hs hUnbounded chain k i hi
  have hcastL : Fin.cast hsize e.castSucc = leftRank := by
    apply Fin.ext
    rfl
  have hcastR : Fin.cast hsize e.succ = rightRank := by
    apply Fin.ext
    change e.1 + 1 = rightRank.1
    simp [e, chainBlockLocalEdgeIndex, leftRank, rightRank, hstep]
  have hleftValue := chainBlockPointRank_value hs hUnbounded chain k
    i.castSucc hleftMem
  have hrightValue := chainBlockPointRank_value hs hUnbounded chain k
    i.succ hrightMem
  constructor
  · change chain.index (t.orderEmbOfFin rfl (Fin.cast hsize e.castSucc)) = _
    rw [hcastL, hleftValue]
  · change chain.index (t.orderEmbOfFin rfl (Fin.cast hsize e.succ)) = _
    rw [hcastR, hrightValue]

/-- The powered sum of the original edges contained in one block is bounded
by the variation of the restricted chain formed by that block's points. -/
theorem chainBlockEdge_rpow_sum_le_variation {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (k : ℕ)
    (u : Scale → ℂ) {r : ℝ} (hr : 0 < r)
    (hE : (chainBlockEdgeSet hs hUnbounded chain k).Nonempty) :
    (∑ i ∈ chainBlockEdgeSet hs hUnbounded chain k,
      (ENNReal.ofReal ‖u (chain.index i.succ) -
        u (chain.index i.castSucc)‖).rpow r) ≤
      (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r := by
  classical
  let E := chainBlockEdgeSet hs hUnbounded chain k
  let t := chainBlockPointSet hs hUnbounded chain k
  obtain ⟨i₀, hi₀⟩ := hE
  have hlabels₀ := (mem_chainBlockEdgeSet hs hUnbounded chain k i₀).mp hi₀
  have ht : t.Nonempty := ⟨i₀.castSucc,
    (mem_chainBlockPointSet hs hUnbounded chain k i₀.castSucc).2 hlabels₀.1⟩
  have hcard : 1 ≤ t.card := Nat.one_le_iff_ne_zero.mpr
    (Finset.card_ne_zero.mpr ht)
  have hpos : 0 < t.card - 1 := by
    have hleft : i₀.castSucc ∈ t :=
      (mem_chainBlockPointSet hs hUnbounded chain k i₀.castSucc).2 hlabels₀.1
    have hright : i₀.succ ∈ t :=
      (mem_chainBlockPointSet hs hUnbounded chain k i₀.succ).2 hlabels₀.2
    have hne : i₀.castSucc ≠ i₀.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    have htwo : 1 < t.card := Finset.one_lt_card.mpr
      ⟨i₀.castSucc, hleft, i₀.succ, hright, hne⟩
    omega
  let B := chainBlockPointChain hs hUnbounded chain k ht
  let e : Fin length → Fin (t.card - 1) := fun i =>
    if hi : i ∈ E then chainBlockLocalEdgeIndex hs hUnbounded chain k i hi
    else ⟨0, hpos⟩
  have heval (i : Fin length) (hi : i ∈ E) :
      e i = chainBlockLocalEdgeIndex hs hUnbounded chain k i hi := by
    simp [e, hi]
  have hinj : Set.InjOn e (↑E) := by
    intro i hi j hj hij
    have heq := congrArg (fun a : Fin (t.card - 1) => B.index a.castSucc) hij
    have hleft := (chainBlockLocalEdgeIndex_endpoints hs hUnbounded chain k ht i hi).1
    have hright := (chainBlockLocalEdgeIndex_endpoints hs hUnbounded chain k ht j hj).1
    rw [heval i hi, heval j hj, hleft, hright] at heq
    have hindex : i.castSucc = j.castSucc := chain.strictMono.injective heq
    exact Fin.ext (by simpa using congrArg Fin.val hindex)
  let f : Fin (t.card - 1) → ℝ≥0∞ := fun a =>
    (ENNReal.ofReal ‖u (B.index a.succ) - u (B.index a.castSucc)‖).rpow r
  have hsumImage :
      (∑ i ∈ E,
        (ENNReal.ofReal ‖u (chain.index i.succ) -
          u (chain.index i.castSucc)‖).rpow r) =
        ∑ i ∈ E, f (e i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [heval i hi]
    have hend := chainBlockLocalEdgeIndex_endpoints hs hUnbounded chain k ht i hi
    simp only [f]
    rw [hend.1, hend.2]
  have hImageBound : (∑ i ∈ E, f (e i)) ≤ ∑ a, f a := by
    have hinj' : Set.InjOn e (↑E) := hinj
    calc
      (∑ i ∈ E, f (e i)) = ∑ a ∈ E.image e, f a := by
        symm
        exact Finset.sum_image (f := f) hinj'
      _ ≤ ∑ a, f a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          simp only [Finset.mem_image] at ha
          simp
        · intro a _ _
          exact bot_le
  have hlocal : chainVariation r u B ≤
      rVariationOn r u (Set.Icc (s k) (s (k + 1))) := by
    unfold rVariationOn
    have hmem : ∀ j, B.index j ∈ Set.Icc (s k) (s (k + 1)) := by
      intro j
      exact chainBlockPointChain_mem_interval hs0 hs hUnbounded chain k ht j
    exact le_iSup_of_le (t.card - 1) (le_iSup_of_le B (by simp [hmem]))
  have hrpow := ENNReal.rpow_le_rpow hlocal hr.le
  calc
    (∑ i ∈ E,
        (ENNReal.ofReal ‖u (chain.index i.succ) -
          u (chain.index i.castSucc)‖).rpow r)
      = ∑ i ∈ E, f (e i) := hsumImage
    _ ≤ ∑ a, f a := hImageBound
    _ = (chainVariation r u B).rpow r := by
      change (∑ a : Fin (t.card - 1),
        (ENNReal.ofReal ‖u (B.index a.succ) - u (B.index a.castSucc)‖).rpow r) = _
      rw [chainVariation_eq]
      exact (ENNReal.rpow_inv_rpow hr.ne' _).symm
    _ ≤ (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r := hrpow

/-- Edges whose endpoints receive the same sparse block label. -/
def chainSameBlockEdgeSet {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) : Finset (Fin length) := by
  classical
  exact Finset.univ.filter (fun i =>
    chainScaleBlockIndex hs hUnbounded chain i.castSucc =
      chainScaleBlockIndex hs hUnbounded chain i.succ)

/-- Membership in the finite family of same-block edges. -/
theorem mem_chainSameBlockEdgeSet {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (i : Fin length) :
    i ∈ chainSameBlockEdgeSet hs hUnbounded chain ↔
      chainScaleBlockIndex hs hUnbounded chain i.castSucc =
        chainScaleBlockIndex hs hUnbounded chain i.succ := by
  classical
  simp [chainSameBlockEdgeSet]

/-- A same-block edge belongs to the fixed-block edge family indexed by its
left endpoint label. -/
theorem chainSameBlockEdge_mem_blockSet {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (i : Fin length)
    (hi : i ∈ chainSameBlockEdgeSet hs hUnbounded chain) :
    i ∈ chainBlockEdgeSet hs hUnbounded chain
      (chainScaleBlockIndex hs hUnbounded chain i.castSucc) := by
  have h := (mem_chainSameBlockEdgeSet hs hUnbounded chain i).mp hi
  exact (mem_chainBlockEdgeSet hs hUnbounded chain _ i).mpr ⟨rfl, h.symm⟩

/-- The powered increment sum over all same-block edges is bounded by the
sum of the corresponding restricted block variations. -/
theorem chainSameBlockEdge_sum_le_blockVariations {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) {r : ℝ} (hr : 0 < r) :
    (∑ i ∈ chainSameBlockEdgeSet hs hUnbounded chain,
      (ENNReal.ofReal ‖u (chain.index i.succ) -
        u (chain.index i.castSucc)‖).rpow r) ≤
      ∑ k ∈ Finset.range
        (chainScaleBlockIndex hs hUnbounded chain (Fin.last length) + 1),
        (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r := by
  classical
  let S := chainSameBlockEdgeSet hs hUnbounded chain
  let lastBlock := chainScaleBlockIndex hs hUnbounded chain (Fin.last length)
  let T := Finset.range (lastBlock + 1)
  let g : Fin length → ℕ := fun i =>
    chainScaleBlockIndex hs hUnbounded chain i.castSucc
  let f : Fin length → ℝ≥0∞ := fun i =>
    (ENNReal.ofReal ‖u (chain.index i.succ) -
      u (chain.index i.castSucc)‖).rpow r
  have hmap : ∀ i ∈ S, g i ∈ T := by
    intro i _
    apply Finset.mem_range.mpr
    have hle := chainScaleBlockIndex_monotone hs0 hs hUnbounded chain
      (Fin.le_last i.castSucc)
    exact Nat.lt_succ_of_le hle
  have hgroup := Finset.sum_fiberwise_of_maps_to (s := S) (t := T)
    (g := g) hmap f
  have hfiber (k : ℕ) :
      (∑ i ∈ S with g i = k, f i) =
        ∑ i ∈ chainBlockEdgeSet hs hUnbounded chain k, f i := by
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hiS, hgk⟩
        have hsame := (mem_chainSameBlockEdgeSet hs hUnbounded chain i).mp hiS
        change chainScaleBlockIndex hs hUnbounded chain i.castSucc = k at hgk
        exact (mem_chainBlockEdgeSet hs hUnbounded chain k i).mpr
          ⟨hgk, hsame.symm.trans hgk⟩
      · intro hblock
        have hblock' := (mem_chainBlockEdgeSet hs hUnbounded chain k i).mp hblock
        have hiS := (mem_chainSameBlockEdgeSet hs hUnbounded chain i).mpr
          (hblock'.1.trans hblock'.2.symm)
        exact ⟨hiS, hblock'.1⟩
    · intro i _
      rfl
  have hbound (k : ℕ) :
      (∑ i ∈ S with g i = k, f i) ≤
        (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r := by
    rw [hfiber]
    by_cases hk : (chainBlockEdgeSet hs hUnbounded chain k).Nonempty
    · exact chainBlockEdge_rpow_sum_le_variation hs0 hs hUnbounded chain k u hr hk
    · have hempty : chainBlockEdgeSet hs hUnbounded chain k = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hk
      simp [hempty]
  calc
    (∑ i ∈ S, f i) = ∑ k ∈ T, ∑ i ∈ S with g i = k, f i := by
      exact hgroup.symm
    _ ≤ ∑ k ∈ T,
        (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r :=
      Finset.sum_le_sum fun k hk => hbound k

/-- The same-block increment norm is bounded by the full sparse-block square
function. -/
theorem chainSameBlock_norm_le_sparseBlockSquare {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) {r : ℝ} (hr2 : 2 ≤ r) :
    (∑ i ∈ chainSameBlockEdgeSet hs hUnbounded chain,
      (ENNReal.ofReal ‖u (chain.index i.succ) -
        u (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ ≤
      (∑' k : ℕ,
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) := by
  classical
  let T := Finset.range
    (chainScaleBlockIndex hs hUnbounded chain (Fin.last length) + 1)
  let V : ℕ → ℝ≥0∞ := fun k =>
    rVariationOn r u (Set.Icc (s k) (s (k + 1)))
  let W : ℕ → ℝ≥0∞ := fun k =>
    rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr2
  have hsum := chainSameBlockEdge_sum_le_blockVariations hs0 hs hUnbounded
    chain u hrpos
  have hsumRoot := ENNReal.rpow_le_rpow hsum
    (inv_nonneg.mpr hrpos.le)
  have hblock := finiteSparseBlockVariation_rpow_le_two (s := s) u hr2 T
  have hfinite : (∑ k ∈ T, (W k).rpow 2) ≤ ∑' k : ℕ, (W k).rpow 2 :=
    ENNReal.sum_le_tsum T
  have hfiniteRoot := ENNReal.rpow_le_rpow hfinite
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
  calc
    (∑ i ∈ chainSameBlockEdgeSet hs hUnbounded chain,
      (ENNReal.ofReal ‖u (chain.index i.succ) -
        u (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ ≤
        (∑ k ∈ T, (V k).rpow r).rpow r⁻¹ := by
          simpa [T, V] using hsumRoot
    _ ≤ (∑ k ∈ T, (W k).rpow 2).rpow (1 / 2 : ℝ) := by
          simpa [T, V, W] using hblock
    _ ≤ (∑' k : ℕ, (W k).rpow 2).rpow (1 / 2 : ℝ) := by
          simpa only [ENNReal.rpow_eq_pow] using hfiniteRoot

/-- An injective selection of finite indices contributes at most the full
sum of a nonnegative family. -/
theorem finiteSum_injective_image_le_univ {n m : ℕ}
    (s : Finset (Fin n)) (e : Fin n → Fin m) (he : Set.InjOn e s)
    (f : Fin m → ℝ≥0∞) :
    (∑ i ∈ s, f (e i)) ≤ ∑ j : Fin m, f j := by
  classical
  have hsum : (∑ i ∈ s, f (e i)) = ∑ j ∈ s.image e, f j := by
    exact (Finset.sum_image (f := f) he).symm
  calc
    (∑ i ∈ s, f (e i)) = ∑ j ∈ s.image e, f j := hsum
    _ ≤ ∑ j : Fin m, f j :=
      Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by
        intro j _ _
        exact bot_le)

/-- Enumerate any nonempty finite set of positive scales as a strict chain,
using Mathlib's order-preserving finite-set enumeration. -/
noncomputable def strictScaleChainOfFinset (t : Finset Scale) (ht : t.Nonempty) :
    StrictScaleChain (t.card - 1) := by
  classical
  have hcard : 1 ≤ t.card := Nat.one_le_iff_ne_zero.mpr
    (Finset.card_ne_zero.mpr ht)
  have hsize : t.card - 1 + 1 = t.card := Nat.sub_add_cancel hcard
  refine ⟨fun i => t.orderEmbOfFin rfl (Fin.cast hsize i), ?_⟩
  intro i j hij
  exact (t.orderEmbOfFin rfl).strictMono ((Fin.cast_lt_cast hsize).2 hij)

theorem strictScaleChainOfFinset_index (t : Finset Scale) (ht : t.Nonempty)
    (i : Fin ((t.card - 1) + 1)) :
    (strictScaleChainOfFinset t ht).index i =
      t.orderEmbOfFin rfl
        (Fin.cast (Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ht))) i) := by
  rfl

/-- The finite set of endpoints of a family of ordered intervals. -/
noncomputable def orderedPairEndpointSet {α : Type*} [LinearOrder α] {n : ℕ}
    (a b : Fin n → α) : Finset α := by
  classical
  exact Finset.univ.biUnion (fun i => ({a i, b i} : Finset α))

/-- If both endpoints of every pair come from a sequence, every member of
the finite endpoint set also comes from that sequence. -/
theorem orderedPairEndpointSet_range {α β : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α) (s : β → α)
    (ha : ∀ i, ∃ k, s k = a i) (hb : ∀ i, ∃ k, s k = b i) :
    ∀ x ∈ orderedPairEndpointSet a b, ∃ k, s k = x := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨i, -, hxi⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxi
  rcases hxi with rfl | rfl
  · exact ha i
  · exact hb i

theorem orderedPairEndpointSet_left_mem {α : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α) (i : Fin n) :
    a i ∈ orderedPairEndpointSet a b := by
  classical
  unfold orderedPairEndpointSet
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩

theorem orderedPairEndpointSet_right_mem {α : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α) (i : Fin n) :
    b i ∈ orderedPairEndpointSet a b := by
  classical
  unfold orderedPairEndpointSet
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩

/-- The canonical finite-chain index of a left endpoint in an ordered pair
family. -/
noncomputable def orderedPairLeftIndex {α : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α) (i : Fin n) :
    Fin (orderedPairEndpointSet a b).card :=
  (orderedPairEndpointSet a b).orderIsoOfFin rfl |>.symm
    ⟨a i, orderedPairEndpointSet_left_mem a b i⟩

/-- The canonical finite-chain index of a right endpoint in an ordered pair
family. -/
noncomputable def orderedPairRightIndex {α : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α) (i : Fin n) :
    Fin (orderedPairEndpointSet a b).card :=
  (orderedPairEndpointSet a b).orderIsoOfFin rfl |>.symm
    ⟨b i, orderedPairEndpointSet_right_mem a b i⟩

theorem orderedPairLeftIndex_value {α : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α) (i : Fin n) :
    (orderedPairEndpointSet a b).orderEmbOfFin rfl (orderedPairLeftIndex a b i) = a i := by
  simp [orderedPairLeftIndex, Finset.orderEmbOfFin]

theorem orderedPairRightIndex_value {α : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α) (i : Fin n) :
    (orderedPairEndpointSet a b).orderEmbOfFin rfl (orderedPairRightIndex a b i) = b i := by
  simp [orderedPairRightIndex, Finset.orderEmbOfFin]

/-- If closed intervals occur in order without overlap, no endpoint from the
family lies strictly inside any one of those intervals. -/
theorem orderedPairEndpointSet_no_between {α : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α)
    (hinterval : ∀ i, a i ≤ b i)
    (horder : ∀ i j, i < j → b i ≤ a j) (i : Fin n) :
    ∀ x ∈ orderedPairEndpointSet a b,
      ¬ (a i < x ∧ x < b i) := by
  classical
  intro x hx hbetween
  rcases Finset.mem_biUnion.mp hx with ⟨j, -, hxj⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxj
  rcases hxj with rfl | rfl
  · by_cases hji : j < i
    · have hleft := horder j i hji
      exact (not_lt_of_ge ((hinterval j).trans hleft)) hbetween.1
    · by_cases hij : i < j
      · exact (not_lt_of_ge (horder i j hij)) hbetween.2
      · have hEq : i = j := by omega
        subst j
        exact (lt_irrefl _ hbetween.1)
  · by_cases hji : j < i
    · exact (not_lt_of_ge (horder j i hji)) hbetween.1
    · by_cases hij : i < j
      · have hright := (horder i j hij).trans (hinterval j)
        exact (not_lt_of_ge hright) hbetween.2
      · have hEq : i = j := by omega
        subst j
        exact (lt_irrefl _ hbetween.2)

/-- Every strict interval in a finite ordered family is an adjacent edge in
the increasing enumeration of all family endpoints. -/
theorem orderedPairEndpoints_adjacent {α : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α)
    (hinterval : ∀ i, a i ≤ b i)
    (horder : ∀ i j, i < j → b i ≤ a j)
    (i : Fin n) (hab : a i < b i) :
    ∃ u v : Fin (orderedPairEndpointSet a b).card,
      (orderedPairEndpointSet a b).orderEmbOfFin rfl u = a i ∧
      (orderedPairEndpointSet a b).orderEmbOfFin rfl v = b i ∧
      v.1 = u.1 + 1 := by
  classical
  let t := orderedPairEndpointSet a b
  have ha : a i ∈ t := by
    dsimp [t, orderedPairEndpointSet]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
  have hb : b i ∈ t := by
    dsimp [t, orderedPairEndpointSet]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
  have hrange : Set.range (t.orderEmbOfFin (k := t.card) rfl) = t :=
    Finset.range_orderEmbOfFin t rfl
  have haRange : a i ∈ Set.range (t.orderEmbOfFin (k := t.card) rfl) := by
    rw [hrange]
    exact ha
  have hbRange : b i ∈ Set.range (t.orderEmbOfFin (k := t.card) rfl) := by
    rw [hrange]
    exact hb
  obtain ⟨u, hu⟩ := Set.mem_range.mp haRange
  obtain ⟨v, hv⟩ := Set.mem_range.mp hbRange
  have huv : u < v := by
    by_contra hnot
    have hvu : v ≤ u := le_of_not_gt hnot
    have hle := (t.orderEmbOfFin rfl).monotone hvu
    rw [hv, hu] at hle
    exact (not_le_of_gt hab) hle
  have hno : ∀ x ∈ t, ¬ (t.orderEmbOfFin rfl u < x ∧
      x < t.orderEmbOfFin rfl v) := by
    intro x hx hxbetween
    apply orderedPairEndpointSet_no_between a b hinterval horder i x hx
    rw [← hu, ← hv]
    exact hxbetween
  have hadj := orderEmbOfFin_succ_of_no_between t rfl u v huv hno
  exact ⟨u, v, hu, hv, hadj⟩

/-- The canonical endpoint indices of a strict interval are consecutive. -/
theorem orderedPairIndices_adjacent {α : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α)
    (hinterval : ∀ i, a i ≤ b i)
    (horder : ∀ i j, i < j → b i ≤ a j)
    (i : Fin n) (hab : a i < b i) :
    (orderedPairRightIndex a b i).1 =
      (orderedPairLeftIndex a b i).1 + 1 := by
  obtain ⟨u, v, hu, hv, hadj⟩ :=
    orderedPairEndpoints_adjacent a b hinterval horder i hab
  have hu' : u = orderedPairLeftIndex a b i := by
    apply (orderedPairEndpointSet a b).orderEmbOfFin rfl |>.injective
    rw [hu, orderedPairLeftIndex_value]
  have hv' : v = orderedPairRightIndex a b i := by
    apply (orderedPairEndpointSet a b).orderEmbOfFin rfl |>.injective
    rw [hv, orderedPairRightIndex_value]
  rw [hv', hu'] at hadj
  exact hadj

/-- Strictly ordered nondegenerate intervals have strictly ordered left
endpoint indices in the finite endpoint chain. -/
theorem orderedPairLeftIndex_strictMono {α : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α)
    (hstrict : ∀ i, a i < b i)
    (horder : ∀ i j, i < j → b i ≤ a j) :
    StrictMono (orderedPairLeftIndex a b) := by
  intro i j hij
  have hleft : a i < a j := (hstrict i).trans_le (horder i j hij)
  by_contra hnot
  have hji : orderedPairLeftIndex a b j ≤ orderedPairLeftIndex a b i :=
    le_of_not_gt hnot
  have hright := (orderedPairEndpointSet a b).orderEmbOfFin rfl |>.monotone hji
  rw [orderedPairLeftIndex_value, orderedPairLeftIndex_value] at hright
  exact (not_le_of_gt hleft) hright

/-- The increment index in the endpoint chain corresponding to a strict
interval in an ordered family. -/
noncomputable def orderedPairEdgeIndex {α : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α)
    (hinterval : ∀ i, a i ≤ b i)
    (hstrict : ∀ i, a i < b i)
    (horder : ∀ i j, i < j → b i ≤ a j) (i : Fin n) :
    Fin ((orderedPairEndpointSet a b).card - 1) := by
  have hadj := orderedPairIndices_adjacent a b hinterval horder i (hstrict i)
  have hbound := (orderedPairRightIndex a b i).isLt
  rw [hadj] at hbound
  exact ⟨(orderedPairLeftIndex a b i).1, by omega⟩

/-- The interval-to-edge map is injective because its indices increase
strictly with the ordered intervals. -/
theorem orderedPairEdgeIndex_strictMono {α : Type*} [LinearOrder α]
    {n : ℕ} (a b : Fin n → α)
    (hinterval : ∀ i, a i ≤ b i)
    (hstrict : ∀ i, a i < b i)
    (horder : ∀ i j, i < j → b i ≤ a j) :
    StrictMono (orderedPairEdgeIndex a b hinterval hstrict horder) := by
  intro i j hij
  apply Fin.mk_lt_mk.mpr
  exact Fin.mk_lt_mk.mp
    (orderedPairLeftIndex_strictMono a b hstrict horder hij)

/-- The finite endpoint-chain increment selected by `orderedPairEdgeIndex`
has exactly the original interval endpoints. -/
theorem orderedPairEdgeIndex_chain_endpoints {n : ℕ}
    (a b : Fin n → Scale)
    (hinterval : ∀ i, a i ≤ b i)
    (hstrict : ∀ i, a i < b i)
    (horder : ∀ i j, i < j → b i ≤ a j) (i : Fin n)
    (ht : (orderedPairEndpointSet a b).Nonempty) :
    (strictScaleChainOfFinset (orderedPairEndpointSet a b) ht).index
        (orderedPairEdgeIndex a b hinterval hstrict horder i).castSucc = a i ∧
      (strictScaleChainOfFinset (orderedPairEndpointSet a b) ht).index
        (orderedPairEdgeIndex a b hinterval hstrict horder i).succ = b i := by
  let t := orderedPairEndpointSet a b
  have hsize : t.card - 1 + 1 = t.card :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ht))
  constructor
  · rw [strictScaleChainOfFinset_index]
    have hcast : Fin.cast hsize
        (orderedPairEdgeIndex a b hinterval hstrict horder i).castSucc =
          orderedPairLeftIndex a b i := by
      apply Fin.ext
      rfl
    rw [hcast, orderedPairLeftIndex_value]
  · rw [strictScaleChainOfFinset_index]
    have hadj := orderedPairIndices_adjacent a b hinterval horder i (hstrict i)
    have hcast : Fin.cast hsize
        (orderedPairEdgeIndex a b hinterval hstrict horder i).succ =
          orderedPairRightIndex a b i := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_succ]
      simp [orderedPairEdgeIndex, hadj]
    rw [hcast, orderedPairRightIndex_value]

/-- The sum of the powered increments across a finite ordered family of
strict intervals is bounded by the increment sum of its endpoint chain. -/
theorem orderedPair_rpow_sum_le_endpointChain {n : ℕ} (a b : Fin n → Scale)
    (hinterval : ∀ i, a i ≤ b i)
    (hstrict : ∀ i, a i < b i)
    (horder : ∀ i j, i < j → b i ≤ a j)
    (ht : (orderedPairEndpointSet a b).Nonempty)
    (u : Scale → ℂ) (r : ℝ) :
    (∑ i : Fin n,
      (ENNReal.ofReal ‖u (b i) - u (a i)‖).rpow r) ≤
    ∑ j : Fin ((orderedPairEndpointSet a b).card - 1),
      (ENNReal.ofReal ‖u ((strictScaleChainOfFinset
        (orderedPairEndpointSet a b) ht).index j.succ) -
        u ((strictScaleChainOfFinset
        (orderedPairEndpointSet a b) ht).index j.castSucc)‖).rpow r := by
  let t := orderedPairEndpointSet a b
  let chain := strictScaleChainOfFinset t ht
  let edge := orderedPairEdgeIndex a b hinterval hstrict horder
  let f : Fin (t.card - 1) → ℝ≥0∞ := fun j =>
    (ENNReal.ofReal ‖u (chain.index j.succ) - u (chain.index j.castSucc)‖).rpow r
  have hterm (i : Fin n) :
      f (edge i) = (ENNReal.ofReal ‖u (b i) - u (a i)‖).rpow r := by
    dsimp [f, edge, chain, t]
    have hend := orderedPairEdgeIndex_chain_endpoints a b hinterval hstrict
      horder i ht
    rw [hend.2, hend.1]
  have hinj : Set.InjOn edge (↑(Finset.univ : Finset (Fin n))) := by
    intro i _ j _ hij
    exact (orderedPairEdgeIndex_strictMono a b hinterval hstrict horder).injective hij
  have hsum := finiteSum_injective_image_le_univ
    (Finset.univ : Finset (Fin n)) edge hinj f
  calc
    (∑ i : Fin n, (ENNReal.ofReal ‖u (b i) - u (a i)‖).rpow r) =
        ∑ i : Fin n, f (edge i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact (hterm i).symm
    _ ≤ ∑ j : Fin (t.card - 1), f j := hsum

/-- A finite strict chain whose points lie in the range of a monotone sparse
sequence has variation bounded by the variation along that sequence. The
positive scale `k+1` represents natural sparse index `k`. -/
theorem chainVariation_le_sparseRange_rVariation {length : ℕ}
    (s : ℕ → Scale) (hs : Monotone s) (u : Scale → ℂ)
    (chain : StrictScaleChain length)
    (hrange : ∀ i, ∃ k, s k = chain.index i) (r : ℝ) :
    chainVariation r u chain ≤
      rVariation r (fun K : Scale => u (s (K.1 - 1))) := by
  classical
  let k : Fin (length + 1) → ℕ := fun i => Classical.choose (hrange i)
  have hk (i : Fin (length + 1)) : s (k i) = chain.index i :=
    Classical.choose_spec (hrange i)
  let sparseChain : StrictScaleChain length := {
    index := fun i => ⟨k i + 1, by omega⟩
    strictMono := by
      intro i j hij
      have hki : k i < k j := by
        by_contra hnot
        have hji : k j ≤ k i := by omega
        have hscale := hs hji
        rw [hk j, hk i] at hscale
        exact (not_le_of_gt (chain.strictMono hij)) hscale
      change k i + 1 < k j + 1
      omega
  }
  have hsumEq :
      (∑ i : Fin length,
        (ENNReal.ofReal ‖u (chain.index i.succ) -
          u (chain.index i.castSucc)‖).rpow r) =
      (∑ i : Fin length,
        (ENNReal.ofReal ‖(fun K : Scale => u (s (K.1 - 1)))
          (sparseChain.index i.succ) -
          (fun K : Scale => u (s (K.1 - 1)))
            (sparseChain.index i.castSucc)‖).rpow r) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [sparseChain, Nat.add_sub_cancel]
    rw [hk i.succ, hk i.castSucc]
  calc
    chainVariation r u chain =
        chainVariation r (fun K : Scale => u (s (K.1 - 1))) sparseChain := by
      rw [chainVariation_eq, chainVariation_eq, hsumEq]
    _ ≤ rVariation r (fun K : Scale => u (s (K.1 - 1))) :=
      chainVariation_le_rVariation r
        (fun K : Scale => u (s (K.1 - 1))) sparseChain

/-- If every endpoint in a finite ordered interval family comes from a
monotone sparse sequence, its endpoint-chain variation is bounded by the
sparse-sequence variation. -/
theorem orderedPairEndpointChain_le_sparseVariation {n : ℕ}
    (a b : Fin n → Scale)
    (s : ℕ → Scale) (hs : Monotone s)
    (ha : ∀ i, ∃ k, s k = a i) (hb : ∀ i, ∃ k, s k = b i)
    (ht : (orderedPairEndpointSet a b).Nonempty)
    (u : Scale → ℂ) (r : ℝ) :
    chainVariation r u (strictScaleChainOfFinset
      (orderedPairEndpointSet a b) ht) ≤
      rVariation r (fun K : Scale => u (s (K.1 - 1))) := by
  apply chainVariation_le_sparseRange_rVariation s hs u
    (strictScaleChainOfFinset (orderedPairEndpointSet a b) ht)
  intro i
  have hsize := Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ht))
  rw [strictScaleChainOfFinset_index]
  have hmem :
      (orderedPairEndpointSet a b).orderEmbOfFin rfl
        (Fin.cast hsize i) ∈ orderedPairEndpointSet a b :=
    Finset.orderEmbOfFin_mem _ _ _
  exact orderedPairEndpointSet_range a b s ha hb _ hmem

/-- The variation of a finite ordered interval family is bounded by the
variation of a monotone sparse sequence containing all its endpoints. -/
theorem orderedPairVariation_le_sparseVariation {n : ℕ}
    (a b : Fin n → Scale)
    (hinterval : ∀ i, a i ≤ b i)
    (hstrict : ∀ i, a i < b i)
    (horder : ∀ i j, i < j → b i ≤ a j)
    (s : ℕ → Scale) (hs : Monotone s)
    (ha : ∀ i, ∃ k, s k = a i) (hb : ∀ i, ∃ k, s k = b i)
    (ht : (orderedPairEndpointSet a b).Nonempty)
    (u : Scale → ℂ) (r : ℝ) (hr : 0 < r) :
    (∑ i : Fin n,
      (ENNReal.ofReal ‖u (b i) - u (a i)‖).rpow r).rpow r⁻¹ ≤
      rVariation r (fun K : Scale => u (s (K.1 - 1))) := by
  have hsum := orderedPair_rpow_sum_le_endpointChain a b hinterval hstrict
    horder ht u r
  have hpow := ENNReal.rpow_le_rpow hsum (one_div_nonneg.mpr hr.le)
  calc
    (∑ i : Fin n,
        (ENNReal.ofReal ‖u (b i) - u (a i)‖).rpow r).rpow r⁻¹ ≤
        (∑ j : Fin ((orderedPairEndpointSet a b).card - 1),
          (ENNReal.ofReal ‖u ((strictScaleChainOfFinset
            (orderedPairEndpointSet a b) ht).index j.succ) -
            u ((strictScaleChainOfFinset
            (orderedPairEndpointSet a b) ht).index j.castSucc)‖).rpow r).rpow r⁻¹ := by
              simpa only [ENNReal.rpow_eq_pow, one_div] using hpow
    _ = chainVariation r u (strictScaleChainOfFinset
        (orderedPairEndpointSet a b) ht) := rfl
    _ ≤ rVariation r (fun K : Scale => u (s (K.1 - 1))) :=
      orderedPairEndpointChain_le_sparseVariation a b s hs ha hb ht u r

/-- The finite set of chain edges whose block crossing has a nonzero middle
increment after inserting sparse block endpoints. -/
noncomputable def chainSparseCrossingSet {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) : Finset (Fin length) := by
  classical
  exact Finset.univ.filter (fun i =>
    let k := chainScaleBlockIndex hs hUnbounded chain i.castSucc
    let l := chainScaleBlockIndex hs hUnbounded chain i.succ
    k < l ∧ s (k + 1) < s l)

theorem mem_chainSparseCrossingSet {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (i : Fin length) :
    i ∈ chainSparseCrossingSet hs hUnbounded chain ↔
      chainScaleBlockIndex hs hUnbounded chain i.castSucc <
        chainScaleBlockIndex hs hUnbounded chain i.succ ∧
      s (chainScaleBlockIndex hs hUnbounded chain i.castSucc + 1) <
        s (chainScaleBlockIndex hs hUnbounded chain i.succ) := by
  classical
  simp [chainSparseCrossingSet]

noncomputable def chainSparseCrossingStartBlock {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (i : Fin (chainSparseCrossingSet hs hUnbounded chain).card) : ℕ :=
  chainScaleBlockIndex hs hUnbounded chain
    ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin rfl i).castSucc

noncomputable def chainSparseCrossingEndBlock {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (i : Fin (chainSparseCrossingSet hs hUnbounded chain).card) : ℕ :=
  chainScaleBlockIndex hs hUnbounded chain
    ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin rfl i).succ

/-- Starting block indices of nondegenerate crossings increase strictly. -/
theorem chainSparseCrossingStartBlock_strictMono {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) :
    StrictMono (chainSparseCrossingStartBlock hs hUnbounded chain) := by
  classical
  intro i j hij
  let E := chainSparseCrossingSet hs hUnbounded chain
  have hi : E.orderEmbOfFin rfl i ∈ E := Finset.orderEmbOfFin_mem E rfl i
  have hj : E.orderEmbOfFin rfl j ∈ E := Finset.orderEmbOfFin_mem E rfl j
  have hcrossi := (mem_chainSparseCrossingSet hs hUnbounded chain
    (E.orderEmbOfFin rfl i)).mp hi
  have hcrossj := (mem_chainSparseCrossingSet hs hUnbounded chain
    (E.orderEmbOfFin rfl j)).mp hj
  have horder : E.orderEmbOfFin rfl i < E.orderEmbOfFin rfl j :=
    (E.orderEmbOfFin rfl).strictMono hij
  have hblocks := chainCrossings_block_order hs0 hs hUnbounded chain horder rfl rfl
  change chainScaleBlockIndex hs hUnbounded chain
      (E.orderEmbOfFin rfl i).castSucc <
    chainScaleBlockIndex hs hUnbounded chain
      (E.orderEmbOfFin rfl j).castSucc
  exact hcrossi.1.trans_le hblocks

/-- Ending block indices of nondegenerate crossings increase strictly. -/
theorem chainSparseCrossingEndBlock_strictMono {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) :
    StrictMono (chainSparseCrossingEndBlock hs hUnbounded chain) := by
  classical
  intro i j hij
  let E := chainSparseCrossingSet hs hUnbounded chain
  have hi : E.orderEmbOfFin rfl i ∈ E := Finset.orderEmbOfFin_mem E rfl i
  have hj : E.orderEmbOfFin rfl j ∈ E := Finset.orderEmbOfFin_mem E rfl j
  have hcrossi := (mem_chainSparseCrossingSet hs hUnbounded chain
    (E.orderEmbOfFin rfl i)).mp hi
  have hcrossj := (mem_chainSparseCrossingSet hs hUnbounded chain
    (E.orderEmbOfFin rfl j)).mp hj
  have horder : E.orderEmbOfFin rfl i < E.orderEmbOfFin rfl j :=
    (E.orderEmbOfFin rfl).strictMono hij
  have hblocks := chainCrossings_block_order hs0 hs hUnbounded chain horder rfl rfl
  change chainScaleBlockIndex hs hUnbounded chain
      (E.orderEmbOfFin rfl i).succ <
    chainScaleBlockIndex hs hUnbounded chain
      (E.orderEmbOfFin rfl j).succ
  exact hblocks.trans_lt hcrossj.1

/-- The starting-endpoint piece for a crossing in the finite enumeration is
controlled by the restricted variation of its starting block. -/
theorem chainSparseCrossing_leftPiece_blockBound {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (i : Fin (chainSparseCrossingSet hs hUnbounded chain).card)
    (u : Scale → ℂ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ‖u (s (chainSparseCrossingStartBlock hs hUnbounded chain i + 1)) -
      u (chain.index ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin
        rfl i).castSucc)‖ ≤
      rVariationOn r u (Set.Icc
        (s (chainSparseCrossingStartBlock hs hUnbounded chain i))
        (s (chainSparseCrossingStartBlock hs hUnbounded chain i + 1))) := by
  classical
  let e := (chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin rfl i
  have he : e ∈ chainSparseCrossingSet hs hUnbounded chain :=
    Finset.orderEmbOfFin_mem _ _ _
  have hcross := (mem_chainSparseCrossingSet hs hUnbounded chain e).mp he
  have hk : chainScaleBlockIndex hs hUnbounded chain e.castSucc =
      chainSparseCrossingStartBlock hs hUnbounded chain i := rfl
  have hl : chainScaleBlockIndex hs hUnbounded chain e.succ =
      chainSparseCrossingEndBlock hs hUnbounded chain i := rfl
  have hbound := chainCrossing_leftPiece_le_blockVariation hs0 hs hUnbounded
    chain e hk hl hcross.1 hr u
  simpa [e, chainSparseCrossingStartBlock] using hbound

/-- The ending-endpoint piece for a crossing in the finite enumeration is
controlled by the restricted variation of its ending block. -/
theorem chainSparseCrossing_rightPiece_blockBound {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (i : Fin (chainSparseCrossingSet hs hUnbounded chain).card)
    (u : Scale → ℂ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ‖u (chain.index ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin
        rfl i).succ) -
      u (s (chainSparseCrossingEndBlock hs hUnbounded chain i))‖ ≤
      rVariationOn r u (Set.Icc
        (s (chainSparseCrossingEndBlock hs hUnbounded chain i))
        (s (chainSparseCrossingEndBlock hs hUnbounded chain i + 1))) := by
  classical
  let e := (chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin rfl i
  have he : e ∈ chainSparseCrossingSet hs hUnbounded chain :=
    Finset.orderEmbOfFin_mem _ _ _
  have hcross := (mem_chainSparseCrossingSet hs hUnbounded chain e).mp he
  have hk : chainScaleBlockIndex hs hUnbounded chain e.castSucc =
      chainSparseCrossingStartBlock hs hUnbounded chain i := rfl
  have hl : chainScaleBlockIndex hs hUnbounded chain e.succ =
      chainSparseCrossingEndBlock hs hUnbounded chain i := rfl
  have hbound := chainCrossing_rightPiece_le_blockVariation hs0 hs hUnbounded
    chain e hk hl hcross.1 hr u
  simpa [e, chainSparseCrossingEndBlock] using hbound

/-- The powered sum of starting endpoint pieces is bounded by the sum of
powered block variations over the finite set of starting blocks. -/
theorem chainSparseCrossing_leftPiece_sum_le_blockImage {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr : 0 < r) :
    (∑ i : Fin (chainSparseCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (s (chainSparseCrossingStartBlock hs hUnbounded chain i + 1)) -
        u (chain.index ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).castSucc)‖).rpow r) ≤
      ∑ k ∈ (Finset.univ : Finset
        (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
          (chainSparseCrossingStartBlock hs hUnbounded chain),
        (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r := by
  classical
  let e := chainSparseCrossingStartBlock hs hUnbounded chain
  let f : Fin (chainSparseCrossingSet hs hUnbounded chain).card → ℝ≥0∞ := fun i =>
    ENNReal.ofReal ‖u (s (e i + 1)) - u (chain.index
      ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin rfl i).castSucc)‖
  let g : ℕ → ℝ≥0∞ := fun k => rVariationOn r u (Set.Icc (s k) (s (k + 1)))
  have he : Function.Injective e :=
    (chainSparseCrossingStartBlock_strictMono hs0 hs hUnbounded chain).injective
  have hpoint (i : Fin (chainSparseCrossingSet hs hUnbounded chain).card) :
      f i ≤ g (e i) := by
    exact chainSparseCrossing_leftPiece_blockBound hs0 hs hUnbounded chain i u hr
  have hsum := finiteSum_rpow_le_image e he f g r hr.le hpoint
  simpa [e, f, g] using hsum

/-- The powered sum of ending endpoint pieces is bounded by the sum of
powered block variations over the finite set of ending blocks. -/
theorem chainSparseCrossing_rightPiece_sum_le_blockImage {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr : 0 < r) :
    (∑ i : Fin (chainSparseCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (chain.index ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).succ) -
        u (s (chainSparseCrossingEndBlock hs hUnbounded chain i))‖).rpow r) ≤
      ∑ k ∈ (Finset.univ : Finset
        (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
          (chainSparseCrossingEndBlock hs hUnbounded chain),
        (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r := by
  classical
  let e := chainSparseCrossingEndBlock hs hUnbounded chain
  let f : Fin (chainSparseCrossingSet hs hUnbounded chain).card → ℝ≥0∞ := fun i =>
    ENNReal.ofReal ‖u (chain.index ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin
      rfl i).succ) - u (s (e i))‖
  let g : ℕ → ℝ≥0∞ := fun k => rVariationOn r u (Set.Icc (s k) (s (k + 1)))
  have he : Function.Injective e :=
    (chainSparseCrossingEndBlock_strictMono hs0 hs hUnbounded chain).injective
  have hpoint (i : Fin (chainSparseCrossingSet hs hUnbounded chain).card) :
      f i ≤ g (e i) := by
    exact chainSparseCrossing_rightPiece_blockBound hs0 hs hUnbounded chain i u hr
  have hsum := finiteSum_rpow_le_image e he f g r hr.le hpoint
  simpa [e, f, g] using hsum

/-- The starting endpoint pieces are bounded in `ℓ^r` by the block
square-function over their starting-block image, for `r ≥ 2`. -/
theorem chainSparseCrossing_leftPiece_le_blockSquare {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr2 : 2 ≤ r) :
    (∑ i : Fin (chainSparseCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (s (chainSparseCrossingStartBlock hs hUnbounded chain i + 1)) -
        u (chain.index ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).castSucc)‖).rpow r).rpow r⁻¹ ≤
      (∑ k ∈ (Finset.univ : Finset
        (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
          (chainSparseCrossingStartBlock hs hUnbounded chain),
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) := by
  have hsum := chainSparseCrossing_leftPiece_sum_le_blockImage hs0 hs hUnbounded
    chain u r (by linarith)
  have hroot := ENNReal.rpow_le_rpow hsum (one_div_nonneg.mpr (by linarith : 0 < r).le)
  have hblocks := finiteSparseBlockVariation_rpow_le_two (s := s) u hr2
    ((Finset.univ : Finset
      (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
        (chainSparseCrossingStartBlock hs hUnbounded chain))
  calc
    (∑ i : Fin (chainSparseCrossingSet hs hUnbounded chain).card,
        (ENNReal.ofReal ‖u (s (chainSparseCrossingStartBlock hs hUnbounded chain i + 1)) -
          u (chain.index ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin
            rfl i).castSucc)‖).rpow r).rpow r⁻¹ ≤
        (∑ k ∈ (Finset.univ : Finset
          (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
            (chainSparseCrossingStartBlock hs hUnbounded chain),
          (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r).rpow r⁻¹ := by
            simpa only [ENNReal.rpow_eq_pow, one_div] using hroot
    _ ≤ (∑ k ∈ (Finset.univ : Finset
          (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
            (chainSparseCrossingStartBlock hs hUnbounded chain),
          (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) := hblocks

/-- The ending endpoint pieces are bounded in `ℓ^r` by the block
square-function over their ending-block image, for `r ≥ 2`. -/
theorem chainSparseCrossing_rightPiece_le_blockSquare {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr2 : 2 ≤ r) :
    (∑ i : Fin (chainSparseCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (chain.index ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).succ) -
        u (s (chainSparseCrossingEndBlock hs hUnbounded chain i))‖).rpow r).rpow r⁻¹ ≤
      (∑ k ∈ (Finset.univ : Finset
        (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
          (chainSparseCrossingEndBlock hs hUnbounded chain),
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) := by
  have hsum := chainSparseCrossing_rightPiece_sum_le_blockImage hs0 hs hUnbounded
    chain u r (by linarith)
  have hroot := ENNReal.rpow_le_rpow hsum (one_div_nonneg.mpr (by linarith : 0 < r).le)
  have hblocks := finiteSparseBlockVariation_rpow_le_two (s := s) u hr2
    ((Finset.univ : Finset
      (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
        (chainSparseCrossingEndBlock hs hUnbounded chain))
  calc
    (∑ i : Fin (chainSparseCrossingSet hs hUnbounded chain).card,
        (ENNReal.ofReal ‖u (chain.index ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin
            rfl i).succ) -
          u (s (chainSparseCrossingEndBlock hs hUnbounded chain i))‖).rpow r).rpow r⁻¹ ≤
        (∑ k ∈ (Finset.univ : Finset
          (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
            (chainSparseCrossingEndBlock hs hUnbounded chain),
          (rVariationOn r u (Set.Icc (s k) (s (k + 1)))).rpow r).rpow r⁻¹ := by
            simpa only [ENNReal.rpow_eq_pow, one_div] using hroot
    _ ≤ (∑ k ∈ (Finset.univ : Finset
          (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
            (chainSparseCrossingEndBlock hs hUnbounded chain),
          (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) := hblocks

/-- The two endpoint-piece norms are jointly bounded by twice the block
square function over the union of their starting and ending block images. -/
theorem chainSparseCrossing_endpointPieces_le_unionBlockSquare {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr2 : 2 ≤ r) :
    (∑ i : Fin (chainSparseCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (s (chainSparseCrossingStartBlock hs hUnbounded chain i + 1)) -
        u (chain.index ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).castSucc)‖).rpow r).rpow r⁻¹ +
    (∑ i : Fin (chainSparseCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (chain.index ((chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin
          rfl i).succ) -
        u (s (chainSparseCrossingEndBlock hs hUnbounded chain i))‖).rpow r).rpow r⁻¹ ≤
      (∑ k ∈ ((Finset.univ : Finset
        (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
          (chainSparseCrossingStartBlock hs hUnbounded chain) ∪
        (Finset.univ : Finset
          (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
            (chainSparseCrossingEndBlock hs hUnbounded chain)),
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) +
      (∑ k ∈ ((Finset.univ : Finset
        (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
          (chainSparseCrossingStartBlock hs hUnbounded chain) ∪
        (Finset.univ : Finset
          (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
            (chainSparseCrossingEndBlock hs hUnbounded chain)),
        (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ) := by
  classical
  let startBlocks := (Finset.univ : Finset
    (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
      (chainSparseCrossingStartBlock hs hUnbounded chain)
  let endBlocks := (Finset.univ : Finset
    (Fin (chainSparseCrossingSet hs hUnbounded chain).card)).image
      (chainSparseCrossingEndBlock hs hUnbounded chain)
  let allBlocks := startBlocks ∪ endBlocks
  let V : ℕ → ℝ≥0∞ := fun k =>
    rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))
  have hstartSubset : startBlocks ⊆ allBlocks := Finset.subset_union_left
  have hendSubset : endBlocks ⊆ allBlocks := Finset.subset_union_right
  have hstartSum : (∑ k ∈ startBlocks, (V k).rpow 2) ≤
      ∑ k ∈ allBlocks, (V k).rpow 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hstartSubset (by
      intro k hk hk'
      exact bot_le)
  have hendSum : (∑ k ∈ endBlocks, (V k).rpow 2) ≤
      ∑ k ∈ allBlocks, (V k).rpow 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hendSubset (by
      intro k hk hk'
      exact bot_le)
  have hstartRoot := ENNReal.rpow_le_rpow hstartSum
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
  have hendRoot := ENNReal.rpow_le_rpow hendSum
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
  have hleft := chainSparseCrossing_leftPiece_le_blockSquare hs0 hs hUnbounded
    chain u r hr2
  have hright := chainSparseCrossing_rightPiece_le_blockSquare hs0 hs hUnbounded
    chain u r hr2
  apply add_le_add
  · exact hleft.trans (by simpa [startBlocks, allBlocks, V] using hstartRoot)
  · exact hright.trans (by simpa [endBlocks, allBlocks, V] using hendRoot)

noncomputable def chainSparseCrossingLeftScale {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (i : Fin (chainSparseCrossingSet hs hUnbounded chain).card) : Scale :=
  let e := (chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin rfl i
  s (chainScaleBlockIndex hs hUnbounded chain e.castSucc + 1)

noncomputable def chainSparseCrossingRightScale {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (i : Fin (chainSparseCrossingSet hs hUnbounded chain).card) : Scale :=
  let e := (chainSparseCrossingSet hs hUnbounded chain).orderEmbOfFin rfl i
  s (chainScaleBlockIndex hs hUnbounded chain e.succ)

theorem chainSparseCrossingFamily_properties {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) :
    (∀ i, chainSparseCrossingLeftScale hs hUnbounded chain i ≤
      chainSparseCrossingRightScale hs hUnbounded chain i) ∧
    (∀ i, chainSparseCrossingLeftScale hs hUnbounded chain i <
      chainSparseCrossingRightScale hs hUnbounded chain i) ∧
    (∀ i j, i < j → chainSparseCrossingRightScale hs hUnbounded chain i ≤
      chainSparseCrossingLeftScale hs hUnbounded chain j) ∧
    (∀ i, ∃ k, s k = chainSparseCrossingLeftScale hs hUnbounded chain i) ∧
    (∀ i, ∃ k, s k = chainSparseCrossingRightScale hs hUnbounded chain i) := by
  classical
  let E := chainSparseCrossingSet hs hUnbounded chain
  let a := chainSparseCrossingLeftScale hs hUnbounded chain
  let b := chainSparseCrossingRightScale hs hUnbounded chain
  have hmem (i : Fin E.card) :
      (E.orderEmbOfFin rfl i) ∈ E := Finset.orderEmbOfFin_mem E rfl i
  have hcross (i : Fin E.card) :=
    (mem_chainSparseCrossingSet hs hUnbounded chain (E.orderEmbOfFin rfl i)).mp
      (hmem i)
  have horderIndex {i j : Fin E.card} (hij : i < j) :
      E.orderEmbOfFin rfl i < E.orderEmbOfFin rfl j :=
    (E.orderEmbOfFin rfl).strictMono hij
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp [a, b, chainSparseCrossingLeftScale, chainSparseCrossingRightScale]
    exact hs (Nat.succ_le_of_lt (hcross i).1)
  · intro i
    dsimp [a, b, chainSparseCrossingLeftScale, chainSparseCrossingRightScale]
    exact (hcross i).2
  · intro i j hij
    dsimp [a, b, chainSparseCrossingLeftScale, chainSparseCrossingRightScale]
    have hblocks := chainCrossings_block_order hs0 hs hUnbounded chain
      (horderIndex hij) rfl rfl
    exact (hs hblocks).trans (hs (Nat.le_succ _))
  · intro i
    exact ⟨chainScaleBlockIndex hs hUnbounded chain
      (E.orderEmbOfFin rfl i).castSucc + 1, rfl⟩
  · intro i
    exact ⟨chainScaleBlockIndex hs hUnbounded chain
      (E.orderEmbOfFin rfl i).succ, rfl⟩

/-- The powered middle increments from all nondegenerate sparse crossings
are bounded by the sparse variation. The empty crossing family contributes
zero. -/
theorem chainSparseCrossing_middleVariation_le_sparseVariation
    {s : ℕ → Scale} (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩)
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) (r : ℝ) (hr : 0 < r) :
    (∑ i : Fin (chainSparseCrossingSet hs hUnbounded chain).card,
      (ENNReal.ofReal ‖u (chainSparseCrossingRightScale hs hUnbounded chain i) -
        u (chainSparseCrossingLeftScale hs hUnbounded chain i)‖).rpow r).rpow r⁻¹ ≤
      rVariation r (fun K : Scale => u (s (K.1 - 1))) := by
  classical
  let E := chainSparseCrossingSet hs hUnbounded chain
  let a := chainSparseCrossingLeftScale hs hUnbounded chain
  let b := chainSparseCrossingRightScale hs hUnbounded chain
  have hprops := chainSparseCrossingFamily_properties hs0 hs hUnbounded chain
  by_cases hE : E.Nonempty
  · have ht : (orderedPairEndpointSet a b).Nonempty := by
      have hcardpos : 0 < E.card := Finset.card_pos.mpr hE
      let i : Fin E.card := ⟨0, hcardpos⟩
      exact ⟨a i, orderedPairEndpointSet_left_mem a b i⟩
    have hbound := orderedPairVariation_le_sparseVariation a b hprops.1
      hprops.2.1 hprops.2.2.1 s hs hprops.2.2.2.1 hprops.2.2.2.2 ht u r hr
    simpa [a, b] using hbound
  · have hEeq : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    have hcard : E.card = 0 := by simp [hEeq]
    have hcard0 : (chainSparseCrossingSet hs hUnbounded chain).card = 0 := by
      simpa [E] using hcard
    have hsum : (∑ i : Fin (chainSparseCrossingSet hs hUnbounded chain).card,
        (ENNReal.ofReal ‖u (chainSparseCrossingRightScale hs hUnbounded chain i) -
          u (chainSparseCrossingLeftScale hs hUnbounded chain i)‖).rpow r) = 0 := by
      simp [hcard0]
    have hsumzero : (∑ i : Fin (chainSparseCrossingSet hs hUnbounded chain).card,
        (ENNReal.ofReal ‖u (chainSparseCrossingRightScale hs hUnbounded chain i) -
          u (chainSparseCrossingLeftScale hs hUnbounded chain i)‖).rpow r).rpow r⁻¹ = 0 := by
      rw [hsum]
      exact ENNReal.zero_rpow_of_pos (inv_pos.mpr hr)
    calc
      (∑ i : Fin (chainSparseCrossingSet hs hUnbounded chain).card,
        (ENNReal.ofReal ‖u (chainSparseCrossingRightScale hs hUnbounded chain i) -
          u (chainSparseCrossingLeftScale hs hUnbounded chain i)‖).rpow r).rpow r⁻¹ = 0 := hsumzero
      _ ≤ rVariation r (fun K : Scale => u (s (K.1 - 1))) := bot_le

/-- Extend the sparse middle increments by zero to the original chain's edge
indices without changing their `ℓʳ` norm. -/
theorem chainSparseCrossing_middleVector_le_sparseVariation
    {s : ℕ → Scale} (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩)
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) {r : ℝ} (hr : 0 < r) :
    (∑ i : Fin length,
      (if i ∈ chainSparseCrossingSet hs hUnbounded chain then
        ENNReal.ofReal ‖u (s (chainScaleBlockIndex hs hUnbounded chain i.succ)) -
          u (s (chainScaleBlockIndex hs hUnbounded chain i.castSucc + 1))‖
        else 0).rpow r).rpow r⁻¹ ≤
      rVariation r (fun K : Scale => u (s (K.1 - 1))) := by
  classical
  let E := chainSparseCrossingSet hs hUnbounded chain
  let f : Fin length → ℝ≥0∞ := fun i =>
    ENNReal.ofReal ‖u (s (chainScaleBlockIndex hs hUnbounded chain i.succ)) -
      u (s (chainScaleBlockIndex hs hUnbounded chain i.castSucc + 1))‖
  have hsum :
      (∑ i : Fin length,
        (if i ∈ E then f i else 0).rpow r) =
      ∑ i ∈ E, (f i).rpow r := by
    simp [Finset.sum_ite_mem, ENNReal.zero_rpow_of_pos hr]
  have hindex :
      (∑ i ∈ E, (f i).rpow r) =
      ∑ j : Fin E.card,
        (ENNReal.ofReal ‖u (chainSparseCrossingRightScale hs hUnbounded chain j) -
          u (chainSparseCrossingLeftScale hs hUnbounded chain j)‖).rpow r := by
    rw [finiteSet_sum_eq_fin_card]
    apply Finset.sum_congr rfl
    intro j _
    simp [f, E, chainSparseCrossingRightScale, chainSparseCrossingLeftScale]
  have hmain := chainSparseCrossing_middleVariation_le_sparseVariation
    hs0 hs hUnbounded chain u r hr
  rw [hsum, hindex]
  exact hmain

/-- Every adjacent chain edge lies within one sparse block, or crosses two
blocks with equal or strictly separated inserted boundaries. -/
theorem chainEdge_block_trichotomy {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length) (i : Fin length) :
    let k := chainScaleBlockIndex hs hUnbounded chain i.castSucc
    let l := chainScaleBlockIndex hs hUnbounded chain i.succ
    k = l ∨ (k < l ∧ s (k + 1) = s l) ∨ (k < l ∧ s (k + 1) < s l) := by
  dsimp only
  have hkl : chainScaleBlockIndex hs hUnbounded chain i.castSucc ≤
      chainScaleBlockIndex hs hUnbounded chain i.succ :=
    chainScaleBlockIndex_monotone hs0 hs hUnbounded chain
      (Fin.castSucc_le_succ i)
  rcases eq_or_lt_of_le hkl with heq | hlt
  · exact Or.inl heq
  · have hboundary :
        s (chainScaleBlockIndex hs hUnbounded chain i.castSucc + 1) ≤
          s (chainScaleBlockIndex hs hUnbounded chain i.succ) :=
      hs (Nat.succ_le_of_lt hlt)
    rcases eq_or_lt_of_le hboundary with heq | hltBoundary
    · exact Or.inr (Or.inl ⟨hlt, heq⟩)
    · exact Or.inr (Or.inr ⟨hlt, hltBoundary⟩)

/-- Long/short decomposition for the contribution of one finite chain. -/
theorem chainVariation_le_sparse_and_blockSquare {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    {length : ℕ} (chain : StrictScaleChain length)
    (u : Scale → ℂ) {r : ℝ} (hr2 : 2 ≤ r) :
    chainVariation r u chain ≤
      3 * rVariation r (fun K : Scale => u (s (K.1 - 1))) +
        3 * (∑' k : ℕ,
          (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow
            (1 / 2 : ℝ) := by
  classical
  let Same := chainSameBlockEdgeSet hs hUnbounded chain
  let Cross := chainAllCrossingSet hs hUnbounded chain
  let Middle := chainSparseCrossingSet hs hUnbounded chain
  let Q := (∑' k : ℕ,
    (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow (1 / 2 : ℝ)
  let V := rVariation r (fun K : Scale => u (s (K.1 - 1)))
  let same (i : Fin length) : ℝ≥0∞ :=
    if i ∈ Same then
      ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖
    else 0
  let left (i : Fin length) : ℝ≥0∞ :=
    if i ∈ Cross then
      ENNReal.ofReal ‖u (s (chainScaleBlockIndex hs hUnbounded chain i.castSucc + 1)) -
        u (chain.index i.castSucc)‖
    else 0
  let middle (i : Fin length) : ℝ≥0∞ :=
    if i ∈ Middle then
      ENNReal.ofReal ‖u (s (chainScaleBlockIndex hs hUnbounded chain i.succ)) -
        u (s (chainScaleBlockIndex hs hUnbounded chain i.castSucc + 1))‖
    else 0
  let right (i : Fin length) : ℝ≥0∞ :=
    if i ∈ Cross then
      ENNReal.ofReal ‖u (chain.index i.succ) -
        u (s (chainScaleBlockIndex hs hUnbounded chain i.succ))‖
    else 0
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hr2
  have hsameNorm :
      (∑ i : Fin length, (same i).rpow r).rpow r⁻¹ ≤ Q := by
    simpa [Q, same, Same, ENNReal.zero_rpow_of_pos hrpos,
      Finset.sum_ite_mem] using
      chainSameBlock_norm_le_sparseBlockSquare hs0 hs hUnbounded chain u hr2
  have hleftSum :
      (∑ i : Fin length, (left i).rpow r).rpow r⁻¹ =
        (∑ j : Fin Cross.card,
          (ENNReal.ofReal ‖u (s (chainAllCrossingStartBlock hs hUnbounded chain j + 1)) -
            u (chain.index (Cross.orderEmbOfFin rfl j).castSucc)‖).rpow r).rpow r⁻¹ := by
    congr 1
    calc
      (∑ i : Fin length, (left i).rpow r) =
          ∑ i ∈ Cross,
            (ENNReal.ofReal ‖u (s (chainScaleBlockIndex hs hUnbounded chain i.castSucc + 1)) -
              u (chain.index i.castSucc)‖).rpow r := by
                simp [left, Cross, ENNReal.zero_rpow_of_pos hrpos,
                  Finset.sum_ite_mem]
      _ = ∑ j : Fin Cross.card,
          (ENNReal.ofReal ‖u (s (chainAllCrossingStartBlock hs hUnbounded chain j + 1)) -
            u (chain.index (Cross.orderEmbOfFin rfl j).castSucc)‖).rpow r := by
              rw [finiteSet_sum_eq_fin_card]
              apply Finset.sum_congr rfl
              intro j _
              rfl
  have hleftNorm : (∑ i : Fin length, (left i).rpow r).rpow r⁻¹ ≤ Q := by
    rw [hleftSum]
    exact chainAllCrossing_leftPiece_le_globalBlockSquare hs0 hs hUnbounded
      chain u r hr2
  have hrightSum :
      (∑ i : Fin length, (right i).rpow r).rpow r⁻¹ =
        (∑ j : Fin Cross.card,
          (ENNReal.ofReal ‖u (chain.index (Cross.orderEmbOfFin rfl j).succ) -
            u (s (chainAllCrossingEndBlock hs hUnbounded chain j))‖).rpow r).rpow r⁻¹ := by
    congr 1
    calc
      (∑ i : Fin length, (right i).rpow r) =
          ∑ i ∈ Cross,
            (ENNReal.ofReal ‖u (chain.index i.succ) -
              u (s (chainScaleBlockIndex hs hUnbounded chain i.succ))‖).rpow r := by
                simp [right, Cross, ENNReal.zero_rpow_of_pos hrpos,
                  Finset.sum_ite_mem]
      _ = ∑ j : Fin Cross.card,
          (ENNReal.ofReal ‖u (chain.index (Cross.orderEmbOfFin rfl j).succ) -
            u (s (chainAllCrossingEndBlock hs hUnbounded chain j))‖).rpow r := by
              rw [finiteSet_sum_eq_fin_card]
              apply Finset.sum_congr rfl
              intro j _
              rfl
  have hrightNorm : (∑ i : Fin length, (right i).rpow r).rpow r⁻¹ ≤ Q := by
    rw [hrightSum]
    exact chainAllCrossing_rightPiece_le_globalBlockSquare hs0 hs hUnbounded
      chain u r hr2
  have hmiddleNorm : (∑ i : Fin length, (middle i).rpow r).rpow r⁻¹ ≤ V := by
    simpa [middle, Middle] using
      chainSparseCrossing_middleVector_le_sparseVariation hs0 hs hUnbounded
        chain u hrpos
  let A (i : Fin length) : ℝ≥0∞ := same i + left i
  have hAbound : (∑ i : Fin length, (A i).rpow r).rpow r⁻¹ ≤ Q + Q := by
    calc
      (∑ i : Fin length, (A i).rpow r).rpow r⁻¹ ≤
          (∑ i : Fin length, (same i).rpow r).rpow r⁻¹ +
            (∑ i : Fin length, (left i).rpow r).rpow r⁻¹ :=
        finiteENNReal_rpow_sum_add_le (by linarith : 1 ≤ r) same left
      _ ≤ Q + Q := add_le_add hsameNorm hleftNorm
  have hterm (i : Fin length) :
      ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖ ≤
        A i + middle i + right i := by
    let k := chainScaleBlockIndex hs hUnbounded chain i.castSucc
    let l := chainScaleBlockIndex hs hUnbounded chain i.succ
    have htri : k = l ∨ (k < l ∧ s (k + 1) = s l) ∨
        (k < l ∧ s (k + 1) < s l) := by
      simpa [k, l] using chainEdge_block_trichotomy hs0 hs hUnbounded chain i
    have hsameSpec : i ∈ Same ↔ k = l := by
      simpa [Same, k, l] using
        (mem_chainSameBlockEdgeSet hs hUnbounded chain i)
    have hcrossSpec : i ∈ Cross ↔ k < l := by
      simpa [Cross, k, l] using
        (mem_chainAllCrossingSet hs hUnbounded chain i)
    have hmiddleSpec : i ∈ Middle ↔ k < l ∧ s (k + 1) < s l := by
      simpa [Middle, k, l] using
        (mem_chainSparseCrossingSet hs hUnbounded chain i)
    rcases htri with heq | ⟨hlt, hboundaryEq⟩ | ⟨hlt, hboundaryLt⟩
    · have hsm : i ∈ Same := hsameSpec.mpr heq
      have hcr : i ∉ Cross := fun h =>
        (not_lt_of_ge (le_of_eq heq.symm)) (hcrossSpec.mp h)
      have hmid : i ∉ Middle := by
        intro h
        exact (not_lt_of_ge (le_of_eq heq.symm)) (hmiddleSpec.mp h).1
      simp [A, same, left, middle, right, hsm, hcr, hmid]
    · have hcr : i ∈ Cross := hcrossSpec.mpr hlt
      have hsm : i ∉ Same := fun h =>
        (not_lt_of_ge (le_of_eq (hsameSpec.mp h).symm)) hlt
      have hmid : i ∉ Middle := fun h => not_lt_of_ge
        (le_of_eq hboundaryEq.symm) (hmiddleSpec.mp h).2
      have htriangle :
          ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖ ≤
            ENNReal.ofReal ‖u (s (k + 1)) - u (chain.index i.castSucc)‖ +
              ENNReal.ofReal ‖u (s l) - u (s (k + 1))‖ +
                ENNReal.ofReal ‖u (chain.index i.succ) - u (s l)‖ := by
        have hidentity :
            u (chain.index i.succ) - u (chain.index i.castSucc) =
              (u (s (k + 1)) - u (chain.index i.castSucc)) +
                (u (s l) - u (s (k + 1))) +
                  (u (chain.index i.succ) - u (s l)) := by ring
        have hnorm := calc
          ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖ =
              ‖(u (s (k + 1)) - u (chain.index i.castSucc)) +
                (u (s l) - u (s (k + 1))) +
                  (u (chain.index i.succ) - u (s l))‖ := by rw [hidentity]
          _ ≤ ‖(u (s (k + 1)) - u (chain.index i.castSucc)) +
                (u (s l) - u (s (k + 1)))‖ +
                  ‖u (chain.index i.succ) - u (s l)‖ := norm_add_le _ _
          _ ≤ ‖u (s (k + 1)) - u (chain.index i.castSucc)‖ +
                ‖u (s l) - u (s (k + 1))‖ +
                  ‖u (chain.index i.succ) - u (s l)‖ := by
                exact add_le_add (norm_add_le _ _) le_rfl
        have hreal := ENNReal.ofReal_le_ofReal hnorm
        have hconv :
            ENNReal.ofReal
                ((‖u (s (k + 1)) - u (chain.index i.castSucc)‖ +
                    ‖u (s l) - u (s (k + 1))‖) +
                    ‖u (chain.index i.succ) - u (s l)‖) =
              ENNReal.ofReal ‖u (s (k + 1)) - u (chain.index i.castSucc)‖ +
                ENNReal.ofReal ‖u (s l) - u (s (k + 1))‖ +
                  ENNReal.ofReal ‖u (chain.index i.succ) - u (s l)‖ := by
          rw [ENNReal.ofReal_add (add_nonneg (norm_nonneg _) (norm_nonneg _))
              (norm_nonneg _), ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        have hreal' :
            ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖ ≤
              ENNReal.ofReal
                ((‖u (s (k + 1)) - u (chain.index i.castSucc)‖ +
                    ‖u (s l) - u (s (k + 1))‖) +
                    ‖u (chain.index i.succ) - u (s l)‖) := by
          simpa [add_assoc] using hreal
        exact hreal'.trans (le_of_eq hconv)
      have hzero : ‖u (s l) - u (s (k + 1))‖ = 0 := by
        rw [hboundaryEq]
        simp
      simpa [A, same, left, middle, right, hsm, hcr, hmid, hzero] using htriangle
    · have hcr : i ∈ Cross := hcrossSpec.mpr hlt
      have hsm : i ∉ Same := fun h =>
        (not_lt_of_ge (le_of_eq (hsameSpec.mp h).symm)) hlt
      have hmid : i ∈ Middle := hmiddleSpec.mpr ⟨hlt, hboundaryLt⟩
      have htriangle :
          ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖ ≤
            ENNReal.ofReal ‖u (s (k + 1)) - u (chain.index i.castSucc)‖ +
              ENNReal.ofReal ‖u (s l) - u (s (k + 1))‖ +
                ENNReal.ofReal ‖u (chain.index i.succ) - u (s l)‖ := by
        have hidentity :
            u (chain.index i.succ) - u (chain.index i.castSucc) =
              (u (s (k + 1)) - u (chain.index i.castSucc)) +
                (u (s l) - u (s (k + 1))) +
                  (u (chain.index i.succ) - u (s l)) := by ring
        have hnorm := calc
          ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖ =
              ‖(u (s (k + 1)) - u (chain.index i.castSucc)) +
                (u (s l) - u (s (k + 1))) +
                  (u (chain.index i.succ) - u (s l))‖ := by rw [hidentity]
          _ ≤ ‖(u (s (k + 1)) - u (chain.index i.castSucc)) +
                (u (s l) - u (s (k + 1)))‖ +
                  ‖u (chain.index i.succ) - u (s l)‖ := norm_add_le _ _
          _ ≤ ‖u (s (k + 1)) - u (chain.index i.castSucc)‖ +
                ‖u (s l) - u (s (k + 1))‖ +
                  ‖u (chain.index i.succ) - u (s l)‖ := by
                exact add_le_add (norm_add_le _ _) le_rfl
        have hreal := ENNReal.ofReal_le_ofReal hnorm
        have hconv :
            ENNReal.ofReal
                ((‖u (s (k + 1)) - u (chain.index i.castSucc)‖ +
                    ‖u (s l) - u (s (k + 1))‖) +
                    ‖u (chain.index i.succ) - u (s l)‖) =
              ENNReal.ofReal ‖u (s (k + 1)) - u (chain.index i.castSucc)‖ +
                ENNReal.ofReal ‖u (s l) - u (s (k + 1))‖ +
                  ENNReal.ofReal ‖u (chain.index i.succ) - u (s l)‖ := by
          rw [ENNReal.ofReal_add (add_nonneg (norm_nonneg _) (norm_nonneg _))
              (norm_nonneg _), ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        have hreal' :
            ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖ ≤
              ENNReal.ofReal
                ((‖u (s (k + 1)) - u (chain.index i.castSucc)‖ +
                    ‖u (s l) - u (s (k + 1))‖) +
                    ‖u (chain.index i.succ) - u (s l)‖) := by
          simpa [add_assoc] using hreal
        exact hreal'.trans (le_of_eq hconv)
      simpa [A, same, left, middle, right, hsm, hcr, hmid] using htriangle
  have hchain := chainVariation_le_three_increment_families chain u
    (by linarith : 1 ≤ r) A middle right hterm
  have hparts : chainVariation r u chain ≤ (Q + Q) + V + Q := by
    calc
      chainVariation r u chain ≤
          (∑ i : Fin length, (A i).rpow r).rpow r⁻¹ +
            (∑ i : Fin length, (middle i).rpow r).rpow r⁻¹ +
              (∑ i : Fin length, (right i).rpow r).rpow r⁻¹ := hchain
      _ ≤ (Q + Q) + V + Q := add_le_add (add_le_add hAbound hmiddleNorm) hrightNorm
  have hV : V ≤ 3 * V := by
    calc
      V = 1 * V := by simp
      _ ≤ 3 * V := by gcongr; norm_num
  calc
    chainVariation r u chain ≤ (Q + Q) + V + Q := hparts
    _ = V + 3 * Q := by ring
    _ ≤ 3 * V + 3 * Q := add_le_add hV le_rfl

/-- Global long/short variation bound, obtained by taking the supremum over
all finite increasing chains. -/
theorem rVariation_le_sparse_and_blockSquare {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale))
    (u : Scale → ℂ) {r : ℝ} (hr2 : 2 ≤ r) :
    rVariation r u ≤
      3 * rVariation r (fun K : Scale => u (s (K.1 - 1))) +
        3 * (∑' k : ℕ,
          (rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2).rpow
            (1 / 2 : ℝ) := by
  rw [rVariation_eq]
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  exact chainVariation_le_sparse_and_blockSquare hs0 hs hUnbounded
    chain u hr2

end

end FractionalPrimes

end
