module

public import FractionalPrimes.Core
public import FractionalPrimes.SparseScales

/-!
# Sparse partitions of positive scales

For a nondecreasing unbounded scale sequence starting at one, every positive
scale belongs to exactly one nonempty half-open block `[s_k, s_{k+1})`.
Repeated values give empty blocks and are handled directly by the canonical
block index. These indices are the combinatorial input to the long/short
variation decomposition.
-/

public section

namespace FractionalPrimes

open Filter

noncomputable section

private theorem exists_scale_block_upper {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ) Filter.atTop)
    (N : Scale) : ∃ k, N < s (k + 1) := by
  let Ns : Scale := ⟨N.1 + 1, Nat.succ_pos _⟩
  have hEventually := hUnbounded.eventually_ge_atTop Ns
  obtain ⟨n, hn⟩ := hEventually.exists
  refine ⟨n, ?_⟩
  have hNlt : N < Ns := by
    change N.1 < N.1 + 1
    omega
  exact lt_of_lt_of_le hNlt (hn.trans (hs (Nat.le_succ n)))

/-- The unique block index whose half-open sparse-scale interval contains `N`.
The sequence is indexed from zero, as in the blueprint. -/
noncomputable def scaleBlockIndex {s : ℕ → Scale} (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ) Filter.atTop)
    (N : Scale) : ℕ :=
  Nat.find (exists_scale_block_upper hs hUnbounded N)

/-- Every positive scale lies below the right endpoint of its assigned block. -/
theorem scaleBlockIndex_upper {s : ℕ → Scale} (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ) Filter.atTop)
    (N : Scale) :
    N < s (scaleBlockIndex hs hUnbounded N + 1) :=
  Nat.find_spec (exists_scale_block_upper hs hUnbounded N)

/-- Every positive scale lies at or above the left endpoint of its assigned block. -/
theorem scaleBlockIndex_lower {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ) Filter.atTop)
    (N : Scale) : s (scaleBlockIndex hs hUnbounded N) ≤ N := by
  let k := scaleBlockIndex hs hUnbounded N
  have hex := exists_scale_block_upper hs hUnbounded N
  have hkUpper : N < s (k + 1) := Nat.find_spec hex
  by_cases hk0 : k = 0
  · change s k ≤ N
    rw [hk0, hs0]
    change 1 ≤ N.1
    exact N.2
  · have hpred : k - 1 < k := Nat.sub_one_lt hk0
    have hnot : ¬ N < s ((k - 1) + 1) := Nat.find_min hex hpred
    by_contra hkn
    have hNK : N < s k := lt_of_not_ge hkn
    have hidx : (k - 1) + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)
    exact hnot (hidx ▸ hNK)

/-- The assigned block is monotone in the scale. -/
theorem scaleBlockIndex_monotone {s : ℕ → Scale}
    (hs0 : s 0 = ⟨1, Nat.succ_pos 0⟩) (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ) Filter.atTop) :
    Monotone (scaleBlockIndex hs hUnbounded) := by
  intro N M hNM
  by_contra hnot
  have hblock : scaleBlockIndex hs hUnbounded M + 1 ≤
      scaleBlockIndex hs hUnbounded N := by omega
  have hboundary : s (scaleBlockIndex hs hUnbounded M + 1) ≤
      s (scaleBlockIndex hs hUnbounded N) := hs hblock
  have hcontr : M < N := by
    calc
      M < s (scaleBlockIndex hs hUnbounded M + 1) :=
        scaleBlockIndex_upper hs hUnbounded M
      _ ≤ s (scaleBlockIndex hs hUnbounded N) := hboundary
      _ ≤ N := scaleBlockIndex_lower hs0 hs hUnbounded N
  exact (not_lt_of_ge hNM) hcontr

/-- The interval condition determines the block index uniquely. -/
theorem scaleBlockIndex_eq_of_mem {s : ℕ → Scale}
    (hs : Monotone s)
    (hUnbounded : Filter.Tendsto s (Filter.atTop : Filter ℕ) Filter.atTop)
    (N : Scale) {k : ℕ} (hk : s k ≤ N ∧ N < s (k + 1)) :
    scaleBlockIndex hs hUnbounded N = k := by
  apply Nat.le_antisymm
  · exact Nat.find_min' (exists_scale_block_upper hs hUnbounded N) hk.2
  · by_contra hnot
    have hki : scaleBlockIndex hs hUnbounded N + 1 ≤ k := by omega
    have hboundary : s (scaleBlockIndex hs hUnbounded N + 1) ≤ s k := hs hki
    have hle : s (scaleBlockIndex hs hUnbounded N + 1) ≤ N :=
      hboundary.trans hk.1
    exact (not_lt_of_ge hle) (scaleBlockIndex_upper hs hUnbounded N)

/-- The blueprint's natural sparse scale as a positive averaging scale. -/
@[expose] def sparseScaleAsScale {p : ℝ} (hp : 1 < p) (k : ℕ) : Scale :=
  ⟨sparseScale p k, by
    calc
      1 = sparseScale p 0 := (sparseScale_zero hp).symm
      _ ≤ sparseScale p k := sparseScale_monotone hp (Nat.zero_le k)⟩

theorem sparseScaleAsScale_zero {p : ℝ} (hp : 1 < p) :
    sparseScaleAsScale hp 0 = ⟨1, Nat.succ_pos 0⟩ := by
  apply Subtype.ext
  exact sparseScale_zero hp

theorem sparseScaleAsScale_monotone {p : ℝ} (hp : 1 < p) :
    Monotone (sparseScaleAsScale hp) := by
  intro i j hij
  change sparseScale p i ≤ sparseScale p j
  exact sparseScale_monotone hp hij

theorem sparseScaleAsScale_tendsto_atTop {p : ℝ} (hp : 1 < p) :
    Filter.Tendsto (sparseScaleAsScale hp) (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale) := by
  rw [Filter.tendsto_atTop]
  intro N
  have hnat := (sparseScale_tendsto_atTop hp).eventually_ge_atTop N.1
  filter_upwards [hnat] with k hk
  exact_mod_cast hk

/-- The nondecreasing sparse sequence, including repeated initial scales,
assigns each positive scale to its unique nonempty half-open block. -/
theorem sparseScaleBlockIndex_spec {p : ℝ} (hp : 1 < p) (N : Scale) :
    let k := scaleBlockIndex (sparseScaleAsScale_monotone hp)
      (sparseScaleAsScale_tendsto_atTop hp) N
    sparseScale p k ≤ N.1 ∧ N.1 < sparseScale p (k + 1) := by
  dsimp only
  constructor
  · have h := scaleBlockIndex_lower (sparseScaleAsScale_zero hp)
      (sparseScaleAsScale_monotone hp) (sparseScaleAsScale_tendsto_atTop hp) N
    exact_mod_cast h
  · exact_mod_cast scaleBlockIndex_upper (sparseScaleAsScale_monotone hp)
      (sparseScaleAsScale_tendsto_atTop hp) N

end

end FractionalPrimes

end
