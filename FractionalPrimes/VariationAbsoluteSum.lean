module

public import FractionalPrimes.VariationBasics
public import FractionalPrimes.VariationSubadditivity
import Mathlib.Analysis.MeanInequalities

/-!
# Absolute-sum control of homogeneous variation

This module checks the elementary estimate that variation of a summable
family is controlled by twice the absolute sum of its members.
-/

@[expose] public section

namespace FractionalPrimes

open scoped ENNReal NNReal

noncomputable section

private theorem finite_lp_le_l1 {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) (r : ℝ)
    (hr : 1 ≤ r) :
    (∑ i ∈ s, (a i).rpow r).rpow r⁻¹ ≤ ∑ i ∈ s, a i := by
  classical
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  induction s using Finset.induction_on with
  | empty => simp [hrpos]
  | @insert x s hx ih =>
    let f : ι → ℝ≥0∞ := fun i => if i = x then a x else 0
    let g : ι → ℝ≥0∞ := fun i => if i = x then 0 else a i
    have hmink := ENNReal.Lp_add_le (s := insert x s) f g hr
    have hfg : ∀ i ∈ insert x s, f i + g i = a i := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simp [f, g]
      · have hix : i ≠ x := fun h => hx (h ▸ hi)
        simp [f, g, hix]
    have hf : (∑ i ∈ insert x s, (f i).rpow r).rpow r⁻¹ = a x := by
      have hsum : ∑ i ∈ s, (f i).rpow r = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hix : i ≠ x := fun h => hx (h ▸ hi)
        simp [f, hix, hrpos]
      rw [Finset.sum_insert hx, hsum, add_zero]
      simp only [f, ite_eq_left rfl]
      exact ENNReal.rpow_rpow_inv hrpos.ne' _
    have hg : (∑ i ∈ insert x s, (g i).rpow r).rpow r⁻¹ =
        (∑ i ∈ s, (a i).rpow r).rpow r⁻¹ := by
      have hsum : ∑ i ∈ s, (g i).rpow r = ∑ i ∈ s, (a i).rpow r := by
        apply Finset.sum_congr rfl
        intro i hi
        have hix : i ≠ x := fun h => hx (h ▸ hi)
        simp [g, hix]
      rw [Finset.sum_insert hx, hsum]
      simp [g, hrpos]
    have hsumfg : (∑ i ∈ insert x s, (a i).rpow r) =
        ∑ i ∈ insert x s, (f i + g i).rpow r := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfg i hi]
    calc
      (∑ i ∈ insert x s, (a i).rpow r).rpow r⁻¹ =
          (∑ i ∈ insert x s, (f i + g i).rpow r).rpow r⁻¹ := by rw [hsumfg]
      _ ≤ (∑ i ∈ insert x s, (f i).rpow r).rpow r⁻¹ +
          (∑ i ∈ insert x s, (g i).rpow r).rpow r⁻¹ := by
            simpa only [ENNReal.rpow_eq_pow, one_div] using hmink
      _ = a x + (∑ i ∈ s, (a i).rpow r).rpow r⁻¹ := by rw [hf, hg]
      _ ≤ a x + ∑ i ∈ s, a i := add_le_add le_rfl ih
      _ = ∑ i ∈ insert x s, a i := by simp [hx]

/-- For `r ≥ 1`, the global extended-real `ℓʳ` norm is bounded by the
global `ℓ¹` sum. -/
theorem tsum_rpow_root_le_tsum {ι : Type*} (a : ι → ℝ≥0∞) (r : ℝ)
    (hr : 1 ≤ r) :
    (∑' i, (a i).rpow r).rpow r⁻¹ ≤ ∑' i, a i := by
  classical
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsum : (∑' i, (a i).rpow r) ≤ (∑' i, a i).rpow r := by
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro s
    calc
      (∑ i ∈ s, (a i).rpow r) ≤ (∑ i ∈ s, a i).rpow r := by
        have hfinite := finite_lp_le_l1 s a r hr
        have hpow := (ENNReal.rpow_le_rpow_iff hrpos).mpr hfinite
        have hpowEq :
            ((∑ i ∈ s, (a i).rpow r).rpow r⁻¹).rpow r =
              ∑ i ∈ s, (a i).rpow r :=
          ENNReal.rpow_inv_rpow hrpos.ne' _
        change ((∑ i ∈ s, (a i).rpow r).rpow r⁻¹).rpow r ≤
          (∑ i ∈ s, a i).rpow r at hpow
        rw [hpowEq] at hpow
        exact hpow
      _ ≤ (∑' i, a i).rpow r :=
        ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) hrpos.le
  have hroot := ENNReal.rpow_le_rpow hsum (inv_nonneg.mpr hrpos.le)
  have hrootEq : ((∑' i, a i).rpow r).rpow r⁻¹ = ∑' i, a i :=
    ENNReal.rpow_rpow_inv hrpos.ne' _
  change (∑' i, (a i).rpow r).rpow r⁻¹ ≤
    ((∑' i, a i).rpow r).rpow r⁻¹ at hroot
  rw [hrootEq] at hroot
  exact hroot

/-- A finite-chain `ℓ^r` variation is bounded by the `ℓ^1` sum of its increments. -/
theorem chainVariation_le_sum_increments {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (hr : 1 ≤ r) (u : Scale → E) {length : ℕ}
    (chain : StrictScaleChain length) :
    chainVariation r u chain ≤ Finset.sum (Finset.univ : Finset (Fin length)) (fun i =>
      ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖) := by
  rw [chainVariation_eq]
  simpa using
    (finite_lp_le_l1 (Finset.univ : Finset (Fin length))
      (fun i => ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖) r hr)

/-- A finite-chain variation is bounded by the sum of norms of its two endpoints. -/
theorem chainVariation_le_sum_endpoints {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (hr : 1 ≤ r) (u : Scale → E) {length : ℕ}
    (chain : StrictScaleChain length) :
    chainVariation r u chain ≤ Finset.sum (Finset.univ : Finset (Fin length)) (fun i =>
      ENNReal.ofReal ‖u (chain.index i.succ)‖ +
        ENNReal.ofReal ‖u (chain.index i.castSucc)‖) := by
  refine (chainVariation_le_sum_increments r hr u chain).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_sub_le _ _)

private def chainCastSuccEmbedding {length : ℕ} (chain : StrictScaleChain length) :
    Fin length ↪ Scale where
  toFun i := chain.index i.castSucc
  inj' := by
    intro i j hij
    apply Fin.castSucc_injective length
    exact chain.strictMono.injective hij

private def chainSuccEmbedding {length : ℕ} (chain : StrictScaleChain length) :
    Fin length ↪ Scale where
  toFun i := chain.index i.succ
  inj' := by
    intro i j hij
    apply Fin.succ_injective length
    exact chain.strictMono.injective hij

/-- The left endpoints of a strict finite chain contribute at most the full absolute sum. -/
theorem chain_castSucc_sum_le_tsum {E : Type*} [NormedAddCommGroup E]
    (u : Scale → E) {length : ℕ} (chain : StrictScaleChain length) :
    Finset.sum (Finset.univ : Finset (Fin length))
      (fun i => ENNReal.ofReal ‖u (chain.index i.castSucc)‖) ≤
      ∑' N : Scale, ENNReal.ofReal ‖u N‖ := by
  let e := chainCastSuccEmbedding chain
  calc
    Finset.sum (Finset.univ : Finset (Fin length))
        (fun i => ENNReal.ofReal ‖u (chain.index i.castSucc)‖) =
        Finset.sum (Finset.map e Finset.univ) (fun N => ENNReal.ofReal ‖u N‖) := by
          rw [Finset.sum_map]
          rfl
    _ ≤ ∑' N : Scale, ENNReal.ofReal ‖u N‖ := ENNReal.sum_le_tsum _

/-- The right endpoints of a strict finite chain contribute at most the full absolute sum. -/
theorem chain_succ_sum_le_tsum {E : Type*} [NormedAddCommGroup E]
    (u : Scale → E) {length : ℕ} (chain : StrictScaleChain length) :
    Finset.sum (Finset.univ : Finset (Fin length))
      (fun i => ENNReal.ofReal ‖u (chain.index i.succ)‖) ≤
      ∑' N : Scale, ENNReal.ofReal ‖u N‖ := by
  let e := chainSuccEmbedding chain
  calc
    Finset.sum (Finset.univ : Finset (Fin length))
        (fun i => ENNReal.ofReal ‖u (chain.index i.succ)‖) =
        Finset.sum (Finset.map e Finset.univ) (fun N => ENNReal.ofReal ‖u N‖) := by
          rw [Finset.sum_map]
          rfl
    _ ≤ ∑' N : Scale, ENNReal.ofReal ‖u N‖ := ENNReal.sum_le_tsum _

/-- A finite-chain variation is bounded by twice the full endpoint `ℓ^r` norm.
This is the sharper endpoint estimate from the basic variation lemma. -/
theorem chainVariation_le_two_tsum_rpow {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (hr : 1 ≤ r) (u : Scale → E) {length : ℕ}
    (chain : StrictScaleChain length) :
    chainVariation r u chain ≤
      2 * (∑' N : Scale, (ENNReal.ofReal ‖u N‖).rpow r).rpow r⁻¹ := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hrInv : 0 ≤ r⁻¹ := le_of_lt (inv_pos.mpr hrpos)
  let a : Scale → ℝ≥0∞ := fun N => ENNReal.ofReal ‖u N‖
  let left : Fin length → ℝ≥0∞ := fun i => a (chain.index i.succ)
  let right : Fin length → ℝ≥0∞ := fun i => a (chain.index i.castSucc)
  let inc : Fin length → ℝ≥0∞ := fun i =>
    ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖
  have hpoint : ∀ i, inc i ≤ left i + right i := by
    intro i
    dsimp [inc, left, right, a]
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
  have hsumlr :
      (∑ i : Fin length, (left i + right i).rpow r).rpow r⁻¹ ≤
        (∑ i : Fin length, (left i).rpow r).rpow r⁻¹ +
          (∑ i : Fin length, (right i).rpow r).rpow r⁻¹ := by
    simpa only [ENNReal.rpow_eq_pow, one_div] using
      ENNReal.Lp_add_le (Finset.univ : Finset (Fin length)) left right hr
  have hsumLeft :
      (∑ i : Fin length, (left i).rpow r) ≤
        ∑' N : Scale, (a N).rpow r := by
    let e := chainSuccEmbedding chain
    calc
      (∑ i : Fin length, (left i).rpow r) =
          ∑ i ∈ Finset.map e Finset.univ, (a i).rpow r := by
            rw [Finset.sum_map]
            rfl
      _ ≤ ∑' N : Scale, (a N).rpow r := ENNReal.sum_le_tsum _
  have hsumRight :
      (∑ i : Fin length, (right i).rpow r) ≤
        ∑' N : Scale, (a N).rpow r := by
    let e := chainCastSuccEmbedding chain
    calc
      (∑ i : Fin length, (right i).rpow r) =
          ∑ i ∈ Finset.map e Finset.univ, (a i).rpow r := by
            rw [Finset.sum_map]
            rfl
      _ ≤ ∑' N : Scale, (a N).rpow r := ENNReal.sum_le_tsum _
  calc
    chainVariation r u chain = (∑ i, (inc i).rpow r).rpow r⁻¹ := by
      rw [chainVariation_eq]
    _ ≤ (∑ i : Fin length, (left i + right i).rpow r).rpow r⁻¹ := by
      apply ENNReal.rpow_le_rpow _ hrInv
      apply Finset.sum_le_sum
      intro i hi
      exact ENNReal.rpow_le_rpow (hpoint i) hrpos.le
    _ ≤ (∑ i : Fin length, (left i).rpow r).rpow r⁻¹ +
        (∑ i : Fin length, (right i).rpow r).rpow r⁻¹ := hsumlr
    _ ≤ (∑' N : Scale, (a N).rpow r).rpow r⁻¹ +
        (∑' N : Scale, (a N).rpow r).rpow r⁻¹ := by
      gcongr
      · exact ENNReal.rpow_le_rpow hsumLeft hrInv
      · exact ENNReal.rpow_le_rpow hsumRight hrInv
    _ = 2 * (∑' N : Scale, (ENNReal.ofReal ‖u N‖).rpow r).rpow r⁻¹ := by
      simp [a, two_mul]

/-- A finite-chain variation is controlled by twice the full absolute sum. -/
theorem chainVariation_le_two_tsum {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (hr : 1 ≤ r) (u : Scale → E) {length : ℕ}
    (chain : StrictScaleChain length) :
    chainVariation r u chain ≤ 2 * ∑' N : Scale, ENNReal.ofReal ‖u N‖ := by
  let total : ℝ≥0∞ := ∑' N : Scale, ENNReal.ofReal ‖u N‖
  calc
    chainVariation r u chain ≤ Finset.sum (Finset.univ : Finset (Fin length)) (fun i =>
        ENNReal.ofReal ‖u (chain.index i.succ)‖ +
          ENNReal.ofReal ‖u (chain.index i.castSucc)‖) :=
      chainVariation_le_sum_endpoints r hr u chain
    _ = Finset.sum (Finset.univ : Finset (Fin length))
          (fun i => ENNReal.ofReal ‖u (chain.index i.succ)‖) +
        Finset.sum (Finset.univ : Finset (Fin length))
          (fun i => ENNReal.ofReal ‖u (chain.index i.castSucc)‖) := by
            rw [Finset.sum_add_distrib]
    _ ≤ total + total := add_le_add
      (chain_succ_sum_le_tsum u chain) (chain_castSucc_sum_le_tsum u chain)
    _ = 2 * ∑' N : Scale, ENNReal.ofReal ‖u N‖ := by
      simp [total, two_mul]

/-- For `r ≥ 1`, homogeneous variation is bounded by twice the absolute sum. -/
theorem rVariation_le_two_tsum {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (hr : 1 ≤ r) (u : Scale → E) :
    rVariation r u ≤ 2 * ∑' N : Scale, ENNReal.ofReal ‖u N‖ := by
  rw [rVariation_eq]
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  rw [← chainVariation_eq]
  exact chainVariation_le_two_tsum r hr u chain

/-- For `r ≥ 1`, homogeneous variation is at most twice the global endpoint
`ℓ^r` norm. -/
theorem rVariation_le_two_tsum_rpow {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (hr : 1 ≤ r) (u : Scale → E) :
    rVariation r u ≤
      2 * (∑' N : Scale, (ENNReal.ofReal ‖u N‖).rpow r).rpow r⁻¹ := by
  rw [rVariation_eq]
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  exact chainVariation_le_two_tsum_rpow r hr u chain

/-- The two endpoint estimates in the order stated by the basic variation
lemma: the global `ℓʳ` bound followed by the global `ℓ¹` bound. -/
theorem rVariation_le_two_tsum_rpow_le_two_tsum {E : Type*}
    [NormedAddCommGroup E] (r : ℝ) (hr : 1 ≤ r) (u : Scale → E) :
    rVariation r u ≤
        2 * (∑' N : Scale, (ENNReal.ofReal ‖u N‖).rpow r).rpow r⁻¹ ∧
      2 * (∑' N : Scale, (ENNReal.ofReal ‖u N‖).rpow r).rpow r⁻¹ ≤
        2 * ∑' N : Scale, ENNReal.ofReal ‖u N‖ := by
  constructor
  · exact rVariation_le_two_tsum_rpow r hr u
  · have hsum := tsum_rpow_root_le_tsum
      (fun N : Scale => ENNReal.ofReal ‖u N‖) r hr
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- Perturbing a sequence by a summable error adds at most twice the error's
absolute sum to its homogeneous variation. -/
theorem rVariation_add_le_two_tsum_error {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (hr : 1 ≤ r) (u e : Scale → E) :
    rVariation r (u + e) ≤
      rVariation r u + 2 * ∑' N : Scale, ENNReal.ofReal ‖e N‖ := by
  exact (rVariation_add_le r hr u e).trans
    (add_le_add le_rfl (rVariation_le_two_tsum r hr e))

/-- A sequence within a summable pointwise error of a reference sequence has
variation bounded by the reference variation plus twice the error sum. -/
theorem rVariation_le_of_pointwise_error {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (hr : 1 ≤ r) (u v e : Scale → E)
    (he : ∀ N, u N = v N + e N) :
    rVariation r u ≤
      rVariation r v + 2 * ∑' N : Scale, ENNReal.ofReal ‖e N‖ := by
  have huv : u = v + e := by
    funext N
    exact he N
  rw [huv]
  exact rVariation_add_le_two_tsum_error r hr v e

end

end FractionalPrimes

end
