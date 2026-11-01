module

public import FractionalPrimes.VariationAbsoluteSum
public import FractionalPrimes.VariationMeasurability
public import FractionalPrimes.VariationMonotonicity
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Finite-block variation estimates

This module relates the project's finite-chain homogeneous variation to
Mathlib's total variation on an ordered set. The comparison is the first step
toward the blueprint's consecutive-increment estimate.
-/

@[expose] public section

namespace FractionalPrimes

open Set
open MeasureTheory
open Filter
open scoped ENNReal

noncomputable section

/-- Extend a finite strict chain by keeping its last value fixed. -/
private def extendScaleChain {length : ℕ} (chain : StrictScaleChain length) : ℕ → Scale :=
  fun i => chain.index ⟨min i length, by omega⟩

/-- The extension of a strict finite scale chain is monotone. -/
private theorem extendScaleChain_monotone {length : ℕ}
    (chain : StrictScaleChain length) : Monotone (extendScaleChain chain) := by
  intro i j hij
  simp only [extendScaleChain]
  apply chain.strictMono.monotone
  apply Fin.mk_le_mk.mpr
  exact min_le_min hij le_rfl

/-- A chain contained in a set has its `ℓ^r` variation bounded by Mathlib's
total variation on that set. -/
theorem chainVariation_le_eVariationOn {r : ℝ} (hr : 1 ≤ r)
    (u : Scale → ℂ) {length : ℕ} (chain : StrictScaleChain length)
    {s : Set Scale} (hchain : ∀ i, chain.index i ∈ s) :
    chainVariation r u chain ≤ eVariationOn u s := by
  have hsum :
      (∑ i : Fin length,
        ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖) ≤
        eVariationOn u s := by
    have h := eVariationOn.sum_le (f := u) (s := s) (n := length)
      (u := extendScaleChain chain) (extendScaleChain_monotone chain)
      (fun i => hchain ⟨min i length, by omega⟩)
    calc
      (∑ i : Fin length,
          ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖)
          = ∑ i ∈ Finset.range length,
              edist (u (extendScaleChain chain (i + 1)))
                (u (extendScaleChain chain i)) := by
              rw [Finset.sum_bij (fun i _ => i.1)]
              · intro i hi
                exact Finset.mem_range.mpr i.isLt
              · intro i hi j hj hij
                exact Fin.ext hij
              · intro j hj
                exact ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
              · intro i hi
                have hidx1 : chain.index i.succ =
                    chain.index ⟨i.1 + 1, by omega⟩ := by
                  exact congrArg chain.index (Fin.ext rfl)
                have hidx0 : chain.index i.castSucc =
                    chain.index ⟨i.1, by omega⟩ := by
                  exact congrArg chain.index (Fin.ext rfl)
                rw [hidx1, hidx0]
                simp [extendScaleChain, edist_dist, dist_eq_norm]
      _ ≤ eVariationOn u s := h
  exact (chainVariation_le_sum_increments r hr u chain).trans hsum

/-- Homogeneous variation restricted to chains whose scales lie in a set. -/
noncomputable def rVariationOn (r : ℝ) (u : Scale → ℂ) (s : Set Scale) : ℝ≥0∞ := by
  classical
  exact ⨆ length : ℕ, ⨆ chain : StrictScaleChain length,
    if ∀ i, chain.index i ∈ s then chainVariation r u chain else 0

/-- Variation on a singleton scale block is zero for a positive exponent. -/
theorem rVariationOn_singleton_eq_zero {r : ℝ} (hr : 0 < r)
    (u : Scale → ℂ) (a : Scale) :
    rVariationOn r u ({a} : Set Scale) = 0 := by
  classical
  unfold rVariationOn
  simp only [Set.mem_singleton_iff]
  apply le_antisymm
  · apply iSup_le
    intro length
    apply iSup_le
    intro chain
    by_cases hchain : ∀ i, chain.index i ∈ ({a} : Set Scale)
    · have hlength : length = 0 := by
        by_contra hne
        have hpos : 0 < length := Nat.pos_of_ne_zero hne
        have hzero : chain.index ⟨0, by omega⟩ = a := by
          simpa using hchain ⟨0, by omega⟩
        have hone : chain.index ⟨1, by omega⟩ = a := by
          exact hchain ⟨1, by omega⟩
        have hlt : chain.index ⟨0, by omega⟩ < chain.index ⟨1, by omega⟩ := by
          apply chain.strictMono
          exact Fin.mk_lt_mk.mpr (by omega)
        rw [hzero, hone] at hlt
        exact (lt_irrefl a) hlt
      subst length
      simp [chainVariation, ENNReal.zero_rpow_of_pos (inv_pos.mpr hr)]
    · have hnotEq : ¬ ∀ i, chain.index i = a := by
        intro heq
        apply hchain
        intro i
        simpa [heq i]
      simp [hnotEq]
  · exact bot_le

/-- Restricting the allowed scale index set cannot increase homogeneous
variation. -/
theorem rVariationOn_mono_set (r : ℝ) (u : Scale → ℂ) {s t : Set Scale}
    (hst : s ⊆ t) : rVariationOn r u s ≤ rVariationOn r u t := by
  classical
  unfold rVariationOn
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  by_cases hs : ∀ i, chain.index i ∈ s
  · have ht : ∀ i, chain.index i ∈ t := fun i => hst (hs i)
    calc
      (if ∀ i, chain.index i ∈ s then chainVariation r u chain else 0) =
          chainVariation r u chain := by simp [hs]
      _ ≤ (⨆ length : ℕ, ⨆ chain : StrictScaleChain length,
            if ∀ i, chain.index i ∈ t then chainVariation r u chain else 0) := by
          exact le_iSup_of_le length (le_iSup_of_le chain (by simp [ht]))
  · simp [hs]

/-- A single increment with both endpoints in a scale set is bounded by the
variation restricted to that set. This supplies the endpoint control used
when a finite chain crosses between blocks. -/
theorem enorm_sub_le_rVariationOn {r : ℝ} (hr : 0 < r)
    (u : Scale → ℂ) (s : Set Scale) {N M : Scale} (hNM : N < M)
    (hN : N ∈ s) (hM : M ∈ s) :
    ENNReal.ofReal ‖u M - u N‖ ≤ rVariationOn r u s := by
  classical
  have hmem : ∀ i : Fin 2, (twoScaleChain N M hNM).index i ∈ s := by
    intro i
    fin_cases i
    · change (twoScaleChain N M hNM).index (0 : Fin 2) ∈ s
      rw [twoScaleChain_zero]
      exact hN
    · change (twoScaleChain N M hNM).index (1 : Fin 2) ∈ s
      rw [twoScaleChain_one]
      exact hM
  have hchain :
      chainVariation r u (twoScaleChain N M hNM) ≤ rVariationOn r u s := by
    unfold rVariationOn
    calc
      chainVariation r u (twoScaleChain N M hNM) ≤
          (if ∀ i, (twoScaleChain N M hNM).index i ∈ s then
            chainVariation r u (twoScaleChain N M hNM) else 0) := by
              simp [hmem]
      _ ≤ ⨆ length : ℕ, ⨆ chain : StrictScaleChain length,
            if ∀ i, chain.index i ∈ s then chainVariation r u chain else 0 :=
          le_iSup_of_le 1 (le_iSup_of_le (twoScaleChain N M hNM) le_rfl)
  have hvalue :
      chainVariation r u (twoScaleChain N M hNM) =
        ENNReal.ofReal ‖u M - u N‖ := by
    exact chainVariation_twoScaleChain r hr u hNM
  rw [← hvalue]
  exact hchain

/-- Restricted homogeneous variation decreases as its exponent increases. -/
theorem rVariationOn_mono_exponent {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s)
    (u : Scale → ℂ) (t : Set Scale) :
    rVariationOn s u t ≤ rVariationOn r u t := by
  classical
  unfold rVariationOn
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  by_cases hchain : ∀ i, chain.index i ∈ t
  · simp only [ite_eq_left hchain]
    exact (chainVariation_mono_exponent hr hrs u chain).trans
      (le_iSup_of_le length (le_iSup_of_le chain (by simp [hchain])))
  · simp [hchain]

/-- Restricted homogeneous variation is bounded by Mathlib total variation. -/
theorem rVariationOn_le_eVariationOn {r : ℝ} (hr : 1 ≤ r)
    (u : Scale → ℂ) (s : Set Scale) : rVariationOn r u s ≤ eVariationOn u s := by
  classical
  unfold rVariationOn
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  by_cases hchain : ∀ i, chain.index i ∈ s
  · simpa [hchain] using chainVariation_le_eVariationOn hr u chain hchain
  · simp [hchain]

/-- Pointwise homogeneous variation restricted to chains contained in a set. -/
noncomputable def rVariationOnFun {X : Type*} (r : ℝ) (F : Scale → X → ℂ)
    (s : Set Scale) : X → ℝ≥0∞ :=
  fun x => rVariationOn r (fun N => F N x) s

/-- Restricted pointwise variation is a.e. measurable when each scale is. -/
theorem aemeasurable_rVariationOnFun {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r : ℝ) (F : Scale → X → ℂ) (s : Set Scale)
    (hF : ∀ N, AEMeasurable (F N) μ) :
    AEMeasurable (rVariationOnFun r F s) μ := by
  classical
  unfold rVariationOnFun rVariationOn
  apply AEMeasurable.iSup
  intro length
  let _ : Countable (StrictScaleChain length) :=
    (strictScaleChainEmbedding length).countable
  apply AEMeasurable.iSup
  intro chain
  by_cases hchain : ∀ i, chain.index i ∈ s
  · simpa only [ite_eq_left hchain, chainVariationFun, chainVariation_eq] using
      aemeasurable_chainVariationFun μ r F hF chain
  · simp only [ite_eq_right hchain]
    exact aemeasurable_const

/-- The scale reached after `i` consecutive steps from a positive scale. -/
def scaleOffset (a : Scale) (i : ℕ) : Scale := ⟨a.1 + i, by omega⟩

/-- Total variation on a finite interval of positive integer scales is the sum
of its consecutive increments. -/
theorem eVariationOn_scaleInterval_eq_sum {u : Scale → ℂ} (a b : Scale)
    (hab : a ≤ b) :
    eVariationOn u (Icc a b) =
      ∑ i ∈ Finset.range (b.1 - a.1),
        ‖u (scaleOffset a (i + 1)) - u (scaleOffset a i)‖ₑ := by
  let I : ℕ → Scale := scaleOffset a
  have hI : Monotone I := by
    intro i j hij
    change a.1 + i ≤ a.1 + j
    omega
  have habval : a.1 ≤ b.1 := hab
  have hstart : I 0 = a := by
    apply Subtype.ext
    simp [I, scaleOffset]
  have hend : I (b.1 - a.1) = b := by
    apply Subtype.ext
    dsimp [I, scaleOffset]
    omega
  have hpair (i : ℕ) : Icc (I i) (I (i + 1)) = {I i, I (i + 1)} := by
    ext x
    simp only [mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hleft, hright⟩
      by_cases hx : x.1 = a.1 + i
      · left
        exact Subtype.ext hx
      · right
        apply Subtype.ext
        change x.1 = a.1 + i + 1
        change a.1 + i ≤ x.1 at hleft
        change x.1 ≤ a.1 + i + 1 at hright
        omega
    · intro hx
      rcases hx with hx | hx
      · subst x
        simp [I, scaleOffset]
      · subst x
        simp [I, scaleOffset]
  calc
    eVariationOn u (Icc a b) = eVariationOn u (Icc (I 0) (I (b.1 - a.1))) := by
      rw [hstart, hend]
    _ = ∑ i ∈ Finset.range (b.1 - a.1), eVariationOn u (Icc (I i) (I (i + 1))) :=
      (eVariationOn.sum' u hI (n := b.1 - a.1)).symm
    _ = ∑ i ∈ Finset.range (b.1 - a.1),
          ‖u (I (i + 1)) - u (I i)‖ₑ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hpair i, eVariationOn.pair]
      rw [← ofReal_norm, norm_sub_rev]
      simp [edist_dist, dist_eq_norm]

/-- The finite-block homogeneous variation is bounded by the sum of all
consecutive increments in that block. -/
theorem rVariationOn_scaleInterval_le_sum {r : ℝ} (hr : 1 ≤ r)
    (u : Scale → ℂ) (a b : Scale) (hab : a ≤ b) :
    rVariationOn r u (Icc a b) ≤
      ∑ i ∈ Finset.range (b.1 - a.1),
        ‖u (scaleOffset a (i + 1)) - u (scaleOffset a i)‖ₑ := by
  rw [← eVariationOn_scaleInterval_eq_sum (u := u) a b hab]
  exact rVariationOn_le_eVariationOn hr u (Icc a b)

/-- The `Lᵖ` norm of variation on a finite scale block is bounded by the sum
of the `Lᵖ` norms of its consecutive increments. -/
theorem eLpNorm_rVariationOnFun_scaleInterval_le_sum {X : Type*}
    [MeasurableSpace X] (S : InvertibleSystem X) (p r : ℝ)
    (hp : 1 ≤ p) (hr : 1 ≤ r) (F : Scale → X → ℂ)
    (a b : Scale) (hab : a ≤ b)
    (hF : ∀ N, MemLp (F N) (ENNReal.ofReal p) S.μ) :
    eLpNorm (rVariationOnFun r F (Icc a b)) (ENNReal.ofReal p) S.μ ≤
      ∑ i ∈ Finset.range (b.1 - a.1),
        eLpNorm (fun x => F (scaleOffset a (i + 1)) x -
          F (scaleOffset a i) x) (ENNReal.ofReal p) S.μ := by
  let terms : ℕ → X → ℝ≥0∞ := fun i x =>
    ‖F (scaleOffset a (i + 1)) x - F (scaleOffset a i) x‖ₑ
  let H : X → ℝ≥0∞ := fun x => ∑ i ∈ Finset.range (b.1 - a.1), terms i x
  have hG : AEStronglyMeasurable (rVariationOnFun r F (Icc a b)) S.μ :=
    (aemeasurable_rVariationOnFun S.μ r F (Icc a b)
      (fun N => (hF N).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hH : AEStronglyMeasurable H S.μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro i hi
    have hdiff : AEStronglyMeasurable
        (fun x => F (scaleOffset a (i + 1)) x - F (scaleOffset a i) x) S.μ :=
      ((hF (scaleOffset a (i + 1))).sub (hF (scaleOffset a i))).aestronglyMeasurable
    exact hdiff.enorm.aestronglyMeasurable
  have hdom : ∀ x, ‖rVariationOnFun r F (Icc a b) x‖ₑ ≤ ‖H x‖ₑ := by
    intro x
    have h := rVariationOn_scaleInterval_le_sum hr (fun N => F N x) a b hab
    simpa [rVariationOnFun, H, terms, enorm_eq_self] using h
  calc
    eLpNorm (rVariationOnFun r F (Icc a b)) (ENNReal.ofReal p) S.μ ≤
        eLpNorm H (ENNReal.ofReal p) S.μ :=
      eLpNorm_mono_enorm hG hdom
    _ ≤ ∑ i ∈ Finset.range (b.1 - a.1), eLpNorm (terms i) (ENNReal.ofReal p) S.μ := by
      have hpENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
        simpa using (ENNReal.ofReal_le_ofReal hp)
      have hsum := eLpNorm_sum_le (μ := S.μ) (p := ENNReal.ofReal p)
        (f := fun i x => terms i x) (s := Finset.range (b.1 - a.1)) hpENN
      have hHEq : H = ∑ i ∈ Finset.range (b.1 - a.1), fun x => terms i x := by
        funext x
        simp only [H, Finset.sum_apply]
      rw [hHEq]
      exact hsum
    _ = ∑ i ∈ Finset.range (b.1 - a.1),
        eLpNorm (fun x => F (scaleOffset a (i + 1)) x -
          F (scaleOffset a i) x) (ENNReal.ofReal p) S.μ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact eLpNorm_enorm _
        (((hF (scaleOffset a (i + 1))).sub (hF (scaleOffset a i))).aestronglyMeasurable)

end

end FractionalPrimes

end
