module

public import FractionalPrimes.Literature.Variation.OrderedVariationFatou
public import Mathlib.Data.Set.FiniteExhaustion

/-!
# Finite exhaustion of ordered variation

For a countable ordered index type, the full variation is the increasing
supremum of the variations supported on an arbitrary finite exhaustion.  This
is the final countable-index passage prescribed in `lv:jump-to-variation`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Ordered variation restricted to chains whose points lie in the `N`th
member of a finite exhaustion. -/
def orderedRVariationTrunc
    {I : Type*} [LinearOrder I]
    (K : Set.FiniteExhaustion (Set.univ : Set I))
    (r : ℝ) (u : I → ℂ) (N : ℕ) : ℝ≥0∞ := by
  classical
  exact ⨆ (length : ℕ) (chain : StrictOrderedChain I length),
    if ∀ i, chain.point i ∈ K N then finiteChainVariation r u chain else 0

/-- Restricting to a larger member of the exhaustion can only increase
variation. -/
theorem orderedRVariationTrunc_mono
    {I : Type*} [LinearOrder I]
    (K : Set.FiniteExhaustion (Set.univ : Set I))
    (r : ℝ) (u : I → ℂ) :
    Monotone (orderedRVariationTrunc K r u) := by
  intro N M hNM
  unfold orderedRVariationTrunc
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  by_cases hN : ∀ i, chain.point i ∈ K N
  · have hM : ∀ i, chain.point i ∈ K M :=
      fun i => K.mono hNM (hN i)
    exact le_iSup_of_le length (le_iSup_of_le chain (by simp [hN, hM]))
  · exact le_iSup_of_le length (le_iSup_of_le chain (by simp [hN]))

/-- Every finite chain enters a sufficiently large exhaustion member, so the
truncated variations increase to the full ordered variation. -/
theorem orderedRVariation_eq_iSup_trunc
    {I : Type*} [LinearOrder I]
    (K : Set.FiniteExhaustion (Set.univ : Set I))
    (r : ℝ) (u : I → ℂ) :
    orderedRVariation r u = ⨆ N : ℕ, orderedRVariationTrunc K r u N := by
  classical
  apply le_antisymm
  · unfold orderedRVariation
    apply iSup_le
    intro length
    apply iSup_le
    intro chain
    have hmem : ∀ i : Fin (length + 1), ∃ n : ℕ, chain.point i ∈ K n := by
      intro i
      have hi : chain.point i ∈ ⋃ n, K n := by
        rw [K.iUnion_eq]
        exact Set.mem_univ _
      exact Set.mem_iUnion.mp hi
    choose bound hbound using hmem
    let N := (Finset.univ : Finset (Fin (length + 1))).sup bound
    have hchainN : ∀ i, chain.point i ∈ K N := by
      intro i
      have hiN : bound i ≤ N := by
        dsimp [N]
        exact Finset.le_sup (s := Finset.univ) (f := bound)
          (Finset.mem_univ i)
      exact K.mono hiN (hbound i)
    apply le_iSup_of_le N
    apply le_iSup_of_le length
    apply le_iSup_of_le chain
    change finiteChainVariation r u chain ≤
      if ∀ i, chain.point i ∈ K N then finiteChainVariation r u chain else 0
    simp [hchainN]
  · apply iSup_le
    intro N
    unfold orderedRVariationTrunc
    apply iSup_le
    intro length
    apply iSup_le
    intro chain
    split_ifs
    · exact finiteChainVariation_le_orderedRVariation r u chain
    · exact bot_le

/-- The chain-cutoff definition is exactly ordered variation on the finite
subtype supplied by the exhaustion. -/
theorem orderedRVariationTrunc_eq_subtype
    {I : Type*} [LinearOrder I]
    (K : Set.FiniteExhaustion (Set.univ : Set I))
    (r : ℝ) (u : I → ℂ) (N : ℕ) :
    orderedRVariationTrunc K r u N =
      orderedRVariation r (fun i : K N => u i.1) := by
  classical
  apply le_antisymm
  · unfold orderedRVariationTrunc
    apply iSup_le
    intro length
    apply iSup_le
    intro chain
    by_cases hchain : ∀ i, chain.point i ∈ K N
    · let restricted : StrictOrderedChain (K N) length :=
        { point := fun i => ⟨chain.point i, hchain i⟩
          strictMono := fun _ _ hij => chain.strictMono hij }
      have heq :
          finiteChainVariation r u chain =
            finiteChainVariation r (fun i : K N => u i.1) restricted := rfl
      rw [if_pos hchain, heq]
      exact finiteChainVariation_le_orderedRVariation
        r (fun i : K N => u i.1) restricted
    · simp [hchain]
  · unfold orderedRVariation
    apply iSup_le
    intro length
    apply iSup_le
    intro chain
    let ambient : StrictOrderedChain I length :=
      { point := fun i => (chain.point i).1
        strictMono := fun _ _ hij => chain.strictMono hij }
    have hambient : ∀ i, ambient.point i ∈ K N := fun i => (chain.point i).2
    have heq :
        finiteChainVariation r (fun i : K N => u i.1) chain =
          finiteChainVariation r u ambient := rfl
    rw [heq]
    apply le_iSup_of_le length
    apply le_iSup_of_le ambient
    simp [hambient]

/-- Pointwise finite-exhaustion truncation of a measurable family. -/
def orderedRVariationTruncFun
    {I X : Type*} [LinearOrder I]
    (K : Set.FiniteExhaustion (Set.univ : Set I))
    (r : ℝ) (F : I → X → ℂ) (N : ℕ) : X → ℝ≥0∞ :=
  fun x => orderedRVariationTrunc K r (fun i => F i x) N

/-- Every finite-exhaustion truncation is measurable. -/
theorem measurable_orderedRVariationTruncFun
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (K : Set.FiniteExhaustion (Set.univ : Set I))
    (r : ℝ) (F : I → X → ℂ) (hF : ∀ i, Measurable (F i)) (N : ℕ) :
    Measurable (orderedRVariationTruncFun K r F N) := by
  classical
  unfold orderedRVariationTruncFun orderedRVariationTrunc
  apply Measurable.iSup
  intro length
  let _ : Countable (StrictOrderedChain I length) :=
    (strictOrderedChainEmbedding length).countable
  apply Measurable.iSup
  intro chain
  by_cases hchain : ∀ i, chain.point i ∈ K N
  · have hfun :
        (fun x => if ∀ i, chain.point i ∈ K N then
          finiteChainVariation r (fun i => F i x) chain else 0) =
          finiteChainVariationFun r F chain := by
        funext x
        rw [if_pos hchain]
        rfl
    rw [hfun]
    exact measurable_finiteChainVariationFun r F hF chain
  · simp [hchain]

/-- The full pointwise ordered variation is the supremum of its finite
exhaustion truncations. -/
theorem orderedRVariationFun_eq_iSup_trunc
    {I X : Type*} [LinearOrder I]
    (K : Set.FiniteExhaustion (Set.univ : Set I))
    (r : ℝ) (F : I → X → ℂ) :
    orderedRVariationFun r F =
      fun x => ⨆ N : ℕ, orderedRVariationTruncFun K r F N x := by
  funext x
  exact orderedRVariation_eq_iSup_trunc K r (fun i => F i x)

/-- The pointwise truncation functions increase with the exhaustion. -/
theorem monotone_orderedRVariationTruncFun
    {I X : Type*} [LinearOrder I]
    (K : Set.FiniteExhaustion (Set.univ : Set I))
    (r : ℝ) (F : I → X → ℂ) :
    Monotone (orderedRVariationTruncFun K r F) := by
  intro N M hNM x
  exact orderedRVariationTrunc_mono K r (fun i => F i x) hNM

/-- Monotone convergence for positive powers of the finite-exhaustion
truncations. -/
theorem lintegral_orderedRVariationFun_rpow_eq_iSup_trunc
    {I X : Type*} [LinearOrder I] [Countable I] [MeasurableSpace X]
    (K : Set.FiniteExhaustion (Set.univ : Set I))
    (μ : Measure X) (r p : ℝ) (hp : 0 < p)
    (F : I → X → ℂ) (hF : ∀ i, Measurable (F i)) :
    ∫⁻ x, (orderedRVariationFun r F x) ^ p ∂μ =
      ⨆ N : ℕ,
        ∫⁻ x, (orderedRVariationTruncFun K r F N x) ^ p ∂μ := by
  have hrepr : (fun x => (orderedRVariationFun r F x) ^ p) =
      fun x => ⨆ N : ℕ, (orderedRVariationTruncFun K r F N x) ^ p := by
    funext x
    rw [orderedRVariationFun_eq_iSup_trunc K r F]
    change ENNReal.orderIsoRpow p hp
      (⨆ N : ℕ, orderedRVariationTruncFun K r F N x) = _
    rw [OrderIso.map_iSup]
    rfl
  rw [hrepr]
  apply lintegral_iSup
  · intro N
    exact (ENNReal.continuous_rpow_const (y := p)).measurable.comp
      (measurable_orderedRVariationTruncFun K r F hF N)
  · intro N M hNM x
    exact (ENNReal.orderIsoRpow p hp).monotone
      (monotone_orderedRVariationTruncFun K r F hNM x)

end

end FractionalPrimes.Literature.Variation

end
