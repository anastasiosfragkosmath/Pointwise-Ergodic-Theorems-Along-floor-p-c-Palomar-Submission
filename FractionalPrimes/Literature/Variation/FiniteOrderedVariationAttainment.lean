module

public import FractionalPrimes.Literature.Variation.FiniteOrderedVariation
import Mathlib.Data.Finset.Sort
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Attainment of finite ordered variation

The blueprint defines finite ordered variation as a maximum over finite
increasing chains.  The general definition is an indexed supremum, which is
also suitable for countable orders.  This file verifies that, on a finite
order with at least two points, that supremum is attained by one chain.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open scoped ENNReal

noncomputable section

/-- On a finite linearly ordered type with at least two indices, the
all-chain definition of ordered variation is attained by one strictly
increasing finite chain. -/
theorem orderedRVariation_isAttained_of_two_le_card
    {I : Type*} [LinearOrder I] [Fintype I] (r : ℝ) (u : I → ℂ)
    (hcard : 2 ≤ Fintype.card I) :
    ∃ length : ℕ, ∃ chain : StrictOrderedChain I length,
      orderedRVariation r u = finiteChainVariation r u chain := by
  classical
  let C : ℕ := Fintype.card I
  have hCpos : 0 < C := by dsimp [C]; omega
  letI : Nonempty I := Fintype.card_pos_iff.mp (by simpa [C] using hCpos)
  let BoundedChain := Σ n : Fin C, StrictOrderedChain I n.1
  letI (n : Fin C) : Fintype (StrictOrderedChain I n.1) :=
    Fintype.ofInjective (strictOrderedChainEmbedding n.1)
      (strictOrderedChainEmbedding n.1).injective
  let n0 : Fin C := ⟨0, hCpos⟩
  let chain0 : StrictOrderedChain I 0 :=
    { point := fun _ => Classical.choice (inferInstance : Nonempty I)
      strictMono := by
        intro i j hij
        omega }
  letI : Nonempty BoundedChain := ⟨⟨n0, chain0⟩⟩
  let value : BoundedChain → ℝ≥0∞ := fun z =>
    finiteChainVariation r u z.2
  obtain ⟨z, hz⟩ := exists_eq_ciSup_of_finite (f := value)
  refine ⟨z.1.1, z.2, ?_⟩
  have hbounded : orderedRVariation r u = ⨆ z : BoundedChain, value z := by
    apply le_antisymm
    · unfold orderedRVariation
      apply iSup_le
      intro length
      apply iSup_le
      intro chain
      have hlen : length + 1 ≤ C := by
        dsimp [C]
        simpa using
          (Fintype.card_le_of_injective chain.point chain.strictMono.injective)
      let n : Fin C := ⟨length, by omega⟩
      exact le_iSup_of_le (⟨n, chain⟩ : BoundedChain) le_rfl
    · apply iSup_le
      intro z'
      exact finiteChainVariation_le_orderedRVariation r u z'.2
  exact hbounded.trans hz.symm

/-- In the source range `r > 0`, the maximizing chain may be chosen with
at least one increment, exactly as in the finite maximum displayed in
`lv:jump-count`. -/
theorem orderedRVariation_isAttained_by_nontrivial_chain
    {I : Type*} [LinearOrder I] [Fintype I] (r : ℝ) (u : I → ℂ)
    (hr : 0 < r) (hcard : 2 ≤ Fintype.card I) :
    ∃ length : ℕ, 1 ≤ length ∧
      ∃ chain : StrictOrderedChain I length,
        orderedRVariation r u = finiteChainVariation r u chain := by
  classical
  obtain ⟨length, chain, hmax⟩ :=
    orderedRVariation_isAttained_of_two_le_card r u hcard
  by_cases hlength : 1 ≤ length
  · exact ⟨length, hlength, chain, hmax⟩
  · have hlengthZero : length = 0 := by omega
    have hchainZero : finiteChainVariation r u chain = 0 := by
      subst length
      unfold finiteChainVariation
      rw [Fin.sum_univ_zero]
      exact ENNReal.zero_rpow_of_pos (inv_pos.mpr hr)
    have hvariationZero : orderedRVariation r u = 0 := hmax.trans hchainZero
    let e : Fin (Fintype.card I) ≃o I :=
      Fintype.orderIsoFinOfCardEq I rfl
    let chainOne : StrictOrderedChain I 1 :=
      { point := fun i => e (Fin.castLE hcard i)
        strictMono := e.strictMono.comp (Fin.strictMono_castLE hcard) }
    have hchainOneLe : finiteChainVariation r u chainOne ≤ 0 := by
      simpa [hvariationZero] using
        (finiteChainVariation_le_orderedRVariation r u chainOne)
    refine ⟨1, le_rfl, chainOne, ?_⟩
    rw [hvariationZero]
    exact le_antisymm zero_le hchainOneLe

end

end FractionalPrimes.Literature.Variation

end
