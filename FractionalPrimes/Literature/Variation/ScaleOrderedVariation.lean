module

public import FractionalPrimes.Literature.Variation.FiniteChainVariation

/-! Identify the generic ordered variation with the original positive-scale variation. -/
@[expose] public section
namespace FractionalPrimes.Literature.Variation
noncomputable section

theorem orderedRVariation_scale_eq_rVariation (r : ℝ) (u : Scale → ℂ) :
    orderedRVariation r u = rVariation r u := by
  apply le_antisymm
  · unfold orderedRVariation
    apply iSup_le
    intro length
    apply iSup_le
    intro chain
    let d : StrictScaleChain length := ⟨chain.point, chain.strictMono⟩
    change chainVariation r u d ≤ rVariation r u
    exact chainVariation_le_rVariation r u d
  · rw [rVariation_eq]
    apply iSup_le
    intro length
    apply iSup_le
    intro chain
    let d : StrictOrderedChain Scale length := ⟨chain.index, chain.strictMono⟩
    change finiteChainVariation r u d ≤ orderedRVariation r u
    exact finiteChainVariation_le_orderedRVariation r u d

#print axioms orderedRVariation_scale_eq_rVariation
end
end FractionalPrimes.Literature.Variation
