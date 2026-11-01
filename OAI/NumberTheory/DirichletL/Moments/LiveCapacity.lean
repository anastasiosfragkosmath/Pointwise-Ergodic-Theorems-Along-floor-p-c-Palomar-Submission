/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Moments/LiveCapacity.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Moments.ActualLiveSlotRemoval
@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentLiveCapacity

 def excess {ι:Type*} (J:Finset ι) (w:ι→ℝ) (n₁ n₂ M κ:ℝ) : ℝ :=
  max (n₁+n₂+6*κ*(∑i∈J,w i)-M) 0

 theorem remaining_capacity {ι:Type*} [DecidableEq ι]
    (J R:Finset ι) (hR:R⊆J) (w:ι→ℝ) (n₁ n₂ M κ:ℝ)
    (hpay:R=J ∨ excess J w n₁ n₂ M κ≤6*κ*(∑i∈R,w i)) :
    R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤M := by
  rcases hpay with h|h
  · exact Or.inl h
  · right
    have hs:=Finset.sum_sdiff hR (f:=w)
    have hm:=le_max_left (n₁+n₂+6*κ*(∑i∈J,w i)-M) (0:ℝ)
    change max _ _≤_ at h
    have hh:=hm.trans h
    rw [←hs] at hh
    nlinarith

 theorem removal_excess_cost {ι:Type*} [DecidableEq ι]
    (J:Finset ι) (w:ι→ℝ) (n₁ n₂ M κ mesh:ℝ)
    (hκ:0<κ) (hm:0≤mesh) (hw:∀i∈J,0≤w i) (hwm:∀i∈J,w i≤mesh) :
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤M) ∧
      κ*(∑i∈R,w i)≤excess J w n₁ n₂ M κ/6+κ*mesh := by
  obtain ⟨R,hR,hbound,hpay,hcost⟩:=CenteredMomentWholeSlotDeletion.whole_removal
    J w (excess J w n₁ n₂ M κ) κ mesh (le_max_right _ _) hκ hm hw hwm
  exact ⟨R,hR,remaining_capacity J R hR w n₁ n₂ M κ hpay,hcost⟩

end SevenEighths.CenteredMomentLiveCapacity

end

end OAI
