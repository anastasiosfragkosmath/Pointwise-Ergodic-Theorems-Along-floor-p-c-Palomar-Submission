/-
Modified for the Fractional Primes submission, 2026-10-30.
Derived from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Upstream file: lean/OAI/NumberTheory/DirichletL/Energy/ZeroUnbalancedOriginalGates.lean
Changes include Lean module/public-import conversion and submission integration;
additional compatibility edits are recorded in audits/provenance.json.
Original notices are retained. License: Apache-2.0; see third-party-licenses/LICENSE.
Current attribution and source hashes: audits/attribution.json.
-/
module
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBranchGeometry
@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalGates
open CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBranchGeometry

lemma original_long_positive (Z M X₁ X₂:ℝ)(hZ:1<Z)(hM:0<M)
    (_hX₁:0<X₁)(hX₂:0<X₂)
    (hshort:length Z X₁≤M/4)
    (hlarge:5*M/6≤length Z X₁+length Z X₂):
    0<Real.logb Z X₂ ∧ length Z X₂=Real.logb Z X₂ ∧ 1≤X₂:=by
  have hpos:0<length Z X₂:=by linarith
  have he:=length_eq_max_log Z X₂ hZ hX₂
  have hl:0<Real.logb Z X₂:=by
    by_contra hn
    rw [he,max_eq_left (le_of_not_gt hn)] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨hl,he.trans (max_eq_right hl.le),?_⟩
  by_contra hn
  have hh:=Real.logb_le_logb_of_le hZ hX₂ (le_of_not_ge hn)
  rw [Real.logb_one] at hh
  linarith

lemma raw_short_bound (Z M X:ℝ)(hZ:1<Z)(hX:0<X)
    (hshort:length Z X≤M/4):Real.logb Z X≤M/4:=by
  rw [length_eq_max_log Z X hZ hX] at hshort
  exact (le_max_right _ _).trans hshort

end SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalGates

end

end OAI
