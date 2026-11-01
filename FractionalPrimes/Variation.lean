module

public import FractionalPrimes.Core
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Elementary facts about homogeneous variation

The definition in `FractionalPrimes.Core` is a supremum over finite strictly
increasing chains. This module records the direct consequences of that
definition used by the later analytic development.
-/

@[expose] public section

namespace FractionalPrimes

open scoped NNReal ENNReal
open scoped Topology

noncomputable section

/-- The contribution of one finite chain to homogeneous variation. -/
def chainVariation {E : Type*} [NormedAddCommGroup E] (r : ℝ) (u : Scale → E)
    {length : ℕ} (chain : StrictScaleChain length) : ℝ≥0∞ :=
  (∑ i : Fin length,
    (ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖).rpow r).rpow r⁻¹

/-- The explicit finite-sum form of a chain contribution. -/
theorem chainVariation_eq {E : Type*} [NormedAddCommGroup E] (r : ℝ) (u : Scale → E)
    {length : ℕ} (chain : StrictScaleChain length) :
    chainVariation r u chain =
      (∑ i : Fin length,
        (ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ :=
  rfl

/-- The contribution of a fixed finite scale chain for a family of functions. -/
def chainVariationFun {X : Type*} (r : ℝ) (F : Scale → X → ℂ)
    {length : ℕ} (chain : StrictScaleChain length) : X → ℝ≥0∞ :=
  fun x => chainVariation r (fun N => F N x) chain

theorem rVariation_nonneg {E : Type*} [NormedAddCommGroup E] (r : ℝ) (u : Scale → E) :
    0 ≤ rVariation r u :=
  bot_le

theorem chainVariation_le_rVariation {E : Type*} [NormedAddCommGroup E] (r : ℝ)
    (u : Scale → E) {length : ℕ} (chain : StrictScaleChain length) :
    chainVariation r u chain ≤ rVariation r u := by
  rw [rVariation_eq]
  unfold chainVariation
  exact le_iSup_of_le length (le_iSup_of_le chain le_rfl)

/-- A fixed finite-chain contribution is continuous under coordinatewise
convergence of its finitely many complex values. -/
theorem chainVariation_tendsto_of_pointwise
    {r : ℝ} {length : ℕ} (chain : StrictScaleChain length)
    (u : ℕ → Scale → ℂ) (v : Scale → ℂ)
    (hu : ∀ N, Filter.Tendsto (fun m => u m N) Filter.atTop (nhds (v N))) :
    Filter.Tendsto (fun m => chainVariation r (fun N => u m N) chain) Filter.atTop
      (nhds (chainVariation r v chain)) := by
  unfold chainVariation
  have hterm : ∀ i : Fin length,
      Filter.Tendsto
        (fun m =>
          (ENNReal.ofReal ‖u m (chain.index i.succ) -
            u m (chain.index i.castSucc)‖).rpow r)
        Filter.atTop
        (nhds ((ENNReal.ofReal ‖v (chain.index i.succ) -
          v (chain.index i.castSucc)‖).rpow r)) := by
    intro i
    have hdiff := (hu (chain.index i.succ)).sub (hu (chain.index i.castSucc))
    have hnorm : Filter.Tendsto
        (fun m => ENNReal.ofReal ‖u m (chain.index i.succ) -
          u m (chain.index i.castSucc)‖)
        Filter.atTop
      (nhds (ENNReal.ofReal ‖v (chain.index i.succ) -
          v (chain.index i.castSucc)‖)) := by
      exact (ENNReal.continuous_ofReal.comp continuous_norm).tendsto _ |>.comp hdiff
    exact (ENNReal.continuous_rpow_const (y := r)).tendsto _ |>.comp hnorm
  have hsum : Filter.Tendsto
      (fun m => ∑ i : Fin length,
        (ENNReal.ofReal ‖u m (chain.index i.succ) -
          u m (chain.index i.castSucc)‖).rpow r)
      Filter.atTop
      (nhds (∑ i : Fin length,
        (ENNReal.ofReal ‖v (chain.index i.succ) -
          v (chain.index i.castSucc)‖).rpow r)) := by
    apply tendsto_finsetSum
    intro i hi
    exact hterm i
  exact (ENNReal.continuous_rpow_const (y := r⁻¹)).tendsto _ |>.comp hsum

/-- Homogeneous variation is lower semicontinuous under coordinatewise
convergence along a sequence of scale-indexed complex families. -/
theorem rVariation_le_liminf_of_pointwise
    {r : ℝ} (u : ℕ → Scale → ℂ) (v : Scale → ℂ)
    (hu : ∀ N, Filter.Tendsto (fun m => u m N) Filter.atTop (nhds (v N))) :
    rVariation r v ≤ Filter.liminf (fun m => rVariation r (u m)) Filter.atTop := by
  rw [rVariation_eq]
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  have hchain := chainVariation_tendsto_of_pointwise (r := r) chain u v hu
  have hle : ∀ᶠ m in Filter.atTop,
      chainVariation r (fun N => u m N) chain ≤ rVariation r (u m) :=
    Filter.Eventually.of_forall fun m => chainVariation_le_rVariation r (u m) chain
  have hlim := Filter.liminf_le_liminf hle
  rw [hchain.liminf_eq] at hlim
  exact hlim

/-- The `N`th finite-stage homogeneous variation, retaining exactly the
chains whose scale values are at most `N`. -/
def rVariationTrunc (r : ℝ) (u : Scale → ℂ) (N : ℕ) : ℝ≥0∞ :=
  ⨆ length : ℕ, ⨆ chain : StrictScaleChain length,
    if ∀ i, (chain.index i).1 ≤ N then chainVariation r u chain else 0

/-- Increasing the scale cutoff can only increase the truncated variation. -/
theorem rVariationTrunc_mono (r : ℝ) (u : Scale → ℂ) :
    Monotone (rVariationTrunc r u) := by
  intro N M hNM
  unfold rVariationTrunc
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  by_cases hN : ∀ i, (chain.index i).1 ≤ N
  · have hM : ∀ i, (chain.index i).1 ≤ M := fun i => (hN i).trans hNM
    exact le_iSup_of_le length (le_iSup_of_le chain (by simp [hN, hM]))
  · exact le_iSup_of_le length (le_iSup_of_le chain (by simp [hN]))

/-- Every finite scale chain is included at a sufficiently large cutoff, so
the truncated variations increase to the full variation. -/
theorem rVariation_eq_iSup_trunc (r : ℝ) (u : Scale → ℂ) :
    rVariation r u = ⨆ N : ℕ, rVariationTrunc r u N := by
  apply le_antisymm
  · rw [rVariation_eq]
    apply iSup_le
    intro length
    apply iSup_le
    intro chain
    let N := (chain.index (Fin.last length)).1
    have hbound : ∀ i, (chain.index i).1 ≤ N := by
      intro i
      dsimp [N]
      exact_mod_cast chain.strictMono.monotone (Fin.le_last i)
    apply le_iSup_of_le N
    apply le_iSup_of_le length
    apply le_iSup_of_le chain
    change chainVariation r u chain ≤
      if ∀ i, (chain.index i).1 ≤ N then chainVariation r u chain else 0
    simp [hbound]
  · apply iSup_le
    intro N
    unfold rVariationTrunc
    apply iSup_le
    intro length
    apply iSup_le
    intro chain
    split_ifs with hbound
    · exact chainVariation_le_rVariation r u chain
    · exact bot_le

theorem rVariationFun_nonneg {X E : Type*} [NormedAddCommGroup E] (r : ℝ)
    (u : Scale → X → E) (x : X) :
    0 ≤ rVariationFun r u x := by
  rw [rVariationFun_apply]
  exact rVariation_nonneg r (fun N => u N x)

theorem rVariationFun_const {X E : Type*} [NormedAddCommGroup E] (r : ℝ) (hr : 0 < r)
    (g : X → E) : rVariationFun r (fun _ : Scale => g) = 0 := by
  funext x
  rw [rVariationFun_apply]
  exact rVariation_const r hr (g x)

end

end FractionalPrimes
