module

public import FractionalPrimes.Literature.Variation.FiniteOrderedVariation
import Mathlib.Analysis.MeanInequalities

/-!
# Algebra of finite ordered variation

These are the exact subadditivity and absolute-homogeneity inputs needed to
apply the explicit layer-cake lemma to a finite variation operator in
`lv:jump-to-variation`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open scoped ENNReal NNReal

noncomputable section

/-- One generic ordered chain satisfies the Minkowski inequality. -/
theorem finiteChainVariation_add_le
    {I : Type*} [LinearOrder I] (r : ℝ) (hr : 1 ≤ r)
    (u v : I → ℂ) {length : ℕ} (chain : StrictOrderedChain I length) :
    finiteChainVariation r (u + v) chain ≤
      finiteChainVariation r u chain + finiteChainVariation r v chain := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hrInv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0
  have hstep : ∀ i : Fin length,
      ENNReal.ofReal ‖(u + v) (chain.point i.succ) -
          (u + v) (chain.point i.castSucc)‖ ≤
        ENNReal.ofReal ‖u (chain.point i.succ) -
          u (chain.point i.castSucc)‖ +
        ENNReal.ofReal ‖v (chain.point i.succ) -
          v (chain.point i.castSucc)‖ := by
    intro i
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Pi.add_apply, add_sub_add_comm] using
      norm_add_le
        (u (chain.point i.succ) - u (chain.point i.castSucc))
        (v (chain.point i.succ) - v (chain.point i.castSucc))
  unfold finiteChainVariation
  calc
    (∑ i : Fin length,
        (ENNReal.ofReal ‖(u + v) (chain.point i.succ) -
          (u + v) (chain.point i.castSucc)‖).rpow r).rpow r⁻¹ ≤
        (∑ i : Fin length,
          (ENNReal.ofReal ‖u (chain.point i.succ) -
              u (chain.point i.castSucc)‖ +
            ENNReal.ofReal ‖v (chain.point i.succ) -
              v (chain.point i.castSucc)‖).rpow r).rpow r⁻¹ :=
      ENNReal.rpow_le_rpow
        (Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hstep i) hr0)
        hrInv
    _ ≤
        (∑ i : Fin length,
          (ENNReal.ofReal ‖u (chain.point i.succ) -
            u (chain.point i.castSucc)‖).rpow r).rpow r⁻¹ +
        (∑ i : Fin length,
          (ENNReal.ofReal ‖v (chain.point i.succ) -
            v (chain.point i.castSucc)‖).rpow r).rpow r⁻¹ := by
      simpa only [ENNReal.rpow_eq_pow, one_div] using
        ENNReal.Lp_add_le (Finset.univ : Finset (Fin length))
          (fun i => ENNReal.ofReal ‖u (chain.point i.succ) -
            u (chain.point i.castSucc)‖)
          (fun i => ENNReal.ofReal ‖v (chain.point i.succ) -
            v (chain.point i.castSucc)‖) hr

/-- Generic ordered variation is subadditive for exponents at least one. -/
theorem orderedRVariation_add_le
    {I : Type*} [LinearOrder I] (r : ℝ) (hr : 1 ≤ r)
    (u v : I → ℂ) :
    orderedRVariation r (u + v) ≤
      orderedRVariation r u + orderedRVariation r v := by
  unfold orderedRVariation
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  calc
    finiteChainVariation r (u + v) chain ≤
        finiteChainVariation r u chain + finiteChainVariation r v chain :=
      finiteChainVariation_add_le r hr u v chain
    _ ≤ (⨆ length, ⨆ chain : StrictOrderedChain I length,
          finiteChainVariation r u chain) +
        (⨆ length, ⨆ chain : StrictOrderedChain I length,
          finiteChainVariation r v chain) :=
      add_le_add
        (le_iSup_of_le length (le_iSup_of_le chain le_rfl))
        (le_iSup_of_le length (le_iSup_of_le chain le_rfl))

/-- One generic ordered chain is absolutely homogeneous. -/
theorem finiteChainVariation_smul
    {I : Type*} [LinearOrder I] (r : ℝ) (hr : 0 < r)
    (c : ℂ) (u : I → ℂ) {length : ℕ}
    (chain : StrictOrderedChain I length) :
    finiteChainVariation r (c • u) chain =
      ENNReal.ofReal ‖c‖ * finiteChainVariation r u chain := by
  have hstep (i : Fin length) :
      ENNReal.ofReal ‖(c • u) (chain.point i.succ) -
          (c • u) (chain.point i.castSucc)‖ =
        ENNReal.ofReal ‖c‖ *
          ENNReal.ofReal ‖u (chain.point i.succ) -
            u (chain.point i.castSucc)‖ := by
    rw [show (c • u) (chain.point i.succ) -
        (c • u) (chain.point i.castSucc) =
          c • (u (chain.point i.succ) -
            u (chain.point i.castSucc)) by
              change c * u (chain.point i.succ) -
                c * u (chain.point i.castSucc) =
                  c * (u (chain.point i.succ) -
                    u (chain.point i.castSucc))
              ring]
    rw [norm_smul]
    exact ENNReal.ofReal_mul (norm_nonneg c)
  have hsum :
      (∑ i : Fin length,
        (ENNReal.ofReal ‖(c • u) (chain.point i.succ) -
          (c • u) (chain.point i.castSucc)‖).rpow r) =
        (ENNReal.ofReal ‖c‖).rpow r *
          ∑ i : Fin length,
            (ENNReal.ofReal ‖u (chain.point i.succ) -
              u (chain.point i.castSucc)‖).rpow r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hstep i]
    exact ENNReal.mul_rpow_of_nonneg _ _ hr.le
  unfold finiteChainVariation
  rw [hsum]
  calc
    ((ENNReal.ofReal ‖c‖).rpow r *
        ∑ i : Fin length,
          (ENNReal.ofReal ‖u (chain.point i.succ) -
            u (chain.point i.castSucc)‖).rpow r).rpow r⁻¹ =
        ((ENNReal.ofReal ‖c‖).rpow r).rpow r⁻¹ *
          (∑ i : Fin length,
            (ENNReal.ofReal ‖u (chain.point i.succ) -
              u (chain.point i.castSucc)‖).rpow r).rpow r⁻¹ :=
      ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hr.le)
    _ = ENNReal.ofReal ‖c‖ *
          (∑ i : Fin length,
            (ENNReal.ofReal ‖u (chain.point i.succ) -
              u (chain.point i.castSucc)‖).rpow r).rpow r⁻¹ := by
      congr 1
      calc
        ((ENNReal.ofReal ‖c‖).rpow r).rpow r⁻¹ =
            (ENNReal.ofReal ‖c‖).rpow (r * r⁻¹) :=
          (ENNReal.rpow_mul (ENNReal.ofReal ‖c‖) r r⁻¹).symm
        _ = (ENNReal.ofReal ‖c‖).rpow 1 := by
          rw [mul_inv_cancel₀ hr.ne']
        _ = ENNReal.ofReal ‖c‖ := ENNReal.rpow_one _

/-- Generic ordered variation is absolutely homogeneous for positive
exponents. -/
theorem orderedRVariation_smul
    {I : Type*} [LinearOrder I] (r : ℝ) (hr : 0 < r)
    (c : ℂ) (u : I → ℂ) :
    orderedRVariation r (c • u) =
      ENNReal.ofReal ‖c‖ * orderedRVariation r u := by
  unfold orderedRVariation
  simp_rw [finiteChainVariation_smul r hr c u, ENNReal.mul_iSup]

end

end FractionalPrimes.Literature.Variation

end
