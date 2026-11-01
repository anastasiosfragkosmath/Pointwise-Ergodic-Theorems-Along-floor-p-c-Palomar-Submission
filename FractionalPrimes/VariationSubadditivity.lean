module

public import FractionalPrimes.Variation
import Mathlib.Analysis.MeanInequalities

/-!
# Subadditivity of homogeneous variation

This module proves the finite-chain Minkowski step and its consequence for
the homogeneous variation used by the project.
-/

public section

namespace FractionalPrimes

open scoped ENNReal NNReal

noncomputable section

/-- The explicit contribution of one finite chain is subadditive for exponents at least one. -/
theorem finiteChainVariation_add_le {E : Type*} [NormedAddCommGroup E] (r : ℝ)
    (hr : 1 ≤ r) (u v : Scale → E) {length : ℕ} (chain : StrictScaleChain length) :
    (∑ i : Fin length,
      (ENNReal.ofReal ‖(u + v) (chain.index i.succ) -
        (u + v) (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ ≤
      (∑ i : Fin length,
        (ENNReal.ofReal ‖u (chain.index i.succ) -
          u (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ +
        (∑ i : Fin length,
          (ENNReal.ofReal ‖v (chain.index i.succ) -
            v (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hr_inv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0
  have hstep : ∀ i : Fin length,
      ENNReal.ofReal ‖(u + v) (chain.index i.succ) - (u + v) (chain.index i.castSucc)‖ ≤
        ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖ +
          ENNReal.ofReal ‖v (chain.index i.succ) - v (chain.index i.castSucc)‖ := by
    intro i
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Pi.add_apply, add_sub_add_comm] using
      norm_add_le (u (chain.index i.succ) - u (chain.index i.castSucc))
        (v (chain.index i.succ) - v (chain.index i.castSucc))
  calc
    (∑ i : Fin length,
        (ENNReal.ofReal ‖(u + v) (chain.index i.succ) -
          (u + v) (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ ≤
        (∑ i : Fin length,
          (ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖ +
            ENNReal.ofReal ‖v (chain.index i.succ) - v (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ :=
      ENNReal.rpow_le_rpow
        (Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hstep i) hr0) hr_inv
    _ ≤
        (∑ i : Fin length,
          (ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ +
          (∑ i : Fin length,
            (ENNReal.ofReal ‖v (chain.index i.succ) - v (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ := by
      simpa only [ENNReal.rpow_eq_pow, one_div] using
        ENNReal.Lp_add_le (Finset.univ : Finset (Fin length))
          (fun i => ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖)
          (fun i => ENNReal.ofReal ‖v (chain.index i.succ) - v (chain.index i.castSucc)‖) hr

/-- Homogeneous variation is subadditive for exponents at least one. -/
theorem rVariation_add_le {E : Type*} [NormedAddCommGroup E] (r : ℝ)
    (hr : 1 ≤ r) (u v : Scale → E) :
    rVariation r (u + v) ≤ rVariation r u + rVariation r v := by
  rw [rVariation_eq]
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  have hu :
      (∑ i : Fin length,
        (ENNReal.ofReal ‖u (chain.index i.succ) -
          u (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ ≤ rVariation r u := by
    rw [rVariation_eq]
    exact le_iSup_of_le length (le_iSup_of_le chain le_rfl)
  have hv :
      (∑ i : Fin length,
        (ENNReal.ofReal ‖v (chain.index i.succ) -
          v (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ ≤ rVariation r v := by
    rw [rVariation_eq]
    exact le_iSup_of_le length (le_iSup_of_le chain le_rfl)
  calc
    (∑ i : Fin length,
        (ENNReal.ofReal ‖(u + v) (chain.index i.succ) -
          (u + v) (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ ≤
        (∑ i : Fin length,
          (ENNReal.ofReal ‖u (chain.index i.succ) -
            u (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ +
          (∑ i : Fin length,
            (ENNReal.ofReal ‖v (chain.index i.succ) -
              v (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ :=
      finiteChainVariation_add_le r hr u v chain
    _ ≤ rVariation r u + rVariation r v := add_le_add hu hv

end

end FractionalPrimes

end
