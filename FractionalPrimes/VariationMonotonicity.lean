module

public import FractionalPrimes.Variation
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Monotonicity of homogeneous variation

The homogeneous variation from `FractionalPrimes.Core` is the supremum of
finite `ℓ^r` norms of scale increments. This file proves its exponent
monotonicity directly from that definition, and records monotonicity under an
increasing reindexing of the scales.
-/

public section

namespace FractionalPrimes

open scoped ENNReal NNReal

noncomputable section

/-- A finite `ℓ^s` norm of extended nonnegative values is bounded by its
`ℓ^r` norm when `0 < r ≤ s`. -/
theorem finiteENNReal_rpow_sum_mono_exponent {ι : Type*} (t : Finset ι)
    (a : ι → ℝ≥0∞) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    (∑ i ∈ t, (a i) ^ s) ^ (1 / s) ≤
      (∑ i ∈ t, (a i) ^ r) ^ (1 / r) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have hs : 0 < s := lt_of_lt_of_le hr hrs
    simp only [Finset.sum_empty]
    rw [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hs),
      ENNReal.zero_rpow_of_pos (one_div_pos.mpr hr)]
  | @insert x t hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have hs : 0 < s := lt_of_lt_of_le hr hrs
    have hpair := ENNReal.rpow_add_rpow_le
      ((∑ i ∈ t, (a i) ^ s) ^ (1 / s)) (a x) hr hrs
    have hpow :
        ((∑ i ∈ t, (a i) ^ s) ^ (1 / s)) ^ r ≤ ∑ i ∈ t, (a i) ^ r := by
      calc
        ((∑ i ∈ t, (a i) ^ s) ^ (1 / s)) ^ r
            ≤ ((∑ i ∈ t, (a i) ^ r) ^ (1 / r)) ^ r := by
              exact ENNReal.rpow_le_rpow ih hr.le
        _ = ∑ i ∈ t, (a i) ^ r := by
              rw [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]
    simpa only [add_comm] using calc
      (∑ i ∈ t, (a i) ^ s + (a x) ^ s) ^ (1 / s)
          = (((∑ i ∈ t, (a i) ^ s) ^ (1 / s)) ^ s + (a x) ^ s) ^ (1 / s) := by
              rw [← ENNReal.rpow_mul, one_div_mul_cancel hs.ne', ENNReal.rpow_one]
      _ ≤ (((∑ i ∈ t, (a i) ^ s) ^ (1 / s)) ^ r + (a x) ^ r) ^ (1 / r) := hpair
      _ ≤ (∑ i ∈ t, (a i) ^ r + (a x) ^ r) ^ (1 / r) := by
              gcongr

/-- Homogeneous variation decreases as its exponent increases. -/
theorem rVariation_mono_exponent {E : Type*} [NormedAddCommGroup E]
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (u : Scale → E) :
    rVariation s u ≤ rVariation r u := by
  rw [rVariation_eq, rVariation_eq]
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  let increments : Fin length → ℝ≥0∞ := fun i =>
    ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖
  change (∑ i : Fin length, (increments i) ^ s) ^ s⁻¹ ≤ rVariation r u
  calc
    (∑ i : Fin length, (increments i) ^ s) ^ s⁻¹
        ≤ (∑ i : Fin length, (increments i) ^ r) ^ r⁻¹ := by
          simpa only [one_div] using
            finiteENNReal_rpow_sum_mono_exponent (t := Finset.univ) increments hr hrs
    _ ≤ rVariation r u := by
      exact le_iSup_of_le length (le_iSup_of_le chain le_rfl)

/-- A fixed finite-chain contribution decreases as its exponent increases. -/
theorem chainVariation_mono_exponent {E : Type*} [NormedAddCommGroup E]
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (u : Scale → E)
    {length : ℕ} (chain : StrictScaleChain length) :
    chainVariation s u chain ≤ chainVariation r u chain := by
  rw [chainVariation_eq, chainVariation_eq]
  let increments : Fin length → ℝ≥0∞ := fun i =>
    ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖
  change (∑ i : Fin length, (increments i) ^ s) ^ s⁻¹ ≤
    (∑ i : Fin length, (increments i) ^ r) ^ r⁻¹
  simpa only [one_div] using
    finiteENNReal_rpow_sum_mono_exponent (t := Finset.univ) increments hr hrs

/-- Restricting a scale family along a strictly increasing reindexing cannot
increase its homogeneous variation. -/
theorem rVariation_comp_le {E : Type*} [NormedAddCommGroup E] (r : ℝ)
    (u : Scale → E) (φ : Scale → Scale) (hφ : StrictMono φ) :
    rVariation r (u ∘ φ) ≤ rVariation r u := by
  rw [rVariation_eq]
  apply iSup_le
  intro length
  apply iSup_le
  intro chain
  let imageChain : StrictScaleChain length :=
    { index := fun i => φ (chain.index i)
      strictMono := hφ.comp chain.strictMono }
  change
    (∑ i : Fin length,
      (ENNReal.ofReal ‖u (φ (chain.index i.succ)) - u (φ (chain.index i.castSucc))‖).rpow r).rpow r⁻¹
      ≤ rVariation r u
  calc
    (∑ i : Fin length,
      (ENNReal.ofReal ‖u (φ (chain.index i.succ)) - u (φ (chain.index i.castSucc))‖).rpow r).rpow r⁻¹
        = (∑ i : Fin length,
          (ENNReal.ofReal ‖u (imageChain.index i.succ) -
            u (imageChain.index i.castSucc)‖).rpow r).rpow r⁻¹ := by rfl
    _ ≤ rVariation r u := by
      exact le_iSup_of_le length (le_iSup_of_le imageChain le_rfl)

end

end FractionalPrimes
