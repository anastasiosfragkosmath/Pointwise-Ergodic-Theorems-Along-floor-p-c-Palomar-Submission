module

public import FractionalPrimes.Core
public import FractionalPrimes.Systems
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Finite averages on `L^p`

This module records elementary measurability and finite-norm facts for the
unweighted averages. These facts use only preservation of the underlying
measure by the individual time maps.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

theorem aestronglyMeasurable_shift_floorPower {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (n : ℕ) {f : X → ℂ}
    (hf : AEStronglyMeasurable f S.μ) :
    AEStronglyMeasurable (S.shift (floorPower c n) f) S.μ := by
  have hshift : S.shift (floorPower c n) f =
      f ∘ ((S.T : X → X)^[floorTime c n]) := by
    funext x
    exact S.shift_floorPower_apply c n f x
  rw [hshift]
  exact MeasureTheory.AEStronglyMeasurable.comp_measurePreserving hf
    (S.measurePreserving_floorTime c n)

theorem memLp_shift_floorPower {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (n : ℕ) {p : ℝ≥0∞} {f : X → ℂ}
    (hf : MemLp f p S.μ) :
    MemLp (S.shift (floorPower c n) f) p S.μ := by
  have hshift : S.shift (floorPower c n) f =
      f ∘ ((S.T : X → X)^[floorTime c n]) := by
    funext x
    exact S.shift_floorPower_apply c n f x
  rw [hshift]
  exact hf.comp_measurePreserving (S.measurePreserving_floorTime c n)

theorem eLpNorm_shift_floorPower {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (n : ℕ) {p : ℝ≥0∞} {f : X → ℂ}
    (hf : AEStronglyMeasurable f S.μ) :
    eLpNorm (S.shift (floorPower c n) f) p S.μ = eLpNorm f p S.μ := by
  have hshift : S.shift (floorPower c n) f =
      f ∘ ((S.T : X → X)^[floorTime c n]) := by
    funext x
    exact S.shift_floorPower_apply c n f x
  rw [hshift]
  exact eLpNorm_comp_measurePreserving hf (S.measurePreserving_floorTime c n)

/-- The unweighted average is a scalar multiple of the finite sum of its translates. -/
theorem unweightedAverage_eq_smul_sum_shift_floorPower {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) (N : Scale) :
    unweightedAverage S c f N = (N.1 : ℂ)⁻¹ •
      ∑ n ∈ Finset.Icc 1 N.1, S.shift (floorPower c n) f := by
  funext x
  simp [unweightedAverage, weightedAverage, InvertibleSystem.shift]

/-- A finite unweighted average of an almost strongly measurable function is almost strongly
measurable. -/
theorem aestronglyMeasurable_unweightedAverage {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) (N : Scale)
    (hf : AEStronglyMeasurable f S.μ) :
    AEStronglyMeasurable (unweightedAverage S c f N) S.μ := by
  rw [unweightedAverage_eq_smul_sum_shift_floorPower]
  apply AEStronglyMeasurable.const_smul
  have hsum := Finset.aestronglyMeasurable_fun_sum (Finset.Icc 1 N.1)
    (fun n _ => aestronglyMeasurable_shift_floorPower S c n hf)
  convert hsum using 1
  ext x
  simp only [Finset.sum_apply]

/-- A finite unweighted average of an `Lᵖ` function remains in `Lᵖ`. -/
theorem memLp_unweightedAverage {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) (N : Scale) {p : ℝ≥0∞}
    (hf : MemLp f p S.μ) :
    MemLp (unweightedAverage S c f N) p S.μ := by
  rw [unweightedAverage_eq_smul_sum_shift_floorPower]
  apply MemLp.const_smul
  have hsum := memLp_finsetSum (Finset.Icc 1 N.1)
    (fun n _ => memLp_shift_floorPower S c n hf)
  convert hsum using 1
  ext x
  simp only [Finset.sum_apply]

/-- Minkowski's inequality gives a finite-sum `Lᵖ` estimate for every unweighted average. -/
theorem eLpNorm_unweightedAverage_le {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) (N : Scale) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hf : AEStronglyMeasurable f S.μ) :
    eLpNorm (unweightedAverage S c f N) p S.μ ≤ ‖(N.1 : ℂ)⁻¹‖ₑ *
      ∑ _ ∈ Finset.Icc 1 N.1, eLpNorm f p S.μ := by
  rw [unweightedAverage_eq_smul_sum_shift_floorPower, eLpNorm_const_smul]
  calc
    ‖(N.1 : ℂ)⁻¹‖ₑ * eLpNorm (∑ n ∈ Finset.Icc 1 N.1,
        S.shift (floorPower c n) f) p S.μ ≤
        ‖(N.1 : ℂ)⁻¹‖ₑ * ∑ n ∈ Finset.Icc 1 N.1,
          eLpNorm (S.shift (floorPower c n) f) p S.μ :=
      mul_le_mul_of_nonneg_left (eLpNorm_sum_le hp) bot_le
    _ = ‖(N.1 : ℂ)⁻¹‖ₑ * ∑ _ ∈ Finset.Icc 1 N.1, eLpNorm f p S.μ := by
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      exact eLpNorm_shift_floorPower S c n hf

/-- Each finite unweighted average is an `Lᵖ` contraction when `p ≥ 1`. -/
theorem eLpNorm_unweightedAverage_le_self {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (f : X → ℂ) (N : Scale) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hf : AEStronglyMeasurable f S.μ) :
    eLpNorm (unweightedAverage S c f N) p S.μ ≤ eLpNorm f p S.μ := by
  calc
    eLpNorm (unweightedAverage S c f N) p S.μ ≤ ‖(N.1 : ℂ)⁻¹‖ₑ *
        ∑ _ ∈ Finset.Icc 1 N.1, eLpNorm f p S.μ :=
      eLpNorm_unweightedAverage_le S c f N hp hf
    _ = eLpNorm f p S.μ := by
      have hNcomplex : (N.1 : ℂ) ≠ 0 := by
        exact_mod_cast N.2.ne'
      have hN : (N.1 : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast N.2.ne'
      rw [enorm_inv hNcomplex]
      have henorm : ‖(N.1 : ℂ)‖ₑ = (N.1 : ℝ≥0∞) := by
        simp [enorm]
      rw [henorm]
      simp [Nat.card_Icc]
      rw [← mul_assoc, ENNReal.inv_mul_cancel hN ENNReal.coe_ne_top, one_mul]

end

end FractionalPrimes

end
