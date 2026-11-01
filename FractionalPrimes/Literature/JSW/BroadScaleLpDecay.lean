module

public import FractionalPrimes.Literature.JSW.ComplexMeasureYoung
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic

/-!
# Broad-scale decay from L¹ mass and a shrinking pointwise bound

This is the abstract interpolation step in the high-pass part of the
Littlewood--Paley resolution. The kernel and convolution identities
are handled in the caller.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace FractionalPrimes.Literature.JSW

/-- Equality under the measure weighted by `‖K‖` suffices to replace a
representative in an integral multiplied by `K`. -/
theorem integral_mul_congr_of_ae_withDensity_norm
    (K f g : ℝ → ℂ) (hK : Measurable K)
    (hfg : f =ᵐ[(volume : Measure ℝ).withDensity
      (fun y => ENNReal.ofReal ‖K y‖)] g) :
    (∫ y : ℝ, K y * f y ∂volume) =
      ∫ y : ℝ, K y * g y ∂volume := by
  have hd : Measurable (fun y : ℝ => ENNReal.ofReal ‖K y‖) :=
    hK.norm.ennreal_ofReal
  have hfg' : ∀ᵐ y : ℝ ∂volume,
      ENNReal.ofReal ‖K y‖ ≠ 0 → f y = g y :=
    (ae_withDensity_iff hd).mp hfg
  apply integral_congr_ae
  filter_upwards [hfg'] with y hy
  by_cases hKy : K y = 0
  · simp [hKy]
  · have hdens : ENNReal.ofReal ‖K y‖ ≠ 0 := by
      exact (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hKy)).ne'
    rw [hy hdens]

/-- If a family has uniformly bounded `L¹` mass and its pointwise
norm is bounded almost everywhere by a sequence tending to zero,
then its `Lᵖ` norm tends to zero for every `p>1`. -/
theorem lp_tendsto_zero_of_L1_bound_and_sup_tendsto
    {p : ℝ} (hp : 1 < p)
    (u : ℕ → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (A : ℕ → ℝ) (hA : Tendsto A atTop (𝓝 0))
    (hA0 : ∀ n, 0 ≤ A n)
    (B : ℝ)
    (hL1 : ∀ n, Integrable (fun x : ℝ => ‖(u n : ℝ → ℂ) x‖) volume ∧
      (∫ x : ℝ, ‖(u n : ℝ → ℂ) x‖ ∂volume) ≤ B)
    (hSup : ∀ n, ∀ᵐ x : ℝ ∂volume, ‖(u n : ℝ → ℂ) x‖ ≤ A n) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    Tendsto u atTop (𝓝 0) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hp0 : 0 < p := by linarith
  have hpm1 : 0 < p - 1 := by linarith
  have hpENN0 : (ENNReal.ofReal p) ≠ 0 := by
    exact ENNReal.ofReal_pos.mpr hp0 |>.ne'
  have hpENNtop : (ENNReal.ofReal p) ≠ ∞ := ENNReal.ofReal_ne_top
  have hnorm (n : ℕ) : ‖u n‖ =
      (∫ x : ℝ, ‖(u n : ℝ → ℂ) x‖ ^ p ∂volume) ^ p⁻¹ := by
    rw [Lp.norm_def]
    change lpNorm (u n : ℝ → ℂ) (ENNReal.ofReal p) volume = _
    rw [lpNorm_eq_integral_norm_rpow_toReal hpENN0 hpENNtop
      (Lp.aestronglyMeasurable (u n))]
    simp [ENNReal.toReal_ofReal hp0.le]
  have hpowerInt (n : ℕ) :
      Integrable (fun x : ℝ => ‖(u n : ℝ → ℂ) x‖ ^ p) volume := by
    simpa [ENNReal.toReal_ofReal hp0.le] using
      (Lp.memLp (u n)).integrable_norm_rpow hpENN0 hpENNtop
  have hbound (n : ℕ) :
      (∫ x : ℝ, ‖(u n : ℝ → ℂ) x‖ ^ p ∂volume) ≤
        (A n) ^ (p - 1) * B := by
    have hpoint : ∀ᵐ x : ℝ ∂volume,
        ‖(u n : ℝ → ℂ) x‖ ^ p ≤
          (A n) ^ (p - 1) * ‖(u n : ℝ → ℂ) x‖ := by
      filter_upwards [hSup n] with x hx
      have hnorm0 : 0 ≤ ‖(u n : ℝ → ℂ) x‖ := norm_nonneg _
      calc
        ‖(u n : ℝ → ℂ) x‖ ^ p =
            ‖(u n : ℝ → ℂ) x‖ ^ ((p - 1) + 1) := by ring
        _ = ‖(u n : ℝ → ℂ) x‖ ^ (p - 1) *
            ‖(u n : ℝ → ℂ) x‖ := by
              rw [Real.rpow_add_of_nonneg hnorm0 hpm1.le (by norm_num)]
              simp
        _ ≤ (A n) ^ (p - 1) * ‖(u n : ℝ → ℂ) x‖ :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hnorm0 hx hpm1.le) hnorm0
    calc
      (∫ x : ℝ, ‖(u n : ℝ → ℂ) x‖ ^ p ∂volume) ≤
          ∫ x : ℝ, (A n) ^ (p - 1) *
            ‖(u n : ℝ → ℂ) x‖ ∂volume := by
              exact integral_mono_ae (hpowerInt n)
                ((hL1 n).1.const_mul _) hpoint
      _ = (A n) ^ (p - 1) *
          ∫ x : ℝ, ‖(u n : ℝ → ℂ) x‖ ∂volume := by
            rw [integral_const_mul]
      _ ≤ (A n) ^ (p - 1) * B :=
        mul_le_mul_of_nonneg_left (hL1 n).2
          (Real.rpow_nonneg (hA0 n) _)
  have hbound0 : Tendsto (fun n => (A n) ^ (p - 1) * B) atTop (𝓝 0) := by
    have hpwr : Tendsto (fun n => (A n) ^ (p - 1)) atTop (𝓝 0) := by
      have hcont := (Real.continuous_rpow_const hpm1.le).continuousAt (x := (0 : ℝ))
      have h := hcont.tendsto.comp hA
      simpa only [Function.comp_def, Real.zero_rpow hpm1.ne'] using h
    simpa using hpwr.mul_const B
  have hint0 : Tendsto
      (fun n => ∫ x : ℝ, ‖(u n : ℝ → ℂ) x‖ ^ p ∂volume)
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun n =>
        integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))
    · exact Filter.Eventually.of_forall hbound
    · exact hbound0
  have hnorm0 : Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by
    have hcont := (Real.continuous_rpow_const (inv_nonneg.mpr hp0.le)).continuousAt
      (x := (0 : ℝ))
    have h := hcont.tendsto.comp hint0
    simpa only [Function.comp_def, Real.zero_rpow (inv_pos.mpr hp0).ne', hnorm]
      using h
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm0

#print axioms lp_tendsto_zero_of_L1_bound_and_sup_tendsto
#print axioms integral_mul_congr_of_ae_withDensity_norm

end FractionalPrimes.Literature.JSW

end
