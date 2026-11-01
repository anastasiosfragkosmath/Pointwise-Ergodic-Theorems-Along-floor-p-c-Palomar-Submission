module
public import FractionalPrimes.Literature.Ergodic.FiniteKernelTransference
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory Filter
open FractionalPrimes.Literature.Ergodic
open scoped ENNReal Topology
noncomputable section

/-- Summability of p-th powers of Lp norms implies pointwise convergence
to zero almost everywhere, even on a space of infinite measure. -/
theorem ae_tendsto_zero_of_tsum_eLpNorm_rpow_ne_top
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ} (hp : 0 < p)
    (F : ℕ → X → ℂ) (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (hsum : (∑' k, eLpNorm (F k) (ENNReal.ofReal p) μ ^ p) ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 0) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hmeas (k : ℕ) : AEMeasurable (fun x => ‖F k x‖ₑ ^ p) μ :=
    (ENNReal.continuous_rpow_const (y := p)).measurable.comp_aemeasurable (hF k).enorm
  have hmom (k : ℕ) : ∫⁻ x, ‖F k x‖ₑ ^ p ∂μ = eLpNorm (F k) (ENNReal.ofReal p) μ ^ p := by
    have h := extendedLpNorm_rpow μ (ENNReal.ofReal p) (fun x => ‖F k x‖ₑ)
      hp0 ENNReal.ofReal_ne_top
    rw [extendedLpNorm_eq_eLpNorm μ _ (F k) hp0 ENNReal.ofReal_ne_top (hF k),
      ENNReal.toReal_ofReal hp.le] at h
    exact h.symm
  have hfinite : (∫⁻ x, ∑' k, ‖F k x‖ₑ ^ p ∂μ) ≠ ∞ := by
    rw [lintegral_tsum hmeas]
    simpa only [hmom] using hsum
  have hAE := ae_lt_top' (AEMeasurable.tsum hmeas) hfinite
  filter_upwards [hAE] with x hx
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne
  have hroot := (ENNReal.continuous_rpow_const (y := p⁻¹)).continuousAt.tendsto.comp ht
  have hnorm : Tendsto (fun k => ‖F k x‖ₑ) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.rpow_eq_pow, ← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one,
      ENNReal.zero_rpow_of_pos (inv_pos.mpr hp)] using hroot
  exact (tendsto_zero_iff_enorm_tendsto_zero).mpr hnorm

theorem ae_tendsto_zero_of_tsum_ennreal_eLpNorm_rpow_ne_top
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ} (hp : 0 < p)
    (F : ℕ → X → ℝ≥0∞) (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (hsum : (∑' k, eLpNorm (F k) (ENNReal.ofReal p) μ ^ p) ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 0) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hmeas (k : ℕ) : AEMeasurable (fun x => ‖F k x‖ₑ ^ p) μ :=
    (ENNReal.continuous_rpow_const (y := p)).measurable.comp_aemeasurable (hF k).enorm
  have hmom (k : ℕ) : ∫⁻ x, ‖F k x‖ₑ ^ p ∂μ = eLpNorm (F k) (ENNReal.ofReal p) μ ^ p := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top (hF k),
      ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul]
    simp [one_div, hp.ne']
  have hfinite : (∫⁻ x, ∑' k, ‖F k x‖ₑ ^ p ∂μ) ≠ ∞ := by
    rw [lintegral_tsum hmeas]
    simpa only [hmom] using hsum
  have hAE := ae_lt_top' (AEMeasurable.tsum hmeas) hfinite
  filter_upwards [hAE] with x hx
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne
  have hroot := (ENNReal.continuous_rpow_const (y := p⁻¹)).continuousAt.tendsto.comp ht
  have hnorm : Tendsto (fun k => ‖F k x‖ₑ) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.rpow_eq_pow, ← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one,
      ENNReal.zero_rpow_of_pos (inv_pos.mpr hp)] using hroot
  simpa only [enorm_eq_self] using hnorm

/-- A p-summable scalar majorant of Lp norms gives an almost-sure zero limit. -/
theorem ae_tendsto_zero_of_summable_coefficient
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ} (hp : 0 < p)
    (F : ℕ → X → ℝ≥0∞) (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (E : ℕ → ℝ) (hE : ∀ k, 0 ≤ E k) (hseries : Summable (fun k => (E k) ^ p))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ k, eLpNorm (F k) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (E k) * C) :
    ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 0) := by
  have hcoeff : (∑' k, (ENNReal.ofReal (E k)) ^ p) ≠ ∞ := by
    have heq : (∑' k, (ENNReal.ofReal (E k)) ^ p) = ENNReal.ofReal (∑' k, E k ^ p) := by
      calc
        _ = ∑' k, ENNReal.ofReal (E k ^ p) := tsum_congr (fun k =>
          (ENNReal.ofReal_rpow_of_nonneg (hE k) hp.le))
        _ = _ := (ENNReal.ofReal_tsum_of_nonneg (fun k => Real.rpow_nonneg (hE k) p) hseries).symm
    rw [heq]
    exact ENNReal.ofReal_ne_top
  apply ae_tendsto_zero_of_tsum_ennreal_eLpNorm_rpow_ne_top μ hp F hF
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hcoeff
    (ENNReal.rpow_ne_top_of_nonneg hp.le hC))
  calc
    _ ≤ ∑' k, (ENNReal.ofReal (E k) * C) ^ p :=
      ENNReal.tsum_le_tsum (fun k => ENNReal.rpow_le_rpow (hbound k) hp.le)
    _ = _ := by simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]; rw [ENNReal.tsum_mul_right]


#print axioms ae_tendsto_zero_of_tsum_eLpNorm_rpow_ne_top
end
end FractionalPrimes.Final
