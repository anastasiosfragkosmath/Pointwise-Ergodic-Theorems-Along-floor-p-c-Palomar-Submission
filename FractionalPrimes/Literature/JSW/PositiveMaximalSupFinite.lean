module

public import FractionalPrimes.Literature.JSW.PositiveSquaredSliceIntegrable
public import FractionalPrimes.Literature.JSW.FiniteDenseMaximalInterpolation

/-!
# Almost-everywhere finiteness of monotone positive maximal suprema

This exposes the finite-supremum step in the checked JSW maximal proof,
which is needed to compare raw scale values with the real maximal
representative outside a null set.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal
open scoped Topology

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- Uniform finite `L^q` bounds on a monotone sequence of nonnegative
measurable functions force the extended pointwise supremum to be finite
a.e. -/
theorem iSup_ofReal_lt_top_ae_of_uniform_eLpNorm
    {q : ℝ} (hq : 0 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (f : ℕ → ℝ → ℝ) (hf : ∀ n, Measurable (f n))
    (hnonneg : ∀ n, ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ f n x)
    (hmono : ∀ n, ∀ᵐ x ∂(volume : Measure ℝ), f n x ≤ f n.succ x)
    {C : ℝ≥0∞} (hCtop : C ≠ ∞)
    (hbound : ∀ n, eLpNorm (f n) (ENNReal.ofReal q) volume ≤ C) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      (⨆ n, ENNReal.ofReal (f n x)) < ∞ := by
  let P : ℝ≥0∞ := ENNReal.ofReal q
  have hP0 : P ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hPtop : P ≠ ∞ := ENNReal.ofReal_ne_top
  have hPtoReal : P.toReal = q := by simp [P, hq.le]
  let U : ℝ → ℝ≥0∞ := fun x => ⨆ n, ENNReal.ofReal (f n x)
  let W : ℕ → ℝ → ℝ≥0∞ := fun n x => ENNReal.ofReal (f n x) ^ q
  have hUmeas : Measurable U := by
    dsimp [U]
    exact Measurable.iSup fun n => ENNReal.continuous_ofReal.measurable.comp (hf n)
  have hWmeas : ∀ n, Measurable (W n) := by
    intro n
    dsimp [W]
    exact (ENNReal.continuous_rpow_const (y := q)).measurable.comp
      (ENNReal.continuous_ofReal.measurable.comp (hf n))
  have hWmono : ∀ n, ∀ᵐ x ∂(volume : Measure ℝ), W n x ≤ W n.succ x := by
    intro n
    filter_upwards [hmono n] with x hx
    dsimp [W]
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal hx) hq.le
  have hWsup : ∀ᵐ x ∂(volume : Measure ℝ), (⨆ n, W n x) = U x ^ q := by
    filter_upwards [ae_all_iff.mpr hmono] with x hx
    have hvmono : Monotone (fun n => ENNReal.ofReal (f n x)) := by
      intro n m hnm
      induction hnm with
      | refl => exact le_rfl
      | @step m hnm ih =>
          exact ih.trans (ENNReal.ofReal_le_ofReal (hx m))
    let v : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (f n x)
    have hv : Tendsto v atTop (𝓝 (⨆ n, v n)) :=
      tendsto_atTop_iSup (by simpa [v] using hvmono)
    have hvpow : Tendsto (fun n => v n ^ q) atTop
        (𝓝 ((⨆ n, v n) ^ q)) :=
      (ENNReal.continuous_rpow_const (y := q)).continuousAt.tendsto.comp hv
    have hvpowMono : Monotone (fun n => v n ^ q) := by
      intro n m hnm
      exact ENNReal.rpow_le_rpow (hvmono hnm) hq.le
    have hvpowSup : Tendsto (fun n => v n ^ q) atTop
        (𝓝 (⨆ n, v n ^ q)) := tendsto_atTop_iSup hvpowMono
    have hEq := tendsto_nhds_unique hvpowSup hvpow
    simpa [U, W, v] using hEq
  have hWint_eq :
      (∫⁻ x, U x ^ q ∂(volume : Measure ℝ)) =
        ⨆ n, ∫⁻ x, W n x ∂(volume : Measure ℝ) := by
    calc
      _ = ∫⁻ x, ⨆ n, W n x ∂(volume : Measure ℝ) := by
        apply lintegral_congr_ae
        filter_upwards [hWsup] with x hx
        exact hx.symm
      _ = _ := lintegral_iSup_ae hWmeas hWmono
  have hWbound (n : ℕ) :
      ∫⁻ x, W n x ∂(volume : Measure ℝ) ≤ C ^ q := by
    have hnormIntegral :
        eLpNorm (f n) P volume ^ q = ∫⁻ x, W n x ∂(volume : Measure ℝ) := by
      calc
        _ = (∫⁻ x, ‖f n x‖ₑ ^ q ∂(volume : Measure ℝ)) := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop
            (hf n).aestronglyMeasurable, hPtoReal]
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
        _ = _ := by
          apply lintegral_congr_ae
          filter_upwards [hnonneg n] with x hx
          simp [W, Real.enorm_eq_ofReal_abs, abs_of_nonneg hx]
    rw [← hnormIntegral]
    exact ENNReal.rpow_le_rpow (hbound n) hq.le
  have hWintBound :
      (∫⁻ x, U x ^ q ∂(volume : Measure ℝ)) ≤ C ^ q := by
    rw [hWint_eq]
    exact iSup_le hWbound
  have hCpow : C ^ q ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq.le hCtop
  have hUqfinite : ∀ᵐ x ∂(volume : Measure ℝ), U x ^ q < ∞ :=
    ae_lt_top ((ENNReal.continuous_rpow_const (y := q)).measurable.comp hUmeas)
      (ne_top_of_le_ne_top hCpow hWintBound)
  have hUfinite : ∀ᵐ x ∂(volume : Measure ℝ), U x < ∞ := by
    filter_upwards [hUqfinite] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos hq).mp hx
  simpa only [U] using hUfinite

/-- Outside the exceptional set where an extended maximal supremum is
infinite, every real scale value is bounded by its real maximal
representative. Negative scale values are covered without a
nonnegativity hypothesis. -/
theorem real_le_toReal_iSup_ofReal_of_lt_top
    {ι : Type*} (f : ι → ℝ) (i : ι)
    (hfinite : (⨆ j, ENNReal.ofReal (f j)) < ∞) :
    f i ≤ (⨆ j, ENNReal.ofReal (f j)).toReal := by
  by_cases hnonneg : 0 ≤ f i
  · have hi : ENNReal.ofReal (f i) ≤
        (⨆ j, ENNReal.ofReal (f j)) := le_iSup (fun j => ENNReal.ofReal (f j)) i
    have hmono := ENNReal.toReal_mono (ne_top_of_lt hfinite) hi
    simpa [ENNReal.toReal_ofReal hnonneg] using hmono
  · exact (le_of_lt (lt_of_not_ge hnonneg)).trans ENNReal.toReal_nonneg

#print axioms iSup_ofReal_lt_top_ae_of_uniform_eLpNorm
#print axioms real_le_toReal_iSup_ofReal_of_lt_top

end

end FractionalPrimes.Literature.JSW

end
