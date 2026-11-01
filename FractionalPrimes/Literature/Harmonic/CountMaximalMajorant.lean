module

public import FractionalPrimes.GeneralDiscreteLpBridge
public import FractionalPrimes.VariationConvergence

/-! A finite counting-measure maximal bound gives an actual nonnegative real lp majorant. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.Harmonic
noncomputable section

theorem realSequenceMajorant_of_ennreal_eLpNorm_bound
    {p B : ℝ} (hp : 1 < p) (hB : 0 ≤ B) (H : ℤ → ℝ≥0∞)
    (hH : MemLp H (ENNReal.ofReal p) (Measure.count : Measure ℤ))
    (hbound : eLpNorm H (ENNReal.ofReal p) Measure.count ≤ ENNReal.ofReal B) :
    ∃ g : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p),
      (∀ x, g x = (H x).toReal) ∧ (∀ x, 0 ≤ g x) ∧
      (∀ x, ENNReal.ofReal (g x) = H x) ∧ ‖g‖ ≤ B := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hfinite : ∀ x, H x < ∞ := ae_count_int_iff_forall.mp
    (ae_lt_top_of_memLp_ennreal (by linarith : 0 < p) H hH)
  have hreal := memLp_toReal_of_memLp_ennreal (by linarith : 0 < p) H hH
  have hz : MemLp (fun x => ((H x).toReal : ℂ)) (ENNReal.ofReal p) Measure.count :=
    Complex.ofRealCLM.comp_memLp' hreal
  let F := hz.toLp (fun x => ((H x).toReal : ℂ))
  let W := countLpToGeneralLp hp0 ENNReal.ofReal_ne_top F
  have hw (x : ℤ) : W x = ((H x).toReal : ℂ) :=
    (countLpToGeneralLp_apply hp0 ENNReal.ofReal_ne_top F x).trans
      (ae_count_int_iff_forall.mp hz.coeFn_toLp x)
  let g : lp (fun _ : ℤ => ℝ) (ENNReal.ofReal p) :=
    ⟨fun x => (W x).re, (lp.memℓp W).mono' (fun x => Complex.abs_re_le_norm (W x))⟩
  have hg (x : ℤ) : g x = (H x).toReal := by
    change (W x).re = _
    rw [hw,Complex.ofReal_re]
  have hnorm : ‖g‖ ≤ ‖W‖ := lp.norm_mono hp0 (fun x => Complex.abs_re_le_norm (W x))
  have he : eLpNorm (fun x => ((H x).toReal : ℂ)) (ENNReal.ofReal p) Measure.count =
      eLpNorm H (ENNReal.ofReal p) Measure.count := by
    apply eLpNorm_congr_enorm_ae hz.aestronglyMeasurable hH.aestronglyMeasurable
    filter_upwards [] with x
    rw [← ofReal_norm,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (hfinite x).ne]
    simp
  have hnW : ‖W‖ = (eLpNorm H (ENNReal.ofReal p) Measure.count).toReal := by
    rw [countLpToGeneralLp_norm,Lp.norm_def]
    exact congrArg ENNReal.toReal ((eLpNorm_congr_ae hz.coeFn_toLp).trans he)
  have hnormB := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal hB] at hnormB
  refine ⟨g,hg,fun x => ?_,fun x => ?_,?_⟩
  · rw [hg]
    exact ENNReal.toReal_nonneg
  · rw [hg,ENNReal.ofReal_toReal (hfinite x).ne]
  · exact hnorm.trans (hnW ▸ hnormB)

#print axioms realSequenceMajorant_of_ennreal_eLpNorm_bound
end
end FractionalPrimes.Literature.Harmonic
end
