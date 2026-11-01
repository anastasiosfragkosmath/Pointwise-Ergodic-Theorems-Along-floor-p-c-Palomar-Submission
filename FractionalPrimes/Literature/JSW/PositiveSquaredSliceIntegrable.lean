module

public import FractionalPrimes.Literature.JSW.PositiveEnergyPairing

/-!
# Almost-everywhere integrability of translated squares

For the JSW probability-measure Jensen step, an `L^p` input with `p>2`
has squared translates integrable against any finite measure for almost
every spatial point. Compact support of the measure is unnecessary.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

theorem integrable_sq_translation_ae_of_memLp
    {p : ℝ} (hp : 2 < p)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂volume, Integrable (fun y => ‖f (x - y)‖ ^ 2) μ := by
  let r : ℝ := p / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hsq : MemLp (fun x => ‖f x‖ ^ 2)
      (ENNReal.ofReal r) volume := by
    have h := hf.norm_rpow_div (2 : ℝ≥0∞)
    convert h using 1
    · ext x
      simp
    · dsimp [r]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ))]
      norm_num
  have hprod : MemLp
      (fun z : ℝ × ℝ => ‖f (z.1 - z.2)‖ ^ 2)
      (ENNReal.ofReal r) (volume.prod μ) := by
    exact (hsq.comp_fst μ).comp_measurePreserving
      (measurePreserving_sub_prod volume μ)
  apply ae_of_forall_measure_lt_top_ae_restrict
    (μ := volume)
    (fun x => Integrable (fun y => ‖f (x - y)‖ ^ 2) μ)
  intro s hs hfinite
  letI : IsFiniteMeasure (volume.restrict s) := ⟨by simpa using hfinite⟩
  letI : IsFiniteMeasure ((volume.restrict s).prod μ) := inferInstance
  have hlocal : MemLp
      (fun z : ℝ × ℝ => ‖f (z.1 - z.2)‖ ^ 2)
      (ENNReal.ofReal r) ((volume.restrict s).prod μ) :=
    hprod.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hlocalOne : MemLp
      (fun z : ℝ × ℝ => ‖f (z.1 - z.2)‖ ^ 2)
      1 ((volume.restrict s).prod μ) :=
    hlocal.mono_exponent (ENNReal.one_le_ofReal.mpr hr.le)
  have hint : Integrable
      (fun z : ℝ × ℝ => ‖f (z.1 - z.2)‖ ^ 2)
      ((volume.restrict s).prod μ) :=
    memLp_one_iff_integrable.mp hlocalOne
  exact (integrable_prod_iff hint.aestronglyMeasurable).mp hint |>.1

#print axioms integrable_sq_translation_ae_of_memLp

end

end FractionalPrimes.Literature.JSW

end
