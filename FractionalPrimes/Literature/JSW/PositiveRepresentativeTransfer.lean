module

public import FractionalPrimes.Literature.JSW.PositiveMaximalSupFinite

/-!
# AE representative transfer through translated finite-measure integrals

An `Lᵖ` representative may be only almost-everywhere measurable. The
source positive maximal adapter needs its translated finite-measure
averages to be independent of that representative for almost every
spatial point.
-/

@[expose] public section

open MeasureTheory

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- Almost-everywhere equal real functions have the same translated
finite-measure average for almost every spatial point. No pointwise
measurability assumption on either representative is needed. -/
theorem integral_add_translation_congr_ae
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f g : ℝ → ℝ) (hfg : f =ᵐ[volume] g) :
    (fun x : ℝ => ∫ y, f (x + y) ∂μ) =ᵐ[volume]
      (fun x : ℝ => ∫ y, g (x + y) ∂μ) := by
  have hfst :
      (fun z : ℝ × ℝ => f z.1) =ᵐ[volume.prod μ]
        (fun z : ℝ × ℝ => g z.1) :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hfg
  have hshear :
      (fun z : ℝ × ℝ => f (z.1 + z.2)) =ᵐ[volume.prod μ]
        (fun z : ℝ × ℝ => g (z.1 + z.2)) := by
    simpa only [Function.comp_def] using
      (measurePreserving_add_prod volume μ).quasiMeasurePreserving.ae_eq_comp hfst
  have hslices : ∀ᵐ x ∂volume,
      (fun y : ℝ => f (x + y)) =ᵐ[μ]
        (fun y : ℝ => g (x + y)) :=
    Measure.ae_ae_of_ae_prod hshear
  filter_upwards [hslices] with x hx
  exact integral_congr_ae hx

#print axioms integral_add_translation_congr_ae

/-- Almost-everywhere equal complex inputs also have equal subtraction
convolution averages for almost every spatial point. -/
theorem integral_sub_translation_congr_ae
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f g : ℝ → ℂ) (hfg : f =ᵐ[volume] g) :
    (fun x : ℝ => ∫ y, f (x - y) ∂μ) =ᵐ[volume]
      (fun x : ℝ => ∫ y, g (x - y) ∂μ) := by
  have hfst :
      (fun z : ℝ × ℝ => f z.1) =ᵐ[volume.prod μ]
        (fun z : ℝ × ℝ => g z.1) :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hfg
  have hshear :
      (fun z : ℝ × ℝ => f (z.1 - z.2)) =ᵐ[volume.prod μ]
        (fun z : ℝ × ℝ => g (z.1 - z.2)) := by
    simpa only [Function.comp_def] using
      (measurePreserving_sub_prod volume μ).quasiMeasurePreserving.ae_eq_comp hfst
  have hslices : ∀ᵐ x ∂volume,
      (fun y : ℝ => f (x - y)) =ᵐ[μ]
        (fun y : ℝ => g (x - y)) :=
    Measure.ae_ae_of_ae_prod hshear
  filter_upwards [hslices] with x hx
  exact integral_congr_ae hx

#print axioms integral_sub_translation_congr_ae

/-- Complex-valued addition averages also respect almost-everywhere
representatives for any finite measure. -/
theorem integral_add_complex_translation_congr_ae
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f g : ℝ → ℂ) (hfg : f =ᵐ[volume] g) :
    (fun x : ℝ => ∫ y, f (x + y) ∂μ) =ᵐ[volume]
      (fun x : ℝ => ∫ y, g (x + y) ∂μ) := by
  have hfst :
      (fun z : ℝ × ℝ => f z.1) =ᵐ[volume.prod μ]
        (fun z : ℝ × ℝ => g z.1) :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hfg
  have hshear :
      (fun z : ℝ × ℝ => f (z.1 + z.2)) =ᵐ[volume.prod μ]
        (fun z : ℝ × ℝ => g (z.1 + z.2)) := by
    simpa only [Function.comp_def] using
      (measurePreserving_add_prod volume μ).quasiMeasurePreserving.ae_eq_comp hfst
  have hslices : ∀ᵐ x ∂volume,
      (fun y : ℝ => f (x + y)) =ᵐ[μ]
        (fun y : ℝ => g (x + y)) :=
    Measure.ae_ae_of_ae_prod hshear
  filter_upwards [hslices] with x hx
  exact integral_congr_ae hx

#print axioms integral_add_complex_translation_congr_ae

end

end FractionalPrimes.Literature.JSW

end
