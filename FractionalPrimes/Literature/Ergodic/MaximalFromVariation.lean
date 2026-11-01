module

public import FractionalPrimes.VariationConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
noncomputable section

def scaleFamilyMaximal {X : Type*} (F : Scale → X → ℂ) : X → ℝ≥0∞ :=
  fun x => ⨆ N : Scale, ENNReal.ofReal ‖F N x‖

theorem scaleFamilyMaximal_le_base_add_variation
    {X : Type*} (r : ℝ) (hr : 0 < r) (F : Scale → X → ℂ)
    (base : Scale) (x : X) :
    scaleFamilyMaximal F x ≤ ENNReal.ofReal ‖F base x‖ + rVariationFun r F x := by
  apply iSup_le
  intro N
  have hnorm : ‖F N x‖ ≤ ‖F base x‖ + ‖F N x - F base x‖ := by
    calc
      _ = ‖F base x + (F N x - F base x)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  calc
    _ ≤ ENNReal.ofReal (‖F base x‖ + ‖F N x - F base x‖) := ENNReal.ofReal_le_ofReal hnorm
    _ = ENNReal.ofReal ‖F base x‖ + ENNReal.ofReal ‖F N x - F base x‖ :=
      ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := add_le_add (le_refl _)
      (enorm_sub_le_rVariation_of_base r hr (fun N => F N x) base N)

theorem aemeasurable_scaleFamilyMaximal
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : Scale → X → ℂ) (hF : ∀ N, AEStronglyMeasurable (F N) μ) :
    AEMeasurable (scaleFamilyMaximal F) μ := by
  change AEMeasurable (fun x => ⨆ N : Scale, ENNReal.ofReal ‖F N x‖) μ
  have hcoord (N : Scale) : AEMeasurable (fun x => ENNReal.ofReal ‖F N x‖) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable (hF N).norm.aemeasurable
  exact AEMeasurable.iSup hcoord

theorem eLpNorm_scaleFamilyMaximal_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℝ) (hr : 0 < r)
    (F : Scale → X → ℂ) (hF : ∀ N, AEStronglyMeasurable (F N) μ) (base : Scale) :
    eLpNorm (scaleFamilyMaximal F) p μ ≤
      eLpNorm (F base) p μ + eLpNorm (rVariationFun r F) p μ := by
  have hmax := aemeasurable_scaleFamilyMaximal μ F hF
  have hdom : eLpNorm (scaleFamilyMaximal F) p μ ≤
      eLpNorm (fun x => ENNReal.ofReal ‖F base x‖ + rVariationFun r F x) p μ := by
    apply eLpNorm_mono_enorm_ae (f := scaleFamilyMaximal F)
      (g := fun x => ENNReal.ofReal ‖F base x‖ + rVariationFun r F x)
      hmax.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [enorm_eq_self] using scaleFamilyMaximal_le_base_add_variation r hr F base x)
  have hsum : eLpNorm (fun x => ENNReal.ofReal ‖F base x‖ + rVariationFun r F x) p μ ≤
      eLpNorm (fun x => ENNReal.ofReal ‖F base x‖) p μ +
        eLpNorm (rVariationFun r F) p μ :=
    eLpNorm_add_le (f := fun x => ENNReal.ofReal ‖F base x‖) (g := rVariationFun r F) hp
  have hbase : eLpNorm (fun x => ENNReal.ofReal ‖F base x‖) p μ = eLpNorm (F base) p μ := by
    simpa only [ofReal_norm] using eLpNorm_enorm (p := p) (F base) (hF base)
  rw [hbase] at hsum
  exact hdom.trans hsum

#print axioms eLpNorm_scaleFamilyMaximal_le
end
end FractionalPrimes
