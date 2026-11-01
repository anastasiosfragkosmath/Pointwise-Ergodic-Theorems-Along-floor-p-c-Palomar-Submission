module

public import FractionalPrimes.Literature.JSW.PositiveProbabilityVectorRealization
public import FractionalPrimes.Literature.JSW.PositiveMaximalReflection

/-!
# Reflected finite-family probability convolution bound

This is the exact adjoint-side upper-exponent test used by the
lower-exponent paragraph of `lj:positivity`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- Reflection changes the subtraction convention for convolution into
the exact addition convention used by the vector adjoint pairing. -/
theorem jswConvolution_reflected_ae_eq_add
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) :
    (fun x => jswConvolution (Measure.map Neg.neg μ) f x) =ᵐ[volume]
      (fun x => ∫ y, f (x + y) ∂μ) := by
  let f' : ℝ → ℂ := hf.mk f
  have hrep : f =ᵐ[volume] f' := hf.ae_eq_mk
  have hf'Strong : StronglyMeasurable f' := hf.stronglyMeasurable_mk
  haveI : IsFiniteMeasure (Measure.map Neg.neg μ) := by infer_instance
  have hsub := integral_sub_translation_congr_ae
    (Measure.map Neg.neg μ) f f' hrep
  have hadd := integral_add_complex_translation_congr_ae μ f f' hrep
  have hmap (x : ℝ) :
      (∫ y, f' (x - y) ∂Measure.map Neg.neg μ) =
        ∫ y, f' (x + y) ∂μ := by
    rw [MeasureTheory.integral_map (φ := Neg.neg)
      (f := fun y => f' (x - y)) (by fun_prop)
      ((hf'Strong.comp_measurable (by fun_prop)).aestronglyMeasurable)]
    congr 1
    funext y
    congr 1
    ring
  filter_upwards [hsub, hadd] with x hxsub hxadd
  change (∫ y, f (x - y) ∂Measure.map Neg.neg μ) =
    ∫ y, f (x + y) ∂μ
  calc
    _ = ∫ y, f' (x - y) ∂Measure.map Neg.neg μ := hxsub
    _ = ∫ y, f' (x + y) ∂μ := hmap x
    _ = ∫ y, f (x + y) ∂μ := hxadd.symm

#print axioms jswConvolution_reflected_ae_eq_add

/-- An upper-exponent vector bound for the reflected probability family,
with a raw a.e. coordinate representation and unchanged maximal constant. -/
theorem finiteProbabilityConvolution_reflected_vector_lp_bound
    {ι : Type*} [Fintype ι] {p q : ℝ} (hp : 2 < p)
    (hrq : (p / 2).HolderConjugate q)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (F : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F (ENNReal.ofReal p) volume)
    (B : ℝ) (hB : 0 ≤ B)
    (hMax : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal q) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal q) volume ≤
          B * lpNorm g (ENNReal.ofReal q) volume) :
    ∃ U : ℝ → EuclideanSpace ℂ ι,
      MemLp U (ENNReal.ofReal p) volume ∧
      (∀ i, (fun x => U x i) =ᵐ[volume]
        (fun x => jswConvolution (Measure.map Neg.neg (μ i))
          (fun y => F y i) x)) ∧
      lpNorm U (ENNReal.ofReal p) volume ≤
        Real.sqrt B * lpNorm F (ENNReal.ofReal p) volume := by
  classical
  have hμfinite (i : ι) : IsFiniteMeasure (μ i) := by
    letI : IsProbabilityMeasure (μ i) := hμ i
    infer_instance
  have hμref (i : ι) : IsProbabilityMeasure (Measure.map Neg.neg (μ i)) := by
    letI : IsProbabilityMeasure (μ i) := hμ i
    infer_instance
  have hMaxRef := finitePositiveMaximalBound_reflect hrq.symm.lt
    μ hμfinite B hMax
  exact finiteProbabilityConvolution_vector_lp_bound hp hrq
    (fun i => Measure.map Neg.neg (μ i)) hμref F hF B hB hMaxRef

#print axioms finiteProbabilityConvolution_reflected_vector_lp_bound

end

end FractionalPrimes.Literature.JSW

end
