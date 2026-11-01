module

public import FractionalPrimes.Literature.JSW.Conventions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.MeasureTheory.Integral.Prod

/-! A common linear interface agreeing with the actual convolution on bounded measurable inputs.
The algebraic extension is used only outside that domain by the abstract variation interface. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

def boundedMeasurableFunctionSubmodule : Submodule ℂ (ℝ → ℂ) where
  carrier := fun f => Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
  zero_mem' := ⟨measurable_const, ⟨0, fun x => by simp⟩⟩
  add_mem' := by
    rintro f g ⟨hf,C,hC⟩ ⟨hg,D,hD⟩
    refine ⟨hf.add hg, C+D, fun x => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hC x) (hD x))
  smul_mem' := by
    rintro c f ⟨hf,C,hC⟩
    refine ⟨hf.const_smul c, ‖c‖*C, fun x => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)

theorem integrable_boundedMeasurable_translate
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : boundedMeasurableFunctionSubmodule) (x : ℝ) :
    Integrable (fun y => f.1 (x-y)) μ := by
  obtain ⟨C,hC⟩ := f.2.2
  apply Integrable.of_bound (f.2.1.comp (by fun_prop)).aestronglyMeasurable C
  exact ae_of_all μ fun y => hC (x-y)

def boundedMeasurableConvolutionLinearMap
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    boundedMeasurableFunctionSubmodule →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := jswConvolution μ f.1
  map_add' f g := by
    funext x
    exact integral_add (integrable_boundedMeasurable_translate μ f x)
      (integrable_boundedMeasurable_translate μ g x)
  map_smul' c f := by
    funext x
    exact integral_smul c (fun y => f.1 (x-y))

def boundedMeasurableFunctionProjection : (ℝ → ℂ) →ₗ[ℂ] boundedMeasurableFunctionSubmodule :=
  boundedMeasurableFunctionSubmodule.projectionOnto
    (Classical.choose boundedMeasurableFunctionSubmodule.exists_isCompl)
    (Classical.choose_spec boundedMeasurableFunctionSubmodule.exists_isCompl)

def probabilityConvolutionRawLinearMap
    (μ : Measure ℝ) [IsFiniteMeasure μ] : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
  (boundedMeasurableConvolutionLinearMap μ).comp boundedMeasurableFunctionProjection

theorem probabilityConvolutionRawLinearMap_eq
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ → ℂ)
    (hf : Measurable f) (hbound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    probabilityConvolutionRawLinearMap μ f = jswConvolution μ f := by
  have hd : f ∈ boundedMeasurableFunctionSubmodule := ⟨hf,hbound⟩
  have hp : boundedMeasurableFunctionProjection f = ⟨f,hd⟩ :=
    Submodule.projectionOnto_apply_left
      (Classical.choose_spec boundedMeasurableFunctionSubmodule.exists_isCompl) ⟨f,hd⟩
  change boundedMeasurableConvolutionLinearMap μ (boundedMeasurableFunctionProjection f) = _
  rw [hp]
  rfl

theorem measurable_jswConvolution_of_measurable
    (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (jswConvolution μ f) :=
  (hf.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

#print axioms probabilityConvolutionRawLinearMap_eq
#print axioms measurable_jswConvolution_of_measurable
end
end FractionalPrimes.Literature.JSW
end
