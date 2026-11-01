module

public import FractionalPrimes.Literature.JSW.Conventions
public import Mathlib.MeasureTheory.VectorMeasure.Prod
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Young's inequality for finite complex measures

This module implements the complex-measure convolution clause of
`lj:vector-duality`.  For finite exponents, convolution is the vector-measure
integral of the translation orbit in `Lᵖ`.  The `L∞` endpoint is stated for a
function representative and uses its canonical strongly measurable version.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- Right translation with the source's convention `f(x-y)`, acting on
measure-theoretic `Lᵖ`. -/
def lpRightTranslate (p : ℝ≥0∞) (y : ℝ)
    (F : Lp ℂ p (volume : Measure ℝ)) : Lp ℂ p (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (fun x : ℝ => x - y)
    (measurePreserving_sub_right volume y) F

theorem coeFn_lpRightTranslate (p : ℝ≥0∞) (y : ℝ)
    (F : Lp ℂ p (volume : Measure ℝ)) :
    lpRightTranslate p y F =ᵐ[(volume : Measure ℝ)] fun x => F (x - y) := by
  exact Lp.coeFn_compMeasurePreserving F (measurePreserving_sub_right volume y)

theorem norm_lpRightTranslate (p : ℝ≥0∞) (y : ℝ)
    (F : Lp ℂ p (volume : Measure ℝ)) :
    ‖lpRightTranslate p y F‖ = ‖F‖ := by
  exact Lp.norm_compMeasurePreserving F (measurePreserving_sub_right volume y)

/-- For finite `p`, the exact translation orbit is continuous in `Lᵖ`. -/
theorem continuous_lpRightTranslate {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (F : Lp ℂ p (volume : Measure ℝ)) :
    Continuous (fun y : ℝ => lpRightTranslate p y F) := by
  let g : ℝ → C(ℝ, ℝ) := fun y => ⟨fun x => x - y, by fun_prop⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : ℝ × ℝ => z.2 - z.1)
    fun_prop
  have hgm : ∀ y : ℝ, MeasurePreserving (g y) volume volume := by
    intro y
    simpa [g] using measurePreserving_sub_right volume y
  have hcont :=
    (continuous_const : Continuous (fun _ : ℝ => F)).compMeasurePreservingLp
      hg hgm hp
  simpa [lpRightTranslate, g] using hcont

/-- The finite-exponent translation orbit is integrable against every complex
measure of finite total variation. -/
theorem integrable_lpRightTranslate {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ p (volume : Measure ℝ)) :
    μ.Integrable (fun y : ℝ => lpRightTranslate p y F) := by
  apply Integrable.of_bound (continuous_lpRightTranslate hp F).aestronglyMeasurable ‖F‖
  filter_upwards [] with y
  exact (norm_lpRightTranslate p y F).le

/-- Complex scalar multiplication on `Lᵖ`, ordered as function value first
and complex-measure value second. -/
def lpComplexSmulBilinear (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℂ p (volume : Measure ℝ) →L[ℝ] ℂ →L[ℝ]
      Lp ℂ p (volume : Measure ℝ) :=
  (ContinuousLinearMap.lsmul ℝ ℂ :
    ℂ →L[ℝ] Lp ℂ p (volume : Measure ℝ) →L[ℝ]
      Lp ℂ p (volume : Measure ℝ)).flip

@[simp]
theorem lpComplexSmulBilinear_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (F : Lp ℂ p (volume : Measure ℝ)) (z : ℂ) :
    lpComplexSmulBilinear p F z = z • F := rfl

/-- Convolution of an `Lᵖ` element by a finite complex measure, defined as
the vector-measure integral of its exact translation orbit. -/
def lpComplexMeasureConvolution (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : ComplexMeasure ℝ) (F : Lp ℂ p (volume : Measure ℝ)) :
    Lp ℂ p (volume : Measure ℝ) :=
  ∫ᵛ y, lpRightTranslate p y F ∂[lpComplexSmulBilinear p; μ]

theorem norm_lpComplexSmulBilinear_le (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖lpComplexSmulBilinear p‖ ≤ 1 := by
  rw [lpComplexSmulBilinear, ContinuousLinearMap.opNorm_flip]
  exact ContinuousLinearMap.opNorm_lsmul_le

/-- Young's inequality for convolution by an arbitrary finite complex measure
at every finite exponent `1 ≤ p < ∞`. -/
theorem norm_lpComplexMeasureConvolution_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ p (volume : Measure ℝ)) :
    ‖lpComplexMeasureConvolution p μ F‖ ≤
      μ.variation.real Set.univ * ‖F‖ := by
  have _hint : μ.Integrable (fun y : ℝ => lpRightTranslate p y F) :=
    integrable_lpRightTranslate hp μ F
  have hbound := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := μ) (B := lpComplexSmulBilinear p)
    (f := fun y : ℝ => lpRightTranslate p y F)
    (ae_of_all μ.variation fun y => (norm_lpRightTranslate p y F).le)
  calc
    ‖lpComplexMeasureConvolution p μ F‖ ≤
        ‖F‖ * ‖lpComplexSmulBilinear p‖ * μ.variation.real Set.univ := hbound
    _ ≤ ‖F‖ * 1 * μ.variation.real Set.univ := by
      gcongr
      exact norm_lpComplexSmulBilinear_le p
    _ = μ.variation.real Set.univ * ‖F‖ := by ring

/-- Pointwise complex-measure convolution using the canonical strongly
measurable representative of `f`. -/
def complexMeasureConvolution (μ : ComplexMeasure ℝ) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure ℝ)) (x : ℝ) : ℂ :=
  ∫ᵛ y, hf.mk f (x - y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ]

theorem stronglyMeasurable_complexMeasureConvolution
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    StronglyMeasurable (complexMeasureConvolution μ f hf) := by
  have hjoint : StronglyMeasurable
      (fun z : ℝ × ℝ => hf.mk f (z.1 - z.2)) :=
    hf.stronglyMeasurable_mk.comp_measurable (by fun_prop)
  change StronglyMeasurable
    (fun x : ℝ => ∫ᵛ y, hf.mk f (x - y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
  exact hjoint.integral_vectorMeasure_prod_right'
    (B := ContinuousLinearMap.mul ℝ ℂ) (ν := μ)

/-- The `p = ∞` endpoint of complex-measure Young inequality, including
membership of the convolution in `L∞`. -/
theorem complexMeasureConvolution_memLp_top_and_norm_le
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (f : ℝ → ℂ) (hf : MemLp f ∞ (volume : Measure ℝ)) :
    MemLp (complexMeasureConvolution μ f hf.aestronglyMeasurable) ∞
        (volume : Measure ℝ) ∧
      lpNorm (complexMeasureConvolution μ f hf.aestronglyMeasurable) ∞
          (volume : Measure ℝ) ≤
        μ.variation.real Set.univ * lpNorm f ∞ (volume : Measure ℝ) := by
  let f' : ℝ → ℂ := hf.aestronglyMeasurable.mk f
  let C : ℝ := lpNorm f ∞ (volume : Measure ℝ)
  have hbound' : ∀ᵐ x ∂(volume : Measure ℝ), ‖f' x‖ ≤ C := by
    filter_upwards [ae_le_lpNorm_exponent_top hf,
      hf.aestronglyMeasurable.ae_eq_mk] with x hx hfx
    rw [hfx] at hx
    simpa [f', C] using hx
  have hyx : ∀ᵐ y ∂μ.variation, ∀ᵐ x ∂(volume : Measure ℝ),
      ‖f' (x - y)‖ ≤ C := by
    filter_upwards [] with y
    exact (measurePreserving_sub_right volume y).quasiMeasurePreserving.ae hbound'
  have hmeas : MeasurableSet
      {z : ℝ × ℝ | ‖f' (z.1 - z.2)‖ ≤ C} := by
    have hsm : StronglyMeasurable
        (fun z : ℝ × ℝ => ‖f' (z.1 - z.2)‖) :=
      (hf.aestronglyMeasurable.stronglyMeasurable_mk.comp_measurable
        (by fun_prop)).norm
    exact hsm.measurableSet_le stronglyMeasurable_const
  have hxy : ∀ᵐ x ∂(volume : Measure ℝ), ∀ᵐ y ∂μ.variation,
      ‖f' (x - y)‖ ≤ C :=
    (Measure.ae_ae_comm hmeas).2 hyx
  have hpoint : ∀ᵐ x ∂(volume : Measure ℝ),
      ‖complexMeasureConvolution μ f hf.aestronglyMeasurable x‖ ≤
        μ.variation.real Set.univ * C := by
    filter_upwards [hxy] with x hx
    have hi := VectorMeasure.norm_integral_le_of_norm_le_const
      (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ)
      (f := fun y : ℝ => f' (x - y)) hx
    calc
      ‖complexMeasureConvolution μ f hf.aestronglyMeasurable x‖ ≤
          C * ‖ContinuousLinearMap.mul ℝ ℂ‖ * μ.variation.real Set.univ := by
        simpa [complexMeasureConvolution, f'] using hi
      _ ≤ C * 1 * μ.variation.real Set.univ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_mul_le ℝ ℂ) lpNorm_nonneg)
          (by positivity)
      _ = μ.variation.real Set.univ * C := by ring
  have houtsm : StronglyMeasurable
      (complexMeasureConvolution μ f hf.aestronglyMeasurable) :=
    stronglyMeasurable_complexMeasureConvolution μ f hf.aestronglyMeasurable
  have hout : AEStronglyMeasurable
      (complexMeasureConvolution μ f hf.aestronglyMeasurable)
      (volume : Measure ℝ) := houtsm.aestronglyMeasurable
  have hmem : MemLp (complexMeasureConvolution μ f hf.aestronglyMeasurable) ∞
      (volume : Measure ℝ) :=
    memLp_top_of_bound hout (μ.variation.real Set.univ * C) hpoint
  refine ⟨hmem, ?_⟩
  rw [lpNorm_exponent_top_eq_essSup hmem]
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) (ae (volume : Measure ℝ))
      (fun x => ‖complexMeasureConvolution μ f hf.aestronglyMeasurable x‖) :=
    Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
      (Filter.Frequently.of_forall fun x => norm_nonneg _)
  simpa [C] using essSup_le_of_ae_le
    (μ.variation.real Set.univ * C) hpoint hcob

end

end FractionalPrimes.Literature.JSW
