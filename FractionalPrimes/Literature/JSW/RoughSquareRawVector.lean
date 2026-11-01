module

public import FractionalPrimes.Literature.JSW.RoughSquareBootstrap

/-! Pointwise finite-vector structure on the bounded input class used in
the approved rough-square layer-cake interpolation. -/

@[expose] public section

open MeasureTheory

namespace FractionalPrimes.Literature.JSW

noncomputable section

def roughSquareRawVector {ι : Type*} [Fintype ι]
    (K : ι → ℝ → ℂ) (μ : ι → ComplexMeasure ℝ) (f : ℝ → ℂ)
    (x : ℝ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => localizedSquareRawNuAfterKernel (K i) (μ i) f x)

theorem roughSquareRawVector_measurable_norm
    {ι : Type*} [Fintype ι] (K : ι → ℝ → ℂ)
    (μ : ι → ComplexMeasure ℝ) (hKm : ∀ i, Measurable (K i))
    (hμ : ∀ i, IsFiniteMeasure (μ i).variation)
    (f : Variation.LayerCakeInput (volume : Measure ℝ)) :
    Measurable (fun x => ‖roughSquareRawVector K μ f.1 x‖) := by
  apply Measurable.norm
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro i
  exact (localizedSquareRawNuAfterKernel_stronglyMeasurable
    (K i) (μ i) f.1 (hKm i) (hμ i) f.2.1).measurable

theorem roughSquareRawVector_subadditive
    {ι : Type*} [Fintype ι] (K : ι → ℝ → ℂ)
    (μ : ι → ComplexMeasure ℝ)
    (hK : ∀ i, Integrable (K i) volume)
    (hKm : ∀ i, Measurable (K i))
    (hμ : ∀ i, IsFiniteMeasure (μ i).variation)
    (f g : Variation.LayerCakeInput (volume : Measure ℝ)) (x : ℝ) :
    ‖roughSquareRawVector K μ (f.1 + g.1) x‖ ≤
      ‖roughSquareRawVector K μ f.1 x‖ + ‖roughSquareRawVector K μ g.1 x‖ := by
  have hadd : roughSquareRawVector K μ (f.1 + g.1) x =
      roughSquareRawVector K μ f.1 x + roughSquareRawVector K μ g.1 x := by
    ext i
    change localizedSquareRawNuAfterKernel (K i) (μ i) (f.1 + g.1) x = _
    exact localizedSquareRawNuAfterKernel_add (K i) (μ i) f.1 g.1 x
      (localizedSquareRawNuAfterKernel_inner_integrable (K i) f.1 (hK i) f.2.1 f.2.2.1)
      (localizedSquareRawNuAfterKernel_inner_integrable (K i) g.1 (hK i) g.2.1 g.2.2.1)
      (localizedSquareRawNuAfterKernel_outer_integrable (K i) (μ i) f.1
        (hK i) (hKm i) (hμ i) f.2.1 f.2.2.1)
      (localizedSquareRawNuAfterKernel_outer_integrable (K i) (μ i) g.1
        (hK i) (hKm i) (hμ i) g.2.1 g.2.2.1)
  rw [hadd]
  exact norm_add_le _ _

theorem roughSquareRawVector_positive_homogeneous
    {ι : Type*} [Fintype ι] (K : ι → ℝ → ℂ)
    (μ : ι → ComplexMeasure ℝ) (f : ℝ → ℂ) (x c : ℝ) (hc : 0 ≤ c) :
    ‖roughSquareRawVector K μ (c • f) x‖ = c * ‖roughSquareRawVector K μ f x‖ := by
  have hsmul : roughSquareRawVector K μ (c • f) x =
      c • roughSquareRawVector K μ f x := by
    ext i
    change localizedSquareRawNuAfterKernel (K i) (μ i) (c • f) x =
      c • localizedSquareRawNuAfterKernel (K i) (μ i) f x
    have hfun : c • f = fun y => (c : ℂ) * f y := by
      funext y
      simp only [Pi.smul_apply, Complex.real_smul]
    rw [hfun]
    simpa only [Complex.real_smul] using
      localizedSquareRawNuAfterKernel_smul_real (K i) (μ i) f x c
  rw [hsmul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

#print axioms roughSquareRawVector_subadditive
#print axioms roughSquareRawVector_measurable_norm
#print axioms roughSquareRawVector_positive_homogeneous

end

end FractionalPrimes.Literature.JSW

end
