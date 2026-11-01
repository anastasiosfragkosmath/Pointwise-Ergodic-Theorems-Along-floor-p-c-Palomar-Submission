module

public import FractionalPrimes.Literature.JSW.BoundedKernelRepresentative
public import FractionalPrimes.Literature.JSW.RoughSquareRawVector

/-! The bounded-input raw kernel/measure composition agrees with its
genuine L² realization, as required before rough-square interpolation. -/

@[expose] public section
open MeasureTheory

namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem localizedSquareRawNuAfterKernel_ae_eq_l2
    (K : ℝ → ℂ) (hKcont : Continuous K) (hKint : Integrable K volume)
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (f : ℝ → ℂ) (hf : Measurable f) (hf₂ : MemLp f 2 volume)
    (hfbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    localizedSquareRawNuAfterKernel K μ f =ᵐ[volume]
      (lpComplexMeasureConvolution 2 μ
        (kernelConvolutionL2Operator K hKint (hf₂.toLp f)) : ℝ → ℂ) := by
  let H : ℝ → ℂ := fun x => ∫ y, K y * f (x-y) ∂volume
  let G : Lp ℂ 2 volume := kernelConvolutionL2Operator K hKint (hf₂.toLp f)
  have hH : StronglyMeasurable H := by
    have hjoint : Measurable (fun q : ℝ × ℝ => K q.2 * f (q.1-q.2)) :=
      (hKcont.measurable.comp measurable_snd).mul
        (hf.comp (measurable_fst.sub measurable_snd))
    exact hjoint.stronglyMeasurable.integral_prod_right'
  have hGH : (G : ℝ → ℂ) =ᵐ[volume] H :=
    kernelConvolutionL2Operator_ae_eq_kernelIntegral_of_bounded
      K hKcont hKint f hf hf₂ hfbdd
  have hraw := rawComplexMeasureConvolution_ae_congr μ H (G : ℝ → ℂ)
    hH (Lp.stronglyMeasurable G) hGH.symm
  have hrep := complexMeasureConvolution_ae_eq_raw_integral μ G
  have hLp := lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution μ G
  exact hraw.trans (hrep.symm.trans hLp.symm)

theorem localizedSquareRawNuAfterKernel_ae_eq_projection
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b)
    (j k : ℤ) (f : ℝ → ℂ) (hf : Measurable f)
    (hf₂ : MemLp f 2 volume) (hfbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    localizedSquareRawNuAfterKernel
      (littlewoodPaleyScaledKernel b (ne_of_gt (by linarith : 0 < b)) (k+j))
      (initialSquareDilateComplexMeasure (initialSquareNuComplexMeasure σ) (b^k)) f
      =ᵐ[volume] (localizedSquareNuProjectionConvolution hSupp hσ hb j k
        (hf₂.toLp f) : ℝ → ℂ) := by
  let μ := initialSquareNuComplexMeasure σ
  letI : IsFiniteMeasure μ.variation :=
    initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  letI : IsFiniteMeasure
      (initialSquareDilateComplexMeasure μ (b^k)).variation := by
    change IsFiniteMeasure (μ.map (fun x : ℝ => b^k*x)).variation
    infer_instance
  exact localizedSquareRawNuAfterKernel_ae_eq_l2 _
    (littlewoodPaleyScaledKernel_smooth (ne_of_gt (by linarith : 0 < b)) (k+j)).continuous
    (littlewoodPaleyScaledKernel_integrable (ne_of_gt (by linarith : 0 < b)) (k+j))
    _ f hf hf₂ hfbdd

#print axioms localizedSquareRawNuAfterKernel_ae_eq_l2
#print axioms localizedSquareRawNuAfterKernel_ae_eq_projection
end
end FractionalPrimes.Literature.JSW
end
