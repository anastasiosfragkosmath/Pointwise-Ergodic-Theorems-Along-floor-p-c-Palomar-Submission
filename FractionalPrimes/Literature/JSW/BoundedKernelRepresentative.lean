module

public import FractionalPrimes.Literature.JSW.ConvolutionCZBound

/-! The bounded measurable input representative needed by layer-cake
interpolation of the localized rough-square operator. -/

@[expose] public section
open MeasureTheory

namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem kernelConvolutionL2Operator_ae_eq_kernelIntegral_of_bounded
    (K : ℝ → ℂ) (hKcont : Continuous K) (hKint : Integrable K volume)
    (f : ℝ → ℂ) (hf : Measurable f) (hf₂ : MemLp f 2 volume)
    (hfbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    (kernelConvolutionL2Operator K hKint (hf₂.toLp f) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y, K y * f (x-y) ∂volume := by
  let F : Lp ℂ 2 volume := hf₂.toLp f
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact kernelVariationMeasure_isFinite hKint
  have hraw := complexMeasureConvolution_ae_eq_raw_integral μ F
  have hcongr := rawComplexMeasureConvolution_ae_congr μ f (fun y => F y)
    hf.stronglyMeasurable (Lp.stronglyMeasurable F)
    (by simpa [F] using hf₂.coeFn_toLp.symm)
  have hpoint : (fun x : ℝ => complexMeasureConvolution μ (fun y => F y)
      (Lp.aestronglyMeasurable F) x) =ᵐ[volume]
      fun x => ∫ y, K y * f (x-y) ∂volume := by
    filter_upwards [hraw, hcongr] with x hrawX hcongrX
    calc
      _ = ∫ᵛ y, F (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hrawX
      _ = ∫ᵛ y, f (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hcongrX.symm
      _ = ∫ y, K y * f (x-y) ∂volume :=
        kernelDensity_vectorIntegral_eq_function K hKcont hKint _ (by
          letI : IsFiniteMeasure (kernelVariationMeasure K) :=
            kernelVariationMeasure_isFinite hKint
          obtain ⟨C, hC⟩ := hfbdd
          exact MemLp.of_bound
            ((hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
            C (ae_of_all _ fun y => hC (x-y)))
  exact (lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution μ F).trans hpoint

#print axioms kernelConvolutionL2Operator_ae_eq_kernelIntegral_of_bounded
end
end FractionalPrimes.Literature.JSW
end
