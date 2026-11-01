module

public import FractionalPrimes.Literature.JSW.PositiveGeometricLowerRealization

/-!
# Exact signed geometric cancellation convolution identity

The source cancellation measure is identified with the difference of
the two positive geometric probability measures at the level of `Lp`
convolution operators. This identity is independent of exponent range.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The source geometric ν convolution on finite `Lᵖ` is exactly the
difference of the σ and smooth ψ probability convolutions. -/
theorem geometricNuLpConvolution_eq_positive_sub
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hp : 1 < p) (k : ℤ)
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    letI : IsProbabilityMeasure (initialSquarePsiProbabilityMeasure σ) :=
      initialSquarePsiProbabilityMeasure_isProbability hSupp
    lpComplexMeasureConvolution (ENNReal.ofReal p)
        (initialSquareDilateComplexMeasure
          (initialSquareNuComplexMeasure σ) (b ^ k)) F =
      lpComplexMeasureConvolution (ENNReal.ofReal p)
        (initialSquareSigmaComplexMeasure
          (Measure.map (fun y : ℝ => b ^ k * y) σ)) F -
      lpComplexMeasureConvolution (ENNReal.ofReal p)
        (initialSquareSigmaComplexMeasure
          (Measure.map (fun y : ℝ => b ^ k * y)
            (initialSquarePsiProbabilityMeasure σ))) F := by
  let ψbase : Measure ℝ := initialSquarePsiProbabilityMeasure σ
  have hψprob : IsProbabilityMeasure ψbase :=
    initialSquarePsiProbabilityMeasure_isProbability hSupp
  let μσ : Measure ℝ := Measure.map (fun y : ℝ => b ^ k * y) σ
  let μψ : Measure ℝ := Measure.map (fun y : ℝ => b ^ k * y) ψbase
  letI : IsProbabilityMeasure ψbase := hψprob
  haveI : IsFiniteMeasure μσ := by dsimp [μσ]; infer_instance
  haveI : IsFiniteMeasure μψ := by dsimp [μψ]; infer_instance
  let ν : ComplexMeasure ℝ :=
    initialSquareDilateComplexMeasure (initialSquareNuComplexMeasure σ) (b ^ k)
  have hνbase : IsFiniteMeasure
      (initialSquareNuComplexMeasure σ).variation :=
    initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  letI : IsFiniteMeasure (initialSquareNuComplexMeasure σ).variation := hνbase
  haveI : IsFiniteMeasure ν.variation := by
    dsimp [ν, initialSquareDilateComplexMeasure]
    infer_instance
  have hσvar : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μσ).variation := by
    rw [initialSquareSigmaComplexMeasure_variation_eq]
    infer_instance
  have hψvar : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μψ).variation := by
    rw [initialSquareSigmaComplexMeasure_variation_eq]
    infer_instance
  letI : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μσ).variation := hσvar
  letI : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μψ).variation := hψvar
  have hmeasure : ν =
      initialSquareSigmaComplexMeasure μσ -
        initialSquareSigmaComplexMeasure μψ := by
    simpa [ν, μσ, μψ, ψbase] using
      initialSquareNuDilateComplexMeasure_eq_sigma_sub_psi
        hSupp (b ^ k) (inferInstance : IsFiniteMeasure ψbase)
        (inferInstance : IsFiniteMeasure μσ)
        (inferInstance : IsFiniteMeasure μψ)
  have hsubvar : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μσ -
        initialSquareSigmaComplexMeasure μψ).variation := by
    rw [← hmeasure]
    infer_instance
  letI : IsFiniteMeasure
      (initialSquareSigmaComplexMeasure μσ -
        initialSquareSigmaComplexMeasure μψ).variation := hsubvar
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  change lpComplexMeasureConvolution (ENNReal.ofReal p) ν F =
    lpComplexMeasureConvolution (ENNReal.ofReal p)
        (initialSquareSigmaComplexMeasure μσ) F -
      lpComplexMeasureConvolution (ENNReal.ofReal p)
        (initialSquareSigmaComplexMeasure μψ) F
  rw [hmeasure]
  exact lpComplexMeasureConvolution_sub ENNReal.ofReal_ne_top
    (initialSquareSigmaComplexMeasure μσ)
    (initialSquareSigmaComplexMeasure μψ) F

#print axioms geometricNuLpConvolution_eq_positive_sub

end

end FractionalPrimes.Literature.JSW

end
