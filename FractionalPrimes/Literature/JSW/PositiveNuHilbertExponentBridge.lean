module

public import FractionalPrimes.Literature.JSW.PositiveGeometricNuL2

/-! The exact exponent transport at the Hilbert endpoint of `lj:positivity`. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- A common operator presentation whose exponent is explicit. It unfolds to
the approved `localizedSquareNuLpConvolution` at real exponent `u` when
`P = ENNReal.ofReal u`; no source operator is changed. -/
noncomputable def geometricNuLpConvolutionAt
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (P : ℝ≥0∞) [Fact (1 ≤ P)] (b : ℝ) (k : ℤ)
    (F : Lp ℂ P (volume : Measure ℝ)) :
    Lp ℂ P (volume : Measure ℝ) := by
  let μ : ComplexMeasure ℝ := initialSquareNuComplexMeasure σ
  have hμvar : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    exact initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  letI : IsFiniteMeasure μ.variation := hμvar
  let μk := initialSquareDilateComplexMeasure μ (b ^ k)
  have hμkvar : IsFiniteMeasure μk.variation := by
    dsimp [μk, μ, initialSquareDilateComplexMeasure]
    infer_instance
  letI : IsFiniteMeasure μk.variation := hμkvar
  exact lpComplexMeasureConvolution P μk F

private theorem finiteGeometricNuVector_at_two_bound
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P = 2)
    (b : ℝ) (κ : ι → ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) P volume) :
    lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i : ι =>
      (geometricNuLpConvolutionAt hSupp P b (κ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x)) P volume ≤
      2 * lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i => f i x))
        P volume := by
  subst P
  simpa only [geometricNuLpConvolutionAt,
    geometricNuLpConvolutionTwo] using
      finiteGeometricNuVector_two_bound hSupp b κ f hf

/-- The source `Lp` notation uses `ENNReal.ofReal 2`, while the Hilbert
probability-contraction theorem uses the numeral `2 : ℝ≥0∞`. The two
dependent operator types are transported here once. -/
theorem finiteGeometricNuVector_two_ofReal_bound
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (b : ℝ) (κ : ι → ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal (2 : ℝ)) volume) :
    lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i : ι =>
      (localizedSquareNuLpConvolution hSupp 2 b (by norm_num) (κ i)
        ((hf i).toLp (f i)) : ℝ → ℂ) x))
      (ENNReal.ofReal (2 : ℝ)) volume ≤
      2 * lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i => f i x))
        (ENNReal.ofReal (2 : ℝ)) volume := by
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have hbound := finiteGeometricNuVector_at_two_bound hSupp
    (P := ENNReal.ofReal (2 : ℝ)) (by norm_num) b κ f hf
  simpa only [geometricNuLpConvolutionAt,
    localizedSquareNuLpConvolution] using hbound

#print axioms finiteGeometricNuVector_two_ofReal_bound

end

end FractionalPrimes.Literature.JSW

end
