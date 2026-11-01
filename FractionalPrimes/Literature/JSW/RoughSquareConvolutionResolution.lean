module

public import FractionalPrimes.Literature.JSW.RoughSquareGeometricSum

/-! Reconstruction after cancellation convolution. Once localized terms
are summable, this centered resolution identifies their sum uniquely. -/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem localizedSquareNuLpConvolution_resolution
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hp : 1 < p) (hb : 1 < b) (k : ℤ)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      localizedSquareNuLpConvolution hSupp p b hp k
        (littlewoodPaleyProjectionLp hb hp n f)) atTop
      (𝓝 (localizedSquareNuLpConvolution hSupp p b hp k f)) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let μ := initialSquareNuComplexMeasure σ
  letI : IsFiniteMeasure μ.variation :=
    initialSquareNuComplexMeasure_variation_isFinite_of_support hSupp
  let μk := initialSquareDilateComplexMeasure μ (b^k)
  letI : IsFiniteMeasure μk.variation := by
    change IsFiniteMeasure (μ.map (fun x : ℝ => b^k*x)).variation
    infer_instance
  let T := lpComplexMeasureConvolutionCLM (ENNReal.ofReal p) ENNReal.ofReal_ne_top μk
  have h := (T.continuous.tendsto f).comp (littlewoodPaleyResolutionLp hp hb f)
  change Tendsto (fun N : ℕ => T (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    littlewoodPaleyProjectionLp hb hp n f)) atTop (𝓝 (T f)) at h
  change Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    T (littlewoodPaleyProjectionLp hb hp n f)) atTop (𝓝 (T f))
  simpa only [map_sum] using h

#print axioms localizedSquareNuLpConvolution_resolution
end
end FractionalPrimes.Literature.JSW
end
