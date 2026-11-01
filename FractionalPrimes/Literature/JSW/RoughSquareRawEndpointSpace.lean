module

public import FractionalPrimes.Literature.JSW.RawKernelL2Representative

/-! The actual raw finite-square output belongs to each finite endpoint
space on the source layer-cake class. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem roughSquare_layerCakeInput_memLp
    (f : Variation.LayerCakeInput (volume : Measure ℝ)) (p : ℝ≥0∞) :
    MemLp f.1 p volume := by
  rcases f.2 with ⟨hf, ⟨C, hC⟩, hfinite⟩
  have htop : MemLp f.1 ∞ volume :=
    memLp_top_of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  exact htop.mono_exponent_of_measure_support_ne_top
    (s := {x | f.1 x ≠ 0})
    (by intro x hx; by_contra hn; exact hx hn) hfinite.ne le_top

def roughSquareSourceRawVector
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ} (hb : 1 < b)
    (j : ℤ) (F : Finset ℤ) (f : ℝ → ℂ) :
    ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ F} :=
  roughSquareRawVector
    (fun k => littlewoodPaleyScaledKernel b
      (ne_of_gt (by linarith : 0 < b)) (k.1+j))
    (fun k => initialSquareDilateComplexMeasure (initialSquareNuComplexMeasure σ) (b^k.1)) f

theorem roughSquareSourceRawVector_ae_eq_lp
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hp : 1 < p)
    (j : ℤ) (F : Finset ℤ) (f : Variation.LayerCakeInput (volume : Measure ℝ)) :
    roughSquareSourceRawVector (σ := σ) hb j F f.1 =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp p b hp k.1
          (littlewoodPaleyProjectionLp hb hp (k.1+j)
            ((roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p)).toLp f.1)) : ℝ → ℂ) x)) := by
  have hcoord : ∀ k : {k : ℤ // k ∈ F},
      localizedSquareRawNuAfterKernel
        (littlewoodPaleyScaledKernel b (ne_of_gt (by linarith : 0 < b)) (k.1+j))
        (initialSquareDilateComplexMeasure (initialSquareNuComplexMeasure σ) (b^k.1)) f.1
        =ᵐ[volume] (localizedSquareNuProjectionConvolution hSupp hσ hb j k.1
          ((roughSquare_layerCakeInput_memLp f 2).toLp f.1) : ℝ → ℂ) := by
    intro k
    exact localizedSquareRawNuAfterKernel_ae_eq_projection hSupp hσ hb j k.1
      f.1 f.2.1 (roughSquare_layerCakeInput_memLp f 2) f.2.2.1
  have hraw : roughSquareSourceRawVector (σ := σ) hb j F f.1 =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuProjectionConvolution hSupp hσ hb j k.1
          ((roughSquare_layerCakeInput_memLp f 2).toLp f.1) : ℝ → ℂ) x)) := by
    filter_upwards [ae_all_iff.mpr hcoord] with x hx
    ext k
    exact hx k
  exact hraw.trans (localizedSquareFiniteNuProjectionConvolution_ae_eq_lp_of_memLp
    hSupp hσ hb hp j F f.1 (roughSquare_layerCakeInput_memLp f 2)
      (roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p)))

theorem roughSquareSourceRawVector_memLp
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hp : 1 < p)
    (j : ℤ) (F : Finset ℤ) (f : Variation.LayerCakeInput (volume : Measure ℝ)) :
    MemLp (roughSquareSourceRawVector (σ := σ) hb j F f.1)
      (ENNReal.ofReal p) volume := by
  apply (memLp_congr_ae
    (roughSquareSourceRawVector_ae_eq_lp hSupp hσ hb hp j F f)).2
  apply MemLp.of_eval_piLp
  intro k
  exact Lp.memLp _

#print axioms roughSquare_layerCakeInput_memLp
#print axioms roughSquareSourceRawVector_ae_eq_lp
#print axioms roughSquareSourceRawVector_memLp
end
end FractionalPrimes.Literature.JSW
end
