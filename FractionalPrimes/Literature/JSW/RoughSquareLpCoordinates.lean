module

public import FractionalPrimes.Literature.JSW.RoughSquareSeriesIdentification

/-! Actual coordinate evaluation of the reconstructed rough-square series. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def roughSquareLpCoordinate {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι) :
    Lp (EuclideanSpace ℂ ι) p (volume : Measure ℝ) →L[ℝ]
      Lp ℂ p (volume : Measure ℝ) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℂ) i).compLpL p volume

theorem roughSquareLpCoordinate_rawTerm
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hp : 1 < p)
    (j : ℤ) (F : Finset ℤ) (f : Variation.LayerCakeInput (volume : Measure ℝ))
    (k : {k : ℤ // k ∈ F}) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    roughSquareLpCoordinate (ENNReal.ofReal p) k
      (roughSquareSourceRawLpVector hSupp hσ hb hp j F f) =
    localizedSquareNuLpConvolution hSupp p b hp k.1
      (littlewoodPaleyProjectionLp hb hp (k.1+j)
        ((roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p)).toLp f.1)) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : {k : ℤ // k ∈ F} => ℂ) k
  have hcoord := P.coeFn_compLpL (roughSquareSourceRawLpVector hSupp hσ hb hp j F f)
  have hraw := (roughSquareSourceRawVector_memLp hSupp hσ hb hp j F f).coeFn_toLp
  have hAE := roughSquareSourceRawVector_ae_eq_lp hSupp hσ hb hp j F f
  apply Lp.ext
  filter_upwards [hcoord, hraw, hAE] with x hc hr ha
  change (P.compLpL _ _ (roughSquareSourceRawLpVector hSupp hσ hb hp j F f)) x = _
  rw [hc]
  change P (((roughSquareSourceRawVector_memLp hSupp hσ hb hp j F f).toLp
    (roughSquareSourceRawVector (σ := σ) hb j F f.1)) x) = _
  rw [hr, ha]
  rfl

theorem roughSquareLpCoordinate_tsum
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hp : 1 < p)
    (F : Finset ℤ) (f : Variation.LayerCakeInput (volume : Measure ℝ))
    (k : {k : ℤ // k ∈ F}) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    Summable (fun j : ℤ => roughSquareSourceRawLpVector hSupp hσ hb hp j F f) →
    roughSquareLpCoordinate (ENNReal.ofReal p) k
      (∑' j : ℤ, roughSquareSourceRawLpVector hSupp hσ hb hp j F f) =
      localizedSquareNuLpConvolution hSupp p b hp k.1
        ((roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p)).toLp f.1) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  intro hsum
  exact roughSquareSeries_coordinate_identification
    (roughSquareLpCoordinate (ENNReal.ofReal p) k) _ _ _ k.1 hsum
    (fun j => roughSquareLpCoordinate_rawTerm hSupp hσ hb hp j F f k)
    (localizedSquareNuLpConvolution_resolution hSupp hp hb k.1 _)

theorem roughSquareSourceRawLpVector_tsum_ae_eq
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hp : 1 < p)
    (F : Finset ℤ) (f : Variation.LayerCakeInput (volume : Measure ℝ)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    Summable (fun j : ℤ => roughSquareSourceRawLpVector hSupp hσ hb hp j F f) →
    ((∑' j : ℤ, roughSquareSourceRawLpVector hSupp hσ hb hp j F f :
      Lp (EuclideanSpace ℂ {k : ℤ // k ∈ F}) (ENNReal.ofReal p) (volume : Measure ℝ)) :
      ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ F}) =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp p b hp k.1
          ((roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p)).toLp f.1) : ℝ → ℂ) x)) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  intro hsum
  have hc : ∀ k : {k : ℤ // k ∈ F}, ∀ᵐ x ∂volume,
      (∑' j : ℤ, roughSquareSourceRawLpVector hSupp hσ hb hp j F f) x k =
      (localizedSquareNuLpConvolution hSupp p b hp k.1
        ((roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p)).toLp f.1) : ℝ → ℂ) x := by
    intro k
    have heq := roughSquareLpCoordinate_tsum hSupp hσ hb hp F f k hsum
    have hre := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : {k : ℤ // k ∈ F} => ℂ) k).coeFn_compLpL
      (∑' j : ℤ, roughSquareSourceRawLpVector hSupp hσ hb hp j F f)
    exact hre.symm.trans (Lp.ext_iff.mp heq)
  filter_upwards [ae_all_iff.mpr hc] with x hx
  ext k
  exact hx k

#print axioms roughSquareSourceRawLpVector_tsum_ae_eq
#print axioms roughSquareLpCoordinate_rawTerm
#print axioms roughSquareLpCoordinate_tsum
end
end FractionalPrimes.Literature.JSW
end
