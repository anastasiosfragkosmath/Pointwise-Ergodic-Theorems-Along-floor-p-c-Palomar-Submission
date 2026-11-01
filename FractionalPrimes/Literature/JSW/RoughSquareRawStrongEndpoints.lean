module

public import FractionalPrimes.Literature.JSW.RoughSquareRawEndpointSpace
public import FractionalPrimes.Literature.JSW.PositiveLocalizedSquareFromMaximal
public import FractionalPrimes.Literature.JSW.RoughSquareL2VectorNorm

/-! Source strong endpoints on the common raw finite-square operator. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem eLpNorm_le_mul_of_lpNorm_le
    {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]
    {f : ℝ → E} {g : ℝ → G} {p : ℝ≥0∞} {A : ℝ}
    (hf : MemLp f p volume) (hg : MemLp g p volume)
    (h : lpNorm f p volume ≤ A * lpNorm g p volume) :
    eLpNorm f p volume ≤ ENNReal.ofReal A * eLpNorm g p volume := by
  calc
    _ = ENNReal.ofReal (lpNorm f p volume) := (ofReal_lpNorm hf).symm
    _ ≤ ENNReal.ofReal (A * lpNorm g p volume) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [mul_comm A, ENNReal.ofReal_mul (lpNorm_nonneg), ofReal_lpNorm hg, mul_comm]

theorem roughSquareSourceRawVector_strong_of_maximal
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q₀ p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hp : 1 < p) (hregion : |p⁻¹ - (2 : ℝ)⁻¹| < (2*q₀)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (F : Finset ℤ)
      (f : Variation.LayerCakeInput (volume : Measure ℝ)),
      eLpNorm (roughSquareSourceRawVector (σ := σ) hb j F f.1)
        (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (C * littlewoodPaleyUpperConstant p b
        (ne_of_gt (by linarith : 0 < b))) * eLpNorm f.1 (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hbound⟩ := localizedSquareLpBoundFromMaximal
    hSupp hb hq₀ hMax hp hregion
  refine ⟨C, hC, ?_⟩
  intro j F f
  apply eLpNorm_le_mul_of_lpNorm_le
    (roughSquareSourceRawVector_memLp hSupp hσ hb hp j F f)
    (roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p))
  have hAE := roughSquareSourceRawVector_ae_eq_lp hSupp hσ hb hp j F f
  have hn := congrArg ENNReal.toReal (eLpNorm_congr_ae hAE (p := ENNReal.ofReal p))
  change lpNorm _ _ _ = lpNorm _ _ _ at hn
  rw [hn]
  simpa only [Lp.norm_toLp, toReal_eLpNorm, mul_assoc] using
    hbound j F ((roughSquare_layerCakeInput_memLp f (ENNReal.ofReal p)).toLp f.1)

theorem roughSquareSourceRawVector_strong_two
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    (j : ℤ) (F : Finset ℤ) (f : Variation.LayerCakeInput (volume : Measure ℝ)) :
    eLpNorm (roughSquareSourceRawVector (σ := σ) hb j F f.1)
      (ENNReal.ofReal 2) volume ≤
      ENNReal.ofReal ((2 * Real.pi + 2 * |D|) * max 2 (Real.rpow b β) *
        Real.sqrt (littlewoodPaleyNb b) * Real.rpow b (-(min 1 β * |(j : ℝ)|))) *
          eLpNorm f.1 (ENNReal.ofReal 2) volume := by
  apply eLpNorm_le_mul_of_lpNorm_le
    (roughSquareSourceRawVector_memLp hSupp hσ hb (by norm_num : (1 : ℝ) < 2) j F f)
    (roughSquare_layerCakeInput_memLp f (ENNReal.ofReal 2))
  have hraw := roughSquareSourceRawVector_ae_eq_lp hSupp hσ hb
    (by norm_num : (1 : ℝ) < 2) j F f
  have hcommon := localizedSquareFiniteNuProjectionConvolution_ae_eq_lp_of_memLp
    hSupp hσ hb (by norm_num : (1 : ℝ) < 2) j F f.1
    (roughSquare_layerCakeInput_memLp f 2)
    (roughSquare_layerCakeInput_memLp f (ENNReal.ofReal 2))
  have hn := congrArg ENNReal.toReal
    (eLpNorm_congr_ae (hraw.trans hcommon.symm) (p := ENNReal.ofReal 2))
  change lpNorm _ _ _ = lpNorm _ _ _ at hn
  rw [hn]
  simpa only [Lp.norm_toLp, toReal_eLpNorm, ENNReal.ofReal_ofNat] using
    localizedSquare_finite_l2_vector_bound hSupp hσ hb hβ j F
      ((roughSquare_layerCakeInput_memLp f 2).toLp f.1)

#print axioms roughSquareSourceRawVector_strong_two
#print axioms eLpNorm_le_mul_of_lpNorm_le
#print axioms roughSquareSourceRawVector_strong_of_maximal
end
end FractionalPrimes.Literature.JSW
end
