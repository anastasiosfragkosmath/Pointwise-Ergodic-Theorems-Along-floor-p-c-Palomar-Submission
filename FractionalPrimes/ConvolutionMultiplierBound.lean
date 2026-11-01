module

import FractionalPrimes.AdjointKernel
import FractionalPrimes.FourierLpBridge
import FractionalPrimes.LpAverages
import FractionalPrimes.ShortVariation
import FractionalPrimes.VonMangoldtLpAverages

/-!
# The convolution and endpoint package from blueprint `lem:fourier`

This packages exactly the clauses displayed in the approved blueprint.  The
finite adjoint-pairing calculation is kept separate: it is proof support, not
an additional clause in the paper's stated result.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The convolution/Fourier and three averaging endpoint assertions of
blueprint `lem:fourier`, specialized to the paper's fixed fractional
exponent. -/
structure ConvolutionMultiplierBound (c : FractionalExponent) : Prop where
  young : ∀ {p : ℝ≥0∞}, ∀ (hp : 1 ≤ p) (K : IntegerL1Kernel)
      (f : Lp ℂ p (Measure.count : Measure ℤ)),
    eLpNorm (integerKernelConvolution K (f : ℤ → ℂ)) p Measure.count ≤
      (∑' m : ℤ, ‖K.coeff m‖ₑ) * eLpNorm (f : ℤ → ℂ) p Measure.count
  sharpL2 : ∀ (K : IntegerL1Kernel) (f : Lp ℂ 2 (Measure.count : Measure ℤ)),
    eLpNorm (integerKernelConvolution K (f : ℤ → ℂ)) 2 Measure.count ≤
      eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
        eLpNorm (f : ℤ → ℂ) 2 Measure.count
  adjointCoeff : ∀ (K : IntegerL1Kernel) (m : ℤ),
    (integerKernelAdjoint K).coeff m = starRingEnd ℂ (K.coeff (-m))
  adjointNormMass : ∀ K : IntegerL1Kernel,
    (∑' m : ℤ, ‖(integerKernelAdjoint K).coeff m‖) = ∑' m : ℤ, ‖K.coeff m‖
  adjointENormMass : ∀ K : IntegerL1Kernel,
    (∑' m : ℤ, ‖(integerKernelAdjoint K).coeff m‖ₑ) =
      ∑' m : ℤ, ‖K.coeff m‖ₑ
  adjointEndpoint : ∀ {p : ℝ≥0∞}, ∀ (hp : 1 ≤ p)
      (K : IntegerL1Kernel) (f : Lp ℂ p (Measure.count : Measure ℤ)),
    eLpNorm (integerKernelConvolution (integerKernelAdjoint K) (f : ℤ → ℂ))
        p Measure.count ≤
      (∑' m : ℤ, ‖K.coeff m‖ₑ) * eLpNorm (f : ℤ → ℂ) p Measure.count
  adjointFourierNorm : ∀ K : IntegerL1Kernel,
    eLpNormEssSup (integerKernelFourierSymbol (integerKernelAdjoint K))
        (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) =
      eLpNormEssSup (integerKernelFourierSymbol K)
        (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩)
  unweightedEndpoint : ∀ {X : Type*} [MeasurableSpace X]
      (S : InvertibleSystem X) (f : X → ℂ) (N : Scale) {p : ℝ≥0∞},
    1 ≤ p → AEStronglyMeasurable f S.μ →
      eLpNorm (unweightedAverage S c.value f N) p S.μ ≤ eLpNorm f p S.μ
  mobiusEndpoint : ∀ {X : Type*} [MeasurableSpace X]
      (S : InvertibleSystem X) (f : X → ℂ) (N : Scale) {p : ℝ≥0∞},
    1 ≤ p → AEStronglyMeasurable f S.μ →
      eLpNorm (mobiusAverage S c.value f N) p S.μ ≤ eLpNorm f p S.μ
  vonMangoldtEndpoint : ∀ {X : Type*} [MeasurableSpace X]
      (S : InvertibleSystem X) (f : X → ℂ) (N : Scale) {p : ℝ≥0∞},
    1 ≤ p → AEStronglyMeasurable f S.μ →
      eLpNorm (vonMangoldtAverage S c.value f N) p S.μ ≤
        ENNReal.ofReal (Real.log (N.1 : ℝ)) * eLpNorm f p S.μ

/-- The exact collection of convolution/Fourier and endpoint results required
by blueprint `lem:fourier`. -/
theorem convolutionMultiplierBound (c : FractionalExponent) :
    ConvolutionMultiplierBound c :=
  ⟨eLpNorm_integerKernelConvolution_le,
    eLpNorm_integerKernelConvolution_two_le_fourierSymbol (hT := ⟨by norm_num⟩),
    integerKernelAdjoint_coeff,
    integerKernelAdjoint_norm_tsum,
    integerKernelAdjoint_enorm_tsum,
    eLpNorm_integerKernelConvolution_adjoint_le,
    eLpNormEssSup_integerKernelFourierSymbol_adjoint,
    fun S f N p hp hf =>
      eLpNorm_unweightedAverage_le_self S c.value f N (p := p) hp hf,
    fun S f N p hp hf =>
      eLpNorm_mobiusAverage_le_self S c.value f N (p := p) hp hf,
    fun S f N p hp hf =>
      eLpNorm_vonMangoldtAverage_le_log S c.value f N (p := p) hp hf⟩

end

end FractionalPrimes
