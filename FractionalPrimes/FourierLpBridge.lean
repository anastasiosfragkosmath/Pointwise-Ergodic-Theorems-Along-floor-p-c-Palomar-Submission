module

public import FractionalPrimes.DiscreteLpBridge
public import FractionalPrimes.FourierSequence

/-!
# Transport of the discrete Fourier `L²` estimate

This file applies the explicit counting-measure/sequence `L²` isometry to
the already checked Fourier-sequence convolution theorem.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The sequence-model convolution, transported back to counting-measure
`L²`, has exactly the paper's pointwise convolution representative. -/
theorem lpToCountLp_integerKernelConvolutionL2_apply
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (f : Lp ℂ 2 (Measure.count : Measure ℤ)) (k : ℤ) :
    (lpToCountLp
      (integerKernelConvolutionL2 (hT := hT) K (countLpToLp f)) : ℤ → ℂ) k =
      integerKernelConvolution K (f : ℤ → ℂ) k := by
  rw [lpToCountLp_apply, integerKernelConvolutionL2_apply]
  congr 1

/-- The sharp Fourier multiplier estimate in the counting-measure `L²`
model, with the exact paper convolution. -/
theorem eLpNorm_integerKernelConvolution_two_le_fourierSymbol
    {hT : Fact (0 < (1 : ℝ))} (K : IntegerL1Kernel)
    (f : Lp ℂ 2 (Measure.count : Measure ℤ)) :
    eLpNorm (integerKernelConvolution K (f : ℤ → ℂ)) 2 Measure.count ≤
      eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
        eLpNorm (f : ℤ → ℂ) 2 Measure.count := by
  let out := lpToCountLp
    (integerKernelConvolutionL2 (hT := hT) K (countLpToLp f))
  have hpoint : integerKernelConvolution K (f : ℤ → ℂ) = (out : ℤ → ℂ) := by
    funext k
    exact (lpToCountLp_integerKernelConvolutionL2_apply (hT := hT) K f k).symm
  rw [hpoint, ← Lp.enorm_def out, ← Lp.enorm_def f]
  calc
    ‖out‖ₑ =
        ‖integerKernelConvolutionL2 (hT := hT) K (countLpToLp f)‖ₑ :=
      by exact enorm_lpToCountLp _
    _ ≤ eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
        ‖countLpToLp f‖ₑ :=
      integerKernelConvolutionL2_enorm_le (hT := hT) K (countLpToLp f)
    _ = eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) * ‖f‖ₑ := by
      rw [enorm_countLpToLp]

end

end FractionalPrimes
