module

public import FractionalPrimes.Literature.MSZ.SourceShortVariationFinite

/-! The positive-convolution short-variation adapter in the approved blueprint. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.External
open Literature.MSZ
noncomputable section

/-- `ha:msz`, with the hypotheses bundled in the exact source admissible data.
The conclusion concerns the ENNReal square, rather than its real coordinate. -/
theorem positiveConvolutionShortVariation
    (A : AdmissibleData) (p : ℝ)
    (hp : p = A.q ∨ p = A.q / (A.q - 1))
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) :
    eLpNorm (mszSourceShortVariation A (f : ℤ → ℂ))
        (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (sourceShortVariationConstant A) *
        eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count :=
  mszSourceShortVariation_eLpNorm_le A p hp f

#print axioms positiveConvolutionShortVariation
end
end FractionalPrimes.External
