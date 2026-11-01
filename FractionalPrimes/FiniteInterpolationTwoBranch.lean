module

public import FractionalPrimes.LpConvolutionCLM

@[expose] public section

/-!
# The exact `p = 2` branch of the interpolation estimate

The blueprint takes `C₂ = 1`; this branch is exactly the assumed `L²`
operator bound after translating `eLpNorm` into the `Lp` norm.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

theorem integerKernelLpConvolutionCLM_norm_le_of_l2
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (K : IntegerL1Kernel)
    (hL2 : ∀ g : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm (integerKernelConvolution K (g : ℤ → ℂ)) 2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (g : ℤ → ℂ) 2 Measure.count)
    (f : Lp ℂ 2 (Measure.count : Measure ℤ)) :
    ‖integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞)) K f‖ ≤
      epsilon * ‖f‖ := by
  rw [integerKernelLpConvolutionCLM_apply, Lp.norm_def]
  have hpoint : (integerKernelLpConvolution K f : ℤ → ℂ) =
      integerKernelConvolution K (f : ℤ → ℂ) := by
    funext k
    exact integerKernelLpConvolution_apply_eq_integerKernelConvolution K f k
  have hL2' :
      eLpNorm (integerKernelLpConvolution K f : ℤ → ℂ) 2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (f : ℤ → ℂ) 2 Measure.count := by
    rw [hpoint]
    exact hL2 f
  calc
    (eLpNorm (integerKernelLpConvolution K f : ℤ → ℂ) 2 Measure.count).toReal ≤
        (ENNReal.ofReal epsilon *
          eLpNorm (f : ℤ → ℂ) 2 Measure.count).toReal := by
            exact ENNReal.toReal_mono
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f))
              hL2'
    _ = epsilon * ‖f‖ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hepsilon),
        Lp.norm_def]

end FractionalPrimes
