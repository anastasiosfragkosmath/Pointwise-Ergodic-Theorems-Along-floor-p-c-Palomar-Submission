module

public import FractionalPrimes.FiniteInterpolationTwoBranch
public import FractionalPrimes.FiniteInterpolationLowerLpOperator
public import FractionalPrimes.FiniteInterpolationUpperLpAssembly
public import FractionalPrimes.InterpolationExponents

@[expose] public section

/-!
# The positive-endpoint convolution interpolation theorem

This assembles the exact `1<p<2`, `p=2`, and `p>2` branches of blueprint
`lem:interpolation`, retaining its piecewise constant and minimum exponent.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

private theorem lp_norm_cast {q r : ℝ≥0∞} (hqr : q = r)
    (f : Lp ℂ q (Measure.count : Measure ℤ)) :
    ‖f‖ = ‖hqr ▸ f‖ := by
  cases hqr
  rfl

private theorem convolution_clm_norm_cast {q r : ℝ≥0∞}
    [Fact (1 ≤ q)] [Fact (1 ≤ r)] (hqr : q = r)
    (K : IntegerL1Kernel) (f : Lp ℂ q (Measure.count : Measure ℤ)) :
    ‖integerKernelLpConvolutionCLM (p := q) K f‖ =
      ‖integerKernelLpConvolutionCLM (p := r) K (hqr ▸ f)‖ := by
  cases hqr
  rfl

theorem interpolateKernelGain
    {p B epsilon : ℝ} (hp1 : 1 < p) (K : IntegerL1Kernel)
    (hB : ∑' m : ℤ, ‖K.coeff m‖ ≤ B)
    (hBpos : 0 < B) (hepsilon : 0 < epsilon)
    (hL2 : ∀ g : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm (integerKernelConvolution K (g : ℤ → ℂ)) 2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (g : ℤ → ℂ) 2 Measure.count) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨(ENNReal.one_le_ofReal).2 (by linarith)⟩
    ∀ f : Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ),
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) K f‖ ≤
        interpolationConstant p * B ^ (1 - interpolationBeta p) *
          epsilon ^ interpolationBeta p * ‖f‖ := by
  have hp0 : 0 < p := by linarith
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨(ENNReal.one_le_ofReal).2 (by linarith)⟩
  rcases lt_trichotomy p 2 with hp2 | hp2 | hp2
  · have hlow := integerKernelLpConvolutionCLM_norm_le_of_interpolation_lower
      hp1 hp2 K hB hBpos hepsilon hL2
    have hcoeff := interpolation_optimal_coefficient_rpow
      hp1 hp2 hBpos hepsilon
    have hbeta : interpolationBeta p = 2 - 2 / p :=
      interpolationBeta_eq_lower hp1 hp2
    have hbexp : 1 - interpolationBeta p = 2 / p - 1 := by
      rw [hbeta]
      ring
    have hconstant : interpolationConstant p =
        (4 * p / (2 - p) + 2 * p / (p - 1)) ^ (1 / p) := by
      simp [interpolationConstant, interpolationLowerConstant, hp2]
    intro f
    calc
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) K f‖ ≤
          ((4 * p / (2 - p) + 2 * p / (p - 1)) *
            B ^ (2 - p) * epsilon ^ (2 * p - 2)) ^ (1 / p) * ‖f‖ :=
        hlow f
      _ = interpolationConstant p * B ^ (1 - interpolationBeta p) *
            epsilon ^ interpolationBeta p * ‖f‖ := by
          rw [hcoeff, hconstant, hbexp, hbeta]
  · subst p
    have hP₂ : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
    intro f
    have htwo := integerKernelLpConvolutionCLM_norm_le_of_l2
      hepsilon K hL2 (hP₂ ▸ f)
    have hbeta : interpolationBeta 2 = 1 := by
      norm_num [interpolationBeta]
    have hconstant : interpolationConstant 2 = 1 := by
      norm_num [interpolationConstant, interpolationLowerConstant]
    rw [convolution_clm_norm_cast hP₂ K f]
    rw [lp_norm_cast hP₂ f]
    simpa [hbeta, hconstant] using htwo
  · have hupper := integerKernelLpConvolutionCLM_norm_le_of_interpolation_upper
      hp2 K hB hBpos hepsilon hL2
    have hbeta : interpolationBeta p = 2 / p :=
      interpolationBeta_eq_upper hp2
    have hp0 : 0 < p := by linarith
    have hpden : 0 < p - 1 := by linarith
    have hInv : 1 / (p / (p - 1)) = (p - 1) / p := by
      field_simp [ne_of_gt hp0, ne_of_gt hpden]
    intro f
    dsimp only at hupper
    calc
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) K f‖ ≤
          (4 * (p / (p - 1)) / (2 - p / (p - 1)) +
            2 * (p / (p - 1)) / ((p / (p - 1)) - 1)) ^
              (1 / (p / (p - 1))) * B ^ (1 - 2 / p) *
                epsilon ^ (2 / p) * ‖f‖ := by
          exact hupper f
      _ = interpolationConstant p * B ^ (1 - interpolationBeta p) *
            epsilon ^ interpolationBeta p * ‖f‖ := by
          rw [hbeta]
          unfold interpolationConstant interpolationLowerConstant
          simp only [not_lt_of_gt hp2, ne_of_gt hp2, ite_false]

end FractionalPrimes
