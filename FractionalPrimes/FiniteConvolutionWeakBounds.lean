module

public import FractionalPrimes.Operators
public import FractionalPrimes.ConvolutionMultiplierBound
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

@[expose] public section

/-!
# Weak endpoint estimates for integer-kernel convolution

These are the counting-measure Chebyshev estimates used in the finite
low/high split in blueprint `lem:interpolation`.  The `L²` theorem keeps the
operator-norm bound as an explicit hypothesis, exactly as in that blueprint.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Strict superlevel sets are controlled by the `Lᵖ` norm through
Mathlib's non-strict Chebyshev-Markov inequality. -/
theorem integerSequence_strictLevel_mul_le_eLpNorm
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (f : ℤ → ℂ) {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    ENNReal.ofReal threshold ^ p.toReal *
        Measure.count {k : ℤ | ENNReal.ofReal threshold < ‖f k‖ₑ} ≤
      eLpNorm f p Measure.count ^ p.toReal := by
  have hsubset :
      {k : ℤ | ENNReal.ofReal threshold < ‖f k‖ₑ} ⊆
        {k : ℤ | ENNReal.ofReal threshold ≤ ‖f k‖ₑ} := by
    intro k hk
    change ENNReal.ofReal threshold < ‖f k‖ₑ at hk
    exact hk.le
  calc
    ENNReal.ofReal threshold ^ p.toReal *
        Measure.count {k : ℤ | ENNReal.ofReal threshold < ‖f k‖ₑ} ≤
      ENNReal.ofReal threshold ^ p.toReal *
        Measure.count {k : ℤ | ENNReal.ofReal threshold ≤ ‖f k‖ₑ} := by
          gcongr
    _ ≤ eLpNorm f p Measure.count ^ p.toReal :=
      MeasureTheory.mul_meas_ge_le_pow_eLpNorm' (μ := Measure.count)
        hp0 hpTop (ENNReal.ofReal threshold)

/-- The `L¹` endpoint gives the exact weak `(1,1)` counting-measure bound
for convolution by an absolutely summable kernel. -/
theorem integerKernelConvolution_weakL1
    (K : IntegerL1Kernel)
    (f : Lp ℂ 1 (Measure.count : Measure ℤ))
    {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    ENNReal.ofReal threshold *
        Measure.count {k : ℤ | ENNReal.ofReal threshold <
          ‖integerKernelConvolution K (f : ℤ → ℂ) k‖ₑ} ≤
      (∑' m : ℤ, ‖K.coeff m‖ₑ) * eLpNorm (f : ℤ → ℂ) 1 Measure.count := by
  have hcheb := integerSequence_strictLevel_mul_le_eLpNorm
    (p := (1 : ℝ≥0∞)) (by norm_num) (by norm_num)
    (integerKernelConvolution K (f : ℤ → ℂ)) hthreshold
  have hyoung := eLpNorm_integerKernelConvolution_le
    (p := (1 : ℝ≥0∞)) (by norm_num) K f
  calc
    ENNReal.ofReal threshold *
        Measure.count {k : ℤ | ENNReal.ofReal threshold <
          ‖integerKernelConvolution K (f : ℤ → ℂ) k‖ₑ} ≤
        eLpNorm (integerKernelConvolution K (f : ℤ → ℂ)) 1 Measure.count := by
          simpa using hcheb
    _ ≤ (∑' m : ℤ, ‖K.coeff m‖ₑ) * eLpNorm (f : ℤ → ℂ) 1 Measure.count :=
      hyoung

/-- The `L²` endpoint gives the weak `(2,2)` estimate from the stated
operator bound. -/
theorem integerKernelConvolution_weakL2_of_bound
    (K : IntegerL1Kernel)
    (f : Lp ℂ 2 (Measure.count : Measure ℤ))
    (epsilon : ℝ≥0∞)
    (hL2 : eLpNorm (integerKernelConvolution K (f : ℤ → ℂ)) 2 Measure.count ≤
      epsilon * eLpNorm (f : ℤ → ℂ) 2 Measure.count)
    {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    ENNReal.ofReal threshold ^ 2 *
        Measure.count {k : ℤ | ENNReal.ofReal threshold <
          ‖integerKernelConvolution K (f : ℤ → ℂ) k‖ₑ} ≤
      (epsilon * eLpNorm (f : ℤ → ℂ) 2 Measure.count) ^ 2 := by
  have hcheb := integerSequence_strictLevel_mul_le_eLpNorm
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    (integerKernelConvolution K (f : ℤ → ℂ)) hthreshold
  calc
    ENNReal.ofReal threshold ^ 2 *
        Measure.count {k : ℤ | ENNReal.ofReal threshold <
          ‖integerKernelConvolution K (f : ℤ → ℂ) k‖ₑ} ≤
        eLpNorm (integerKernelConvolution K (f : ℤ → ℂ)) 2 Measure.count ^ 2 := by
          simpa using hcheb
    _ ≤ (epsilon * eLpNorm (f : ℤ → ℂ) 2 Measure.count) ^ 2 := by
      exact pow_le_pow_left' hL2 2

end

end FractionalPrimes
