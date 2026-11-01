module

public import FractionalPrimes.FiniteInterpolationOptimizedMoment
public import FractionalPrimes.FiniteMomentExhaustion

@[expose] public section

/-!
# Full-output sequence `lp` bound for finite inputs, `1 < p < 2`

The optimized moment estimate is uniform over every finite output set.
Finite-set exhaustion therefore gives an actual sequence `lp` representative
of the convolution on all of `ℤ`, with the exact optimized coefficient.
This file does not assert the density extension to arbitrary inputs.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

/-- For a finite-support input and `1 < p < 2`, the exact convolution output
belongs to sequence `lp` on all of `ℤ`, with the optimized constant from the
finite-output p-moment estimate. -/
theorem exists_finiteInput_convolution_lp_of_optimal_moment
    {p B epsilon : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (K : IntegerL1Kernel) (s : Finset ℤ) (f : ℤ → ℂ)
    (hB : ∑' m : ℤ, ‖K.coeff m‖ ≤ B)
    (hBpos : 0 < B) (hepsilon : 0 < epsilon)
    (hL2 : ∀ g : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm (integerKernelConvolution K (g : ℤ → ℂ)) 2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (g : ℤ → ℂ) 2 Measure.count) :
    ∃ F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      (F : ℤ → ℂ) =
        integerKernelConvolution K (finiteSupportCountLpTwo s f : ℤ → ℂ) ∧
      ‖F‖ ≤
        ((4 * p / (2 - p) + 2 * p / (p - 1)) *
          B ^ (2 - p) * epsilon ^ (2 * p - 2)) ^ (1 / p) *
          (∑ k ∈ s, ‖f k‖ ^ p) ^ (1 / p) := by
  let coefficient : ℝ :=
    (4 * p / (2 - p) + 2 * p / (p - 1)) *
      B ^ (2 - p) * epsilon ^ (2 * p - 2)
  let inputMoment : ℝ := ∑ k ∈ s, ‖f k‖ ^ p
  let totalMoment : ℝ := coefficient * inputMoment
  let output : ℤ → ℂ :=
    integerKernelConvolution K (finiteSupportCountLpTwo s f : ℤ → ℂ)
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hpReal : 0 < p := by linarith
  have hp0 : P ≠ 0 := by
    dsimp [P]
    exact ENNReal.ofReal_ne_zero_iff.mpr hpReal
  have hpTop : P ≠ ∞ := by
    dsimp [P]
    exact ENNReal.ofReal_ne_top
  have hPto : P.toReal = p := by
    dsimp [P]
    exact ENNReal.toReal_ofReal hpReal.le
  have hC : 0 ≤ totalMoment := by
    dsimp [totalMoment, coefficient, inputMoment]
    apply mul_nonneg
    · apply mul_nonneg
      · have hsum : 0 ≤ 4 * p / (2 - p) + 2 * p / (p - 1) := by positivity
        apply mul_nonneg hsum
        exact Real.rpow_nonneg (le_of_lt hBpos) _
      · exact Real.rpow_nonneg (le_of_lt hepsilon) _
    · apply Finset.sum_nonneg
      intro k hk
      exact Real.rpow_nonneg (norm_nonneg (f k)) _
  have hfinite : ∀ out : Finset ℤ,
      ∑ k ∈ out, ‖output k‖ ^ P.toReal ≤ totalMoment := by
    intro out
    rw [hPto]
    simpa [output, coefficient, inputMoment, totalMoment] using
      finiteIntegerKernelConvolution_optimal_pMoment_le hp1 hp2 K s out f
        hB hBpos hepsilon hL2
  let F : lp (fun _ : ℤ => ℂ) P :=
    lpOfUniformFiniteMomentBound hp0 hpTop output hC hfinite
  refine ⟨F, ?_, ?_⟩
  · funext k
    exact lpOfUniformFiniteMomentBound_apply hp0 hpTop output hC hfinite k
  · have hnorm := lpOfUniformFiniteMomentBound_norm_le
      hp0 hpTop output hC hfinite
    rw [hPto] at hnorm
    have hfactor : totalMoment ^ (1 / p) =
        coefficient ^ (1 / p) * inputMoment ^ (1 / p) := by
      dsimp [totalMoment]
      exact Real.mul_rpow
        (by
          dsimp [coefficient]
          apply mul_nonneg
          · have hsum : 0 ≤ 4 * p / (2 - p) + 2 * p / (p - 1) := by positivity
            exact mul_nonneg hsum (Real.rpow_nonneg (le_of_lt hBpos) _)
          · exact Real.rpow_nonneg (le_of_lt hepsilon) _)
        (by
          dsimp [inputMoment]
          apply Finset.sum_nonneg
          intro k hk
          exact Real.rpow_nonneg (norm_nonneg (f k)) _)
    calc
      ‖F‖ ≤ totalMoment ^ (1 / p) := by simpa [F] using hnorm
      _ = coefficient ^ (1 / p) * inputMoment ^ (1 / p) := hfactor
      _ = _ := by simp [coefficient, inputMoment]

end FractionalPrimes
