module

public import FractionalPrimes.FiniteOutputLayercake
public import FractionalPrimes.InterpolationPowerOptimization

@[expose] public section

/-!
# Optimized finite-support interpolation moment bound

This module converts the integrated ENNReal layer-cake estimate to the exact
real p-moment coefficient in the approved elementary interpolation argument.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

theorem finiteIntegerKernelConvolution_optimal_pMoment_le
    {p B epsilon : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (K : IntegerL1Kernel) (s out : Finset ℤ) (f : ℤ → ℂ)
    (hB : ∑' m : ℤ, ‖K.coeff m‖ ≤ B)
    (hBpos : 0 < B) (hepsilon : 0 < epsilon)
    (hL2 : ∀ g : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm (integerKernelConvolution K (g : ℤ → ℂ)) 2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (g : ℤ → ℂ) 2 Measure.count) :
    (∑ k ∈ out,
      ‖integerKernelConvolution K (finiteSupportCountLpTwo s f : ℤ → ℂ) k‖ ^ p) ≤
      (4 * p / (2 - p) + 2 * p / (p - 1)) *
        B ^ (2 - p) * epsilon ^ (2 * p - 2) *
          (∑ k ∈ s, ‖f k‖ ^ p) := by
  let a : ℝ := B / epsilon ^ 2
  let inputMoment : ℝ := ∑ k ∈ s, ‖f k‖ ^ p
  let lowMoment : ℝ :=
    ∑ k ∈ s, a ^ (2 - p) * ‖f k‖ ^ p / (2 - p)
  let highMoment : ℝ :=
    ∑ k ∈ s, a ^ (1 - p) * ‖f k‖ ^ p / (p - 1)
  let coefficient : ℝ :=
    (4 * p / (2 - p) + 2 * p / (p - 1)) *
      B ^ (2 - p) * epsilon ^ (2 * p - 2)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hENN := finiteIntegerKernelConvolution_output_pMoment_le
    (p := p) (a := a) hp1 hp2 ha K s out f hB hBpos hepsilon hL2

  have hlowENN :
      (∑ k ∈ s, ENNReal.ofReal
        (a ^ (2 - p) * ‖f k‖ ^ p / (2 - p))) = ENNReal.ofReal lowMoment := by
    dsimp [lowMoment]
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro k hk
    positivity
  have hhighENN :
      (∑ k ∈ s, ENNReal.ofReal
        (a ^ (1 - p) * ‖f k‖ ^ p / (p - 1))) = ENNReal.ofReal highMoment := by
    dsimp [highMoment]
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro k hk
    positivity

  have hleft :
      (∑ k ∈ out,
        ‖integerKernelConvolution K (finiteSupportCountLpTwo s f : ℤ → ℂ) k‖ₑ ^ p) =
        ENNReal.ofReal (∑ k ∈ out,
          ‖integerKernelConvolution K (finiteSupportCountLpTwo s f : ℤ → ℂ) k‖ ^ p) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (le_of_lt (lt_trans zero_lt_one hp1))]
    · intro k hk
      exact Real.rpow_nonneg (norm_nonneg _) _

  have hlowFactor : lowMoment = (a ^ (2 - p) / (2 - p)) * inputMoment := by
    dsimp [lowMoment, inputMoment]
    calc
      (∑ k ∈ s, a ^ (2 - p) * ‖f k‖ ^ p / (2 - p)) =
          ∑ k ∈ s, (a ^ (2 - p) / (2 - p)) * ‖f k‖ ^ p := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = (a ^ (2 - p) / (2 - p)) * ∑ k ∈ s, ‖f k‖ ^ p := by
            rw [← Finset.mul_sum]
  have hhighFactor : highMoment = (a ^ (1 - p) / (p - 1)) * inputMoment := by
    dsimp [highMoment, inputMoment]
    calc
      (∑ k ∈ s, a ^ (1 - p) * ‖f k‖ ^ p / (p - 1)) =
          ∑ k ∈ s, (a ^ (1 - p) / (p - 1)) * ‖f k‖ ^ p := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = (a ^ (1 - p) / (p - 1)) * ∑ k ∈ s, ‖f k‖ ^ p := by
            rw [← Finset.mul_sum]

  have hopt :
      p * (4 * epsilon ^ 2 * (a ^ (2 - p) / (2 - p)) +
        2 * B * (a ^ (1 - p) / (p - 1))) = coefficient := by
    dsimp [a, coefficient]
    calc
      _ = (4 * p / (2 - p) * epsilon ^ 2 *
            (B / epsilon ^ 2) ^ (2 - p) +
          2 * p / (p - 1) * B *
            (B / epsilon ^ 2) ^ (1 - p)) := by ring
      _ = _ := interpolation_optimal_scale_coefficient hBpos hepsilon

  have hrealRhs :
      p * (4 * epsilon ^ 2 * lowMoment + 2 * B * highMoment) =
        coefficient * inputMoment := by
    rw [hlowFactor, hhighFactor]
    calc
      p * (4 * epsilon ^ 2 *
            ((a ^ (2 - p) / (2 - p)) * inputMoment) +
          2 * B * ((a ^ (1 - p) / (p - 1)) * inputMoment)) =
          (p * (4 * epsilon ^ 2 * (a ^ (2 - p) / (2 - p)) +
            2 * B * (a ^ (1 - p) / (p - 1))) * inputMoment) := by ring
      _ = coefficient * inputMoment := by rw [hopt]

  have hlowProduct :
      4 * ENNReal.ofReal (epsilon ^ 2) * ENNReal.ofReal lowMoment =
        ENNReal.ofReal (4 * epsilon ^ 2 * lowMoment) := by
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * epsilon ^ 2)]
  have hhighProduct :
      2 * ENNReal.ofReal B * ENNReal.ofReal highMoment =
        ENNReal.ofReal (2 * B * highMoment) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * B)]
  have hsumRhs :
      ENNReal.ofReal (4 * epsilon ^ 2 * lowMoment) +
        ENNReal.ofReal (2 * B * highMoment) =
      ENNReal.ofReal (4 * epsilon ^ 2 * lowMoment + 2 * B * highMoment) := by
    exact (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  have hRhsENN :
      ENNReal.ofReal p *
        (4 * ENNReal.ofReal (epsilon ^ 2) * ENNReal.ofReal lowMoment +
          2 * ENNReal.ofReal B * ENNReal.ofReal highMoment) =
      ENNReal.ofReal (coefficient * inputMoment) := by
    rw [hlowProduct, hhighProduct, hsumRhs,
      ← ENNReal.ofReal_mul (le_of_lt (lt_trans zero_lt_one hp1)), hrealRhs]

  have hbound :
      ENNReal.ofReal (∑ k ∈ out,
        ‖integerKernelConvolution K (finiteSupportCountLpTwo s f : ℤ → ℂ) k‖ ^ p) ≤
          ENNReal.ofReal (coefficient * inputMoment) := by
    calc
      _ = ∑ k ∈ out,
          ‖integerKernelConvolution K (finiteSupportCountLpTwo s f : ℤ → ℂ) k‖ₑ ^ p := hleft.symm
      _ ≤ ENNReal.ofReal p *
          (4 * ENNReal.ofReal (epsilon ^ 2) *
              (∑ k ∈ s, ENNReal.ofReal
                (a ^ (2 - p) * ‖f k‖ ^ p / (2 - p))) +
            2 * ENNReal.ofReal B *
              (∑ k ∈ s, ENNReal.ofReal
                (a ^ (1 - p) * ‖f k‖ ^ p / (p - 1)))) := hENN
      _ = ENNReal.ofReal (coefficient * inputMoment) := by
          rw [hlowENN, hhighENN]
          exact hRhsENN
  have hnonneg : 0 ≤ coefficient * inputMoment := by
    apply mul_nonneg
    · dsimp [coefficient]
      positivity
    · dsimp [inputMoment]
      apply Finset.sum_nonneg
      intro k hk
      exact Real.rpow_nonneg (norm_nonneg _) _
  exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hbound

end FractionalPrimes
