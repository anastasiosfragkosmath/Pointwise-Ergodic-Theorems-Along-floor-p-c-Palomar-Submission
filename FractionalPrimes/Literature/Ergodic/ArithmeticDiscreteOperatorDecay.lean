module

public import FractionalPrimes.Literature.Ergodic.LogarithmicKernelDecay
public import FractionalPrimes.Literature.Ergodic.ArithmeticKernelMass

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
noncomputable section

theorem primeComparisonIntegerKernel_fourier (c ξ : ℝ) (N : Scale) :
    integerKernelFourierTransform (primeComparisonIntegerKernel c N) ξ =
      (N.val : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.val,
        ((vonMangoldtWeight n : ℂ) - 1) *
          unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) :=
  finiteWeightedIntegerKernel_fourier c ξ N _

/-- The actual arithmetic kernels satisfy the discrete operator-decay conclusion
once the two source scalar Fourier comparisons have been proved. -/
theorem arithmeticComparisonDiscreteOperatorDecay_of_fourier
    {p : ℝ} (hp : 1 < p) (c : ℝ)
    (hPrime : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val → ∀ ξ : ℝ,
        ‖(N.val : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.val,
          ((vonMangoldtWeight n : ℂ) - 1) *
            unitFrequencyPhase (ξ * (floorPower c n : ℝ))‖ ≤
          C * (Real.log (N.val : ℝ)) ^ (-A))
    (hMobius : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val → ∀ ξ : ℝ,
        ‖(N.val : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.val,
          (mobiusWeight n : ℂ) *
            unitFrequencyPhase (ξ * (floorPower c n : ℝ))‖ ≤
          C * (Real.log (N.val : ℝ)) ^ (-A)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ∀ D : ℝ, 0 < D → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
            (primeComparisonIntegerKernel c N)‖ +
          ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
            (mobiusIntegerKernel c N)‖ ≤
          C * (Real.log (N.val : ℝ)) ^ (-D) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hlog (N : Scale) (hN : 3 ≤ N.val) : 1 ≤ Real.log (N.val : ℝ) := by
    have hlog3 : 1 < Real.log 3 := by nlinarith [Real.log_three_gt_d9]
    exact hlog3.le.trans
      (Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hN))
  have hprimeMass (N : Scale) (hN : 3 ≤ N.val) :
      (∑' m : ℤ, ‖(primeComparisonIntegerKernel c N).coeff m‖) ≤
        2 * Real.log (N.val : ℝ) :=
    (primeComparisonIntegerKernel_norm_tsum_le c N).trans (by linarith [hlog N hN])
  have hmobMass (N : Scale) (hN : 3 ≤ N.val) :
      (∑' m : ℤ, ‖(mobiusIntegerKernel c N).coeff m‖) ≤
        1 * Real.log (N.val : ℝ) :=
    (mobiusIntegerKernel_norm_tsum_le c N).trans (by simpa only [one_mul] using hlog N hN)
  have hprimeTransform : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val → ∀ ξ : ℝ,
        ‖integerKernelFourierTransform (primeComparisonIntegerKernel c N) ξ‖ ≤
          C * (Real.log (N.val : ℝ)) ^ (-A) := by
    intro A hA
    obtain ⟨C, hC, hbound⟩ := hPrime A hA
    exact ⟨C, hC, fun N hN ξ => by
      rw [primeComparisonIntegerKernel_fourier]
      exact hbound N hN (-ξ)⟩
  have hmobTransform : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val → ∀ ξ : ℝ,
        ‖integerKernelFourierTransform (mobiusIntegerKernel c N) ξ‖ ≤
          C * (Real.log (N.val : ℝ)) ^ (-A) := by
    intro A hA
    obtain ⟨C, hC, hbound⟩ := hMobius A hA
    exact ⟨C, hC, fun N hN ξ => by
      rw [mobiusIntegerKernel_fourier]
      exact hbound N hN (-ξ)⟩
  intro D hD
  obtain ⟨C₁, hC₁, hb₁⟩ := logarithmicKernelOperatorDecay_of_transform hp
    (primeComparisonIntegerKernel c) 2 (by norm_num) hprimeMass hprimeTransform D hD
  obtain ⟨C₂, hC₂, hb₂⟩ := logarithmicKernelOperatorDecay_of_transform hp
    (mobiusIntegerKernel c) 1 (by norm_num) hmobMass hmobTransform D hD
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun N hN => ?_⟩
  simpa only [add_mul] using add_le_add (hb₁ N hN) (hb₂ N hN)

#print axioms arithmeticComparisonDiscreteOperatorDecay_of_fourier
end
end FractionalPrimes
