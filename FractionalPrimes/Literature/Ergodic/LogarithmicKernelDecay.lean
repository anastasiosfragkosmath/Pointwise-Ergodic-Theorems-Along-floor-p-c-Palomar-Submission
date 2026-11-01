module

public import FractionalPrimes.Literature.Ergodic.LogarithmicInterpolationScalar
public import FractionalPrimes.InterpolationKernelGain
public import FractionalPrimes.FourierLpBridge
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Scalar Fourier decay implies the logarithmic lp operator decay required
by the arithmetic comparison. The Fourier input remains explicit here. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
noncomputable section

theorem logarithmicKernelOperatorDecay
    {p : ℝ} (hp : 1 < p) (K : Scale → IntegerL1Kernel)
    (M : ℝ) (hM : 0 ≤ M)
    (hmass : ∀ N : Scale, 3 ≤ N.val →
      (∑' m : ℤ, ‖(K N).coeff m‖) ≤ M * Real.log (N.val : ℝ))
    (hFourier : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val →
        eLpNormEssSup (integerKernelFourierSymbol (K N))
            (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) ≤
          ENNReal.ofReal (C * (Real.log (N.val : ℝ)) ^ (-A))) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ∀ D : ℝ, 0 < D → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) (K N)‖ ≤
          C * (Real.log (N.val : ℝ)) ^ (-D) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  intro D hD
  have hβ := interpolationBeta_pos hp
  let A := (D + 1) / interpolationBeta p
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨C, hC, hFourierC⟩ := hFourier A hA
  let R := interpolationConstant p * (M + 1) ^ (1 - interpolationBeta p) *
    (C + 1) ^ interpolationBeta p
  have hI := interpolationConstant_nonneg hp
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨R, hR, fun N hN => ?_⟩
  let L := Real.log (N.val : ℝ)
  have hNreal : (3 : ℝ) ≤ (N.val : ℝ) := by exact_mod_cast hN
  have hlog3 : 1 < Real.log 3 := by nlinarith [Real.log_three_gt_d9]
  have hL : 1 ≤ L := hlog3.le.trans
    (Real.log_le_log (by norm_num : (0 : ℝ) < 3) hNreal)
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let B := (M + 1) * L
  let ε := (C + 1) * L ^ (-A)
  have hB : 0 < B := by dsimp [B]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hmassB : (∑' m : ℤ, ‖(K N).coeff m‖) ≤ B :=
    (hmass N hN).trans (by dsimp [B]; nlinarith)
  have hFourierε : eLpNormEssSup (integerKernelFourierSymbol (K N))
      (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) ≤ ENNReal.ofReal ε :=
    (hFourierC N hN).trans (ENNReal.ofReal_le_ofReal
      (by dsimp [ε, L]; nlinarith [Real.rpow_pos_of_pos hL0 (-A)]))
  have hL2 (g : Lp ℂ 2 (Measure.count : Measure ℤ)) :
      eLpNorm (integerKernelConvolution (K N) (g : ℤ → ℂ)) 2 Measure.count ≤
        ENNReal.ofReal ε * eLpNorm (g : ℤ → ℂ) 2 Measure.count :=
    (eLpNorm_integerKernelConvolution_two_le_fourierSymbol
      (hT := ⟨by norm_num⟩) (K N) g).trans
        (mul_le_mul_of_nonneg_right hFourierε bot_le)
  have hscalar : interpolationConstant p * B ^ (1 - interpolationBeta p) *
      ε ^ interpolationBeta p ≤ R * L ^ (-D) := by
    calc
      _ = interpolationConstant p *
          (B ^ (1 - interpolationBeta p) * ε ^ interpolationBeta p) := by ring
      _ ≤ interpolationConstant p *
          (((M + 1) ^ (1 - interpolationBeta p) * (C + 1) ^ interpolationBeta p) *
            L ^ (-D)) :=
        mul_le_mul_of_nonneg_left (logarithmicInterpolationScalar hβ hD hM hC hL) hI
      _ = _ := by dsimp [R]; ring
  apply (integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) (K N)).opNorm_le_bound
    (mul_nonneg hR (Real.rpow_nonneg hL0.le _))
  intro f
  exact (interpolateKernelGain hp (K N) hmassB hB hε hL2 f).trans
    (mul_le_mul_of_nonneg_right hscalar (norm_nonneg f))

#print axioms logarithmicKernelOperatorDecay

/-- Uniform bounds on the literal real-frequency transform supply the circle
essential-supremum premise, with no loss in the arithmetic constant. -/
theorem logarithmicKernelOperatorDecay_of_transform
    {p : ℝ} (hp : 1 < p) (K : Scale → IntegerL1Kernel)
    (M : ℝ) (hM : 0 ≤ M)
    (hmass : ∀ N : Scale, 3 ≤ N.val →
      (∑' m : ℤ, ‖(K N).coeff m‖) ≤ M * Real.log (N.val : ℝ))
    (hTransform : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val → ∀ ξ : ℝ,
        ‖integerKernelFourierTransform (K N) ξ‖ ≤
          C * (Real.log (N.val : ℝ)) ^ (-A)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ∀ D : ℝ, 0 < D → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) (K N)‖ ≤
          C * (Real.log (N.val : ℝ)) ^ (-D) := by
  apply logarithmicKernelOperatorDecay hp K M hM hmass
  intro A hA
  obtain ⟨C, hC, hbound⟩ := hTransform A hA
  refine ⟨C, hC, fun N hN => ?_⟩
  apply eLpNormEssSup_le_of_ae_bound
  apply Filter.Eventually.of_forall
  intro x
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hx : x ∈ ((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ico 0 (0 + (1 : ℝ)) := by
    rw [AddCircle.coe_image_Ico_eq]
    exact Set.mem_univ x
  obtain ⟨ξ, hξ, rfl⟩ := hx
  rw [integerKernelFourierSymbol_coe_Ico (K N) ξ (by simpa using hξ)]
  exact hbound N hN ξ

#print axioms logarithmicKernelOperatorDecay_of_transform
end
end FractionalPrimes
