module
public import FractionalPrimes.Final.ForwardWeightedVariation
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory
open FractionalPrimes.Literature.Ergodic
open FractionalPrimes.Literature.Variation
open scoped ENNReal NNReal
noncomputable section
theorem transferForwardFiniteKernelOperatorNorm
    {X : Type*} [MeasurableSpace X]
    (S : System X) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hpTop : p < ∞)
    (K : ℤ →₀ ℂ) (hpos : ∀ m ∈ K.support, 0 ≤ m) (C : NNReal)
    (hdisc : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      extendedLpNorm (Measure.count : Measure ℤ) p
          (fun j => ‖finiteKernelConvolution K g j‖ₑ) ≤
        (C : ℝ≥0∞) * extendedLpNorm (Measure.count : Measure ℤ) p
          (fun j => ‖g j‖ₑ))
    (f : X → ℂ) (hf : MemLp f p S.μ) :
    eLpNorm (forwardKernelOperator S K f) p S.μ ≤
      (C : ℝ≥0∞) * eLpNorm f p S.μ := by
  classical
  let K₂ : Fin 2 → ℤ →₀ ℂ := fun i => if i = 0 then 0 else K
  have hK0 : K₂ 0 = 0 := by simp [K₂]
  have hK1 : K₂ 1 = K := by simp [K₂]
  have hrpos : 0 < (1 : ℝ) := by norm_num
  have hdiscVar : ∀ g : ℤ → ℂ, (Function.support g).Finite →
      finiteKernelDiscreteVariationLpNorm p 1 K₂ g ≤
        (C : ℝ≥0∞) * extendedLpNorm (Measure.count : Measure ℤ) p
          (fun j => ‖g j‖ₑ) := by
    intro g hg
    have heq : finiteKernelDiscreteVariation 1 K₂ g =
        fun j => ENNReal.ofReal ‖finiteKernelConvolution K g j‖ := by
      funext j
      change orderedRVariation (1 : ℝ)
        (fun i : Fin 2 => finiteKernelConvolution (K₂ i) g j) = _
      rw [orderedRVariation_finTwo_eq 1 hrpos]
      simp [hK0, hK1, finiteKernelConvolution, ofReal_norm]
    simpa [finiteKernelDiscreteVariationLpNorm, heq] using hdisc g hg
  have hfinite := transferForwardFiniteKernelVariation S p 1 hp1 hpTop (by norm_num) (by norm_num)
    K₂ (by
      intro i m hm
      by_cases hi : i = 0
      · simp [K₂, hi] at hm
      · exact hpos m (by simpa [K₂, hi] using hm)) C hdiscVar f hf
  have hsysVar : forwardKernelVariation S 1 K₂ f =
      fun x => ENNReal.ofReal ‖forwardKernelOperator S K f x‖ := by
    funext x
    change orderedRVariation (1 : ℝ)
      (fun i : Fin 2 => forwardKernelOperator S (K₂ i) f x) = _
    rw [orderedRVariation_finTwo_eq 1 hrpos]
    simp [hK0, hK1, forwardKernelOperator, ofReal_norm]
  have hsysMeas : AEStronglyMeasurable
      (forwardKernelOperator S K f) S.μ := by
    exact aemeasurable_forwardKernelOperator S K f hf.aestronglyMeasurable
      |>.aestronglyMeasurable
  have hnormEq := extendedLpNorm_eq_eLpNorm S.μ p
    (forwardKernelOperator S K f)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)) (ne_of_lt hpTop) hsysMeas
  have hfinite' :
      extendedLpNorm S.μ p (forwardKernelVariation S 1 K₂ f) ≤
        (C : ℝ≥0∞) * eLpNorm f p S.μ := by
    exact hfinite
  rw [hsysVar] at hfinite'
  rw [← hnormEq]
  simpa [extendedLpNorm_eq_eLpNorm S.μ p f
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)) (ne_of_lt hpTop)
      hf.aestronglyMeasurable] using hfinite'


theorem transferForwardWeightedFloorKernelOperatorNorm
    {X : Type*} [MeasurableSpace X] (S : System X)
    {p : ℝ} (hp : 1 < p) (c : ℝ) (N : Scale) (w : ℕ → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hdisc : letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
        (finiteWeightedIntegerKernel c N w)‖ ≤ C)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    eLpNorm (weightedAverage S c w f N) (ENNReal.ofReal p) S.μ ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) S.μ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hfinite (g : ℤ → ℂ) (hg : (Function.support g).Finite) :
      extendedLpNorm Measure.count (ENNReal.ofReal p)
          (fun j => ‖finiteKernelConvolution (weightedFloorKernelFinsupp c N w) g j‖ₑ) ≤
        ENNReal.ofReal C * extendedLpNorm Measure.count (ENNReal.ofReal p)
          (fun j => ‖g j‖ₑ) := by
    have hgseq : Memℓp g (ENNReal.ofReal p) :=
      (memℓp_zero hg).of_exponent_ge bot_le
    have hmemg : MemLp g (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
      memLp_count_of_memlp_seq_finite hp0 ENNReal.ofReal_ne_top ⟨g, hgseq⟩
    let G := hmemg.toLp g
    have hG : (G : ℤ → ℂ) = g :=
      funext (ae_count_int_iff_forall.mp hmemg.coeFn_toLp)
    have hout : (integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
        (finiteWeightedIntegerKernel c N w) G : ℤ → ℂ) =
        integerKernelConvolution (finiteWeightedIntegerKernel c N w) g := by
      funext j
      rw [integerKernelLpConvolutionCLM_apply,
        integerKernelLpConvolution_apply_eq_integerKernelConvolution, hG]
    rw [weightedFloorKernelFinsupp_convolution,
      extendedLpNorm_eq_eLpNorm _ _ _ hp0 ENNReal.ofReal_ne_top
        (measurable_of_countable _).aestronglyMeasurable,
      extendedLpNorm_eq_eLpNorm _ _ _ hp0 ENNReal.ofReal_ne_top
        (measurable_of_countable _).aestronglyMeasurable,
      ← hout, ← hG, ← Lp.enorm_def, ← Lp.enorm_def]
    change ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
        (finiteWeightedIntegerKernel c N w) G‖ₑ ≤
      ENNReal.ofReal C * ‖G‖ₑ
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal
      (((integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
        (finiteWeightedIntegerKernel c N w)).le_opNorm G).trans
          (mul_le_mul_of_nonneg_right hdisc (norm_nonneg G)))
  have hCcoe : ENNReal.ofNNReal (Real.toNNReal C) = ENNReal.ofReal C :=
    ENNReal.ofNNReal_toNNReal C
  have hfinite' := hfinite
  simp_rw [← hCcoe] at hfinite'
  have htransfer := transferForwardFiniteKernelOperatorNorm S (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr hp.le) ENNReal.ofReal_lt_top
    (weightedFloorKernelFinsupp c N w) (weightedFloorKernel_nonnegative c N w) (Real.toNNReal C) hfinite' f hf
  rw [weightedFloorKernel_forwardOperator] at htransfer
  change eLpNorm (weightedAverage S c w f N) (ENNReal.ofReal p) S.μ ≤
    ENNReal.ofNNReal (Real.toNNReal C) * eLpNorm f (ENNReal.ofReal p) S.μ at htransfer
  rw [hCcoe] at htransfer
  exact htransfer

#print axioms transferForwardWeightedFloorKernelOperatorNorm
end
end FractionalPrimes.Final
