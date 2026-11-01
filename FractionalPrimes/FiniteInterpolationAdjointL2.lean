module

public import FractionalPrimes.FiniteInterpolationTwoBranch
public import FractionalPrimes.GeneralAdjointPairing
public import FractionalPrimes.DiscreteLpBridge
public import FractionalPrimes.LpConvolutionCLM
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-!
# Transfer of the full `L²` convolution bound to the adjoint kernel

The transfer uses the checked convolution pairing identity and Mathlib's
Hilbert-space adjoint. It assumes only the abstract full-`L²` estimate for
the original kernel, with no Fourier-symbol hypothesis.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal InnerProduct

noncomputable section

local instance countL2Fact : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
/-- The completed sequence-space pairing transports the convolution adjoint
identity to counting-measure `L²`. -/
theorem integerKernelLpConvolutionCLM_pairing_adjoint
    (K : IntegerL1Kernel)
    (f g : Lp ℂ 2 (Measure.count : Measure ℤ)) :
    inner ℂ g (integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞)) K f) =
      inner ℂ
        (integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞))
          (integerKernelAdjoint K) g) f := by
  let F : lp (fun _ : ℤ => ℂ) 2 := countLpToLp f
  let G : lp (fun _ : ℤ => ℂ) 2 := countLpToLp g
  have hbridge (L : IntegerL1Kernel)
      (v : Lp ℂ 2 (Measure.count : Measure ℤ)) :
      countLpToLp (integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞)) L v) =
        integerKernelConvolutionL2 (hT := ⟨by norm_num⟩) L
          (countLpToLp v) := by
    apply lp.ext
    funext k
    calc
      countLpToLp (integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞)) L v) k =
          integerKernelConvolution L (v : ℤ → ℂ) k := by
            rw [countLpToLp_apply, integerKernelLpConvolutionCLM_apply,
              integerKernelLpConvolution_apply_eq_integerKernelConvolution]
      _ = integerKernelConvolutionL2 (hT := ⟨by norm_num⟩) L
          (countLpToLp v) k := by
            rw [integerKernelConvolutionL2_apply (hT := ⟨by norm_num⟩)]
            congr 1
  have hseq := integerKernelConvolutionL2_pairing_adjoint
    (hT := ⟨by norm_num⟩) K F G
  calc
    inner ℂ g (integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞)) K f) =
        inner ℂ G
          (countLpToLp (integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞)) K f)) := by
            symm
            exact countLpToLp_inner g
              (integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞)) K f)
    _ = inner ℂ G (integerKernelConvolutionL2 K F) := by rw [hbridge K f]
    _ = inner ℂ (integerKernelConvolutionL2 (integerKernelAdjoint K) G) F := hseq
    _ = inner ℂ
        (countLpToLp
          (integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞))
            (integerKernelAdjoint K) g)) F := by rw [hbridge (integerKernelAdjoint K) g]
    _ = inner ℂ
        (integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞))
          (integerKernelAdjoint K) g) f :=
          countLpToLp_inner _ _

/-- As a continuous linear map on counting-measure `L²`, convolution by the
reflected-conjugate kernel is the Hilbert-space adjoint of convolution by K. -/
theorem integerKernelLpConvolutionCLM_eq_adjoint
    (K : IntegerL1Kernel) :
    integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞))
        (integerKernelAdjoint K) =
      (integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞)) K).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  exact (integerKernelLpConvolutionCLM_pairing_adjoint K g f).symm

/-- The abstract full-`L²` estimate for K transfers with the same epsilon to
the exact convolution by its reflected-conjugate adjoint kernel. -/
theorem integerKernelAdjointConvolution_eLpNorm_le_of_l2
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (K : IntegerL1Kernel)
    (hL2 : ∀ f : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm (integerKernelConvolution K (f : ℤ → ℂ)) 2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (f : ℤ → ℂ) 2 Measure.count) :
    ∀ g : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm
          (integerKernelConvolution (integerKernelAdjoint K) (g : ℤ → ℂ))
          2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (g : ℤ → ℂ) 2 Measure.count := by
  intro g
  let T := integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞)) K
  let Tstar := integerKernelLpConvolutionCLM (p := (2 : ℝ≥0∞))
    (integerKernelAdjoint K)
  have hTpoint (f : Lp ℂ 2 (Measure.count : Measure ℤ)) :
      (T f : ℤ → ℂ) = integerKernelConvolution K (f : ℤ → ℂ) := by
    funext k
    dsimp [T]
    rw [integerKernelLpConvolutionCLM_apply,
      integerKernelLpConvolution_apply_eq_integerKernelConvolution]
  have hTbound : ∀ f : Lp ℂ 2 (Measure.count : Measure ℤ),
      ‖T f‖ ≤ epsilon * ‖f‖ := by
    intro f
    have h := integerKernelLpConvolutionCLM_norm_le_of_l2 hepsilon K hL2 f
    simpa [T] using h
  have hTnorm : ‖T‖ ≤ epsilon := by
    apply ContinuousLinearMap.opNorm_le_bound T (le_of_lt hepsilon)
    intro f
    exact hTbound f
  have hTstarEq : Tstar = T.adjoint := by
    exact integerKernelLpConvolutionCLM_eq_adjoint K
  have hAdjNorm : ‖Tstar‖ = ‖T‖ := by
    rw [hTstarEq]
    exact ContinuousLinearMap.adjoint.norm_map T
  have hTstarBound : ‖Tstar g‖ ≤ epsilon * ‖g‖ := by
    calc
      ‖Tstar g‖ ≤ ‖Tstar‖ * ‖g‖ := Tstar.le_opNorm g
      _ = ‖T‖ * ‖g‖ := by rw [hAdjNorm]
      _ ≤ epsilon * ‖g‖ := mul_le_mul_of_nonneg_right hTnorm (norm_nonneg _)
  have hTstarPoint : (Tstar g : ℤ → ℂ) =
      integerKernelConvolution (integerKernelAdjoint K) (g : ℤ → ℂ) := by
    funext k
    dsimp [Tstar]
    rw [integerKernelLpConvolutionCLM_apply,
      integerKernelLpConvolution_apply_eq_integerKernelConvolution]
  have hreal :
      (eLpNorm (Tstar g : ℤ → ℂ) 2 Measure.count).toReal ≤
        (ENNReal.ofReal epsilon * eLpNorm (g : ℤ → ℂ) 2 Measure.count).toReal := by
    calc
      _ = ‖Tstar g‖ := (Lp.norm_def _).symm
      _ ≤ epsilon * ‖g‖ := hTstarBound
      _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hepsilon),
          Lp.norm_def]
  rw [← hTstarPoint]
  exact (ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top (Tstar g))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top g))).1 hreal

end

end FractionalPrimes
