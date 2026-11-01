module

public import FractionalPrimes.FiniteP2FullOutput
public import FractionalPrimes.FiniteSupportDensityExtension
public import FractionalPrimes.FiniteSupportLpGeneral
public import FractionalPrimes.GeneralDiscreteLpBridge
public import FractionalPrimes.LpConvolutionCLM

@[expose] public section

/-!
# The upper-exponent interpolation operator bound

The finite-output sequence-`ℓᵖ` estimate is identified with the concrete
counting-measure convolution CLM on exact finite-support inputs. The checked
density theorem then extends the estimate to all counting-measure `Lᵖ`
inputs. The adjoint `Lᵠ` estimate remains an explicit premise.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal NNReal

/-- The p>2 bound for the concrete convolution CLM on the exact finite
truncations. -/
theorem finiteSupportCountLpGeneral_integerKernelLpConvolutionCLM_norm_le_of_adjoint
    (p : ℝ) (hp : 2 < p) (K : IntegerL1Kernel) (C : ℝ≥0)
    (hAdj : ∀ g : Lp ℂ (ENNReal.ofReal (p / (p - 1)))
        (Measure.count : Measure ℤ),
      eLpNorm
          (integerKernelConvolution (integerKernelAdjoint K) (g : ℤ → ℂ))
          (ENNReal.ofReal (p / (p - 1))) Measure.count ≤
        (C : ℝ≥0∞) *
          eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal (p / (p - 1))) Measure.count)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    let P := ENNReal.ofReal p
    letI : Fact (1 ≤ P) := ⟨by
      dsimp [P]
      exact (ENNReal.one_le_ofReal).2 (by linarith)⟩
    let input := finiteSupportCountLpGeneral
      (ENNReal.ofReal_ne_zero_iff.mpr (by linarith : 0 < p))
      ENNReal.ofReal_ne_top Fact.out s f
    ‖integerKernelLpConvolutionCLM (p := P) K input‖ ≤
      (C : ℝ) * ‖input‖ := by
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
  have hPone : 1 ≤ P := by
    dsimp [P]
    exact (ENNReal.one_le_ofReal).2 (by linarith)
  letI : Fact (1 ≤ P) := ⟨hPone⟩
  let input : Lp ℂ P (Measure.count : Measure ℤ) :=
    finiteSupportCountLpGeneral hp0 hpTop hPone s f
  let outputSeq : lp (fun _ : ℤ => ℂ) P :=
    ⟨finiteSupportConvolutionOutput K s f,
      finiteSupportConvolution_memℓp_of_adjoint K p hp C hAdj s f⟩
  have hInputFunction : (input : ℤ → ℂ) =
      (fun k : ℤ => if k ∈ s then f k else 0) := by
    funext k
    exact finiteSupportCountLpGeneral_apply hp0 hpTop hPone s f k
  have hOutput : integerKernelLpConvolutionCLM (p := P) K input =
      generalLpToCountLp (p := P) hp0 hpTop outputSeq := by
    apply Lp.ext
    apply ae_count_int_iff_forall.mpr
    intro k
    calc
      (integerKernelLpConvolutionCLM (p := P) K input : ℤ → ℂ) k =
          integerKernelConvolution K (input : ℤ → ℂ) k := by
            rw [integerKernelLpConvolutionCLM_apply]
            exact integerKernelLpConvolution_apply_eq_integerKernelConvolution K input k
      _ = finiteSupportConvolutionOutput K s f k := by
            rw [hInputFunction]
            rfl
      _ = (generalLpToCountLp (p := P) hp0 hpTop outputSeq : ℤ → ℂ) k := by
            symm
            exact generalLpToCountLp_apply hp0 hpTop outputSeq k
  have hInputNorm : ‖input‖ = (∑ k ∈ s, ‖f k‖ ^ p) ^ (1 / p) := by
    dsimp [input]
    rw [finiteSupportCountLpGeneral_norm hp0 hpTop hPone s f, hPto]
  have hOutputNorm : ‖outputSeq‖ ≤ (C : ℝ) * ‖input‖ := by
    calc
      ‖outputSeq‖ ≤ (C : ℝ) * (∑ k ∈ s, ‖f k‖ ^ p) ^ (1 / p) := by
        exact finiteSupportConvolution_lpNorm_le_of_adjoint
          K p hp C hAdj s f
      _ = (C : ℝ) * ‖input‖ := by rw [hInputNorm]
  change ‖integerKernelLpConvolutionCLM (p := P) K input‖ ≤ _
  calc
    ‖integerKernelLpConvolutionCLM (p := P) K input‖ = ‖outputSeq‖ := by
      rw [hOutput, generalLpToCountLp_norm hp0 hpTop]
    _ ≤ (C : ℝ) * ‖input‖ := hOutputNorm

/-- The adjoint-bound p>2 convolution estimate for every counting-measure
`Lᵖ` input, obtained by extending the exact finite-support estimate through
density. -/
theorem integerKernelLpConvolutionCLM_norm_le_of_adjoint
    (p : ℝ) (hp : 2 < p) (K : IntegerL1Kernel) (C : ℝ≥0)
    (hAdj : ∀ g : Lp ℂ (ENNReal.ofReal (p / (p - 1)))
        (Measure.count : Measure ℤ),
      eLpNorm
          (integerKernelConvolution (integerKernelAdjoint K) (g : ℤ → ℂ))
          (ENNReal.ofReal (p / (p - 1))) Measure.count ≤
        (C : ℝ≥0∞) *
          eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal (p / (p - 1))) Measure.count) :
    let P := ENNReal.ofReal p
    letI : Fact (1 ≤ P) := ⟨by
      dsimp [P]
      exact (ENNReal.one_le_ofReal).2 (by linarith)⟩
    ∀ f : Lp ℂ P (Measure.count : Measure ℤ),
      ‖integerKernelLpConvolutionCLM (p := P) K f‖ ≤ (C : ℝ) * ‖f‖ := by
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hpReal : 0 < p := by linarith
  have hp0 : P ≠ 0 := by
    dsimp [P]
    exact ENNReal.ofReal_ne_zero_iff.mpr hpReal
  have hpTop : P ≠ ∞ := by
    dsimp [P]
    exact ENNReal.ofReal_ne_top
  have hPone : 1 ≤ P := by
    dsimp [P]
    exact (ENNReal.one_le_ofReal).2 (by linarith)
  letI : Fact (1 ≤ P) := ⟨hPone⟩
  have hfinite : ∀ s : Finset ℤ, ∀ f : ℤ → ℂ,
      ‖integerKernelLpConvolutionCLM (p := P) K
          (finiteSupportCountLpGeneral hp0 hpTop hPone s f)‖ ≤
        (C : ℝ) *
          ‖finiteSupportCountLpGeneral hp0 hpTop hPone s f‖ := by
    intro s f
    exact finiteSupportCountLpGeneral_integerKernelLpConvolutionCLM_norm_le_of_adjoint
      p hp K C hAdj s f
  dsimp only
  intro f
  exact continuousLinearMap_bound_of_finiteSupport
    (p := P) hp0 hpTop (integerKernelLpConvolutionCLM (p := P) K)
    (C : ℝ) hfinite f

end FractionalPrimes
