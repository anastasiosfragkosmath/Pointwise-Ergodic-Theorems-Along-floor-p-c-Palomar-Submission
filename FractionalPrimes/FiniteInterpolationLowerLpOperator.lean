module

public import FractionalPrimes.FiniteInterpolationFullLp
public import FractionalPrimes.FiniteSupportDensityExtension
public import FractionalPrimes.LpConvolutionCLM
public import FractionalPrimes.GeneralDiscreteLpBridge

@[expose] public section

/-!
# The lower-exponent interpolation operator bound

This module identifies the exhausted sequence-space output with the
continuous-linear-map convolution, proves the bound first on the exact finite
truncations, and then extends it to all counting-measure `Lp` inputs by the
checked density theorem.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

theorem finiteSupportCountLpGeneral_integerKernelLpConvolutionCLM_norm_le
    {p B epsilon : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (K : IntegerL1Kernel) (s : Finset ℤ) (f : ℤ → ℂ)
    (hB : ∑' m : ℤ, ‖K.coeff m‖ ≤ B)
    (hBpos : 0 < B) (hepsilon : 0 < epsilon)
    (hL2 : ∀ g : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm (integerKernelConvolution K (g : ℤ → ℂ)) 2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (g : ℤ → ℂ) 2 Measure.count) :
    let C := ((4 * p / (2 - p) + 2 * p / (p - 1)) *
      B ^ (2 - p) * epsilon ^ (2 * p - 2)) ^ (1 / p)
    let P := ENNReal.ofReal p
    letI : Fact (1 ≤ P) := ⟨by
      dsimp [P]
      exact (ENNReal.one_le_ofReal).2 (by linarith)⟩
    let input := finiteSupportCountLpGeneral
      (ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one hp1))
      ENNReal.ofReal_ne_top
      (show 1 ≤ P from Fact.out) s f
    ‖integerKernelLpConvolutionCLM (p := P) K input‖ ≤ C * ‖input‖ := by
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
  let C : ℝ :=
    ((4 * p / (2 - p) + 2 * p / (p - 1)) *
      B ^ (2 - p) * epsilon ^ (2 * p - 2)) ^ (1 / p)
  obtain ⟨F, hF, hFnorm⟩ := exists_finiteInput_convolution_lp_of_optimal_moment
    hp1 hp2 K s f hB hBpos hepsilon hL2
  have hInputFunction : (input : ℤ → ℂ) =
      (finiteSupportCountLpTwo s f : ℤ → ℂ) := by
    funext k
    rw [finiteSupportCountLpGeneral_apply hp0 hpTop hPone s f k,
      finiteSupportCountLpTwo_apply]
  have hOutput : integerKernelLpConvolutionCLM (p := P) K input =
      generalLpToCountLp (p := P) hp0 hpTop F := by
    apply Lp.ext
    apply ae_count_int_iff_forall.mpr
    intro k
    calc
      (integerKernelLpConvolutionCLM (p := P) K input : ℤ → ℂ) k =
          integerKernelConvolution K (input : ℤ → ℂ) k := by
            rw [integerKernelLpConvolutionCLM_apply]
            exact integerKernelLpConvolution_apply_eq_integerKernelConvolution K input k
      _ = integerKernelConvolution K
          (finiteSupportCountLpTwo s f : ℤ → ℂ) k := by rw [hInputFunction]
      _ = (F : ℤ → ℂ) k := by rw [hF]
      _ = (generalLpToCountLp (p := P) hp0 hpTop F : ℤ → ℂ) k := by
            symm
            exact generalLpToCountLp_apply hp0 hpTop F k
  have hInputNorm : ‖input‖ = (∑ k ∈ s, ‖f k‖ ^ p) ^ (1 / p) := by
    dsimp [input]
    rw [finiteSupportCountLpGeneral_norm hp0 hpTop hPone s f, hPto]
  have hOutputNorm : ‖F‖ ≤ C * ‖input‖ := by
    calc
      ‖F‖ ≤
          ((4 * p / (2 - p) + 2 * p / (p - 1)) *
            B ^ (2 - p) * epsilon ^ (2 * p - 2)) ^ (1 / p) *
              (∑ k ∈ s, ‖f k‖ ^ p) ^ (1 / p) := by
                simpa using hFnorm
      _ = C * ‖input‖ := by
            rw [hInputNorm]
  calc
    ‖integerKernelLpConvolutionCLM (p := P) K input‖ = ‖F‖ := by
      rw [hOutput, generalLpToCountLp_norm hp0 hpTop]
    _ ≤ C * ‖input‖ := hOutputNorm

/-- The p<2 interpolation operator estimate on every input, obtained by
extending the checked finite-support estimate through density. -/
theorem integerKernelLpConvolutionCLM_norm_le_of_interpolation_lower
    {p B epsilon : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (K : IntegerL1Kernel)
    (hB : ∑' m : ℤ, ‖K.coeff m‖ ≤ B)
    (hBpos : 0 < B) (hepsilon : 0 < epsilon)
    (hL2 : ∀ g : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm (integerKernelConvolution K (g : ℤ → ℂ)) 2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (g : ℤ → ℂ) 2 Measure.count) :
    let C := ((4 * p / (2 - p) + 2 * p / (p - 1)) *
      B ^ (2 - p) * epsilon ^ (2 * p - 2)) ^ (1 / p)
    let P := ENNReal.ofReal p
    letI : Fact (1 ≤ P) := ⟨by
      dsimp [P]
      exact (ENNReal.one_le_ofReal).2 (by linarith)⟩
    ∀ f : Lp ℂ P (Measure.count : Measure ℤ),
      ‖integerKernelLpConvolutionCLM (p := P) K f‖ ≤ C * ‖f‖ := by
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
  let C : ℝ :=
    ((4 * p / (2 - p) + 2 * p / (p - 1)) *
      B ^ (2 - p) * epsilon ^ (2 * p - 2)) ^ (1 / p)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hfinite : ∀ s : Finset ℤ, ∀ g : ℤ → ℂ,
      ‖integerKernelLpConvolutionCLM (p := P) K
          (finiteSupportCountLpGeneral hp0 hpTop hPone s g)‖ ≤
        C * ‖finiteSupportCountLpGeneral hp0 hpTop hPone s g‖ := by
    intro s g
    exact finiteSupportCountLpGeneral_integerKernelLpConvolutionCLM_norm_le
      hp1 hp2 K s g hB hBpos hepsilon hL2
  dsimp only
  intro x
  exact continuousLinearMap_bound_of_finiteSupport
    (p := P) hp0 hpTop (integerKernelLpConvolutionCLM (p := P) K) C hfinite x

end FractionalPrimes
