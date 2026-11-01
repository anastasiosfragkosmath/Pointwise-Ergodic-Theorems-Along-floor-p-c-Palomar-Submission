module

public import FractionalPrimes.AdjointKernel
public import FractionalPrimes.FiniteInterpolationAdjointL2
public import FractionalPrimes.FiniteInterpolationLowerLpOperator
public import FractionalPrimes.FiniteInterpolationUpperLpOperator
public import FractionalPrimes.InterpolationPowerOptimization

@[expose] public section

/-!
# Exact p>2 interpolation assembly

The p>2 branch applies the checked full-input lower branch at the conjugate
exponent to the adjoint kernel. This file transfers that real norm bound to
the extended-norm premise used by the finite-support duality theorem, and
records the exact conjugate-exponent coefficient identity.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- Rewriting the p'<2 interpolation coefficient at `q = p/(p-1)` gives
the exact p>2 coefficient from the blueprint, without changing the
characteristic factor. -/
theorem interpolation_adjoint_coefficient_eq
    {p B epsilon : ℝ} (hp : 2 < p)
    (hB : 0 < B) (hepsilon : 0 < epsilon) :
    let q : ℝ := p / (p - 1)
    ((4 * q / (2 - q) + 2 * q / (q - 1)) *
      B ^ (2 - q) * epsilon ^ (2 * q - 2)) ^ (1 / q) =
    (4 * q / (2 - q) + 2 * q / (q - 1)) ^ (1 / q) *
      B ^ (1 - 2 / p) * epsilon ^ (2 / p) := by
  let q : ℝ := p / (p - 1)
  have hp1 : 1 < p := by linarith
  have hq1 : 1 < q := by
    dsimp [q]
    have hden : 0 < p - 1 := by linarith
    have hrepr : p / (p - 1) = 1 + 1 / (p - 1) := by
      field_simp
      ; ring
    rw [hrepr]
    have hinv : 0 < 1 / (p - 1) := one_div_pos.mpr hden
    linarith
  have hq2 : q < 2 := by
    dsimp [q]
    have hden : 0 < p - 1 := by linarith
    rw [div_lt_iff₀ hden]
    nlinarith
  have hBexp : 2 / q - 1 = 1 - 2 / p := by
    dsimp [q]
    field_simp
    ; ring
  have heexp : 2 - 2 / q = 2 / p := by
    dsimp [q]
    field_simp
    ; ring
  have hroot := interpolation_optimal_coefficient_rpow hq1 hq2 hB hepsilon
  simpa only [hBexp, heexp] using hroot

/-- The full-input p>2 convolution estimate, assembled from the p'<2 bound
for the adjoint kernel. The `L²` estimate for that adjoint is an explicit
premise, matching the transfer proved separately in
`FiniteInterpolationAdjointL2.lean`. -/
theorem integerKernelLpConvolutionCLM_norm_le_of_interpolation_upper
    {p B epsilon : ℝ} (hp : 2 < p) (K : IntegerL1Kernel)
    (hB : ∑' m : ℤ, ‖K.coeff m‖ ≤ B)
    (hBpos : 0 < B) (hepsilon : 0 < epsilon)
    (hL2 : ∀ g : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm
          (integerKernelConvolution K (g : ℤ → ℂ))
          2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (g : ℤ → ℂ) 2 Measure.count) :
    let q : ℝ := p / (p - 1)
    let C := (4 * q / (2 - q) + 2 * q / (q - 1)) ^ (1 / q) *
      B ^ (1 - 2 / p) * epsilon ^ (2 / p)
    let P := ENNReal.ofReal p
    letI : Fact (1 ≤ P) := ⟨by
      dsimp [P]
      exact (ENNReal.one_le_ofReal).2 (by linarith)⟩
    ∀ f : Lp ℂ P (Measure.count : Measure ℤ),
      ‖integerKernelLpConvolutionCLM (p := P) K f‖ ≤ C * ‖f‖ := by
  let q : ℝ := p / (p - 1)
  let P : ℝ≥0∞ := ENNReal.ofReal p
  let A : ℝ := 4 * q / (2 - q) + 2 * q / (q - 1)
  let Cq : ℝ := (A * B ^ (2 - q) * epsilon ^ (2 * q - 2)) ^ (1 / q)
  let C : ℝ := A ^ (1 / q) * B ^ (1 - 2 / p) * epsilon ^ (2 / p)
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hpden : 0 < p - 1 := by linarith
  have hq1 : 1 < q := by
    dsimp [q]
    have hrepr : p / (p - 1) = 1 + 1 / (p - 1) := by
      field_simp
      ; ring
    rw [hrepr]
    have hinv : 0 < 1 / (p - 1) := one_div_pos.mpr hpden
    linarith
  have hq2 : q < 2 := by
    dsimp [q]
    rw [div_lt_iff₀ hpden]
    nlinarith
  have hqpos : 0 < q := by linarith
  have hCqpos : 0 < Cq := by
    dsimp [Cq, A]
    positivity
  have hCqnonneg : 0 ≤ Cq := le_of_lt hCqpos
  let Cnn : ℝ≥0 := ⟨Cq, hCqnonneg⟩
  have hCnnReal : (Cnn : ℝ) = Cq := rfl
  have hCnnENN : (Cnn : ℝ≥0∞) = ENNReal.ofReal Cq := by
    calc
      (Cnn : ℝ≥0∞) = ENNReal.ofReal (Cnn : ℝ) :=
        (ENNReal.ofReal_coe_nnreal).symm
      _ = ENNReal.ofReal Cq := by rw [hCnnReal]
  have hCoeff : Cq = C := by
    dsimp [Cq, C, A]
    exact interpolation_adjoint_coefficient_eq hp hBpos hepsilon
  have hBadj : ∑' m : ℤ, ‖(integerKernelAdjoint K).coeff m‖ ≤ B := by
    rw [integerKernelAdjoint_norm_tsum]
    exact hB
  have hQone : 1 ≤ ENNReal.ofReal q :=
    (ENNReal.one_le_ofReal).2 (by linarith)
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨hQone⟩
  have hL2Adj := integerKernelAdjointConvolution_eLpNorm_le_of_l2
    hepsilon K hL2
  have hAdjointLower := integerKernelLpConvolutionCLM_norm_le_of_interpolation_lower
    (p := q) hq1 hq2 (integerKernelAdjoint K) hBadj hBpos hepsilon hL2Adj
  dsimp only at hAdjointLower
  have hqop : ∀ g : Lp ℂ (ENNReal.ofReal q) (Measure.count : Measure ℤ),
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal q)
          (integerKernelAdjoint K) g‖ ≤ Cq * ‖g‖ := by
    intro g
    simpa [Cq, A] using hAdjointLower g
  have hAdj : ∀ g : Lp ℂ (ENNReal.ofReal q) (Measure.count : Measure ℤ),
      eLpNorm
          (integerKernelConvolution (integerKernelAdjoint K) (g : ℤ → ℂ))
          (ENNReal.ofReal q) Measure.count ≤
        (Cnn : ℝ≥0∞) *
          eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal q) Measure.count := by
    intro g
    have hpoint :
        (integerKernelLpConvolutionCLM (p := ENNReal.ofReal q)
          (integerKernelAdjoint K) g : ℤ → ℂ) =
          integerKernelConvolution (integerKernelAdjoint K) (g : ℤ → ℂ) := by
      funext k
      rw [integerKernelLpConvolutionCLM_apply,
        integerKernelLpConvolution_apply_eq_integerKernelConvolution]
    rw [← hpoint,
      ← Lp.enorm_def
        (integerKernelLpConvolutionCLM (p := ENNReal.ofReal q)
          (integerKernelAdjoint K) g),
      ← Lp.enorm_def g, hCnnENN]
    calc
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal q)
          (integerKernelAdjoint K) g‖ₑ =
          ENNReal.ofReal
            ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal q)
              (integerKernelAdjoint K) g‖ := by simp
      _ ≤ ENNReal.ofReal (Cq * ‖g‖) :=
        ENNReal.ofReal_le_ofReal (hqop g)
      _ = ENNReal.ofReal Cq * ‖g‖ₑ := by
        rw [ENNReal.ofReal_mul hCqnonneg]
        rw [ofReal_norm]
  have hPone : 1 ≤ P := by
    dsimp [P]
    exact (ENNReal.one_le_ofReal).2 (by linarith)
  letI : Fact (1 ≤ P) := ⟨hPone⟩
  have hUpper := integerKernelLpConvolutionCLM_norm_le_of_adjoint
    p hp K Cnn hAdj
  dsimp only at hUpper
  dsimp only
  intro f
  calc
    ‖integerKernelLpConvolutionCLM (p := P) K f‖ ≤
        (Cnn : ℝ) * ‖f‖ := by
          simpa [P, hCnnReal] using hUpper f
    _ = C * ‖f‖ := by rw [hCnnReal, hCoeff]

end

end FractionalPrimes
