module

public import FractionalPrimes.FiniteInterpolationDuality
public import FractionalPrimes.FiniteMomentExhaustion

@[expose] public section

/-!
# Full-output `ℓᵖ` bound from finite-support adjoint duality

This is the conditional upper-exponent branch of `lem:interpolation`.
The only operator estimate assumed is the explicit `ℓᵠ` estimate for the
adjoint; the conclusion is obtained by exhausting the finite-output bounds.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- The convolution output corresponding to the exact finite-support input
truncation used by the interpolation lemma. -/
def finiteSupportConvolutionOutput
    (K : IntegerL1Kernel) (t : Finset ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  integerKernelConvolution K (fun k => if k ∈ t then f k else 0)

/-- Under the adjoint `ℓᵠ` bound, the convolution of a finite-support input
belongs to `ℓᵖ` for `p > 2`. -/
theorem finiteSupportConvolution_memℓp_of_adjoint
    (K : IntegerL1Kernel) (p : ℝ) (hp : 2 < p) (C : ℝ≥0)
    (hAdj : ∀ g : Lp ℂ (ENNReal.ofReal (p / (p - 1)))
        (Measure.count : Measure ℤ),
      eLpNorm
          (integerKernelConvolution (integerKernelAdjoint K) (g : ℤ → ℂ))
          (ENNReal.ofReal (p / (p - 1))) Measure.count ≤
        (C : ℝ≥0∞) *
          eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal (p / (p - 1))) Measure.count)
    (t : Finset ℤ) (f : ℤ → ℂ) :
    Memℓp (finiteSupportConvolutionOutput K t f) (ENNReal.ofReal p) := by
  let out := finiteSupportConvolutionOutput K t f
  let inputNorm : ℝ≥0 :=
    (∑ k ∈ t, ‖f k‖₊ ^ p) ^ (1 / p)
  let outputBound : ℝ := (C : ℝ) * inputNorm
  have hp0 : 0 < p := by linarith
  have houtputBound : 0 ≤ outputBound := by
    change 0 ≤ (C : ℝ) * (inputNorm : ℝ)
    positivity
  have hfinite : ∀ u : Finset ℤ,
      ∑ k ∈ u, ‖out k‖ ^ p ≤ outputBound ^ p := by
    intro u
    have hrootNN := finiteSupportConvolutionLpBound_of_adjoint
      K p hp C hAdj t u f
    have hrootCast :
        (((∑ k ∈ u, ‖out k‖₊ ^ p) ^ (1 / p) : ℝ≥0) : ℝ) ≤
          outputBound := by
      have hcast := NNReal.coe_le_coe.mpr hrootNN
      simpa [out, finiteSupportConvolutionOutput, outputBound,
        inputNorm, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_sum,
        coe_nnnorm] using hcast
    have hsum_nonneg : 0 ≤ ∑ k ∈ u, ‖out k‖ ^ p := by positivity
    have hroot_nonneg : 0 ≤
        (∑ k ∈ u, ‖out k‖ ^ p) ^ (1 / p) := by positivity
    have hrootEq :
        (∑ k ∈ u, ‖out k‖ ^ p) ^ (1 / p) =
          (((∑ k ∈ u, ‖out k‖₊ ^ p) ^ (1 / p) : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_rpow, NNReal.coe_sum, coe_nnnorm]
    have hroot :
        (∑ k ∈ u, ‖out k‖ ^ p) ^ (1 / p) ≤ outputBound := by
      rw [hrootEq]
      exact hrootCast
    have hrootPow :
        ((∑ k ∈ u, ‖out k‖ ^ p) ^ (1 / p)) ^ p ≤ outputBound ^ p :=
      Real.rpow_le_rpow hroot_nonneg hroot hp0.le
    have hrootIdentity :
        ((∑ k ∈ u, ‖out k‖ ^ p) ^ (1 / p)) ^ p =
          ∑ k ∈ u, ‖out k‖ ^ p := by
      rw [← Real.rpow_mul hsum_nonneg]
      have hexp : (1 / p) * p = 1 := by field_simp [ne_of_gt hp0]
      rw [hexp, Real.rpow_one]
    rw [hrootIdentity] at hrootPow
    exact hrootPow
  have hmem : Memℓp out (ENNReal.ofReal p) := by
    apply memlp_of_uniform_finite_moment_bound out
    intro u
    simpa [ENNReal.toReal_ofReal hp0.le] using hfinite u
  simpa [out, finiteSupportConvolutionOutput] using hmem

/-- The full-output `ℓᵖ` norm is bounded by the finite input norm under the
same adjoint hypothesis. The estimate is stated for the canonical `lp`
representative of the pointwise convolution output. -/
theorem finiteSupportConvolution_lpNorm_le_of_adjoint
    (K : IntegerL1Kernel) (p : ℝ) (hp : 2 < p) (C : ℝ≥0)
    (hAdj : ∀ g : Lp ℂ (ENNReal.ofReal (p / (p - 1)))
        (Measure.count : Measure ℤ),
      eLpNorm
          (integerKernelConvolution (integerKernelAdjoint K) (g : ℤ → ℂ))
          (ENNReal.ofReal (p / (p - 1))) Measure.count ≤
        (C : ℝ≥0∞) *
          eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal (p / (p - 1))) Measure.count)
    (t : Finset ℤ) (f : ℤ → ℂ) :
    ‖(⟨finiteSupportConvolutionOutput K t f,
        finiteSupportConvolution_memℓp_of_adjoint K p hp C hAdj t f⟩ :
          lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p))‖ ≤
      (C : ℝ) * (∑ k ∈ t, ‖f k‖ ^ p) ^ (1 / p) := by
  let out := finiteSupportConvolutionOutput K t f
  let inputNorm : ℝ≥0 := (∑ k ∈ t, ‖f k‖₊ ^ p) ^ (1 / p)
  let outputBound : ℝ := (C : ℝ) * inputNorm
  have hp0 : 0 < p := by linarith
  have houtputBound : 0 ≤ outputBound := by
    change 0 ≤ (C : ℝ) * (inputNorm : ℝ)
    positivity
  have hfinite : ∀ u : Finset ℤ,
      ∑ k ∈ u, ‖out k‖ ^ p ≤ outputBound ^ p := by
    intro u
    have hrootNN := finiteSupportConvolutionLpBound_of_adjoint
      K p hp C hAdj t u f
    have hrootCast :
        (((∑ k ∈ u, ‖out k‖₊ ^ p) ^ (1 / p) : ℝ≥0) : ℝ) ≤
          outputBound := by
      have hcast := NNReal.coe_le_coe.mpr hrootNN
      simpa [out, finiteSupportConvolutionOutput, outputBound,
        inputNorm, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_sum,
        coe_nnnorm] using hcast
    have hsum_nonneg : 0 ≤ ∑ k ∈ u, ‖out k‖ ^ p := by positivity
    have hroot_nonneg : 0 ≤
        (∑ k ∈ u, ‖out k‖ ^ p) ^ (1 / p) := by positivity
    have hrootEq :
        (∑ k ∈ u, ‖out k‖ ^ p) ^ (1 / p) =
          (((∑ k ∈ u, ‖out k‖₊ ^ p) ^ (1 / p) : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_rpow, NNReal.coe_sum, coe_nnnorm]
    have hroot :
        (∑ k ∈ u, ‖out k‖ ^ p) ^ (1 / p) ≤ outputBound := by
      rw [hrootEq]
      exact hrootCast
    have hrootPow :
        ((∑ k ∈ u, ‖out k‖ ^ p) ^ (1 / p)) ^ p ≤ outputBound ^ p :=
      Real.rpow_le_rpow hroot_nonneg hroot hp0.le
    have hrootIdentity :
        ((∑ k ∈ u, ‖out k‖ ^ p) ^ (1 / p)) ^ p =
          ∑ k ∈ u, ‖out k‖ ^ p := by
      rw [← Real.rpow_mul hsum_nonneg]
      have hexp : (1 / p) * p = 1 := by field_simp [ne_of_gt hp0]
      rw [hexp, Real.rpow_one]
    rw [hrootIdentity] at hrootPow
    exact hrootPow
  let hpENN : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hfiniteP : ∀ u : Finset ℤ,
      ∑ k ∈ u, ‖out k‖ ^ (ENNReal.ofReal p).toReal ≤ outputBound ^ p := by
    intro u
    simpa [ENNReal.toReal_ofReal hp0.le] using hfinite u
  have hLpBound := lpOfUniformFiniteMomentBound_norm_le hpENN hpTop out
    (show 0 ≤ outputBound ^ p by positivity) hfiniteP
  have hrootBound : (outputBound ^ p) ^ (1 / p) = outputBound := by
    rw [← Real.rpow_mul houtputBound]
    have hexp : p * (1 / p) = 1 := by field_simp [ne_of_gt hp0]
    rw [hexp, Real.rpow_one]
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hLpBound' :
      ‖lpOfUniformFiniteMomentBound hpENN hpTop out
        (show 0 ≤ outputBound ^ p by positivity) hfiniteP‖ ≤
          (outputBound ^ p) ^ (1 / p) := by
    simpa only [htoReal] using hLpBound
  have hnormBound :
      ‖lpOfUniformFiniteMomentBound hpENN hpTop out
        (show 0 ≤ outputBound ^ p by positivity) hfiniteP‖ ≤
        outputBound := by
    calc
      _ ≤ (outputBound ^ p) ^ (1 / p) := hLpBound'
      _ = outputBound := hrootBound
  have hinputNorm : (inputNorm : ℝ) =
      (∑ k ∈ t, ‖f k‖ ^ p) ^ (1 / p) := by
    change (((∑ k ∈ t, ‖f k‖₊ ^ p) ^ (1 / p) : ℝ≥0) : ℝ) = _
    simp only [NNReal.coe_rpow, NNReal.coe_sum, coe_nnnorm]
  have hEq :
      (⟨finiteSupportConvolutionOutput K t f,
        finiteSupportConvolution_memℓp_of_adjoint K p hp C hAdj t f⟩ :
          lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p)) =
        lpOfUniformFiniteMomentBound hpENN hpTop out
          (show 0 ≤ outputBound ^ p by positivity) hfiniteP := by
    apply Subtype.ext
    rfl
  rw [hEq]
  simpa [outputBound, inputNorm, hinputNorm] using hnormBound

end

end FractionalPrimes
