module

public import FractionalPrimes.PolynomialKernelPsi
public import FractionalPrimes.PolynomialKernelScaling
public import Mathlib.Analysis.Fourier.Convolution

@[expose] public section

open MeasureTheory
open scoped FourierTransform

namespace FractionalPrimes

/-- The Schwartz function `|ψ|²`, represented by the real inner product on ℂ. -/
noncomputable def polynomialKernelPsiAbsSqSchwartz : SchwartzMap ℝ ℝ :=
  SchwartzMap.pairing (innerSL ℝ) polynomialKernelPsiSchwartz polynomialKernelPsiSchwartz

@[simp]
theorem polynomialKernelPsiAbsSqSchwartz_apply (u : ℝ) :
    polynomialKernelPsiAbsSqSchwartz u = ‖polynomialKernelPsiSchwartz u‖ ^ 2 := by
  rw [polynomialKernelPsiAbsSqSchwartz, SchwartzMap.pairing_apply_apply,
    innerSL_apply_apply, real_inner_self_eq_norm_sq]

/-- The finite mass `Z = ∫ |ψ|²` from `lup:kernel-data`. -/
noncomputable def polynomialKernelZ : ℝ :=
  ∫ u : ℝ, polynomialKernelPsiAbsSqSchwartz u

theorem polynomialKernelPsiAbsSqSchwartz_nonneg (u : ℝ) :
    0 ≤ polynomialKernelPsiAbsSqSchwartz u := by
  rw [polynomialKernelPsiAbsSqSchwartz_apply]
  positivity

theorem polynomialKernelPsiAbsSqSchwartz_integrable :
    Integrable polynomialKernelPsiAbsSqSchwartz := by
  exact polynomialKernelPsiAbsSqSchwartz.integrable

theorem polynomialKernelFrequencyCutoff_ne_zero :
    polynomialKernelFrequencyCutoff ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : SchwartzMap ℝ ℂ => f 0) h
  have hval : polynomialKernelFrequencyCutoff 0 = (Real.exp (-1) : ℂ) := by
    simp [polynomialKernelFrequencyCutoff_apply, polynomialKernelCutoff_eq_blueprint]
  rw [hval] at h0
  exact (Complex.ofReal_ne_zero.mpr (Real.exp_pos (-1)).ne') h0

theorem polynomialKernelPsiSchwartz_ne_zero : polynomialKernelPsiSchwartz ≠ 0 := by
  intro h
  apply polynomialKernelFrequencyCutoff_ne_zero
  have hfourier := congrArg (fun f : SchwartzMap ℝ ℂ => 𝓕 f) h
  simpa [polynomialKernelPsiSchwartz] using hfourier

theorem polynomialKernelPsiAbsSqSchwartz_has_nonzero_value :
    ∃ u : ℝ, polynomialKernelPsiAbsSqSchwartz u ≠ 0 := by
  by_contra h
  push Not at h
  apply polynomialKernelPsiSchwartz_ne_zero
  ext u
  have hu := h u
  rw [polynomialKernelPsiAbsSqSchwartz_apply] at hu
  have hnorm : ‖polynomialKernelPsiSchwartz u‖ ^ 2 = 0 := hu
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

theorem polynomialKernelZ_pos : 0 < polynomialKernelZ := by
  rw [polynomialKernelZ]
  obtain ⟨u, hu⟩ := polynomialKernelPsiAbsSqSchwartz_has_nonzero_value
  exact integral_pos_of_integrable_nonneg_nonzero
    polynomialKernelPsiAbsSqSchwartz.continuous
    polynomialKernelPsiAbsSqSchwartz_integrable
    polynomialKernelPsiAbsSqSchwartz_nonneg hu

theorem polynomialKernelZ_ne_zero : polynomialKernelZ ≠ 0 :=
  (ne_of_gt polynomialKernelZ_pos)

/-- The normalized nonnegative smoothing kernel from `lup:kernel-data`. -/
noncomputable def polynomialKernelRhoSchwartz : SchwartzMap ℝ ℝ :=
  polynomialKernelZ⁻¹ • polynomialKernelPsiAbsSqSchwartz

/-- Pointwise form of the approved definition `ρ = Z⁻¹ |ψ|²`. -/
noncomputable def polynomialKernelRho (u : ℝ) : ℝ :=
  polynomialKernelRhoSchwartz u

@[simp]
theorem polynomialKernelRho_apply (u : ℝ) :
    polynomialKernelRho u = polynomialKernelZ⁻¹ *
      ‖polynomialKernelPsiSchwartz u‖ ^ 2 := by
  simp [polynomialKernelRho, polynomialKernelRhoSchwartz,
    polynomialKernelPsiAbsSqSchwartz_apply, smul_eq_mul]

theorem polynomialKernelRho_nonneg (u : ℝ) : 0 ≤ polynomialKernelRho u := by
  rw [polynomialKernelRho_apply]
  exact mul_nonneg (inv_nonneg.mpr polynomialKernelZ_pos.le)
    (sq_nonneg _)

theorem polynomialKernelRho_integral :
    ∫ u : ℝ, polynomialKernelRho u = 1 := by
  change ∫ u : ℝ, polynomialKernelZ⁻¹ * polynomialKernelPsiAbsSqSchwartz u = 1
  rw [integral_const_mul]
  change polynomialKernelZ⁻¹ * polynomialKernelZ = 1
  exact inv_mul_cancel₀ polynomialKernelZ_ne_zero

theorem polynomialKernelRho_even (u : ℝ) :
    polynomialKernelRho (-u) = polynomialKernelRho u := by
  simp [polynomialKernelRho_apply, polynomialKernelPsiSchwartz_even]

/-- The first absolute moment `M₁` in `lup:kernel-data`. -/
noncomputable def polynomialKernelM1 : ℝ :=
  ∫ u : ℝ, |u| * polynomialKernelRho u

theorem polynomialKernelM1_integrable :
    Integrable (fun u : ℝ => |u| * polynomialKernelRho u) := by
  have h := polynomialKernelRhoSchwartz.integrable_pow_mul (μ := volume) 1
  apply h.congr
  filter_upwards with u
  change |u| ^ 1 * ‖polynomialKernelRho u‖ = |u| * polynomialKernelRho u
  rw [Real.norm_eq_abs, abs_of_nonneg (polynomialKernelRho_nonneg u), pow_one]

theorem polynomialKernelRho_firstMoment_finite :
    Integrable (fun u : ℝ => |u| * polynomialKernelRho u) :=
  polynomialKernelM1_integrable

/-- A translate of the frequency cutoff, with convention `gξ(v)=g(v+ξ)`. -/
noncomputable def polynomialKernelFrequencyShift (ξ : ℝ) : SchwartzMap ℝ ℂ :=
  polynomialKernelFrequencyCutoff.compSubConstCLM ℂ (-ξ)

@[simp]
theorem polynomialKernelFrequencyShift_apply (ξ v : ℝ) :
    polynomialKernelFrequencyShift ξ v = polynomialKernelFrequencyCutoff (v + ξ) := by
  simp [polynomialKernelFrequencyShift, SchwartzMap.compSubConstCLM_apply]

/-- The inverse transform of the translated cutoff is the corresponding
modulation of ψ, with Mathlib's `2π` convention kept explicit. -/
noncomputable def polynomialKernelPsiFrequencyShift (ξ : ℝ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (polynomialKernelFrequencyShift ξ)

theorem polynomialKernelPsiFrequencyShift_apply (ξ u : ℝ) :
    polynomialKernelPsiFrequencyShift ξ u =
      Complex.exp (↑(-2 * Real.pi * ξ * u) * Complex.I) * polynomialKernelPsiSchwartz u := by
  let phase : ℝ → ℂ := fun v => Complex.exp (↑(2 * Real.pi * v * u) * Complex.I)
  have hpsi : polynomialKernelPsiSchwartz u =
      ∫ v : ℝ, phase v * polynomialKernelFrequencyCutoff v := by
    rw [polynomialKernelPsiSchwartz, SchwartzMap.fourierInv_coe,
      Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with v
    have hexp :
        Complex.exp (↑(2 * Real.pi * inner ℝ v u) * Complex.I) = phase v := by
      dsimp [phase]
      congr 1
      simp
      ring
    rw [hexp]
    rfl
  change (𝓕⁻ (polynomialKernelFrequencyShift ξ)) u = _
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  calc
    _ = ∫ v : ℝ, phase v * polynomialKernelFrequencyCutoff (v + ξ) := by
      apply integral_congr_ae
      filter_upwards with v
      rw [polynomialKernelFrequencyShift_apply]
      have hexp :
          Complex.exp (↑(2 * Real.pi * inner ℝ v u) * Complex.I) = phase v := by
        dsimp [phase]
        congr 1
        simp
        ring
      rw [hexp]
      rfl
    _ = ∫ v : ℝ, phase (v - ξ) * polynomialKernelFrequencyCutoff v := by
      simpa [phase, sub_add_cancel] using
        (integral_sub_right_eq_self
          (f := fun v : ℝ => phase (v - ξ) * polynomialKernelFrequencyCutoff v) (-ξ))
    _ = Complex.exp (↑(-2 * Real.pi * ξ * u) * Complex.I) *
          ∫ v : ℝ, phase v * polynomialKernelFrequencyCutoff v := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      dsimp [phase]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    _ = _ := by rw [← hpsi]

theorem polynomialKernelPsiFrequencyShift_doubleInv (ξ u : ℝ) :
    𝓕⁻ (polynomialKernelPsiFrequencyShift ξ) u =
      polynomialKernelFrequencyCutoff (ξ - u) := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  change (𝓕 (polynomialKernelPsiFrequencyShift ξ : ℝ → ℂ)) (-u) = _
  have hFourierSchwartz : 𝓕 (polynomialKernelPsiFrequencyShift ξ) =
      polynomialKernelFrequencyShift ξ := by
    simp [polynomialKernelPsiFrequencyShift]
  have hFourier : 𝓕 (polynomialKernelPsiFrequencyShift ξ : ℝ → ℂ) (-u) =
      polynomialKernelFrequencyShift ξ (-u) := by
    simpa only [SchwartzMap.fourier_coe] using
      congrArg (fun f : SchwartzMap ℝ ℂ => f (-u)) hFourierSchwartz
  rw [hFourier]
  simp [polynomialKernelFrequencyShift, SchwartzMap.compSubConstCLM_apply]
  congr 1
  ring

/-- The pointwise square of ψ, kept as a complex Schwartz function for the
Fourier product calculation. -/
noncomputable def polynomialKernelPsiProductSchwartz : SchwartzMap ℝ ℂ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
    polynomialKernelPsiSchwartz polynomialKernelPsiSchwartz

@[simp]
theorem polynomialKernelPsiProductSchwartz_apply (u : ℝ) :
    polynomialKernelPsiProductSchwartz u =
      polynomialKernelPsiSchwartz u * polynomialKernelPsiSchwartz u := by
  simp [polynomialKernelPsiProductSchwartz]

/-- Fourier transform of the square of ψ as the frequency-side convolution.
This uses Mathlib's exact normalized Fourier convention `exp(-2πixξ)`. -/
theorem polynomialKernelPsiProduct_fourier_eq_frequencyConvolution (ξ : ℝ) :
    𝓕 polynomialKernelPsiProductSchwartz ξ =
      ∫ t : ℝ, polynomialKernelFrequencyCutoff t *
        polynomialKernelFrequencyCutoff (ξ - t) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ u : ℝ, polynomialKernelPsiSchwartz u *
          polynomialKernelPsiFrequencyShift ξ u := by
      apply integral_congr_ae
      filter_upwards with u
      rw [polynomialKernelPsiProductSchwartz_apply,
        polynomialKernelPsiFrequencyShift_apply]
      have hexp :
          Complex.exp (↑(-2 * Real.pi * u * ξ) * Complex.I) =
            Complex.exp (↑(-2 * Real.pi * ξ * u) * Complex.I) := by
        congr 1
        push_cast
        ring
      simp only [smul_eq_mul]
      rw [hexp]
      ring
    _ = ∫ t : ℝ, polynomialKernelFrequencyCutoff t *
          polynomialKernelFrequencyCutoff (ξ - t) := by
      have h := SchwartzMap.integral_fourierInv_mul_eq
        polynomialKernelFrequencyCutoff (polynomialKernelPsiFrequencyShift ξ)
      calc
        _ = ∫ u : ℝ, 𝓕⁻ polynomialKernelFrequencyCutoff u *
              polynomialKernelPsiFrequencyShift ξ u := by rfl
        _ = ∫ u : ℝ, polynomialKernelFrequencyCutoff u *
              𝓕⁻ (polynomialKernelPsiFrequencyShift ξ) u := h
        _ = ∫ t : ℝ, polynomialKernelFrequencyCutoff t *
              polynomialKernelFrequencyCutoff (ξ - t) := by
          apply integral_congr_ae
          filter_upwards with t
          rw [polynomialKernelPsiFrequencyShift_doubleInv]

theorem polynomialKernelRho_integrable : Integrable polynomialKernelRho := by
  exact polynomialKernelRhoSchwartz.integrable

end FractionalPrimes
