module

public import FractionalPrimes.PolynomialKernelProperties

@[expose] public section

open MeasureTheory
open scoped FourierTransform

namespace FractionalPrimes

/-- The angular convolution of the fixed cutoff used in `lup:kernel-data`. -/
noncomputable def polynomialKernelCutoffAngularConvolution (t : ℝ) : ℂ :=
  ∫ s : ℝ, (polynomialKernelCutoff s : ℂ) *
    (polynomialKernelCutoff (t - s) : ℂ)

/-- The angular Fourier transform of the normalized smoothing kernel. -/
noncomputable def polynomialKernelRhoAngularFourier (t : ℝ) : ℂ :=
  polynomialAngularFourier (fun u => (polynomialKernelRho u : ℂ)) t

theorem polynomialKernelPsi_normSq_coe (u : ℝ) :
    ((‖polynomialKernelPsiSchwartz u‖ ^ 2 : ℝ) : ℂ) =
      polynomialKernelPsiSchwartz u * polynomialKernelPsiSchwartz u := by
  have hreal : star (polynomialKernelPsiSchwartz u) =
      polynomialKernelPsiSchwartz u := by
    exact Complex.conj_eq_iff_im.mpr (polynomialKernelPsiSchwartz_im u)
  calc
    ((‖polynomialKernelPsiSchwartz u‖ ^ 2 : ℝ) : ℂ) =
        (Complex.normSq (polynomialKernelPsiSchwartz u) : ℂ) := by
      exact congrArg (fun x : ℝ => (x : ℂ))
        (Complex.normSq_eq_norm_sq _).symm
    _ = star (polynomialKernelPsiSchwartz u) *
          polynomialKernelPsiSchwartz u := by
      simpa using (Complex.normSq_eq_conj_mul_self
        (z := polynomialKernelPsiSchwartz u))
    _ = polynomialKernelPsiSchwartz u * polynomialKernelPsiSchwartz u := by
      rw [hreal]

/-- In Mathlib's `2π` Fourier convention, the Fourier transform of `ψ²` is
the convolution of the rescaled frequency cutoff. -/
theorem polynomialKernelRhoAngularFourier_eq_fourier (ξ : ℝ) :
    polynomialKernelRhoAngularFourier (2 * Real.pi * ξ) =
      (polynomialKernelZ⁻¹ : ℂ) * 𝓕 polynomialKernelPsiProductSchwartz ξ := by
  unfold polynomialKernelRhoAngularFourier polynomialAngularFourier
  calc
    _ = (polynomialKernelZ⁻¹ : ℂ) *
          ∫ u : ℝ, Complex.exp (↑(-2 * Real.pi * u * ξ) * Complex.I) *
            polynomialKernelPsiProductSchwartz u := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      rw [polynomialKernelRho_apply, Complex.ofReal_mul,
        polynomialKernelPsiProductSchwartz_apply,
        polynomialKernelPsi_normSq_coe]
      have hexp : Complex.exp (-Complex.I * ↑(2 * Real.pi * ξ) * ↑u) =
          Complex.exp (↑(-2 * Real.pi * u * ξ) * Complex.I) := by
        congr 1
        push_cast
        ring_nf
      rw [hexp]
      rw [Complex.ofReal_inv]
      ring_nf
    _ = (polynomialKernelZ⁻¹ : ℂ) *
          𝓕 polynomialKernelPsiProductSchwartz ξ := by
      congr 1
      rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards with u
      simp only [smul_eq_mul]

/-- Rescaling the Mathlib-frequency convolution converts its integral to
the angular convolution and exposes exactly the factor `1/(2π)`. -/
theorem polynomialKernelFrequencyConvolution_eq_angular (ξ : ℝ) :
    (∫ η : ℝ, polynomialKernelFrequencyCutoff η *
        polynomialKernelFrequencyCutoff (ξ - η)) =
      ((2 * Real.pi)⁻¹ : ℝ) •
        polynomialKernelCutoffAngularConvolution (2 * Real.pi * ξ) := by
  let h : ℝ → ℂ := fun s => (polynomialKernelCutoff s : ℂ) *
    (polynomialKernelCutoff (2 * Real.pi * ξ - s) : ℂ)
  have hchange : (∫ η : ℝ, h ((2 * Real.pi) * η)) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ s : ℝ, h s := by
    rw [Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
  calc
    _ = ∫ η : ℝ, h ((2 * Real.pi) * η) := by
      apply integral_congr_ae
      filter_upwards with η
      dsimp [h]
      simp only [polynomialKernelFrequencyCutoff_apply]
      congr 1
      ring_nf
    _ = ((2 * Real.pi)⁻¹ : ℝ) • ∫ s : ℝ, h s := hchange
    _ = _ := rfl

/-- Exact angular convolution formula for the smoothing kernel, including
the blueprint's `1/(2π)` normalization. -/
theorem polynomialKernelRhoAngularFourier_eq_cutoffConvolution (t : ℝ) :
    polynomialKernelRhoAngularFourier t =
      (((polynomialKernelZ⁻¹ * (2 * Real.pi)⁻¹ : ℝ) : ℂ) *
        polynomialKernelCutoffAngularConvolution t) := by
  let ξ : ℝ := t / (2 * Real.pi)
  have ht : 2 * Real.pi * ξ = t := by
    dsimp [ξ]
    field_simp [Real.pi_ne_zero]
  rw [← ht, polynomialKernelRhoAngularFourier_eq_fourier,
    polynomialKernelPsiProduct_fourier_eq_frequencyConvolution,
    polynomialKernelFrequencyConvolution_eq_angular]
  rw [Complex.real_smul]
  push_cast
  ring

theorem polynomialKernelCutoff_abs_lt_of_ne_zero {x : ℝ}
    (hx : polynomialKernelCutoff x ≠ 0) : |x| < (1 / 2 : ℝ) := by
  have hmem : x ∈ Function.support polynomialKernelCutoff := by
    simpa [Function.mem_support] using hx
  rw [polynomialKernelCutoff_support] at hmem
  exact abs_lt.mpr hmem

theorem polynomialKernelCutoffAngularConvolution_eq_zero_of_one_lt_abs
    {t : ℝ} (ht : 1 < |t|) :
    polynomialKernelCutoffAngularConvolution t = 0 := by
  unfold polynomialKernelCutoffAngularConvolution
  have hzero : (fun s : ℝ => (polynomialKernelCutoff s : ℂ) *
      (polynomialKernelCutoff (t - s) : ℂ)) = 0 := by
    funext s
    by_cases hs : polynomialKernelCutoff s = 0
    · simp [hs]
    · by_cases hts : polynomialKernelCutoff (t - s) = 0
      · simp [hts]
      · have hslt := polynomialKernelCutoff_abs_lt_of_ne_zero hs
        have htslt := polynomialKernelCutoff_abs_lt_of_ne_zero hts
        have htriangle : |t| ≤ |s| + |t - s| := by
          calc
            |t| = |s + (t - s)| := by congr 1; ring
            _ ≤ |s| + |t - s| := abs_add_le _ _
        have hsum : |s| + |t - s| < 1 := by linarith
        have hsmall : |t| < 1 := lt_of_le_of_lt htriangle hsum
        exact (not_lt_of_ge (le_of_lt ht) hsmall).elim
  change (∫ s : ℝ, (fun s : ℝ => (polynomialKernelCutoff s : ℂ) *
      (polynomialKernelCutoff (t - s) : ℂ)) s) = 0
  rw [hzero]
  simp

theorem polynomialKernelRhoAngularFourier_eq_zero_of_one_lt_abs
    {t : ℝ} (ht : 1 < |t|) : polynomialKernelRhoAngularFourier t = 0 := by
  rw [polynomialKernelRhoAngularFourier_eq_cutoffConvolution]
  simp [polynomialKernelCutoffAngularConvolution_eq_zero_of_one_lt_abs ht]

/-- The angular Fourier transform of ρ is supported in the exact interval
`[-1,1]` from the blueprint. -/
theorem polynomialKernelRhoAngularFourier_support_subset_Icc :
    Function.support polynomialKernelRhoAngularFourier ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro t ht
  by_contra hout
  have hlarge : 1 < |t| := by
    by_contra hh
    have hbound : |t| ≤ 1 := le_of_not_gt hh
    exact hout (abs_le.mp hbound)
  have hz := polynomialKernelRhoAngularFourier_eq_zero_of_one_lt_abs hlarge
  have hne : polynomialKernelRhoAngularFourier t ≠ 0 := by
    simpa [Function.mem_support] using ht
  exact hne hz

/-- The modulus bound for the angular Fourier transform follows from the
normalized nonnegative mass of ρ. -/
theorem polynomialKernelRhoAngularFourier_norm_le_one (t : ℝ) :
    ‖polynomialKernelRhoAngularFourier t‖ ≤ 1 := by
  calc
    ‖polynomialKernelRhoAngularFourier t‖ ≤
        ∫ u : ℝ, ‖(polynomialKernelRho u : ℂ)‖ :=
      norm_polynomialAngularFourier_le_integral_norm
        (fun u => (polynomialKernelRho u : ℂ)) t
    _ = ∫ u : ℝ, polynomialKernelRho u := by
      apply integral_congr_ae
      filter_upwards with u
      calc
        ‖(polynomialKernelRho u : ℂ)‖ = |polynomialKernelRho u| :=
          RCLike.norm_ofReal _
        _ = polynomialKernelRho u :=
          abs_of_nonneg (polynomialKernelRho_nonneg u)
    _ = 1 := polynomialKernelRho_integral

theorem polynomialKernelCutoffAngularConvolution_even (t : ℝ) :
    polynomialKernelCutoffAngularConvolution (-t) =
      polynomialKernelCutoffAngularConvolution t := by
  let h : ℝ → ℂ := fun s => (polynomialKernelCutoff s : ℂ) *
    (polynomialKernelCutoff (t - s) : ℂ)
  have hneg : (∫ s : ℝ, h (-s)) = ∫ s : ℝ, h s := by
    calc
      (∫ s : ℝ, h (-s)) = ∫ s : ℝ, h ((-1 : ℝ) * s) := by
        apply integral_congr_ae
        filter_upwards with s
        congr 1
        ring
      _ = |(-1 : ℝ)⁻¹| • ∫ s : ℝ, h s :=
        Measure.integral_comp_mul_left h (-1)
      _ = ∫ s : ℝ, h s := by norm_num
  calc
    polynomialKernelCutoffAngularConvolution (-t) =
        ∫ s : ℝ, h (-s) := by
      unfold polynomialKernelCutoffAngularConvolution
      apply integral_congr_ae
      filter_upwards with s
      change (polynomialKernelCutoff s : ℂ) *
          (polynomialKernelCutoff (-t - s) : ℂ) =
        (polynomialKernelCutoff (-s) : ℂ) *
          (polynomialKernelCutoff (t - -s) : ℂ)
      have harg : -t - s = -(t + s) := by ring
      rw [harg]
      simp only [polynomialKernelCutoff_neg, sub_neg_eq_add]
    _ = ∫ s : ℝ, h s := hneg
    _ = polynomialKernelCutoffAngularConvolution t := rfl

theorem polynomialKernelRhoAngularFourier_even (t : ℝ) :
    polynomialKernelRhoAngularFourier (-t) =
      polynomialKernelRhoAngularFourier t := by
  calc
    polynomialKernelRhoAngularFourier (-t) =
        (((polynomialKernelZ⁻¹ * (2 * Real.pi)⁻¹ : ℝ) : ℂ) *
          polynomialKernelCutoffAngularConvolution (-t)) :=
      polynomialKernelRhoAngularFourier_eq_cutoffConvolution (-t)
    _ = (((polynomialKernelZ⁻¹ * (2 * Real.pi)⁻¹ : ℝ) : ℂ) *
          polynomialKernelCutoffAngularConvolution t) := by
      rw [polynomialKernelCutoffAngularConvolution_even]
    _ = polynomialKernelRhoAngularFourier t :=
      (polynomialKernelRhoAngularFourier_eq_cutoffConvolution t).symm

end FractionalPrimes
