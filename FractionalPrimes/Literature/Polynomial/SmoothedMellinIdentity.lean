module

public import FractionalPrimes.Literature.Polynomial.MellinWindowData
public import FractionalPrimes.PolynomialKernelAngularFourierProperties
public import FractionalPrimes.PolynomialKernelDilationProperties
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open MeasureTheory
open scoped BigOperators FourierTransform

/-- The fixed real smoothing kernel, embedded in the complex Schwartz space. -/
noncomputable def polynomialKernelRhoComplexSchwartz : SchwartzMap ℝ ℂ :=
  FractionalPrimes.polynomialKernelRhoSchwartz.postcompCLM Complex.ofRealCLM

@[simp]
theorem polynomialKernelRhoComplexSchwartz_apply (x : ℝ) :
    polynomialKernelRhoComplexSchwartz x =
      (FractionalPrimes.polynomialKernelRho x : ℂ) := rfl

/-- The blueprint angular transform is Mathlib's Fourier transform after the
explicit frequency rescaling `t ↦ t/(2π)`. -/
theorem polynomialKernelRhoAngularFourier_eq_fourier (t : ℝ) :
    FractionalPrimes.polynomialKernelRhoAngularFourier t =
      𝓕 polynomialKernelRhoComplexSchwartz (t / (2 * Real.pi)) := by
  unfold FractionalPrimes.polynomialKernelRhoAngularFourier
    FractionalPrimes.polynomialAngularFourier
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [smul_eq_mul, polynomialKernelRhoComplexSchwartz_apply]
  have hexp :
      Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ)) =
        Complex.exp (↑(-2 * Real.pi * u * (t / (2 * Real.pi))) * Complex.I) := by
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hexp]
  ring

/-- Fourier inversion for the fixed kernel in the blueprint's angular
normalization. -/
theorem polynomialKernelRhoAngularFourier_inverse (x : ℝ) :
    (FractionalPrimes.polynomialKernelRho x : ℂ) =
      ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ t : ℝ, FractionalPrimes.polynomialKernelRhoAngularFourier t *
          Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
  have hinv : 𝓕⁻ (𝓕 polynomialKernelRhoComplexSchwartz) =
      polynomialKernelRhoComplexSchwartz := by simp
  have hpoint := congrArg (fun f : SchwartzMap ℝ ℂ => f x) hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at hpoint
  simp only [smul_eq_mul] at hpoint
  have hfreq (ξ : ℝ) :
      𝓕 polynomialKernelRhoComplexSchwartz ξ =
        FractionalPrimes.polynomialKernelRhoAngularFourier (2 * Real.pi * ξ) := by
    rw [polynomialKernelRhoAngularFourier_eq_fourier]
    have hscale : (2 * Real.pi * ξ) / (2 * Real.pi) = ξ := by
      field_simp [Real.pi_ne_zero]
    rw [hscale]
  let g : ℝ → ℂ := fun t =>
    FractionalPrimes.polynomialKernelRhoAngularFourier t *
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
  have hchange : (∫ ξ : ℝ, g ((2 * Real.pi) * ξ)) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, g t := by
    rw [Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
  have hpoint' : (FractionalPrimes.polynomialKernelRho x : ℂ) =
      ∫ ξ : ℝ, g ((2 * Real.pi) * ξ) := by
    have hpoint2 : (FractionalPrimes.polynomialKernelRho x : ℂ) =
        ∫ ξ : ℝ, FractionalPrimes.polynomialKernelRhoAngularFourier
            ((2 * Real.pi) * ξ) *
          Complex.exp (Complex.I * (((2 * Real.pi) * ξ : ℝ) : ℂ) * (x : ℂ)) := by
      calc
        (FractionalPrimes.polynomialKernelRho x : ℂ) =
            ∫ ξ : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) *
              (𝓕 polynomialKernelRhoComplexSchwartz) ξ := by
          simpa using hpoint.symm
        _ = ∫ ξ : ℝ, FractionalPrimes.polynomialKernelRhoAngularFourier
              ((2 * Real.pi) * ξ) *
            Complex.exp (Complex.I * (((2 * Real.pi) * ξ : ℝ) : ℂ) * (x : ℂ)) := by
          apply integral_congr_ae
          filter_upwards with ξ
          rw [hfreq ξ]
          have harg :
              ↑(2 * Real.pi * inner ℝ ξ x) * Complex.I =
                Complex.I * ↑(2 * Real.pi * ξ) * (x : ℂ) := by
            simp
            ring
          rw [harg]
          ring
    simpa [g] using hpoint2
  rw [hpoint', hchange]

/-- Inversion for the fixed dilated kernel, with its exact compact frequency
support made explicit. -/
theorem polynomialKernelRhoT_angularFourier_inverse
    (T x : ℝ) (hT : 0 < T) :
    (FractionalPrimes.polynomialKernelRhoT T x : ℂ) =
      ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ t in Set.Icc (-T) T,
          FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
            Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
  let g : ℝ → ℂ := fun t =>
    FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
  have hchange : (∫ s : ℝ, g (T * s)) =
      (T⁻¹ : ℝ) • ∫ t : ℝ, g t := by
    rw [Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.mpr hT)]
  have hchange' :
      (∫ s : ℝ, FractionalPrimes.polynomialKernelRhoAngularFourier s *
        Complex.exp (Complex.I * (s : ℂ) * ((T * x : ℝ) : ℂ))) =
        (T⁻¹ : ℝ) • ∫ t : ℝ, g t := by
    calc
      _ = ∫ s : ℝ, g (T * s) := by
        apply integral_congr_ae
        filter_upwards with s
        have hdiv : (T * s) / T = s := by field_simp [hT.ne']
        simp [g, hdiv, mul_left_comm, mul_comm]
      _ = _ := hchange
  have hwhole := polynomialKernelRhoAngularFourier_inverse (T * x)
  have hcast :
      (↑(FractionalPrimes.polynomialKernelRhoT T x) : ℂ) =
        (T : ℂ) * (↑(FractionalPrimes.polynomialKernelRho (T * x)) : ℂ) := by
    simp [FractionalPrimes.polynomialKernelRhoT]
  have hcancel : (T : ℂ) * (T⁻¹ : ℂ) = 1 := by
    exact_mod_cast (mul_inv_cancel₀ hT.ne' : T * T⁻¹ = 1)
  have hscaled : (↑(FractionalPrimes.polynomialKernelRhoT T x) : ℂ) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, g t := by
    rw [hcast, hwhole, hchange']
    simp only [Complex.real_smul, Complex.ofReal_inv]
    calc
      (T : ℂ) * ((↑(2 * Real.pi) : ℂ)⁻¹ *
          ((T⁻¹ : ℂ) * ∫ t : ℝ, g t)) =
        (↑(2 * Real.pi) : ℂ)⁻¹ * ((T : ℂ) * (T⁻¹ : ℂ)) *
          ∫ t : ℝ, g t := by ring
      _ = (↑(2 * Real.pi) : ℂ)⁻¹ * ∫ t : ℝ, g t := by
        rw [hcancel]
        ring
  have hsupport : Function.support g ⊆ Set.Icc (-T) T := by
    intro t ht
    by_contra hnot
    have hgt : g t ≠ 0 := by
      simpa [Function.mem_support] using ht
    have hF : FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) ≠ 0 := by
      intro hz
      simp [g, hz] at hgt
    have hFmem :
        t / T ∈ Function.support FractionalPrimes.polynomialKernelRhoAngularFourier := by
      simpa [Function.mem_support] using hF
    have hFbounds :=
      FractionalPrimes.polynomialKernelRhoAngularFourier_support_subset_Icc hFmem
    have htin : t ∈ Set.Icc (-T) T := by
      constructor
      · have hlow := (le_div_iff₀ hT).1 hFbounds.1
        nlinarith
      · have hupp := (div_le_iff₀ hT).1 hFbounds.2
        nlinarith
    exact hnot htin
  have htruncate :
      (∫ t : ℝ, g t) = ∫ t in Set.Icc (-T) T, g t := by
    calc
      (∫ t : ℝ, g t) =
          ∫ t : ℝ, (Set.Icc (-T) T).indicator g t := by
        apply integral_congr_ae
        filter_upwards with t
        by_cases ht : t ∈ Set.Icc (-T) T
        · simp [ht]
        · have hzero : g t = 0 := by
            by_contra hne
            have hmem : t ∈ Function.support g := by
              simpa [Function.mem_support] using hne
            exact ht (hsupport hmem)
          simp [ht, hzero]
      _ = _ := integral_indicator measurableSet_Icc
  rw [hscaled, htruncate]

/-- The logarithmic window's Fourier transform is the exact Mellin kernel
`K_H`, with the real natural logarithm convention. -/
theorem mellinSharpLogWindowFourier (X H t : ℝ)
    (hX : 0 < X) (hH : 0 < H) :
    (∫ u : ℝ,
      (Real.exp (u / 2) / H *
        if Real.log X < u ∧ u ≤ Real.log (X + H) then (1 : ℝ) else 0 : ℝ) *
        Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))) =
      (mellinHalfItPower (X + H) t - mellinHalfItPower X t) /
        ((H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  let a := Real.log X
  let b := Real.log (X + H)
  let c : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hXH : 0 < X + H := by linarith
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Real.log_le_log hX (by linarith)
  have hc : c ≠ 0 := mellinWindowDenominator_ne_zero t
  let f : ℝ → ℂ := fun u =>
    ((H : ℂ)⁻¹) * Complex.exp (c * (u : ℂ))
  have hwindow :
      (fun u : ℝ =>
        (Real.exp (u / 2) / H *
          if Real.log X < u ∧ u ≤ Real.log (X + H) then (1 : ℝ) else 0 : ℝ) *
          Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))) =
        (Set.Ioc a b).indicator f := by
    funext u
    by_cases hu : a < u ∧ u ≤ b
    · have hu' : u ∈ Set.Ioc a b := hu
      simp only [Set.indicator_of_mem hu']
      have husrc : Real.log X < u ∧ u ≤ Real.log (X + H) := by
        simpa [a, b] using hu
      rw [if_pos husrc]
      simp only [mul_one]
      dsimp [a, b, f, c]
      have hreal : (↑(Real.exp (u / 2) / H) : ℂ) =
          (H : ℂ)⁻¹ * Complex.exp (↑(u / 2) : ℂ) := by
        rw [Complex.ofReal_div, Complex.ofReal_exp]
        simp [div_eq_mul_inv, mul_comm]
      calc
        _ = (H : ℂ)⁻¹ *
            (Complex.exp (↑(u / 2) : ℂ) *
              Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))) := by
          rw [hreal]
          ring
        _ = (H : ℂ)⁻¹ *
            Complex.exp (↑(u / 2) + Complex.I * (t : ℂ) * (u : ℂ)) := by
          rw [← Complex.exp_add]
        _ = (H : ℂ)⁻¹ *
            Complex.exp (((1 / 2 : ℝ) : ℂ) * (u : ℂ) +
              (t : ℂ) * Complex.I * (u : ℂ)) := by
          congr 2
          push_cast
          ring
        _ = (H : ℂ)⁻¹ *
            Complex.exp ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              (u : ℂ)) := by congr 2 <;> ring
    · have hu' : u ∉ Set.Ioc a b := by simpa [Set.mem_Ioc] using hu
      have husrc : ¬(Real.log X < u ∧ u ≤ Real.log (X + H)) := by
        simpa [a, b] using hu
      simp [Set.indicator, hu', husrc]
  calc
    _ = ∫ u : ℝ, (Set.Ioc a b).indicator f u := by rw [hwindow]
    _ = ∫ u in Set.Ioc a b, f u := integral_indicator measurableSet_Ioc
    _ = ∫ u in a..b, f u := by
      symm
      exact intervalIntegral.integral_of_le hab
    _ = (H : ℂ)⁻¹ * ∫ u in a..b, Complex.exp (c * (u : ℂ)) := by
      dsimp [f]
      rw [intervalIntegral.integral_const_mul]
    _ = (H : ℂ)⁻¹ *
        ((Complex.exp (c * b) - Complex.exp (c * a)) / c) := by
      rw [integral_exp_mul_complex hc]
    _ = _ := by
      dsimp [a, b, c, mellinHalfItPower]
      push_cast
      field_simp [ne_of_gt hH, mellinWindowDenominator_ne_zero t]

/-- The sharp logarithmic window is integrable, with its exact half-open
support retained. -/
theorem mellinSharpLogWindow_integrable (X H : ℝ)
    (hX : 0 < X) (hH : 0 < H) :
    Integrable (fun u : ℝ => Real.exp (u / 2) / H *
      if Real.log X < u ∧ u ≤ Real.log (X + H) then (1 : ℝ) else 0) := by
  let a := Real.log X
  let b := Real.log (X + H)
  let f : ℝ → ℝ := fun u => Real.exp (u / 2) / H
  have hb : a ≤ b := by
    dsimp [a, b]
    exact Real.log_le_log hX (by linarith)
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hficc : IntegrableOn f (Set.Icc a b) :=
    hfcont.continuousOn.integrableOn_compact isCompact_Icc
  have hfIoc : IntegrableOn f (Set.Ioc a b) :=
    hficc.mono_set Set.Ioc_subset_Icc_self
  have hrepr :
      (fun u : ℝ => Real.exp (u / 2) / H *
        if Real.log X < u ∧ u ≤ Real.log (X + H) then (1 : ℝ) else 0) =
      (Set.Ioc a b).indicator f := by
    funext u
    by_cases hu : u ∈ Set.Ioc a b
    · have hu' : Real.log X < u ∧ u ≤ Real.log (X + H) := by
        simpa [a, b, Set.mem_Ioc] using hu
      simp [Set.indicator, hu, hu', f]
    · have hu' : ¬(Real.log X < u ∧ u ≤ Real.log (X + H)) := by
        simpa [a, b, Set.mem_Ioc] using hu
      simp [Set.indicator, hu, hu', f]
  rw [hrepr]
  exact hfIoc.integrable_indicator measurableSet_Ioc

/-- Exact substitution in one real Mellin-window convolution term. -/
theorem mellinWindowConvolution_shiftedIntegral
    (X H T : ℝ) (n : ℕ) (hX : 0 < X) (hH : 0 < H)
    (hn : 0 < n) :
    mellinRealHalfPower n *
        mellinRealConvolution
          (fun u => Real.exp (u / 2) / H *
            if Real.log X < u ∧ u ≤ Real.log (X + H) then (1 : ℝ) else 0)
          (FractionalPrimes.polynomialKernelRhoT T) (Real.log (n : ℝ)) =
      H⁻¹ * ∫ v : ℝ,
        FractionalPrimes.polynomialKernelRhoT T v *
          (Real.exp (-v / 2) *
            mellinIntervalIndicator (X * Real.exp v) ((X + H) * Real.exp v) n) := by
  let x := Real.log (n : ℝ)
  let h : ℝ → ℝ := fun u => Real.exp (u / 2) / H *
    if Real.log X < u ∧ u ≤ Real.log (X + H) then 1 else 0
  let g : ℝ → ℝ := fun v => FractionalPrimes.polynomialKernelRhoT T v * h (x - v)
  have hchange : (∫ u : ℝ, h u *
        FractionalPrimes.polynomialKernelRhoT T (x - u)) = ∫ v : ℝ, g v := by
    calc
      (∫ u : ℝ, h u * FractionalPrimes.polynomialKernelRhoT T (x - u)) =
          ∫ u : ℝ, g (x - u) := by
        apply integral_congr_ae
        filter_upwards with u
        dsimp [g]
        ring
      _ = ∫ v : ℝ, g v := by
        exact (volume.measurePreserving_sub_left x).integral_comp
          (Homeomorph.subLeft x).measurableEmbedding g
  have hwindow : ∀ v : ℝ,
      (Real.log X < x - v ∧ x - v ≤ Real.log (X + H)) ↔
        (X * Real.exp v < (n : ℝ) ∧ (n : ℝ) ≤ (X + H) * Real.exp v) := by
    intro v
    constructor
    · rintro ⟨hl, hu⟩
      constructor
      · have hlog : Real.log X + v < x := by dsimp [x] at hl ⊢; linarith
        have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
        have hexp := Real.exp_lt_exp.mpr hlog
        simpa [x, Real.exp_add, Real.exp_log hX, Real.exp_log hnr] using hexp
      · have hlog : x ≤ Real.log (X + H) + v := by dsimp [x] at hu ⊢; linarith
        have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
        have hXH : 0 < X + H := by linarith
        have hexp := Real.exp_le_exp.mpr hlog
        simpa [x, Real.exp_add, Real.exp_log hXH, Real.exp_log hnr] using hexp
    · rintro ⟨hl, hu⟩
      constructor
      · have hexp : Real.exp (Real.log X + v) < Real.exp x := by
          simpa [x, Real.exp_add, Real.exp_log hX,
            Real.exp_log (show 0 < (n : ℝ) by exact_mod_cast hn)] using hl
        have hlog := Real.exp_lt_exp.mp hexp
        dsimp [x]
        linarith
      · have hexp : Real.exp x ≤ Real.exp (Real.log (X + H) + v) := by
          simpa [x, Real.exp_add,
            Real.exp_log (show 0 < X + H by linarith),
            Real.exp_log (show 0 < (n : ℝ) by exact_mod_cast hn)] using hu
        have hlog := Real.exp_le_exp.mp hexp
        dsimp [x]
        linarith
  have hpoint (v : ℝ) :
      mellinRealHalfPower n * h (x - v) =
        H⁻¹ * (Real.exp (-v / 2) *
          mellinIntervalIndicator (X * Real.exp v) ((X + H) * Real.exp v) n) := by
    have hexp : Real.exp (-Real.log (n : ℝ) / 2) *
        Real.exp ((x - v) / 2) = Real.exp (-v / 2) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [x]
      ring
    have hwin := hwindow v
    by_cases hv : X * Real.exp v < (n : ℝ) ∧
        (n : ℝ) ≤ (X + H) * Real.exp v
    · have hsource : Real.log X < x - v ∧
          x - v ≤ Real.log (X + H) := hwin.mpr hv
      dsimp [h, mellinRealHalfPower]
      rw [mellinIntervalIndicator]
      simp only [if_pos hsource, if_pos hv, mul_one]
      calc
        _ = Real.exp (-Real.log (n : ℝ) / 2) *
            Real.exp ((x - v) / 2) / H := by ring
        _ = Real.exp (-v / 2) / H := by rw [hexp]
        _ = H⁻¹ * Real.exp (-v / 2) := by
          rw [div_eq_mul_inv]
          ring
    · have hsource : ¬(Real.log X < x - v ∧
          x - v ≤ Real.log (X + H)) := by
        intro hs
        exact hv (hwin.mp hs)
      dsimp [h, mellinRealHalfPower]
      rw [mellinIntervalIndicator]
      simp only [if_neg hsource, if_neg hv, mul_zero, zero_mul]
  calc
    _ = mellinRealHalfPower n * ∫ u : ℝ, h u *
          FractionalPrimes.polynomialKernelRhoT T (x - u) := by
      rfl
    _ = mellinRealHalfPower n * ∫ v : ℝ, g v := by rw [hchange]
    _ = ∫ v : ℝ, mellinRealHalfPower n * g v := by
      rw [integral_const_mul]
    _ = ∫ v : ℝ, FractionalPrimes.polynomialKernelRhoT T v *
          (mellinRealHalfPower n * h (x - v)) := by
      apply integral_congr_ae
      filter_upwards with v
      dsimp [g]
      ring
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      rw [hpoint]
      ring

/-- The dilated smoothing density has mass one. -/
theorem polynomialKernelRhoT_integral (T : ℝ) (hT : 0 < T) :
    ∫ u : ℝ, FractionalPrimes.polynomialKernelRhoT T u = 1 := by
  have hchange :
      (∫ u : ℝ, FractionalPrimes.polynomialKernelRho (T * u)) =
        T⁻¹ • ∫ u : ℝ, FractionalPrimes.polynomialKernelRho u := by
    rw [Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.mpr hT)]
  calc
    (∫ u : ℝ, FractionalPrimes.polynomialKernelRhoT T u) =
        T * ∫ u : ℝ, FractionalPrimes.polynomialKernelRho (T * u) := by
      change (∫ u : ℝ, T * FractionalPrimes.polynomialKernelRho (T * u)) = _
      rw [integral_const_mul]
    _ = T * (T⁻¹ * 1) := by
      rw [hchange, smul_eq_mul, FractionalPrimes.polynomialKernelRho_integral]
    _ = 1 := by field_simp [ne_of_gt hT]

/-- The exact dilated density remains integrable. -/
theorem polynomialKernelRhoT_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (FractionalPrimes.polynomialKernelRhoT T) := by
  have hscaled : Integrable (fun u : ℝ => FractionalPrimes.polynomialKernelRho (T * u)) := by
    simpa only [FractionalPrimes.polynomialKernelRho] using
      (FractionalPrimes.polynomialKernelRhoSchwartz.integrable.comp_mul_left' hT.ne')
  have hmul := hscaled.const_mul T
  change Integrable (fun u : ℝ => T * FractionalPrimes.polynomialKernelRho (T * u))
  exact hmul

/-- The first absolute moment of the dilated density is integrable. -/
theorem polynomialKernelRhoT_moment_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (fun u : ℝ => |u| * FractionalPrimes.polynomialKernelRhoT T u) := by
  have hscaled : Integrable (fun u : ℝ =>
      |T * u| * FractionalPrimes.polynomialKernelRho (T * u)) := by
    simpa only [FractionalPrimes.polynomialKernelRho] using
      (FractionalPrimes.polynomialKernelM1_integrable.comp_mul_left' hT.ne')
  have hpoint (u : ℝ) :
      |u| * FractionalPrimes.polynomialKernelRhoT T u =
        |T * u| * FractionalPrimes.polynomialKernelRho (T * u) := by
    rw [FractionalPrimes.polynomialKernelRhoT, abs_mul, abs_of_pos hT]
    ring
  exact hscaled.congr (ae_of_all _ fun u => (hpoint u).symm)

/-- Fourier inversion and finite Fubini for one logarithmic convolution
term. The negative phase is kept explicit so the Dirichlet monomial has the
source's `n^(-1/2-it)` convention. -/
theorem mellinRealConvolution_fourier
    (X H T : ℝ) (n : ℕ) (hX : 0 < X) (hH : 0 < H)
    (hT : 0 < T) (hn : 0 < n) :
    (mellinRealConvolution
      (fun u => Real.exp (u / 2) / H *
        if Real.log X < u ∧ u ≤ Real.log (X + H) then (1 : ℝ) else 0)
      (FractionalPrimes.polynomialKernelRhoT T) (Real.log (n : ℝ)) : ℂ) =
      ((2 * Real.pi)⁻¹ : ℂ) *
        ∫ t in Set.Icc (-T) T,
          FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
            Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) *
            ((mellinHalfItPower (X + H) t - mellinHalfItPower X t) /
              ((H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
  let h : ℝ → ℝ := fun u => Real.exp (u / 2) / H *
    if Real.log X < u ∧ u ≤ Real.log (X + H) then 1 else 0
  let q : ℝ → ℂ := (Set.Icc (-T) T).indicator
    (fun t => FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
      Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)))
  let phase : ℝ → ℝ → ℂ := fun u t =>
    Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))
  have hh : Integrable h := mellinSharpLogWindow_integrable X H hX hH
  have hhc : Integrable (fun u : ℝ => (h u : ℂ)) := hh.ofReal
  have hFourierEval : Continuous (fun t : ℝ =>
      𝓕 polynomialKernelRhoComplexSchwartz (t / (2 * Real.pi))) := by
    fun_prop
  have hFcont :
      Continuous FractionalPrimes.polynomialKernelRhoAngularFourier := by
    apply hFourierEval.congr
    intro t
    exact (polynomialKernelRhoAngularFourier_eq_fourier t).symm
  have hqbase : Continuous (fun t : ℝ =>
      FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))) := by
    fun_prop
  have hq : Integrable q := by
    have hqon : IntegrableOn (fun t : ℝ =>
        FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
          Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)))
        (Set.Icc (-T) T) :=
      hqbase.continuousOn.integrableOn_compact isCompact_Icc
    exact hqon.integrable_indicator measurableSet_Icc
  have hphase : AEStronglyMeasurable (fun z : ℝ × ℝ => phase z.1 z.2)
      (volume.prod volume) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hphaseBound : ∀ᵐ z : ℝ × ℝ ∂(volume.prod volume),
      ‖phase z.1 z.2‖ ≤ 1 := by
    filter_upwards with z
    have hnorm : ‖phase z.1 z.2‖ = 1 := by
      dsimp [phase]
      rw [show Complex.I * (↑z.2 : ℂ) * (↑z.1 : ℂ) =
          ((z.2 * z.1 : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [hnorm]
  have hprod : Integrable
      (fun z : ℝ × ℝ => (h z.1 : ℂ) * q z.2) (volume.prod volume) :=
    hhc.mul_prod hq
  have hfubini : Integrable
      (fun z : ℝ × ℝ => (h z.1 : ℂ) * q z.2 * phase z.1 z.2)
      (volume.prod volume) := by
    have hmul := hprod.mul_bdd hphase hphaseBound
    simpa [mul_assoc] using hmul
  have hswap :
      (∫ u : ℝ, (h u : ℂ) * ∫ t : ℝ, q t * phase u t) =
        ∫ t : ℝ, q t * ∫ u : ℝ, (h u : ℂ) * phase u t := by
    calc
      _ = ∫ u : ℝ, ∫ t : ℝ, (h u : ℂ) * q t * phase u t := by
        apply integral_congr_ae
        filter_upwards with u
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        ring
      _ = ∫ t : ℝ, ∫ u : ℝ, (h u : ℂ) * q t * phase u t :=
        integral_integral_swap hfubini
      _ = ∫ t : ℝ, q t * ∫ u : ℝ, (h u : ℂ) * phase u t := by
        apply integral_congr_ae
        filter_upwards with t
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with u
        ring
  have hcut (u : ℝ) :
      (∫ t : ℝ, q t * phase u t) =
        ∫ t in Set.Icc (-T) T,
          FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
            Complex.exp (Complex.I * (t : ℂ) * ((u - Real.log (n : ℝ)) : ℂ)) := by
    have hrepr : (fun t : ℝ => q t * phase u t) =
        (Set.Icc (-T) T).indicator (fun t =>
          FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
            Complex.exp (Complex.I * (t : ℂ) *
              ((u - Real.log (n : ℝ)) : ℂ))) := by
      funext t
      by_cases ht : t ∈ Set.Icc (-T) T
      · simp only [q, phase, Set.indicator_of_mem ht]
        calc
          _ = FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
              (Complex.exp (-Complex.I * (t : ℂ) *
                (Real.log (n : ℝ) : ℂ)) *
                Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))) := by ring
          _ = FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
              Complex.exp ((-Complex.I * (t : ℂ) *
                (Real.log (n : ℝ) : ℂ)) +
                (Complex.I * (t : ℂ) * (u : ℂ))) := by rw [← Complex.exp_add]
          _ = _ := by congr 2 <;> push_cast <;> ring
      · simp [q, phase, Set.indicator, ht]
    rw [hrepr, integral_indicator measurableSet_Icc]
  have hinv (u : ℝ) :
      (FractionalPrimes.polynomialKernelRhoT T
        (Real.log (n : ℝ) - u) : ℂ) =
        ((2 * Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, q t * phase u t := by
    have heven : FractionalPrimes.polynomialKernelRhoT T
        (Real.log (n : ℝ) - u) =
        FractionalPrimes.polynomialKernelRhoT T
          (u - Real.log (n : ℝ)) := by
      change T * FractionalPrimes.polynomialKernelRho
          (T * (Real.log (n : ℝ) - u)) =
        T * FractionalPrimes.polynomialKernelRho (T * (u - Real.log (n : ℝ)))
      rw [show Real.log (n : ℝ) - u = -(u - Real.log (n : ℝ)) by ring,
        show T * -(u - Real.log (n : ℝ)) =
          -(T * (u - Real.log (n : ℝ))) by ring,
        FractionalPrimes.polynomialKernelRho_even]
    rw [heven]
    rw [FractionalPrimes.Literature.Polynomial.polynomialKernelRhoT_angularFourier_inverse
      T (u - Real.log (n : ℝ)) hT]
    apply congrArg (fun z : ℂ => ((2 * Real.pi)⁻¹ : ℝ) • z)
    simpa only [Complex.ofReal_sub] using (hcut u).symm
  have hconvCast :
      (mellinRealConvolution h
        (FractionalPrimes.polynomialKernelRhoT T) (Real.log (n : ℝ)) : ℂ) =
        ∫ u : ℝ, (h u : ℂ) *
          (FractionalPrimes.polynomialKernelRhoT T
            (Real.log (n : ℝ) - u) : ℂ) := by
    rw [mellinRealConvolution, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with u
    push_cast
    ring
  have hwindowFourier (t : ℝ) :
      (∫ u : ℝ, (h u : ℂ) * phase u t) =
        (mellinHalfItPower (X + H) t - mellinHalfItPower X t) /
          ((H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa [h, phase] using mellinSharpLogWindowFourier X H t hX hH
  calc
    _ = ∫ u : ℝ, (h u : ℂ) *
        (FractionalPrimes.polynomialKernelRhoT T
          (Real.log (n : ℝ) - u) : ℂ) := hconvCast
    _ = ∫ u : ℝ, (h u : ℂ) *
          (((2 * Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, q t * phase u t) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [hinv]
    _ = ((2 * Real.pi)⁻¹ : ℝ) •
          ∫ u : ℝ, (h u : ℂ) * ∫ t : ℝ, q t * phase u t := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with u
      rw [Complex.real_smul, Complex.real_smul]
      ring
    _ = ((2 * Real.pi)⁻¹ : ℝ) •
          ∫ t : ℝ, q t * ∫ u : ℝ, (h u : ℂ) * phase u t := by
      rw [hswap]
    _ = ((2 * Real.pi)⁻¹ : ℝ) •
          ∫ t in Set.Icc (-T) T,
            FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
              Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) *
              ((mellinHalfItPower (X + H) t - mellinHalfItPower X t) /
                ((H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
      have hout : ∫ t : ℝ, q t * ∫ u : ℝ, (h u : ℂ) * phase u t =
          ∫ t in Set.Icc (-T) T,
            FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
              Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) *
              ((mellinHalfItPower (X + H) t - mellinHalfItPower X t) /
                ((H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
        calc
          _ = ∫ t : ℝ, (Set.Icc (-T) T).indicator (fun t =>
                FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
                  Complex.exp (-Complex.I * (t : ℂ) *
                    (Real.log (n : ℝ) : ℂ)) *
                  ((mellinHalfItPower (X + H) t - mellinHalfItPower X t) /
                    ((H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))) t := by
            apply integral_congr_ae
            filter_upwards with t
            by_cases ht : t ∈ Set.Icc (-T) T
            · simp only [q, Set.indicator_of_mem ht, hwindowFourier]
            · simp [q, Set.indicator, ht]
          _ = _ := integral_indicator measurableSet_Icc
      rw [hout]
    _ = ((2 * Real.pi)⁻¹ : ℂ) *
          ∫ t in Set.Icc (-T) T,
            FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
              Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) *
              ((mellinHalfItPower (X + H) t - mellinHalfItPower X t) /
                ((H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
      simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul]
      apply congrArg₂ (· * ·)
      · apply congrArg Inv.inv
        norm_num
      · rfl

/-- The finite Dirichlet-polynomial identity for the fixed normalized
logarithmic kernel. The endpoint estimate is added below in the public
two-part source theorem. -/
theorem smoothedMellinIdentity_formula
    (X H B T : ℝ) (a : ℕ → ℂ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X) (hB : 0 ≤ B)
    (hsupport : ∀ n, 0 < n → a n ≠ 0 →
      X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X)
    (hbound : ∀ n, 0 < n → ‖a n‖ ≤ B) (hT : 0 < T) :
    let w := mellinWindowData FractionalPrimes.polynomialKernelRho
      X H B a hX hH hHX hB hsupport hbound
    w.S_H_T T = ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ t in Set.Icc (-T) T,
        w.A_X t * w.K_H t *
          FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) := by
  classical
  let w := mellinWindowData FractionalPrimes.polynomialKernelRho
    X H B a hX hH hHX hB hsupport hbound
  let S := mellinWindowSupportIndices X
  let h : ℝ → ℝ := fun u => Real.exp (u / 2) / H *
    if Real.log X < u ∧ u ≤ Real.log (X + H) then 1 else 0
  let K : ℝ → ℂ := fun t =>
    (mellinHalfItPower (X + H) t - mellinHalfItPower X t) /
      ((H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
  let f : ℕ → ℝ → ℂ := fun n t =>
    (a n * mellinDirichletMonomial n t) * K t *
      FractionalPrimes.polynomialKernelRhoAngularFourier (t / T)
  have hFcont :
      Continuous FractionalPrimes.polynomialKernelRhoAngularFourier := by
    have hFourierEval : Continuous (fun t : ℝ =>
        𝓕 polynomialKernelRhoComplexSchwartz (t / (2 * Real.pi))) := by
      fun_prop
    apply hFourierEval.congr
    intro t
    exact (polynomialKernelRhoAngularFourier_eq_fourier t).symm
  have hKnum : Continuous (fun t : ℝ =>
      mellinHalfItPower (X + H) t - mellinHalfItPower X t) := by
    unfold mellinHalfItPower
    fun_prop
  have hKden : Continuous (fun t : ℝ =>
      (H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    fun_prop
  have hKden_ne (t : ℝ) :
      (H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast hH.ne'
    · exact mellinWindowDenominator_ne_zero t
  have hKcont : Continuous K := by
    dsimp [K]
    exact hKnum.div₀ hKden hKden_ne
  have hSpos (n : ℕ) (hn : n ∈ S) : 0 < n := by
    have hmem := (mellinIntervalIndices_mem_iff (by positivity) n).1 hn
    have hpos : 0 < (n : ℝ) := lt_trans (by linarith [hX]) hmem.1
    exact_mod_cast hpos
  have hmonomial (n : ℕ) (hn : 0 < n) (t : ℝ) :
      (mellinRealHalfPower n : ℂ) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) =
      mellinDirichletMonomial n t := by
    unfold mellinRealHalfPower mellinDirichletMonomial
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hDircont (n : ℕ) : Continuous (mellinDirichletMonomial n) := by
    unfold mellinDirichletMonomial
    fun_prop
  have hScalecont : Continuous (fun t : ℝ =>
      FractionalPrimes.polynomialKernelRhoAngularFourier (t / T)) := by
    exact hFcont.comp (by fun_prop)
  have hfcont (n : ℕ) : Continuous (f n) := by
    dsimp [f]
    have hc : Continuous (fun t : ℝ =>
        (a n) * (mellinDirichletMonomial n t *
          (K t * FractionalPrimes.polynomialKernelRhoAngularFourier (t / T)))) :=
      continuous_const.mul ((hDircont n).mul (hKcont.mul hScalecont))
    convert hc using 1
    ext t
    ring
  have hfint (n : ℕ) : IntegrableOn (f n) (Set.Icc (-T) T) :=
    (hfcont n).continuousOn.integrableOn_compact isCompact_Icc
  have hterm (n : ℕ) (hn : n ∈ S) :
      a n * (mellinRealHalfPower n : ℂ) *
          (mellinRealConvolution h (FractionalPrimes.polynomialKernelRhoT T)
            (Real.log (n : ℝ)) : ℂ) =
        ((2 * Real.pi)⁻¹ : ℂ) * ∫ t in Set.Icc (-T) T, f n t := by
    have hFour := mellinRealConvolution_fourier X H T n
      (by linarith [hX]) hH hT (hSpos n hn)
    calc
      _ = a n * (mellinRealHalfPower n : ℂ) *
          (((2 * Real.pi)⁻¹ : ℂ) *
            ∫ t in Set.Icc (-T) T,
              FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
                Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) * K t) := by
          rw [hFour]
      _ = ((2 * Real.pi)⁻¹ : ℂ) *
          ((a n * (mellinRealHalfPower n : ℂ)) *
            ∫ t in Set.Icc (-T) T,
              FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
                Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) * K t) := by
          ring
      _ = ((2 * Real.pi)⁻¹ : ℂ) *
          ∫ t in Set.Icc (-T) T,
            (a n * (mellinRealHalfPower n : ℂ)) *
              (FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) *
                Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) * K t) := by
          congr 1
          rw [← integral_const_mul]
      _ = ((2 * Real.pi)⁻¹ : ℂ) * ∫ t in Set.Icc (-T) T, f n t := by
          congr 1
          apply integral_congr_ae
          filter_upwards with t
          calc
            _ = (a n * ((mellinRealHalfPower n : ℂ) *
                Complex.exp (-Complex.I * (t : ℂ) *
                  (Real.log (n : ℝ) : ℂ)))) * K t *
                  FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) := by ring
            _ = f n t := by rw [hmonomial n (hSpos n hn) t]
  have hsumTerms :
      (∑ n ∈ S, a n * (mellinRealHalfPower n : ℂ) *
          (mellinRealConvolution h (FractionalPrimes.polynomialKernelRhoT T)
            (Real.log (n : ℝ)) : ℂ)) =
        ((2 * Real.pi)⁻¹ : ℂ) * ∑ n ∈ S, ∫ t in Set.Icc (-T) T, f n t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact hterm n hn
  have hsumIntegral :
      (∑ n ∈ S, ∫ t in Set.Icc (-T) T, f n t) =
        ∫ t in Set.Icc (-T) T, ∑ n ∈ S, f n t := by
    rw [integral_finsetSum]
    intro n hn
    exact hfint n
  change (∑ n ∈ S, a n * (mellinRealHalfPower n : ℂ) *
      (mellinRealConvolution h (FractionalPrimes.polynomialKernelRhoT T)
        (Real.log (n : ℝ)) : ℂ)) = _
  rw [hsumTerms, hsumIntegral]
  rw [Complex.real_smul]
  simp only [Complex.ofReal_inv, Complex.ofReal_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [f, S]
  simp [w, mellinWindowData, mellinRealConvolution, K, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- On the exact source coefficient support, a shifted window contributes at
most two after its exponential normalization. -/
theorem mellinShiftedWindowWeight_le_two
    (w : MellinWindowData) (n : ℕ)
    (hn : n ∈ mellinWindowSupportIndices w.X) (v : ℝ) :
    0 ≤ Real.exp (-v / 2) *
        mellinIntervalIndicator (w.X * Real.exp v)
          ((w.X + w.H) * Real.exp v) n ∧
      Real.exp (-v / 2) *
        mellinIntervalIndicator (w.X * Real.exp v)
          ((w.X + w.H) * Real.exp v) n ≤ 2 := by
  let c : ℝ := Real.exp (-v / 2)
  let A : ℝ := mellinIntervalIndicator (w.X * Real.exp v)
    ((w.X + w.H) * Real.exp v) n
  have hc : 0 < c := by dsimp [c]; exact Real.exp_pos _
  have hA01 : A = 0 ∨ A = 1 := by
    by_cases hwin : w.X * Real.exp v < (n : ℝ) ∧
        (n : ℝ) ≤ (w.X + w.H) * Real.exp v
    · right
      simp [A, mellinIntervalIndicator, hwin]
    · left
      simp [A, mellinIntervalIndicator, hwin]
  have hmem := (mellinIntervalIndices_mem_iff
    (x := w.X / 2) (y := 3 * w.X) (by linarith [w.X_lower]) n).1 hn
  have hnreal : w.X / 2 < (n : ℝ) := hmem.1
  have hXH : w.X + w.H ≤ 2 * w.X := by linarith [w.H_upper]
  constructor
  · rcases hA01 with hA | hA
    · change 0 ≤ c * A
      rw [hA]
      positivity
    · change 0 ≤ c * A
      rw [hA]
      positivity
  · rcases hA01 with hA | hA
    · change c * A ≤ 2
      rw [hA]
      simp
    · change c * A ≤ 2
      rw [hA]
      have hwin : w.X * Real.exp v < (n : ℝ) ∧
          (n : ℝ) ≤ (w.X + w.H) * Real.exp v := by
        by_contra hnot
        have hzero : A = 0 := by simp [A, mellinIntervalIndicator, hnot]
        simp [hzero] at hA
      have hcSq : c ^ 2 = Real.exp (-v) := by
        dsimp [c]
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      have hexpcancel : Real.exp v * Real.exp (-v) = 1 := by
        rw [← Real.exp_add]
        simp
      have hupper : (n : ℝ) * Real.exp (-v) ≤ w.X + w.H := by
        have hmul := mul_le_mul_of_nonneg_right hwin.2
          (le_of_lt (Real.exp_pos (-v)))
        calc
          (n : ℝ) * Real.exp (-v) ≤
              ((w.X + w.H) * Real.exp v) * Real.exp (-v) := hmul
          _ = w.X + w.H := by rw [mul_assoc, hexpcancel, mul_one]
      have hcSqLe : c ^ 2 ≤ (w.X + w.H) / (n : ℝ) := by
        apply (le_div_iff₀ (by linarith [w.X_lower, hnreal])).2
        rw [hcSq]
        nlinarith [hupper]
      have hratio : (w.X + w.H) / (n : ℝ) < 4 := by
        apply (div_lt_iff₀ (by linarith [w.X_lower, hnreal])).2
        nlinarith [hnreal, hXH]
      have hcSqLt : c ^ 2 < 4 := lt_of_le_of_lt hcSqLe hratio
      have hcLe : c ≤ 2 := by nlinarith [sq_nonneg (c - 2)]
      simpa using hcLe
/-- Endpoint error estimate obtained from the exact shifted-window formula,
the already checked sharp-window displacement bound, and the first moment of
the fixed dilated kernel. -/
theorem smoothedMellinIdentity_endpoint
    (X H B T : ℝ) (a : ℕ → ℂ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X) (hB : 0 ≤ B)
    (hsupport : ∀ n, 0 < n → a n ≠ 0 →
      X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X)
    (hbound : ∀ n, 0 < n → ‖a n‖ ≤ B) (hT : 0 < T) :
    let w := mellinWindowData FractionalPrimes.polynomialKernelRho
      X H B a hX hH hHX hB hsupport hbound
    ‖w.N_H - w.S_H_T T‖ ≤
      32 * B * FractionalPrimes.polynomialKernelM1 * X / (H * T) +
        8 * B / H := by
  classical
  let w := mellinWindowData FractionalPrimes.polynomialKernelRho
    X H B a hX hH hHX hB hsupport hbound
  let S := mellinWindowSupportIndices X
  let M := mellinWindowAverageIndices X H
  let c : ℝ → ℝ := fun v => Real.exp (-v / 2)
  let A : ℕ → ℝ → ℝ := fun n v =>
    mellinIntervalIndicator (X * Real.exp v) ((X + H) * Real.exp v) n
  let r : ℕ → ℝ → ℝ := fun n v =>
    FractionalPrimes.polynomialKernelRhoT T v * (c v * A n v)
  let q : ℕ → ℝ → ℂ := fun n v => a n * ((c v * A n v : ℝ) : ℂ)
  let rhoC : ℝ → ℂ := fun v =>
    (FractionalPrimes.polynomialKernelRhoT T v : ℂ)
  let G : ℝ → ℂ := fun v => ∑ n ∈ S, q n v
  let D : ℂ := ∑ n ∈ S,
    a n * (mellinIntervalIndicator X (X + H) n : ℂ)
  let E : ℝ → ℂ := fun v =>
    ∑ n ∈ S, mellinShiftWindowTerm w v n
  let major : ℝ → ℝ := fun v =>
    FractionalPrimes.polynomialKernelRhoT T v *
      (B * (32 * X * |v| + 8))
  change ‖w.N_H - w.S_H_T T‖ ≤
    32 * B * FractionalPrimes.polynomialKernelM1 * X / (H * T) +
      8 * B / H
  have hXpos : 0 < X := by linarith [hX]
  have hρnonneg (v : ℝ) :
      0 ≤ FractionalPrimes.polynomialKernelRhoT T v := by
    rw [FractionalPrimes.polynomialKernelRhoT]
    exact mul_nonneg (le_of_lt hT)
      (FractionalPrimes.polynomialKernelRho_nonneg _)
  have hρint : Integrable (fun v : ℝ =>
      (FractionalPrimes.polynomialKernelRhoT T v : ℂ)) :=
    (polynomialKernelRhoT_integrable T hT).ofReal
  have hweight (n : ℕ) (hn : n ∈ S) (v : ℝ) :
      0 ≤ c v * A n v ∧ c v * A n v ≤ 2 := by
    have h := mellinShiftedWindowWeight_le_two w n hn v
    simpa [w, mellinWindowData, c, A] using h
  have hcoeff (n : ℕ) (hn : n ∈ S) : ‖a n‖ ≤ B := by
    have hmem := (mellinIntervalIndices_mem_iff
      (x := X / 2) (y := 3 * X) (by linarith [hX]) n).1 hn
    have hnreal : 0 < (n : ℝ) := lt_trans (by linarith [hX]) hmem.1
    have hnpos : 0 < n := by exact_mod_cast hnreal
    exact hbound n hnpos
  have hAmeas (n : ℕ) : Measurable (A n) := by
    dsimp [A]
    unfold mellinIntervalIndicator
    have hleft : Measurable (fun v : ℝ => X * Real.exp v) := by fun_prop
    have hright : Measurable (fun v : ℝ => (n : ℝ)) := measurable_const
    have hright' : Measurable (fun v : ℝ => (X + H) * Real.exp v) := by
      fun_prop
    have hset : MeasurableSet {v : ℝ |
        X * Real.exp v < (n : ℝ) ∧
          (n : ℝ) ≤ (X + H) * Real.exp v} :=
      (measurableSet_lt hleft hright).inter
        (measurableSet_le measurable_const hright')
    exact Measurable.ite hset measurable_const measurable_const
  have hcmeas : Measurable c := by
    dsimp [c]
    fun_prop
  have hqmeas (n : ℕ) : Measurable (q n) := by
    dsimp [q]
    exact measurable_const.mul
      (Complex.measurable_ofReal.comp (hcmeas.mul (hAmeas n)))
  have hqbound (n : ℕ) (hn : n ∈ S) :
      ∀ v : ℝ, ‖q n v‖ ≤ 2 * B := by
    intro v
    dsimp [q]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hweight n hn v).1]
    calc
      ‖a n‖ * (c v * A n v) ≤ B * (c v * A n v) :=
        mul_le_mul_of_nonneg_right (hcoeff n hn) (hweight n hn v).1
      _ ≤ B * 2 := mul_le_mul_of_nonneg_left (hweight n hn v).2 hB
      _ = 2 * B := by ring
  have htermInt (n : ℕ) (hn : n ∈ S) :
      Integrable (fun v : ℝ => rhoC v * q n v) :=
    hρint.mul_bdd (hqmeas n).aestronglyMeasurable
      (Filter.Eventually.of_forall (hqbound n hn))
  have hGmeas : Measurable G := by
    dsimp [G]
    exact Finset.measurable_sum S (by
      intro n hn
      exact hqmeas n)
  have hGbound (v : ℝ) :
      ‖G v‖ ≤ (S.card : ℝ) * (2 * B) := by
    dsimp [G]
    calc
      ‖∑ n ∈ S, q n v‖ ≤ ∑ n ∈ S, ‖q n v‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S, (2 * B) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hqbound n hn v
      _ = (S.card : ℝ) * (2 * B) := by simp [mul_comm]
  have hGint : Integrable (fun v : ℝ => rhoC v * G v) :=
    hρint.mul_bdd hGmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hGbound)
  have hsumTerm (n : ℕ) (hn : n ∈ S) :
      a n * (mellinRealHalfPower n : ℂ) *
          (mellinRealConvolution
            (fun u => Real.exp (u / 2) / H *
              if Real.log X < u ∧ u ≤ Real.log (X + H) then (1 : ℝ) else 0)
            (FractionalPrimes.polynomialKernelRhoT T)
            (Real.log (n : ℝ)) : ℂ) =
        ((H⁻¹ : ℝ) : ℂ) * ∫ v : ℝ, rhoC v * q n v := by
    have hnreal : 0 < (n : ℝ) := by
      have hm := (mellinIntervalIndices_mem_iff
        (x := X / 2) (y := 3 * X) (by linarith [hX]) n).1 hn
      linarith [hm.1]
    have hnpos : 0 < n := by exact_mod_cast hnreal
    have hbase := mellinWindowConvolution_shiftedIntegral X H T n
      hXpos hH hnpos
    calc
      _ = a n *
          ((mellinRealHalfPower n *
            mellinRealConvolution
              (fun u => Real.exp (u / 2) / H *
                if Real.log X < u ∧ u ≤ Real.log (X + H) then (1 : ℝ) else 0)
              (FractionalPrimes.polynomialKernelRhoT T)
              (Real.log (n : ℝ)) : ℝ) : ℂ) := by
            push_cast
            ring
      _ = a n *
          ((H⁻¹ * ∫ v : ℝ, r n v : ℝ) : ℂ) := by
            rw [hbase]
      _ = a n *
          (((H⁻¹ : ℝ) : ℂ) * ∫ v : ℝ, (r n v : ℂ)) := by
            congr 1
            rw [Complex.ofReal_mul, ← integral_complex_ofReal]
      _ = ((H⁻¹ : ℝ) : ℂ) *
          (a n * ∫ v : ℝ, (r n v : ℂ)) := by ring
      _ = ((H⁻¹ : ℝ) : ℂ) *
          ∫ v : ℝ, a n * (r n v : ℂ) := by
            congr 1
            rw [← integral_const_mul]
      _ = ((H⁻¹ : ℝ) : ℂ) *
          ∫ v : ℝ, rhoC v * q n v := by
            congr 1
            apply integral_congr_ae
            filter_upwards with v
            dsimp [rhoC, q, r, c, A]
            push_cast
            ring
  have hsumIntegral :
      (∑ n ∈ S, ∫ v : ℝ, rhoC v * q n v) =
        ∫ v : ℝ, rhoC v * G v := by
    calc
      _ = ∫ v : ℝ, ∑ n ∈ S, rhoC v * q n v := by
        rw [integral_finsetSum]
        intro n hn
        exact htermInt n hn
      _ = ∫ v : ℝ, rhoC v * G v := by
        congr 1
        funext v
        dsimp [G]
        rw [← Finset.mul_sum]
  have hS : w.S_H_T T =
      ((H⁻¹ : ℝ) : ℂ) * ∫ v : ℝ, rhoC v * G v := by
    change (∑ n ∈ S, a n * (mellinRealHalfPower n : ℂ) *
        (mellinRealConvolution
          (fun u => Real.exp (u / 2) / H *
            if Real.log X < u ∧ u ≤ Real.log (X + H) then (1 : ℝ) else 0)
          (FractionalPrimes.polynomialKernelRhoT T)
          (Real.log (n : ℝ)) : ℂ)) = _
    calc
      _ = ∑ n ∈ S, ((H⁻¹ : ℝ) : ℂ) *
          ∫ v : ℝ, rhoC v * q n v := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hsumTerm n hn
      _ = ((H⁻¹ : ℝ) : ℂ) *
          ∑ n ∈ S, ∫ v : ℝ, rhoC v * q n v := by
            rw [← Finset.mul_sum]
      _ = ((H⁻¹ : ℝ) : ℂ) * ∫ v : ℝ, rhoC v * G v := by
        rw [hsumIntegral]
  have hMsubset : M ⊆ S := by
    intro n hn
    have hm := (mellinIntervalIndices_mem_iff
      (x := X) (y := X + H) (by linarith [hX]) n).1 hn
    apply (mellinIntervalIndices_mem_iff
      (x := X / 2) (y := 3 * X) (by linarith [hX]) n).2
    constructor
    · linarith [hm.1, hX]
    · linarith [hm.2, hHX]
  have hfilter : S.filter (fun n => n ∈ M) = M := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hnM⟩
      exact hnM
    · intro hnM
      exact ⟨hMsubset hnM, hnM⟩
  have hsumD : D = ∑ n ∈ M, a n := by
    dsimp [D]
    calc
      _ = ∑ n ∈ S, if n ∈ M then a n else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hmem := mellinIntervalIndices_mem_iff
          (x := X) (y := X + H) (by linarith [hX]) n
        by_cases hnM : n ∈ M
        · have hcond := hmem.1 hnM
          simp [mellinIntervalIndicator, hnM, hcond]
        · have hcond : ¬(X < (n : ℝ) ∧ (n : ℝ) ≤ X + H) := by
            intro h
            exact hnM (hmem.mpr h)
          simp [mellinIntervalIndicator, hnM, hcond]
      _ = ∑ n ∈ S.filter (fun n => n ∈ M), a n := by
        rw [← Finset.sum_filter]
      _ = ∑ n ∈ M, a n := by rw [hfilter]
  have hN : w.N_H = ((H⁻¹ : ℝ) : ℂ) * D := by
    change ((H⁻¹ : ℝ) : ℂ) * ∑ n ∈ M, a n = _
    rw [← hsumD]
  have hE (v : ℝ) : E v = G v - D := by
    dsimp [E, G, D, q, c, A]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp [w, mellinShiftWindowTerm, mellinWindowData,
      mellinIntervalIndicator, mul_comm]
    ring
  have hDint : Integrable (fun v : ℝ => rhoC v * D) :=
    hρint.mul_const D
  have hFint : Integrable (fun v : ℝ => rhoC v * E v) := by
    have hsub := hGint.sub hDint
    have heq : (fun v : ℝ => rhoC v * E v) =
        fun v => rhoC v * G v - rhoC v * D := by
      funext v
      rw [hE v]
      ring
    exact hsub.congr (Filter.Eventually.of_forall fun v =>
      (congrFun heq v).symm)
  have hmass : ∫ v : ℝ, rhoC v = 1 := by
    calc
      _ = ((∫ v : ℝ, FractionalPrimes.polynomialKernelRhoT T v : ℝ) : ℂ) := by
        dsimp [rhoC]
        rw [integral_complex_ofReal]
      _ = 1 := by
        rw [polynomialKernelRhoT_integral T hT]
        norm_num
  have hDintValue : ∫ v : ℝ, rhoC v * D = D := by
    calc
      _ = ∫ v : ℝ, D * rhoC v := by
        apply integral_congr_ae
        filter_upwards with v
        ring
      _ = D * ∫ v : ℝ, rhoC v := by rw [integral_const_mul]
      _ = D := by rw [hmass]; ring
  have hdiff : w.N_H - w.S_H_T T =
      -(((H⁻¹ : ℝ) : ℂ) * ∫ v : ℝ, rhoC v * E v) := by
    rw [hN, hS]
    calc
      ((H⁻¹ : ℝ) : ℂ) * D -
          ((H⁻¹ : ℝ) : ℂ) * ∫ v : ℝ, rhoC v * G v =
        ((H⁻¹ : ℝ) : ℂ) *
          ((∫ v : ℝ, rhoC v * D) - (∫ v : ℝ, rhoC v * G v)) := by
            calc
              _ = ((H⁻¹ : ℝ) : ℂ) *
                  (D - ∫ v : ℝ, rhoC v * G v) := by ring
              _ = _ := by
                exact congrArg (fun z : ℂ => ((H⁻¹ : ℝ) : ℂ) * z)
                  (congrArg₂ (fun x y : ℂ => x - y)
                    hDintValue.symm (Eq.refl _))
      _ = ((H⁻¹ : ℝ) : ℂ) *
          (∫ v : ℝ, (rhoC v * D - rhoC v * G v)) := by
            apply congrArg (fun z : ℂ => ((H⁻¹ : ℝ) : ℂ) * z)
            simpa only using (integral_sub hDint hGint).symm
      _ = ((H⁻¹ : ℝ) : ℂ) *
          ∫ v : ℝ, rhoC v * (D - G v) := by
            congr 1
            apply integral_congr_ae
            filter_upwards with v
            ring
      _ = ((H⁻¹ : ℝ) : ℂ) *
          ∫ v : ℝ, rhoC v * (-E v) := by
            congr 1
            apply integral_congr_ae
            filter_upwards with v
            rw [hE v]
            ring
      _ = -(((H⁻¹ : ℝ) : ℂ) * ∫ v : ℝ, rhoC v * E v) := by
            have hneg : (fun v : ℝ => rhoC v * (-E v)) =
                fun v => -(rhoC v * E v) := by
              funext v
              ring
            rw [hneg, integral_neg]
            ring
  have hmajorEq : major = fun v : ℝ => B *
      (32 * X * (|v| * FractionalPrimes.polynomialKernelRhoT T v) +
        8 * FractionalPrimes.polynomialKernelRhoT T v) := by
    funext v
    dsimp [major]
    ring
  have hmajorInt : Integrable major := by
    have hm1 := polynomialKernelRhoT_moment_integrable T hT
    have hmassInt := polynomialKernelRhoT_integrable T hT
    have hfirst : Integrable (fun v : ℝ =>
        (32 * X) * (|v| * FractionalPrimes.polynomialKernelRhoT T v)) := by
      convert hm1.const_mul (32 * X) using 1 <;> ext v <;> ring
    have hsecond : Integrable (fun v : ℝ =>
        8 * FractionalPrimes.polynomialKernelRhoT T v) := by
      convert hmassInt.const_mul 8 using 1 <;> ext v <;> ring
    rw [hmajorEq]
    exact (hfirst.add hsecond).const_mul B
  have hfirstInt : Integrable (fun v : ℝ =>
      (32 * X) * (|v| * FractionalPrimes.polynomialKernelRhoT T v)) := by
    convert (polynomialKernelRhoT_moment_integrable T hT).const_mul
      (32 * X) using 1 <;> ext v <;> ring
  have hsecondInt : Integrable (fun v : ℝ =>
      8 * FractionalPrimes.polynomialKernelRhoT T v) := by
    convert (polynomialKernelRhoT_integrable T hT).const_mul 8
      using 1 <;> ext v <;> ring
  have hmajorValue : ∫ v : ℝ, major v =
      B * (32 * X * (FractionalPrimes.polynomialKernelM1 / T) + 8) := by
    rw [hmajorEq]
    calc
      _ = B * ∫ v : ℝ,
          (32 * X) * (|v| * FractionalPrimes.polynomialKernelRhoT T v) +
            8 * FractionalPrimes.polynomialKernelRhoT T v := by
              rw [integral_const_mul]
      _ = B * ((∫ v : ℝ,
            (32 * X) * (|v| * FractionalPrimes.polynomialKernelRhoT T v)) +
          ∫ v : ℝ, 8 * FractionalPrimes.polynomialKernelRhoT T v) := by
              rw [integral_add hfirstInt hsecondInt]
      _ = B * (32 * X * (FractionalPrimes.polynomialKernelM1 / T) + 8) := by
              rw [integral_const_mul, integral_const_mul,
                FractionalPrimes.polynomialKernelRhoT_firstMoment T hT,
                polynomialKernelRhoT_integral T hT]
              ring
  have hmajorBound (v : ℝ) : ‖rhoC v * E v‖ ≤ major v := by
    dsimp [rhoC, major]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hρnonneg v)]
    exact mul_le_mul_of_nonneg_left (by
      dsimp [E]
      simpa [w, mellinWindowData] using shiftedWindowError w v)
      (hρnonneg v)
  have hnormIntegral :
      ‖∫ v : ℝ, rhoC v * E v‖ ≤ ∫ v : ℝ, ‖rhoC v * E v‖ := by
    exact norm_integral_le_integral_norm _
  have hboundIntegral :
      (∫ v : ℝ, ‖rhoC v * E v‖) ≤ ∫ v : ℝ, major v :=
    integral_mono_ae hFint.norm hmajorInt
      (Filter.Eventually.of_forall hmajorBound)
  have hInvnorm : ‖((H⁻¹ : ℝ) : ℂ)‖ = H⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (le_of_lt (inv_pos.mpr hH))]
  have hInv : 0 ≤ H⁻¹ := le_of_lt (inv_pos.mpr hH)
  calc
    ‖w.N_H - w.S_H_T T‖ =
        H⁻¹ * ‖∫ v : ℝ, rhoC v * E v‖ := by
          rw [hdiff, norm_neg, norm_mul, hInvnorm]
    _ ≤ H⁻¹ * ∫ v : ℝ, ‖rhoC v * E v‖ :=
      mul_le_mul_of_nonneg_left hnormIntegral hInv
    _ ≤ H⁻¹ * ∫ v : ℝ, major v :=
      mul_le_mul_of_nonneg_left hboundIntegral hInv
    _ = H⁻¹ * (B *
          (32 * X * (FractionalPrimes.polynomialKernelM1 / T) + 8)) := by
        rw [hmajorValue]
    _ = 32 * B * FractionalPrimes.polynomialKernelM1 * X /
          (H * T) + 8 * B / H := by
        field_simp [ne_of_gt hH, ne_of_gt hT]
/-- The exact finite smoothed Mellin identity and its source endpoint error.
The sharp half-open window, finite coefficient support, 1/(2π) factor, and
first-moment error constants match the blueprint node lup:mellin-identity. -/
theorem smoothedMellinIdentity
    (X H B T : ℝ) (a : ℕ → ℂ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X) (hB : 0 ≤ B)
    (hsupport : ∀ n, 0 < n → a n ≠ 0 →
      X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X)
    (hbound : ∀ n, 0 < n → ‖a n‖ ≤ B) (hT : 0 < T) :
    let w := mellinWindowData FractionalPrimes.polynomialKernelRho
      X H B a hX hH hHX hB hsupport hbound
    w.S_H_T T = ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ t in Set.Icc (-T) T,
        w.A_X t * w.K_H t *
          FractionalPrimes.polynomialKernelRhoAngularFourier (t / T) ∧
    ‖w.N_H - w.S_H_T T‖ ≤
      32 * B * FractionalPrimes.polynomialKernelM1 * X / (H * T) +
        8 * B / H := by
  constructor
  · exact smoothedMellinIdentity_formula X H B T a hX hH hHX hB
      hsupport hbound hT
  · exact smoothedMellinIdentity_endpoint X H B T a hX hH hHX hB
      hsupport hbound hT

#print axioms FractionalPrimes.Literature.Polynomial.smoothedMellinIdentity

end FractionalPrimes.Literature.Polynomial

end
