module

public import FractionalPrimes.Core
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Compactly supported measure bridges

Small measure-theoretic facts used to construct convolution by a compactly
supported measure on Schwartz functions.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped Topology ContDiff FourierTransform Convolution

/-- Mathlib's infimum-defined Schwartz seminorm is exactly the supremum of
the weighted pointwise iterated-derivative norms in dimension one. -/
theorem schwartzSeminorm_eq_sSup (F : SchwartzMap ℝ ℂ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n F =
      sSup {c : ℝ | ∃ x : ℝ, |x| ^ k * ‖iteratedDeriv n (F : ℝ → ℂ) x‖ = c} := by
  let S : Set ℝ :=
    {c : ℝ | ∃ x : ℝ, |x| ^ k * ‖iteratedDeriv n (F : ℝ → ℂ) x‖ = c}
  have hne : S.Nonempty := by
    refine ⟨|0| ^ k * ‖iteratedDeriv n (F : ℝ → ℂ) 0‖, ?_⟩
    exact ⟨0, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨SchwartzMap.seminorm ℝ k n F, ?_⟩
    rintro c ⟨x, rfl⟩
    exact SchwartzMap.le_seminorm' ℝ k n F x
  have hsup_nonneg : 0 ≤ sSup S := by
    have hmem : |0| ^ k * ‖iteratedDeriv n (F : ℝ → ℂ) 0‖ ∈ S := ⟨0, rfl⟩
    exact (mul_nonneg (pow_nonneg (abs_nonneg 0) _) (norm_nonneg _)).trans
      (le_csSup hbdd hmem)
  have hsup_bound : ∀ x : ℝ,
      |x| ^ k * ‖iteratedDeriv n (F : ℝ → ℂ) x‖ ≤ sSup S := by
    intro x
    apply le_csSup hbdd
    exact ⟨x, rfl⟩
  apply le_antisymm
  · exact SchwartzMap.seminorm_le_bound' ℝ k n F hsup_nonneg hsup_bound
  · apply csSup_le hne
    intro c hc
    rcases hc with ⟨x, rfl⟩
    exact SchwartzMap.le_seminorm' ℝ k n F x

/-- A support inclusion in a closed interval gives the corresponding
almost-everywhere bound on the integration variable. -/
theorem ae_mem_Icc_of_measure_support_subset {μ : Measure ℝ} {R : ℝ}
    (hμ : μ.support ⊆ Set.Icc (-R) R) : ∀ᵐ y ∂μ, y ∈ Set.Icc (-R) R := by
  filter_upwards [μ.support_mem_ae] with y hy
  exact hμ hy

/-- The polynomial weight at `x` is bounded by the exact binomial expansion
of the translated weight plus a support radius. -/
theorem abs_pow_le_shift_binomial {x y R : ℝ} (hy : |y| ≤ R) (b : ℕ) :
    |x| ^ b ≤ ∑ j ∈ Finset.range (b + 1),
      (Nat.choose b j : ℝ) * R ^ (b - j) * |x - y| ^ j := by
  have hx : |x| ≤ |x - y| + R := by
    calc
      |x| = |(x - y) + y| := by congr 1 <;> ring
      _ ≤ |x - y| + |y| := abs_add_le _ _
      _ ≤ |x - y| + R := add_le_add_right hy _
  calc
    |x| ^ b ≤ (|x - y| + R) ^ b :=
      pow_le_pow_left₀ (abs_nonneg _) hx b
    _ = ∑ j ∈ Finset.range (b + 1),
        |x - y| ^ j * R ^ (b - j) * (Nat.choose b j : ℝ) :=
      Commute.add_pow (Commute.all _ _) b
    _ = ∑ j ∈ Finset.range (b + 1),
        (Nat.choose b j : ℝ) * R ^ (b - j) * |x - y| ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The pointwise weighted translate of a Schwartz function is controlled by
the sum of its exact translated seminorm bounds, almost everywhere for a
measure supported in `[-R,R]`. -/
theorem ae_weighted_schwartz_translate_le_sum {μ : Measure ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hμ : μ.support ⊆ Set.Icc (-R) R)
    (F : SchwartzMap ℝ ℂ) (b : ℕ) (x : ℝ) :
    ∀ᵐ y ∂μ, |x| ^ b * ‖F (x - y)‖ ≤
      ∑ j ∈ Finset.range (b + 1),
        (Nat.choose b j : ℝ) * R ^ (b - j) * SchwartzMap.seminorm ℝ j 0 F := by
  filter_upwards [ae_mem_Icc_of_measure_support_subset hμ] with y hy
  have hbin := abs_pow_le_shift_binomial (x := x) (y := y) (R := R)
    (abs_le.mpr hy) b
  have hterm (j : ℕ) : |x - y| ^ j * ‖F (x - y)‖ ≤ SchwartzMap.seminorm ℝ j 0 F := by
    simpa [iteratedDeriv_zero] using SchwartzMap.le_seminorm' ℝ j 0 F (x - y)
  calc
    |x| ^ b * ‖F (x - y)‖ ≤
        (∑ j ∈ Finset.range (b + 1),
          (Nat.choose b j : ℝ) * R ^ (b - j) * |x - y| ^ j) * ‖F (x - y)‖ :=
      mul_le_mul_of_nonneg_right hbin (norm_nonneg _)
    _ = ∑ j ∈ Finset.range (b + 1),
        ((Nat.choose b j : ℝ) * R ^ (b - j)) *
          (|x - y| ^ j * ‖F (x - y)‖) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ ∑ j ∈ Finset.range (b + 1),
        ((Nat.choose b j : ℝ) * R ^ (b - j)) * SchwartzMap.seminorm ℝ j 0 F := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left (hterm j)
      positivity

/-- A translate of a Schwartz function is integrable against a finite measure. -/
theorem integrable_schwartz_translate {μ : Measure ℝ} [IsFiniteMeasure μ]
    (F : SchwartzMap ℝ ℂ) (x : ℝ) : Integrable (fun y : ℝ => (F (x - y) : ℂ)) μ := by
  have hcont : Continuous (fun y : ℝ => (F (x - y) : ℂ)) :=
    F.continuous.comp (continuous_const.sub continuous_id)
  have hC : 0 ≤ SchwartzMap.seminorm ℝ 0 0 F := by positivity
  have hconst : Integrable (fun _ : ℝ => ((SchwartzMap.seminorm ℝ 0 0 F : ℝ) : ℂ)) μ := by
    exact integrable_const _
  apply hconst.mono hcont.aestronglyMeasurable
  filter_upwards with y
  simpa [Complex.norm_real, abs_of_nonneg hC] using
    (SchwartzMap.norm_le_seminorm ℝ F (x - y))

/-- The pointwise a.e. bound integrates to the compact-measure weighted
estimate, with the measure's real mass as the exact prefactor. -/
theorem norm_mul_abs_pow_integral_schwartz_le {μ : Measure ℝ} {R : ℝ}
    [IsFiniteMeasure μ] (hR : 0 ≤ R) (hμ : μ.support ⊆ Set.Icc (-R) R)
    (F : SchwartzMap ℝ ℂ) (b : ℕ) (x : ℝ) :
    |x| ^ b * ‖∫ y, (F (x - y) : ℂ) ∂μ‖ ≤
      μ.real Set.univ *
        ∑ j ∈ Finset.range (b + 1),
          (Nat.choose b j : ℝ) * R ^ (b - j) * SchwartzMap.seminorm ℝ j 0 F := by
  let M : ℝ := ∑ j ∈ Finset.range (b + 1),
    (Nat.choose b j : ℝ) * R ^ (b - j) * SchwartzMap.seminorm ℝ j 0 F
  have hpoint := ae_weighted_schwartz_translate_le_sum hR hμ F b x
  have hleft : Integrable (fun y : ℝ => |x| ^ b * ‖F (x - y)‖) μ := by
    exact (integrable_schwartz_translate F x).norm.const_mul (|x| ^ b)
  have hright : Integrable (fun _ : ℝ => M) μ := integrable_const M
  have hpoint' : (fun y : ℝ => |x| ^ b * ‖F (x - y)‖) ≤ᵐ[μ] fun _ => M := by
    filter_upwards [hpoint] with y hy
    simpa [M] using hy
  calc
    |x| ^ b * ‖∫ y, (F (x - y) : ℂ) ∂μ‖ ≤
        |x| ^ b * ∫ y, ‖F (x - y)‖ ∂μ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ y, |x| ^ b * ‖F (x - y)‖ ∂μ := by rw [integral_const_mul]
    _ ≤ ∫ _ : ℝ, M ∂μ := integral_mono_ae hleft hright hpoint'
    _ = μ.real Set.univ * M := by simp [integral_const, smul_eq_mul]
    _ = μ.real Set.univ *
        ∑ j ∈ Finset.range (b + 1),
          (Nat.choose b j : ℝ) * R ^ (b - j) * SchwartzMap.seminorm ℝ j 0 F := by
      rfl

/-- Differentiation of convolution by a finite measure at a fixed point.
The compact-support assumption is not needed for this first derivative
identity, since a Schwartz derivative is globally bounded. -/
theorem hasDerivAt_schwartz_measureConvolution {μ : Measure ℝ} [IsFiniteMeasure μ]
    (F : SchwartzMap ℝ ℂ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ y, (F (x - y) : ℂ) ∂μ)
      (∫ y, deriv (F : ℝ → ℂ) (x₀ - y) ∂μ) x₀ := by
  let C : ℝ := SchwartzMap.seminorm ℝ 0 1 F
  have hC : 0 ≤ C := by positivity
  have hderiv_bound : ∀ z : ℝ, ‖deriv (F : ℝ → ℂ) z‖ ≤ C := by
    intro z
    have h := SchwartzMap.le_seminorm' ℝ 0 1 F z
    simpa [C, iteratedDeriv_one] using h
  have hF_meas : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun y : ℝ => (F (x - y) : ℂ)) μ := by
    filter_upwards with x
    exact (F.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hF_int : Integrable (fun y : ℝ => (F (x₀ - y) : ℂ)) μ :=
    integrable_schwartz_translate F x₀
  have hF'_meas : AEStronglyMeasurable
      (fun y : ℝ => deriv (F : ℝ → ℂ) (x₀ - y)) μ := by
    exact (F.smooth 2).continuous_deriv (by norm_num : (1 : ℕ∞ω) ≤ 2) |>.comp_aestronglyMeasurable
      (continuous_const.sub continuous_id).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂μ, ∀ x ∈ Metric.ball x₀ 1,
      ‖deriv (F : ℝ → ℂ) (x - y)‖ ≤ (fun _ : ℝ => C) y := by
    filter_upwards with y
    intro x hx
    exact hderiv_bound (x - y)
  have hbound_int : Integrable (fun _ : ℝ => C) μ := by
    exact integrable_const C
  have h_diff : ∀ᵐ y ∂μ, ∀ x ∈ Metric.ball x₀ 1,
      HasDerivAt (fun x : ℝ => (F (x - y) : ℂ))
        (deriv (F : ℝ → ℂ) (x - y)) x := by
    filter_upwards with y
    intro x hx
    have hFdiff : HasDerivAt (F : ℝ → ℂ)
        (deriv (F : ℝ → ℂ) (x - y)) (x - y) := by
      exact F.differentiableAt.hasDerivAt
    exact HasDerivAt.comp_sub_const x y hFdiff
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (x₀ := x₀) (s := Metric.ball x₀ 1) (bound := fun _ : ℝ => C)
    (F := fun x y => (F (x - y) : ℂ)) (F' := fun x y => deriv (F : ℝ → ℂ) (x - y))
    (Metric.ball_mem_nhds x₀ zero_lt_one) hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa using h.2

/-- The `n`th Schwartz derivative, kept inside the Schwartz space so that
Mathlib's derivative-under-integral theorem can be iterated without rebuilding
the Schwartz structure at each order. -/
noncomputable def iteratedSchwartzDerivative (F : SchwartzMap ℝ ℂ) (n : ℕ) :
    SchwartzMap ℝ ℂ := (SchwartzMap.derivCLM ℂ ℂ)^[n] F

/-- The Schwartz-space iteration agrees pointwise with Mathlib's iterated
derivative. -/
theorem iteratedSchwartzDerivative_apply (F : SchwartzMap ℝ ℂ) :
    ∀ n x, iteratedSchwartzDerivative F n x = iteratedDeriv n (F : ℝ → ℂ) x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [iteratedSchwartzDerivative, iteratedDeriv_zero]
  | succ n ih =>
      intro x
      rw [iteratedDeriv_succ]
      have hfun : (iteratedSchwartzDerivative F n : ℝ → ℂ) =
          iteratedDeriv n (F : ℝ → ℂ) := funext ih
      change ((SchwartzMap.derivCLM ℂ ℂ)^[n + 1] F) x = _
      rw [Function.iterate_succ_apply']
      rw [SchwartzMap.derivCLM_apply]
      change deriv (iteratedSchwartzDerivative F n : ℝ → ℂ) x = _
      rw [hfun]

/-- Every iterated Schwartz derivative has the corresponding pointwise
derivative-under-the-integral identity. -/
theorem hasDerivAt_iteratedSchwartz_measureConvolution {μ : Measure ℝ}
    [IsFiniteMeasure μ] (F : SchwartzMap ℝ ℂ) (n : ℕ) (x₀ : ℝ) :
    HasDerivAt
      (fun x : ℝ => ∫ y, (iteratedSchwartzDerivative F n (x - y) : ℂ) ∂μ)
      (∫ y, (iteratedSchwartzDerivative F (n + 1) (x₀ - y) : ℂ) ∂μ) x₀ := by
  have h := hasDerivAt_schwartz_measureConvolution (μ := μ)
    (iteratedSchwartzDerivative F n) x₀
  simpa [iteratedSchwartzDerivative, Function.iterate_succ_apply',
    SchwartzMap.derivCLM_apply] using h

/-- Pointwise convolution of a Schwartz function with a finite measure. -/
noncomputable def measureSchwartzConvolution (μ : Measure ℝ) (F : SchwartzMap ℝ ℂ) :
    ℝ → ℂ := fun x => ∫ y, (F (x - y) : ℂ) ∂μ

/-- The iterated derivatives of measure convolution are the integrals of
the corresponding Schwartz derivatives. -/
theorem iteratedDeriv_measureSchwartzConvolution {μ : Measure ℝ}
    [IsFiniteMeasure μ] (F : SchwartzMap ℝ ℂ) :
    ∀ n x, iteratedDeriv n (measureSchwartzConvolution μ F) x =
      ∫ y, (iteratedSchwartzDerivative F n (x - y) : ℂ) ∂μ := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [measureSchwartzConvolution, iteratedDeriv_zero, iteratedSchwartzDerivative]
  | succ n ih =>
      intro x
      rw [iteratedDeriv_succ]
      have hrep : iteratedDeriv n (measureSchwartzConvolution μ F) =
          fun z => ∫ y, (iteratedSchwartzDerivative F n (z - y) : ℂ) ∂μ :=
        funext ih
      rw [hrep]
      exact (hasDerivAt_iteratedSchwartz_measureConvolution (μ := μ) F n x).deriv

/-- Convolution of a Schwartz function with a finite measure is smooth. -/
theorem contDiff_measureSchwartzConvolution {μ : Measure ℝ} [IsFiniteMeasure μ]
    (F : SchwartzMap ℝ ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (measureSchwartzConvolution μ F) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n hn x
  have hrep : iteratedDeriv n (measureSchwartzConvolution μ F) =
      fun z => ∫ y, (iteratedSchwartzDerivative F n (z - y) : ℂ) ∂μ :=
    funext (iteratedDeriv_measureSchwartzConvolution (μ := μ) F n)
  rw [hrep]
  exact (hasDerivAt_iteratedSchwartz_measureConvolution (μ := μ) F n x).differentiableAt

/-- The Fourier transform of a finite-measure convolution is the product of
the measure Fourier transform and the Schwartz Fourier transform, in
Mathlib's `exp(-2π i x ξ)` convention. -/
theorem fourier_measureSchwartzConvolution {μ : Measure ℝ} [IsFiniteMeasure μ]
    (F : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (measureSchwartzConvolution μ F) ξ =
      (∫ y, Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) ∂μ) * 𝓕 (F : ℝ → ℂ) ξ := by
  let phase : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I)
  let g : ℝ × ℝ → ℂ := fun z => phase z.1 * F (z.1 - z.2)
  have hFprod : Integrable (fun z : ℝ × ℝ => (F (z.1 - z.2) : ℂ)) (volume.prod μ) := by
    apply (integrable_prod_iff'
      ((F.continuous.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)).mpr
    constructor
    · filter_upwards with y
      exact F.integrable.comp_sub_right y
    · have he : (fun y : ℝ => ∫ x : ℝ, ‖F (x-y)‖) = fun _ => ∫ x, ‖F x‖ := by
        funext y
        exact integral_sub_right_eq_self (fun x => ‖F x‖) y
      change Integrable (fun y : ℝ => ∫ x : ℝ, ‖(F (x-y) : ℂ)‖ ∂volume) μ
      rw [he]
      exact integrable_const _
  have hg : Integrable g (volume.prod μ) := by
    apply hFprod.norm.mono'
    · exact (by fun_prop : Continuous g).aestronglyMeasurable
    · filter_upwards with z
      simp [g, phase, Complex.norm_exp]
  have hFourier : 𝓕 (F : ℝ → ℂ) ξ =
      ∫ u : ℝ, phase u * (F u : ℂ) ∂volume := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with u
    simp [phase, Circle.smul_def]
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ x : ℝ, phase x * (∫ y, (F (x - y) : ℂ) ∂μ) ∂volume) = _
  have hswap : (∫ x : ℝ, phase x * (∫ y, (F (x - y) : ℂ) ∂μ) ∂volume) =
      ∫ y : ℝ, ∫ x : ℝ, phase x * (F (x - y) : ℂ) ∂volume ∂μ := by
    calc
      _ = ∫ x : ℝ, ∫ y : ℝ, phase x * (F (x - y) : ℂ) ∂μ ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        exact (integral_const_mul (phase x) (fun y : ℝ => (F (x-y) : ℂ))).symm
      _ = ∫ y : ℝ, ∫ x : ℝ, phase x * (F (x-y) : ℂ) ∂volume ∂μ := by
        simpa [g] using integral_integral_swap hg
  rw [hswap]
  calc
    _ = ∫ y : ℝ, phase y * 𝓕 (F : ℝ → ℂ) ξ ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      have hshift : (∫ x : ℝ, phase x * (F (x-y) : ℂ) ∂volume) =
          ∫ u : ℝ, phase (u+y) * (F u : ℂ) ∂volume :=
        by simpa only [sub_add_cancel] using
          (integral_sub_right_eq_self
            (fun u : ℝ => phase (u+y) * (F u : ℂ)) y)
      rw [hshift, hFourier, ← integral_const_mul]
      congr 1
      funext u
      dsimp [phase]
      have he : -2 * Real.pi * (u+y) * ξ =
          -2 * Real.pi * y * ξ + -2 * Real.pi * u * ξ := by ring
      have heC : (↑(-2 * Real.pi * (u+y) * ξ) : ℂ) * Complex.I =
          ↑(-2 * Real.pi * y * ξ) * Complex.I +
            ↑(-2 * Real.pi * u * ξ) * Complex.I := by rw [he]; push_cast; ring
      rw [heC, Complex.exp_add]
      ring
    _ = (∫ y, phase y ∂μ) * 𝓕 (F : ℝ → ℂ) ξ := integral_mul_const _ _
    _ = _ := by rfl

/-- A Fourier cutoff equal to one on the support of a factor leaves any
product with that factor unchanged. -/
theorem support_cutoff_mul_eq {f c g a : ℝ → ℂ}
    (hc : ∀ ξ, ξ ∈ Function.support f → c ξ = 1)
    (hg : ∀ ξ, g ξ = a ξ * f ξ) :
    ∀ ξ, c ξ * g ξ = g ξ := by
  intro ξ
  by_cases hf : f ξ = 0
  · rw [hg ξ, hf]
    simp
  · have hξ : ξ ∈ Function.support f := by
      change f ξ ≠ 0
      exact hf
    rw [hg ξ, hc ξ hξ]
    ring

/-- Convolution of a Schwartz function with a finite measure supported in a
compact interval is a Schwartz function, with the explicit binomial decay
estimate inherited from the input seminorms. -/
noncomputable def measureSchwartzConvolutionSchwartz {μ : Measure ℝ} [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0 ≤ R) (hμ : μ.support ⊆ Set.Icc (-R) R)
    (F : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ where
  toFun := measureSchwartzConvolution μ F
  smooth' := contDiff_measureSchwartzConvolution (μ := μ) F
  decay' k n := by
    refine ⟨μ.real Set.univ *
      ∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) * R ^ (k - j) *
          SchwartzMap.seminorm ℝ j 0 (iteratedSchwartzDerivative F n), ?_⟩
    intro x
    rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    rw [iteratedDeriv_measureSchwartzConvolution (μ := μ) F n x]
    exact norm_mul_abs_pow_integral_schwartz_le hR hμ
      (iteratedSchwartzDerivative F n) k x

/-- A Schwartz cutoff equal to one on the Fourier support of `F` fixes the
convolution of `F` with a finite measure. -/
theorem cutoff_measureSchwartzConvolution {μ : Measure ℝ} [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0 ≤ R) (hμ : μ.support ⊆ Set.Icc (-R) R)
    (F χ : SchwartzMap ℝ ℂ)
    (hχ : ∀ ξ, ξ ∈ Function.support (𝓕 (F : ℝ → ℂ)) →
      𝓕 (χ : ℝ → ℂ) ξ = 1) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) χ
      (measureSchwartzConvolutionSchwartz hR hμ F) =
        measureSchwartzConvolutionSchwartz hR hμ F := by
  let G : SchwartzMap ℝ ℂ := measureSchwartzConvolutionSchwartz hR hμ F
  have hG : ∀ ξ, 𝓕 (G : ℝ → ℂ) ξ =
      (∫ y, Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) ∂μ) *
        𝓕 (F : ℝ → ℂ) ξ := by
    intro ξ
    change 𝓕 (measureSchwartzConvolution μ F) ξ = _
    exact fourier_measureSchwartzConvolution (μ := μ) F ξ
  have hmul : ∀ ξ, 𝓕 (χ : ℝ → ℂ) ξ * 𝓕 (G : ℝ → ℂ) ξ =
      𝓕 (G : ℝ → ℂ) ξ := by
    apply support_cutoff_mul_eq
    · exact hχ
    · intro ξ
      exact hG ξ
  have hFourier : 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) χ G) =
      𝓕 G := by
    ext ξ
    calc
      𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) χ G) ξ =
          𝓕 (χ : ℝ → ℂ) ξ * 𝓕 (G : ℝ → ℂ) ξ := by
            rw [SchwartzMap.fourier_convolution]
            simp [SchwartzMap.pairing_apply_apply, SchwartzMap.fourier_coe]
      _ = 𝓕 (G : ℝ → ℂ) ξ := hmul ξ
      _ = 𝓕 G ξ := rfl
  have h := congrArg (fun H : SchwartzMap ℝ ℂ => 𝓕⁻ H) hFourier
  simpa using h

/-- Pointwise form of the cutoff identity, using Mathlib's integral
definition of convolution. -/
theorem cutoff_measureSchwartzConvolution_apply {μ : Measure ℝ}
    [IsFiniteMeasure μ] {R : ℝ} (hR : 0 ≤ R)
    (hμ : μ.support ⊆ Set.Icc (-R) R) (F χ : SchwartzMap ℝ ℂ)
    (hχ : ∀ ξ, ξ ∈ Function.support (𝓕 (F : ℝ → ℂ)) →
      𝓕 (χ : ℝ → ℂ) ξ = 1) (x : ℝ) :
    (χ ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (measureSchwartzConvolutionSchwartz hR hμ F : ℝ → ℂ)) x =
        measureSchwartzConvolution μ F x := by
  have h := cutoff_measureSchwartzConvolution hR hμ F χ hχ
  have hx := congrArg (fun H : SchwartzMap ℝ ℂ => H x) h
  rw [SchwartzMap.convolution_apply] at hx
  have hGfun : (measureSchwartzConvolutionSchwartz hR hμ F : ℝ → ℂ) =
      measureSchwartzConvolution μ F := rfl
  rw [hGfun] at hx ⊢
  simpa [measureSchwartzConvolution] using hx

/-- The paper's pointwise Schwartz seminorm, written as a real supremum over
weighted iterated derivatives. This makes the binomial estimate below use the
same supremum convention as the approved bridge statement. -/
noncomputable def weightedIteratedSchwartzSup (F : SchwartzMap ℝ ℂ)
    (a b : ℕ) : ℝ :=
  sSup {c : ℝ | ∃ x : ℝ,
    |x| ^ b * ‖iteratedDeriv a (F : ℝ → ℂ) x‖ = c}

private theorem schwartzSeminorm_iteratedSchwartzDerivative_eq_weightedSup
    (F : SchwartzMap ℝ ℂ) (a b : ℕ) :
    SchwartzMap.seminorm ℝ b 0 (iteratedSchwartzDerivative F a) =
      weightedIteratedSchwartzSup F a b := by
  rw [schwartzSeminorm_eq_sSup]
  unfold weightedIteratedSchwartzSup
  congr 1
  ext c
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [iteratedDeriv_zero,
      iteratedSchwartzDerivative_apply] using hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [iteratedDeriv_zero,
      iteratedSchwartzDerivative_apply] using hx⟩

/-- The compact-measure Schwartz bridge stated in the paper's pointwise form.
It bundles the exact integral convolution, its Fourier product, the cutoff
reproduction identity, and the explicit binomial seminorm estimate. The
suprema are represented by `weightedIteratedSchwartzSup`, which is exactly
Mathlib's Schwartz seminorm by
`schwartzSeminorm_iteratedSchwartzDerivative_eq_weightedSup`. -/
theorem compactMeasureConvolutionSchwartz {μ : Measure ℝ} [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0 ≤ R)
    (hμ : μ.support ⊆ Set.Icc (-R) R) (F : SchwartzMap ℝ ℂ) :
    ∃ G : SchwartzMap ℝ ℂ,
      (∀ x, G x = ∫ y, (F (x - y) : ℂ) ∂μ) ∧
      (∀ ξ, 𝓕 (G : ℝ → ℂ) ξ =
        (∫ y, Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) ∂μ) *
          𝓕 (F : ℝ → ℂ) ξ) ∧
      (∀ χ : SchwartzMap ℝ ℂ,
        (∀ ξ, ξ ∈ Function.support (𝓕 (F : ℝ → ℂ)) →
          𝓕 (χ : ℝ → ℂ) ξ = 1) →
        ∀ x, (χ ⋆[ContinuousLinearMap.mul ℂ ℂ]
          (G : ℝ → ℂ)) x = G x) ∧
      (∀ a b x, |x| ^ b * ‖iteratedDeriv a (G : ℝ → ℂ) x‖ ≤
        μ.real Set.univ *
          ∑ j ∈ Finset.range (b + 1),
            (Nat.choose b j : ℝ) * R ^ (b - j) *
              weightedIteratedSchwartzSup F a j) := by
  let G : SchwartzMap ℝ ℂ := measureSchwartzConvolutionSchwartz hR hμ F
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro ξ
    change 𝓕 (measureSchwartzConvolution μ F) ξ = _
    exact fourier_measureSchwartzConvolution (μ := μ) F ξ
  · intro χ hχ x
    change (χ ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (measureSchwartzConvolutionSchwartz hR hμ F : ℝ → ℂ)) x = _
    exact cutoff_measureSchwartzConvolution_apply hR hμ F χ hχ x
  · intro a b x
    have h := norm_mul_abs_pow_integral_schwartz_le hR hμ
      (iteratedSchwartzDerivative F a) b x
    change |x| ^ b *
      ‖iteratedDeriv a (measureSchwartzConvolution μ F) x‖ ≤ _
    rw [iteratedDeriv_measureSchwartzConvolution (μ := μ) F a x]
    simpa only [iteratedSchwartzDerivative_apply,
      schwartzSeminorm_iteratedSchwartzDerivative_eq_weightedSup] using h

end FractionalPrimes
