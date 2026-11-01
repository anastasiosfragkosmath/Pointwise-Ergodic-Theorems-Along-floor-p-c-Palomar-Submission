module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open MeasureTheory
open Set
open scoped ContDiff

/-- The outer Dirichlet-polynomial cutoff `ζ(x) = s(4x-3)s(5-2x)` from
`lup:kernel-data`. Mathlib's `Real.smoothTransition` is the exact function
`b(u)/(b(u)+b(1-u))` specified there. -/
noncomputable def polynomialOuterCutoff (x : ℝ) : ℝ :=
  Real.smoothTransition (4 * x - 3) * Real.smoothTransition (5 - 2 * x)

theorem polynomialOuterCutoff_nonneg (x : ℝ) : 0 ≤ polynomialOuterCutoff x := by
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem polynomialOuterCutoff_le_one (x : ℝ) : polynomialOuterCutoff x ≤ 1 := by
  have h₁ : Real.smoothTransition (4 * x - 3) ≤ 1 :=
    Real.smoothTransition.le_one _
  have h₂₀ : 0 ≤ Real.smoothTransition (5 - 2 * x) :=
    Real.smoothTransition.nonneg _
  have h₂ : Real.smoothTransition (5 - 2 * x) ≤ 1 :=
    Real.smoothTransition.le_one _
  calc
    polynomialOuterCutoff x ≤ 1 * Real.smoothTransition (5 - 2 * x) :=
      mul_le_mul_of_nonneg_right h₁ h₂₀
    _ = Real.smoothTransition (5 - 2 * x) := one_mul _
    _ ≤ 1 := h₂

theorem polynomialOuterCutoff_eq_one {x : ℝ} (hx : 1 ≤ x) (hx' : x ≤ 2) :
    polynomialOuterCutoff x = 1 := by
  have h₁ : 1 ≤ 4 * x - 3 := by linarith
  have h₂ : 1 ≤ 5 - 2 * x := by linarith
  simp [polynomialOuterCutoff, Real.smoothTransition.one_of_one_le h₁,
    Real.smoothTransition.one_of_one_le h₂]

theorem polynomialOuterCutoff_eq_zero_of_lt_left {x : ℝ} (hx : x < 3 / 4) :
    polynomialOuterCutoff x = 0 := by
  have h₁ : 4 * x - 3 ≤ 0 := by linarith
  simp [polynomialOuterCutoff, Real.smoothTransition.zero_of_nonpos h₁]

theorem polynomialOuterCutoff_eq_zero_of_lt_right {x : ℝ} (hx : 5 / 2 < x) :
    polynomialOuterCutoff x = 0 := by
  have h₂ : 5 - 2 * x ≤ 0 := by linarith
  simp [polynomialOuterCutoff, Real.smoothTransition.zero_of_nonpos h₂]

@[fun_prop]
theorem polynomialOuterCutoff_contDiff : ContDiff ℝ ∞ polynomialOuterCutoff := by
  unfold polynomialOuterCutoff
  fun_prop

theorem polynomialOuterCutoff_support_subset :
    Function.support polynomialOuterCutoff ⊆ Set.Icc (3 / 4 : ℝ) (5 / 2) := by
  intro x hx
  rw [Function.mem_support] at hx
  constructor
  · by_contra h
    exact hx (polynomialOuterCutoff_eq_zero_of_lt_left (lt_of_not_ge h))
  · by_contra h
    exact hx (polynomialOuterCutoff_eq_zero_of_lt_right (lt_of_not_ge h))

theorem polynomialOuterCutoff_hasCompactSupport : HasCompactSupport polynomialOuterCutoff := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact polynomialOuterCutoff_support_subset

/-- The profile `g(v) = e^(v/2) ζ(e^v)` in the Mellin decay lemma
`lup:smooth-mean`, viewed as a complex-valued function for Fourier estimates. -/
noncomputable def smoothMeanProfile (v : ℝ) : ℂ :=
  ((Real.exp (v / 2) * polynomialOuterCutoff (Real.exp v) : ℝ) : ℂ)

theorem smoothMeanProfile_contDiff : ContDiff ℝ ∞ smoothMeanProfile := by
  change ContDiff ℝ ∞ (Complex.ofRealCLM ∘ fun v : ℝ =>
    Real.exp (v / 2) * polynomialOuterCutoff (Real.exp v))
  apply Complex.ofRealCLM.contDiff.comp
  have hexp : ContDiff ℝ ∞ (fun v : ℝ => Real.exp v) := by fun_prop
  have hscale : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (v / 2)) := by fun_prop
  exact hscale.mul (polynomialOuterCutoff_contDiff.comp hexp)

theorem smoothMeanProfile_support_subset :
    Function.support smoothMeanProfile ⊆
      Set.Icc (Real.log (3 / 4 : ℝ)) (Real.log (5 / 2 : ℝ)) := by
  intro v hv
  rw [Function.mem_support] at hv
  have hζ : polynomialOuterCutoff (Real.exp v) ≠ 0 := by
    intro hζ
    apply hv
    simp [smoothMeanProfile, hζ]
  have hs := polynomialOuterCutoff_support_subset (by simpa [Function.mem_support] using hζ)
  constructor
  · exact (Real.log_le_iff_le_exp (by norm_num : 0 < (3 / 4 : ℝ))).2 hs.1
  · exact (Real.le_log_iff_exp_le (by norm_num : 0 < (5 / 2 : ℝ))).2 hs.2

theorem smoothMeanProfile_hasCompactSupport : HasCompactSupport smoothMeanProfile := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact smoothMeanProfile_support_subset

private theorem smoothMeanProfileIterated_hasCompactSupport (N : ℕ) :
    HasCompactSupport (iteratedDeriv N smoothMeanProfile) := by
  induction N with
  | zero => simpa [iteratedDeriv_zero] using smoothMeanProfile_hasCompactSupport
  | succ N ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

private theorem smoothMeanProfileIterated_continuous (N : ℕ) :
    Continuous (iteratedDeriv N smoothMeanProfile) :=
  ContDiff.continuous_iteratedDeriv N smoothMeanProfile_contDiff (by simp)

private theorem smoothMeanProfileIterated_integrable (N : ℕ) :
    Integrable (iteratedDeriv N smoothMeanProfile) :=
  (smoothMeanProfileIterated_continuous N).integrable_of_hasCompactSupport
    (smoothMeanProfileIterated_hasCompactSupport N)

/-- The exact source constant `Z_N = 2^N (‖g‖₁ + ‖g^(N)‖₁)`. -/
noncomputable def smoothMeanDecayConstant (N : ℕ) : ℝ :=
  2 ^ N * ((∫ v : ℝ, ‖smoothMeanProfile v‖) +
    ∫ v : ℝ, ‖iteratedDeriv N smoothMeanProfile v‖)

theorem smoothMeanDecayConstant_finite (N : ℕ) :
    Integrable (fun v : ℝ => ‖smoothMeanProfile v‖) ∧
      Integrable (fun v : ℝ => ‖iteratedDeriv N smoothMeanProfile v‖) := by
  constructor
  · exact (smoothMeanProfileIterated_integrable 0).norm
  · exact (smoothMeanProfileIterated_integrable N).norm

private noncomputable def smoothMeanOscillation (t v : ℝ) : ℂ :=
  Complex.exp (-((v : ℂ) * (Complex.I * (t : ℂ))))

private theorem smoothMeanOscillation_deriv (t v : ℝ) :
    deriv (smoothMeanOscillation t) v =
      (-Complex.I * (t : ℂ)) * smoothMeanOscillation t v := by
  have hId : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 v :=
    (hasDerivAt_id v).ofReal_comp
  have hLin : HasDerivAt (fun x : ℝ => -((x : ℂ) * (Complex.I * (t : ℂ))))
      (-Complex.I * (t : ℂ)) v := by
    convert (hId.mul_const (Complex.I * (t : ℂ))).neg using 1 <;> ring
  have hExp := (Complex.hasDerivAt_exp (-((v : ℂ) * (Complex.I * (t : ℂ))))).comp v hLin
  have hfun : smoothMeanOscillation t =
      Complex.exp ∘ (fun x : ℝ => -((x : ℂ) * (Complex.I * (t : ℂ)))) := rfl
  rw [hfun]
  calc
    deriv (Complex.exp ∘ fun x : ℝ => -((x : ℂ) * (Complex.I * (t : ℂ)))) v =
        Complex.exp (-((v : ℂ) * (Complex.I * (t : ℂ)))) *
          (-Complex.I * (t : ℂ)) := hExp.deriv
    _ = (-Complex.I * (t : ℂ)) *
        Complex.exp (-((v : ℂ) * (Complex.I * (t : ℂ)))) := by ring

private theorem smoothMeanOscillation_continuous (t : ℝ) :
    Continuous (smoothMeanOscillation t) := by
  unfold smoothMeanOscillation
  fun_prop

private theorem smoothMeanOscillation_differentiable (t : ℝ) :
    Differentiable ℝ (smoothMeanOscillation t) := by
  unfold smoothMeanOscillation
  fun_prop

private theorem smoothMeanPartsIntegrable (N : ℕ) (t : ℝ) :
    Integrable (fun v : ℝ => fderiv ℝ (smoothMeanOscillation t) v 1 *
        iteratedDeriv N smoothMeanProfile v) ∧
      Integrable (fun v : ℝ => smoothMeanOscillation t v *
        fderiv ℝ (iteratedDeriv N smoothMeanProfile) v 1) ∧
      Integrable (fun v : ℝ => smoothMeanOscillation t v *
        iteratedDeriv N smoothMeanProfile v) := by
  have hN := smoothMeanProfileIterated_hasCompactSupport N
  have hN1 : HasCompactSupport (fun v : ℝ => fderiv ℝ
      (iteratedDeriv N smoothMeanProfile) v 1) := by
    simpa only [fderiv_apply_one_eq_deriv] using hN.deriv
  have hcharDeriv : (fun v : ℝ => fderiv ℝ (smoothMeanOscillation t) v 1) =
      fun v => (-Complex.I * (t : ℂ)) * smoothMeanOscillation t v := by
    funext v
    rw [fderiv_apply_one_eq_deriv, smoothMeanOscillation_deriv]
  have hcontCharDeriv : Continuous (fun v : ℝ =>
      fderiv ℝ (smoothMeanOscillation t) v 1) := by
    rw [hcharDeriv]
    exact continuous_const.mul (smoothMeanOscillation_continuous t)
  have hcontChar : Continuous (smoothMeanOscillation t) :=
    smoothMeanOscillation_continuous t
  have hcontN : Continuous (iteratedDeriv N smoothMeanProfile) :=
    smoothMeanProfileIterated_continuous N
  have hcontN1 : Continuous (fun v : ℝ => fderiv ℝ
      (iteratedDeriv N smoothMeanProfile) v 1) := by
    have heq : (fun v : ℝ => fderiv ℝ (iteratedDeriv N smoothMeanProfile) v 1) =
        iteratedDeriv (N + 1) smoothMeanProfile := by
      funext v
      rw [fderiv_apply_one_eq_deriv, iteratedDeriv_succ]
    rw [heq]
    exact smoothMeanProfileIterated_continuous (N + 1)
  constructor
  · have hsupp : HasCompactSupport (fun v : ℝ =>
        fderiv ℝ (smoothMeanOscillation t) v 1 *
          iteratedDeriv N smoothMeanProfile v) :=
      HasCompactSupport.mul_left hN
    exact (hcontCharDeriv.mul hcontN).integrable_of_hasCompactSupport hsupp
  constructor
  · have hsupp : HasCompactSupport (fun v : ℝ =>
        smoothMeanOscillation t v *
          fderiv ℝ (iteratedDeriv N smoothMeanProfile) v 1) :=
      HasCompactSupport.mul_left hN1
    exact (hcontChar.mul hcontN1).integrable_of_hasCompactSupport hsupp
  · have hsupp : HasCompactSupport (fun v : ℝ =>
        smoothMeanOscillation t v * iteratedDeriv N smoothMeanProfile v) :=
      HasCompactSupport.mul_left hN
    exact (hcontChar.mul hcontN).integrable_of_hasCompactSupport hsupp

private theorem smoothMeanOscillation_ibp (N : ℕ) (t : ℝ) :
    (∫ v : ℝ, smoothMeanOscillation t v *
        iteratedDeriv (N + 1) smoothMeanProfile v) =
      (Complex.I * (t : ℂ)) *
        ∫ v : ℝ, smoothMeanOscillation t v *
          iteratedDeriv N smoothMeanProfile v := by
  have hparts := smoothMeanPartsIntegrable N t
  have hdprofile := smoothMeanProfile_contDiff.differentiable_iteratedDeriv N
    (by exact_mod_cast (ENat.natCast_lt_top N))
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hparts.1 hparts.2.1 hparts.2.2
    (fun x _ => smoothMeanOscillation_differentiable t x)
    (fun x _ => hdprofile x)
  calc
    (∫ v : ℝ, smoothMeanOscillation t v *
        iteratedDeriv (N + 1) smoothMeanProfile v) =
      ∫ v : ℝ, smoothMeanOscillation t v *
        fderiv ℝ (iteratedDeriv N smoothMeanProfile) v 1 := by
          congr 1
          funext v
          rw [fderiv_apply_one_eq_deriv, iteratedDeriv_succ]
    _ = - ∫ v : ℝ, ((-Complex.I * (t : ℂ)) * smoothMeanOscillation t v) *
        iteratedDeriv N smoothMeanProfile v := by
          rw [hibp]
          congr 1
          apply integral_congr_ae
          filter_upwards with v
          rw [fderiv_apply_one_eq_deriv, smoothMeanOscillation_deriv]
    _ = (Complex.I * (t : ℂ)) *
        ∫ v : ℝ, smoothMeanOscillation t v *
          iteratedDeriv N smoothMeanProfile v := by
          have hmul : (fun v : ℝ =>
              ((-Complex.I * (t : ℂ)) * smoothMeanOscillation t v) *
                iteratedDeriv N smoothMeanProfile v) =
              fun v => (-Complex.I * (t : ℂ)) *
                (smoothMeanOscillation t v * iteratedDeriv N smoothMeanProfile v) := by
            funext v
            ring
          rw [hmul, integral_const_mul]
          ring

private theorem smoothMeanOscillation_iterated_identity (N : ℕ) (t : ℝ) :
    (∫ v : ℝ, smoothMeanOscillation t v *
        iteratedDeriv N smoothMeanProfile v) =
      (Complex.I * (t : ℂ)) ^ N *
        ∫ v : ℝ, smoothMeanOscillation t v * smoothMeanProfile v := by
  induction N with
  | zero => simp [iteratedDeriv_zero]
  | succ N ih =>
      rw [smoothMeanOscillation_ibp N t, ih]
      ring

private theorem smoothMeanOscillation_norm (t v : ℝ) :
    ‖smoothMeanOscillation t v‖ = 1 := by
  rw [smoothMeanOscillation, Complex.norm_exp]
  simp

private theorem smoothMeanOscillation_integral_norm_bound (N : ℕ) (t : ℝ) :
    ‖∫ v : ℝ, smoothMeanOscillation t v *
        iteratedDeriv N smoothMeanProfile v‖ ≤
      ∫ v : ℝ, ‖iteratedDeriv N smoothMeanProfile v‖ := by
  calc
    ‖∫ v : ℝ, smoothMeanOscillation t v *
        iteratedDeriv N smoothMeanProfile v‖ ≤
      ∫ v : ℝ, ‖smoothMeanOscillation t v *
        iteratedDeriv N smoothMeanProfile v‖ :=
      norm_integral_le_integral_norm
        (fun v : ℝ => smoothMeanOscillation t v * iteratedDeriv N smoothMeanProfile v)
    _ = ∫ v : ℝ, ‖iteratedDeriv N smoothMeanProfile v‖ := by
      apply integral_congr_ae
      filter_upwards with v
      rw [norm_mul, smoothMeanOscillation_norm, one_mul]

private theorem smoothMeanOscillation_fourier_decay (N : ℕ) (t : ℝ) :
    ‖∫ v : ℝ, smoothMeanOscillation t v * smoothMeanProfile v‖ ≤
      smoothMeanDecayConstant N / (1 + |t|) ^ N := by
  let A : ℝ := ∫ v : ℝ, ‖smoothMeanProfile v‖
  let B : ℝ := ∫ v : ℝ, ‖iteratedDeriv N smoothMeanProfile v‖
  let D : ℝ := (1 + |t|) ^ N
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  have hDpos : 0 < D := by
    dsimp [D]
    exact pow_pos (by positivity) _
  have hbase := smoothMeanOscillation_integral_norm_bound 0 t
  have htop := smoothMeanOscillation_integral_norm_bound N t
  by_cases hsmall : |t| ≤ 1
  · apply (le_div_iff₀ hDpos).2
    have hDle : D ≤ 2 ^ N := by
      dsimp [D]
      gcongr
      linarith
    have hbase' :
        ‖∫ v : ℝ, smoothMeanOscillation t v * smoothMeanProfile v‖ ≤ A := by
      simpa [A, iteratedDeriv_zero] using hbase
    calc
      ‖∫ v : ℝ, smoothMeanOscillation t v * smoothMeanProfile v‖ * D ≤ A * D :=
        mul_le_mul_of_nonneg_right hbase' (le_of_lt hDpos)
      _ ≤ A * 2 ^ N := mul_le_mul_of_nonneg_left hDle hA0
      _ ≤ 2 ^ N * (A + B) := by
        have hpow : 0 ≤ (2 : ℝ) ^ N := pow_nonneg (by norm_num) _
        nlinarith
      _ = smoothMeanDecayConstant N := by
        simp [smoothMeanDecayConstant, A, B]
  · have hlarge : 1 ≤ |t| := le_of_not_ge hsmall
    have htne : t ≠ 0 := by
      intro ht
      norm_num [ht] at hlarge
    have hpowt : 0 < |t| ^ N := pow_pos (abs_pos.mpr htne) _
    have hratio : D / |t| ^ N ≤ 2 ^ N := by
      apply (div_le_iff₀ hpowt).2
      calc
        D ≤ (2 * |t|) ^ N := by
          dsimp [D]
          gcongr
          linarith
        _ = 2 ^ N * |t| ^ N := by rw [mul_pow]
    have hprod : |t| ^ N *
        ‖∫ v : ℝ, smoothMeanOscillation t v * smoothMeanProfile v‖ ≤ B := by
      have hid := smoothMeanOscillation_iterated_identity N t
      have hnormid :
          ‖∫ v : ℝ, smoothMeanOscillation t v *
              iteratedDeriv N smoothMeanProfile v‖ =
            |t| ^ N *
              ‖∫ v : ℝ, smoothMeanOscillation t v * smoothMeanProfile v‖ := by
        rw [hid, norm_mul, norm_pow]
        simp
      rw [← hnormid]
      exact htop
    apply (le_div_iff₀ hDpos).2
    calc
      ‖∫ v : ℝ, smoothMeanOscillation t v * smoothMeanProfile v‖ * D =
          (D / |t| ^ N) *
            (|t| ^ N *
              ‖∫ v : ℝ, smoothMeanOscillation t v * smoothMeanProfile v‖) := by
        field_simp [ne_of_gt hpowt] <;> ring
      _ ≤ 2 ^ N * B := by
        apply mul_le_mul hratio hprod
        · exact mul_nonneg (pow_nonneg (abs_nonneg t) N)
            (norm_nonneg (∫ v : ℝ,
              smoothMeanOscillation t v * smoothMeanProfile v))
        · exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N
      _ ≤ smoothMeanDecayConstant N := by
        dsimp [smoothMeanDecayConstant, A, B]
        have hpow : 0 ≤ (2 : ℝ) ^ N := pow_nonneg (by norm_num) _
        nlinarith

/-- The Mellin integral of the fixed outer cutoff, with the branch convention
`exp((-1/2-it) log x)` on positive real `x`. -/
noncomputable def smoothMeanMellinIntegral (X t : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ),
    (polynomialOuterCutoff (x / X) : ℂ) *
      Complex.exp ((-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log x : ℂ))

private noncomputable def smoothMeanLogProfile (t v : ℝ) : ℂ :=
  smoothMeanProfile v * smoothMeanOscillation t v

private theorem smoothMeanMellinLogChange (t : ℝ) :
    (∫ x in Ioi (0 : ℝ), (polynomialOuterCutoff x : ℂ) *
      Complex.exp ((-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log x : ℂ))) =
    ∫ v : ℝ, smoothMeanLogProfile t v := by
  let s : ℂ := -(1 / 2 : ℂ) - Complex.I * (t : ℂ)
  have hpoint (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      (x⁻¹ : ℝ) • smoothMeanLogProfile t (Real.log x) =
        (polynomialOuterCutoff x : ℂ) * Complex.exp (s * (Real.log x : ℂ)) := by
    have hxpos : 0 < x := hx
    have hinv : x⁻¹ = Real.exp (-(Real.log x)) := by
      calc
        x⁻¹ = (Real.exp (Real.log x))⁻¹ := by rw [Real.exp_log hxpos]
        _ = Real.exp (-(Real.log x)) := by rw [Real.exp_neg]
    have hcoeffReal : x⁻¹ * Real.exp (Real.log x / 2) =
        Real.exp (-(Real.log x) / 2) := by
      calc
        x⁻¹ * Real.exp (Real.log x / 2) =
            Real.exp (-(Real.log x)) * Real.exp (Real.log x / 2) := by rw [hinv]
        _ = Real.exp (-(Real.log x) + Real.log x / 2) := by rw [← Real.exp_add]
        _ = Real.exp (-(Real.log x) / 2) := by congr 1 <;> ring
    have hcoeff : (x⁻¹ : ℂ) * Complex.exp ((Real.log x / 2 : ℝ) : ℂ) =
        Complex.exp ((-(Real.log x) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, ← Complex.ofReal_exp]
      exact_mod_cast hcoeffReal
    calc
      (x⁻¹ : ℝ) • smoothMeanLogProfile t (Real.log x) =
          ((x⁻¹ : ℂ) * Complex.exp ((Real.log x / 2 : ℝ) : ℂ)) *
            (polynomialOuterCutoff x : ℂ) *
              Complex.exp (-((Real.log x : ℂ) * (Complex.I * (t : ℂ)))) := by
        simp [smoothMeanLogProfile, smoothMeanProfile, smoothMeanOscillation,
          smul_eq_mul, Complex.ofReal_exp, Real.exp_log hxpos]
        ring
      _ = Complex.exp ((-(Real.log x) / 2 : ℝ) : ℂ) *
          (polynomialOuterCutoff x : ℂ) *
            Complex.exp (-((Real.log x : ℂ) * (Complex.I * (t : ℂ)))) := by
        rw [hcoeff]
      _ = (polynomialOuterCutoff x : ℂ) *
          Complex.exp (s * (Real.log x : ℂ)) := by
        calc
          _ = (polynomialOuterCutoff x : ℂ) *
              (Complex.exp ((-(Real.log x) / 2 : ℝ) : ℂ) *
                Complex.exp (-((Real.log x : ℂ) * (Complex.I * (t : ℂ))))) := by ring
          _ = (polynomialOuterCutoff x : ℂ) *
              Complex.exp (((-(Real.log x) / 2 : ℝ) : ℂ) -
                (Real.log x : ℂ) * (Complex.I * (t : ℂ))) := by
              rw [← Complex.exp_add]
              congr 2
          _ = (polynomialOuterCutoff x : ℂ) *
              Complex.exp (s * (Real.log x : ℂ)) := by
              congr 2
              dsimp [s]
              push_cast
              ring
  calc
    (∫ x in Ioi (0 : ℝ), (polynomialOuterCutoff x : ℂ) *
        Complex.exp ((-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log x : ℂ))) =
      ∫ x in Ioi (0 : ℝ), x⁻¹ • smoothMeanLogProfile t (Real.log x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simpa [s] using (hpoint x hx).symm
    _ = ∫ v : ℝ, smoothMeanLogProfile t v :=
      integral_comp_log_Ioi_zero (smoothMeanLogProfile t)

private theorem smoothMeanMellinScaleChange (X t : ℝ) (hX : 0 < X) :
    smoothMeanMellinIntegral X t =
      Complex.exp (((1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ)) *
        ∫ v : ℝ, smoothMeanLogProfile t v := by
  let s : ℂ := -(1 / 2 : ℂ) - Complex.I * (t : ℂ)
  let G : ℝ → ℂ := fun y =>
    (polynomialOuterCutoff y : ℂ) *
      Complex.exp (s * ((Real.log X : ℂ) + (Real.log y : ℂ)))
  have hpoint (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      (polynomialOuterCutoff (x / X) : ℂ) *
          Complex.exp (s * (Real.log x : ℂ)) = G (X⁻¹ * x) := by
    have hxpos : 0 < x := hx
    have hypos : 0 < X⁻¹ * x := mul_pos (inv_pos.mpr hX) hxpos
    have hdiv : x / X = X⁻¹ * x := by field_simp [ne_of_gt hX]
    have hmul : X * (X⁻¹ * x) = x := by field_simp [ne_of_gt hX]
    have hlog : Real.log x = Real.log X + Real.log (X⁻¹ * x) := by
      rw [← Real.log_mul (ne_of_gt hX) (ne_of_gt hypos), hmul]
    simp [G, s, hdiv, hlog]
  have hscale : smoothMeanMellinIntegral X t =
      (X : ℂ) * ∫ y in Ioi (0 : ℝ), G y := by
    unfold smoothMeanMellinIntegral
    calc
      (∫ x in Ioi (0 : ℝ),
          (polynomialOuterCutoff (x / X) : ℂ) *
            Complex.exp (s * (Real.log x : ℂ))) =
        ∫ x in Ioi (0 : ℝ), G (X⁻¹ * x) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          exact hpoint x hx
      _ = (X⁻¹)⁻¹ • ∫ y in Ioi (X⁻¹ * 0), G y :=
        integral_comp_mul_left_Ioi G 0 (inv_pos.mpr hX)
      _ = (X : ℂ) * ∫ y in Ioi (0 : ℝ), G y := by
        simp [smul_eq_mul, inv_inv, mul_zero]
  have hGpoint (y : ℝ) :
      G y = Complex.exp (s * (Real.log X : ℂ)) *
        ((polynomialOuterCutoff y : ℂ) *
          Complex.exp (s * (Real.log y : ℂ))) := by
    dsimp [G]
    rw [mul_add, Complex.exp_add]
    ring
  have hGint : (∫ y in Ioi (0 : ℝ), G y) =
      Complex.exp (s * (Real.log X : ℂ)) *
        ∫ y in Ioi (0 : ℝ),
          (polynomialOuterCutoff y : ℂ) * Complex.exp (s * (Real.log y : ℂ)) := by
    rw [show (fun y : ℝ => G y) = fun y => Complex.exp (s * (Real.log X : ℂ)) *
        ((polynomialOuterCutoff y : ℂ) * Complex.exp (s * (Real.log y : ℂ))) by
          funext y
          exact hGpoint y,
      integral_const_mul]
  have hXexp : (X : ℂ) = Complex.exp (Real.log X : ℂ) := by
    calc
      (X : ℂ) = (Real.exp (Real.log X) : ℂ) := by rw [Real.exp_log hX]
      _ = Complex.exp (Real.log X : ℂ) := Complex.ofReal_exp _
  calc
    smoothMeanMellinIntegral X t = (X : ℂ) * ∫ y in Ioi (0 : ℝ), G y := hscale
    _ = Complex.exp (((1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ)) *
        ∫ y in Ioi (0 : ℝ),
          (polynomialOuterCutoff y : ℂ) * Complex.exp (s * (Real.log y : ℂ)) := by
      rw [hGint, hXexp]
      calc
        Complex.exp (Real.log X : ℂ) *
            (Complex.exp (s * (Real.log X : ℂ)) *
              ∫ y in Ioi (0 : ℝ),
                (polynomialOuterCutoff y : ℂ) * Complex.exp (s * (Real.log y : ℂ))) =
          (Complex.exp (Real.log X : ℂ) *
            Complex.exp (s * (Real.log X : ℂ))) *
              ∫ y in Ioi (0 : ℝ),
                (polynomialOuterCutoff y : ℂ) * Complex.exp (s * (Real.log y : ℂ)) := by ring
        _ = Complex.exp (Real.log X + s * (Real.log X : ℂ)) *
              ∫ y in Ioi (0 : ℝ),
                (polynomialOuterCutoff y : ℂ) * Complex.exp (s * (Real.log y : ℂ)) := by
          rw [← Complex.exp_add]
        _ = Complex.exp (((1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ)) *
              ∫ y in Ioi (0 : ℝ),
                (polynomialOuterCutoff y : ℂ) * Complex.exp (s * (Real.log y : ℂ)) := by
          have harg : Real.log X + s * (Real.log X : ℂ) =
              ((1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ) := by
            dsimp [s]
            push_cast
            ring
          rw [harg]
    _ = Complex.exp (((1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ)) *
        ∫ v : ℝ, smoothMeanLogProfile t v := by
      rw [← smoothMeanMellinLogChange t]

theorem smoothMeanMellinDecay (N : ℕ) (X t : ℝ) (hX : 0 < X) :
    ‖smoothMeanMellinIntegral X t‖ ≤
      Real.sqrt X * smoothMeanDecayConstant N * ((1 + |t|) ^ N)⁻¹ := by
  rw [smoothMeanMellinScaleChange X t hX]
  have hnormX :
      ‖Complex.exp (((1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ))‖ =
        Real.sqrt X := by
    rw [Complex.norm_exp]
    have hre : (((1 / 2 : ℂ) - Complex.I * (t : ℂ)) *
        (Real.log X : ℂ)).re = (1 / 2 : ℝ) * Real.log X := by simp
    rw [hre]
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX]
    congr 1
    ring
  have hcomm :
      (∫ v : ℝ, smoothMeanProfile v * smoothMeanOscillation t v) =
        ∫ v : ℝ, smoothMeanOscillation t v * smoothMeanProfile v := by
    apply integral_congr_ae
    filter_upwards with v
    ring
  have hdecay : ‖∫ v : ℝ, smoothMeanLogProfile t v‖ ≤
      smoothMeanDecayConstant N / (1 + |t|) ^ N := by
    change ‖∫ v : ℝ, smoothMeanProfile v * smoothMeanOscillation t v‖ ≤ _
    rw [hcomm]
    exact smoothMeanOscillation_fourier_decay N t
  calc
    ‖Complex.exp (((1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ)) *
        ∫ v : ℝ, smoothMeanLogProfile t v‖ =
      ‖Complex.exp (((1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ))‖ *
        ‖∫ v : ℝ, smoothMeanLogProfile t v‖ := norm_mul _ _
    _ = Real.sqrt X * ‖∫ v : ℝ, smoothMeanLogProfile t v‖ := by rw [hnormX]
    _ ≤ Real.sqrt X *
        (smoothMeanDecayConstant N / (1 + |t|) ^ N) := by
      exact mul_le_mul_of_nonneg_left hdecay (Real.sqrt_nonneg X)
    _ = Real.sqrt X * smoothMeanDecayConstant N * ((1 + |t|) ^ N)⁻¹ := by ring

#print axioms smoothMeanMellinDecay

end FractionalPrimes.Literature.Polynomial
