module

public import FractionalPrimes.Literature.Polynomial.SmoothedMellinIdentity
public import FractionalPrimes.Literature.Polynomial.NormalizedWindowKernelBounds
public import FractionalPrimes.Literature.Polynomial.PolynomialDirichletMeanEnvelope
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open MeasureTheory
open intervalIntegral
open scoped FourierTransform
open scoped BigOperators

/-- The finite Dirichlet polynomial obeys the source's uniform bound on the
coefficient support. -/
theorem mellinWindowData_A_X_norm_le
    (rho : ℝ → ℝ) (X H B : ℝ) (a : ℕ → ℂ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X) (hB : 0 ≤ B)
    (hsupport : ∀ n, 0 < n → a n ≠ 0 →
      X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X)
    (hbound : ∀ n, 0 < n → ‖a n‖ ≤ B) (t : ℝ) :
    ‖(mellinWindowData rho X H B a hX hH hHX hB hsupport hbound).A_X t‖ ≤
      5 * B * Real.sqrt X := by
  let w := mellinWindowData rho X H B a hX hH hHX hB hsupport hbound
  let S := mellinWindowSupportIndices X
  have hXpos : 0 < X := by linarith
  have hX2pos : 0 < X / 2 := by positivity
  have hmono (n : ℕ) (hn : n ∈ S) :
      ‖a n * mellinDirichletMonomial n t‖ ≤ B * Real.sqrt (2 / X) := by
    have hmem := (mellinIntervalIndices_mem_iff (by positivity : 0 ≤ X / 2) n).1 hn
    have hnreal : 0 < (n : ℝ) := lt_trans hX2pos hmem.1
    have hnpos : 0 < n := by exact_mod_cast hnreal
    have hcoeff : ‖a n‖ ≤ B := hbound n hnpos
    have hmonomial : ‖mellinDirichletMonomial n t‖ =
        Real.rpow (n : ℝ) (-1 / 2 : ℝ) := by
      calc
        ‖mellinDirichletMonomial n t‖ =
            Real.exp (-Real.log (n : ℝ) / 2) := by
              rw [mellinDirichletMonomial, Complex.norm_exp]
              have hre :
                  ((((-1 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I) *
                    ((Real.log (n : ℝ) : ℝ) : ℂ)).re =
                    -Real.log (n : ℝ) / 2 := by
                simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
                  Complex.ofReal_im, Complex.I_re, Complex.I_im]
                ring
              rw [hre]
        _ = Real.rpow (n : ℝ) (-1 / 2 : ℝ) := by
          have hdef := Real.rpow_def_of_pos hnreal (-1 / 2 : ℝ)
          calc
            Real.exp (-Real.log (n : ℝ) / 2) =
                Real.exp (Real.log (n : ℝ) * (-1 / 2 : ℝ)) := by
                  congr 1
                  ring
            _ = Real.rpow (n : ℝ) (-1 / 2 : ℝ) := hdef.symm
    have hrpow : Real.rpow (n : ℝ) (-1 / 2 : ℝ) ≤
        Real.rpow (X / 2) (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hX2pos hmem.1.le (by norm_num)
    have htarget : Real.rpow (X / 2) (-1 / 2 : ℝ) = Real.sqrt (2 / X) := by
      have hpow : Real.rpow (X / 2) (-1 / 2 : ℝ) =
          (Real.sqrt (X / 2))⁻¹ := by
        change (X / 2) ^ (-1 / 2 : ℝ) = (Real.sqrt (X / 2))⁻¹
        calc
          (X / 2) ^ (-1 / 2 : ℝ) = (X / 2) ^ (-(1 / 2 : ℝ)) := by
            congr 1
            ring
          _ = ((X / 2) ^ (1 / 2 : ℝ))⁻¹ :=
            Real.rpow_neg hX2pos.le (1 / 2 : ℝ)
          _ = (Real.sqrt (X / 2))⁻¹ := by rw [← Real.sqrt_eq_rpow]
      rw [hpow, Real.sqrt_div (by norm_num : 0 ≤ (2 : ℝ)),
        Real.sqrt_div hXpos.le]
      have hrootX : Real.sqrt X ≠ 0 := (Real.sqrt_pos.2 hXpos).ne'
      have hroot2 : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
      field_simp [hrootX, hroot2]
    rw [norm_mul, hmonomial]
    calc
      ‖a n‖ * Real.rpow (n : ℝ) (-1 / 2 : ℝ) ≤
          B * Real.rpow (n : ℝ) (-1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hnreal.le _)
      _ ≤ B * Real.rpow (X / 2) (-1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hrpow hB
      _ = B * Real.sqrt (2 / X) := by rw [htarget]
  have hsum :
      ‖(mellinWindowData rho X H B a hX hH hHX hB hsupport hbound).A_X t‖ ≤
        ∑ n ∈ S, B * Real.sqrt (2 / X) := by
    dsimp [mellinWindowData, S]
    calc
      ‖∑ n ∈ mellinWindowSupportIndices X, a n * mellinDirichletMonomial n t‖ ≤
          ∑ n ∈ mellinWindowSupportIndices X,
            ‖a n * mellinDirichletMonomial n t‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ mellinWindowSupportIndices X, B * Real.sqrt (2 / X) :=
        Finset.sum_le_sum fun n hn => hmono n hn
  have hcard : ((S.card : ℝ)) ≤ 3 * X := by
    dsimp [S, w]
    exact mellinWindowSupportIndices_card_le
      (mellinWindowData rho X H B a hX hH hHX hB hsupport hbound)
  have hsqrt : Real.sqrt (2 / X) ≤ 5 * Real.sqrt X / (3 * X) := by
    have hratio : 0 ≤ 2 / X := by positivity
    have hsqrtX : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
    have hy : 0 ≤ Real.sqrt (2 / X) := Real.sqrt_nonneg _
    have hRHS : 0 ≤ 5 * Real.sqrt X / (3 * X) := by positivity
    apply (sq_le_sq₀ hy hRHS).mp
    have hRHSsq : (5 * Real.sqrt X / (3 * X)) ^ 2 = 25 / (9 * X) := by
      calc
        (5 * Real.sqrt X / (3 * X)) ^ 2 =
            ((5 : ℝ) ^ 2 * (Real.sqrt X) ^ 2) /
              ((3 : ℝ) ^ 2 * X ^ 2) := by rw [div_pow, mul_pow, mul_pow]
        _ = 25 / (9 * X) := by
          rw [Real.sq_sqrt hXpos.le]
          norm_num
          field_simp [hXpos.ne']
    rw [Real.sq_sqrt hratio, hRHSsq]
    have hcmp : 2 / X ≤ 25 / (9 * X) := by
      apply (div_le_div_iff₀ hXpos (by positivity : 0 < 9 * X)).2
      nlinarith
    exact hcmp
  have hsumcard :
      (∑ n ∈ S, B * Real.sqrt (2 / X)) ≤ 3 * X * (B * Real.sqrt (2 / X)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  calc
    ‖(mellinWindowData rho X H B a hX hH hHX hB hsupport hbound).A_X t‖ ≤
        ∑ n ∈ S, B * Real.sqrt (2 / X) := hsum
    _ ≤ 3 * X * (B * Real.sqrt (2 / X)) := hsumcard
    _ = 3 * X * B * Real.sqrt (2 / X) := by ring
    _ ≤ 3 * X * B * (5 * Real.sqrt X / (3 * X)) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = 5 * B * Real.sqrt X := by
      field_simp [hXpos.ne']

private theorem shortLong_squareWindow_le_sqrt
    {X W : ℝ} (hX : 3 ≤ X) (hW : 2 ≤ W)
    (hWX : W ≤ Real.rpow X (1 / 100 : ℝ)) :
    W ^ 2 ≤ Real.sqrt X := by
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hWnonneg : 0 ≤ W := by linarith
  have hpow : W ^ 2 ≤ (Real.rpow X (1 / 100 : ℝ)) ^ 2 := by
    gcongr
  have hpow' : (Real.rpow X (1 / 100 : ℝ)) ^ 2 =
      Real.rpow X (1 / 50 : ℝ) := by
    calc
      (Real.rpow X (1 / 100 : ℝ)) ^ 2 =
          (Real.rpow X (1 / 100 : ℝ)) ^ (2 : ℝ) :=
        (Real.rpow_natCast (Real.rpow X (1 / 100 : ℝ)) 2).symm
      _ = Real.rpow X ((1 / 100 : ℝ) * 2) :=
        (Real.rpow_mul hXpos.le (1 / 100 : ℝ) 2).symm
      _ = Real.rpow X (1 / 50 : ℝ) := by congr 1 <;> norm_num
  have hexp : (1 / 50 : ℝ) ≤ 1 / 2 := by norm_num
  calc
    W ^ 2 ≤ (Real.rpow X (1 / 100 : ℝ)) ^ 2 := hpow
    _ = Real.rpow X (1 / 50 : ℝ) := hpow'
    _ ≤ Real.rpow X (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hXone hexp
    _ = Real.sqrt X := (Real.sqrt_eq_rpow X).symm

private theorem shortLong_normalizedKernel_continuous
    (X H : ℝ) (hH : 0 < H) :
    Continuous (fun t : ℝ => normalizedMellinWindowKernel X H t) := by
  have hnum : Continuous (fun t : ℝ =>
      mellinHalfItPower (X + H) t - mellinHalfItPower X t) := by
    unfold mellinHalfItPower
    fun_prop
  have hden : Continuous (fun t : ℝ =>
      (H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    fun_prop
  have hden_ne (t : ℝ) :
      (H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast hH.ne'
    · exact mellinWindowDenominator_ne_zero t
  unfold normalizedMellinWindowKernel
  exact hnum.div₀ hden hden_ne

private theorem shortLong_angularFourier_continuous :
    Continuous FractionalPrimes.polynomialKernelRhoAngularFourier := by
  have hFourierEval : Continuous (fun t : ℝ =>
      𝓕 polynomialKernelRhoComplexSchwartz
        (t / (2 * Real.pi))) := by
    fun_prop
  apply hFourierEval.congr
  intro t
  exact (polynomialKernelRhoAngularFourier_eq_fourier t).symm

private theorem shortLong_absTail_eq_union
    {W U : ℝ} (hW : 0 < W) :
    {t : ℝ | W ≤ |t| ∧ |t| ≤ U} =
      Set.Icc W U ∪ Set.Icc (-U) (-W) := by
  ext t
  constructor
  · intro ht
    change W ≤ |t| ∧ |t| ≤ U at ht
    by_cases ht0 : 0 ≤ t
    · apply Set.mem_union_left
      apply Set.mem_Icc.mpr
      rw [abs_of_nonneg ht0] at ht
      exact ht
    · have htneg : t < 0 := lt_of_not_ge ht0
      apply Set.mem_union_right
      apply Set.mem_Icc.mpr
      rw [abs_of_neg htneg] at ht
      constructor <;> linarith [ht.1, ht.2]
  · intro ht
    simp only [Set.mem_union] at ht
    rcases ht with hp | hn
    · have hp' := Set.mem_Icc.mp hp
      have ht0 : 0 ≤ t := le_trans (le_of_lt hW) hp'.1
      change W ≤ |t| ∧ |t| ≤ U
      rw [abs_of_nonneg ht0]
      exact hp'
    · have hn' := Set.mem_Icc.mp hn
      have ht0 : t < 0 := lt_of_le_of_lt hn'.2 (neg_neg_of_pos hW)
      change W ≤ |t| ∧ |t| ≤ U
      rw [abs_of_neg ht0]
      constructor <;> linarith [hn'.1, hn'.2]

private theorem shortLong_sqrt_kernel_identity {X : ℝ} (hX : 0 < X) :
    Real.sqrt X * Real.rpow X (-3 / 2 : ℝ) = 1 / X := by
  rw [Real.sqrt_eq_rpow]
  change X ^ (1 / 2 : ℝ) * X ^ (-3 / 2 : ℝ) = 1 / X
  calc
    X ^ (1 / 2 : ℝ) * X ^ (-3 / 2 : ℝ) =
        X ^ ((1 / 2 : ℝ) + (-3 / 2 : ℝ)) :=
      (Real.rpow_add hX (1 / 2 : ℝ) (-3 / 2 : ℝ)).symm
    _ = X ^ (-1 : ℝ) := by congr 1 <;> ring
    _ = X ^ (-(1 : ℝ)) := by congr 1 <;> ring
    _ = (X ^ (1 : ℝ))⁻¹ := Real.rpow_neg hX.le (1 : ℝ)
    _ = 1 / X := by rw [Real.rpow_one]; simp [one_div]

set_option maxHeartbeats 1000000 in
/-- The bounded-coefficient short-to-long transfer, with the exact source
constant `Cρ = 128 (1 + M₁)`. -/
theorem shortLongTransferBoundedCoefficients
    (X W H1 H2 B : ℝ) (a : ℕ → ℂ)
    (hX : 3 ≤ X) (hW : 2 ≤ W)
    (hWX : W ≤ Real.rpow X (1 / 100 : ℝ))
    (hH1 : Real.rpow X (1 / 2 : ℝ) ≤ H1)
    (hH12 : H1 ≤ H2) (hH2 : H2 ≤ X / W ^ 4)
    (hB : 0 ≤ B)
    (hsupport : ∀ n, 0 < n → a n ≠ 0 →
      X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X)
    (hbound : ∀ n, 0 < n → ‖a n‖ ≤ B) :
    let w1 := mellinWindowData FractionalPrimes.polynomialKernelRho
      X H1 B a hX (by
        have hx : 0 < X := by linarith [hX]
        exact lt_of_lt_of_le (Real.rpow_pos_of_pos hx _) hH1) (by
        have hWsq : 1 ≤ W ^ 2 := by nlinarith [sq_nonneg (W - 2)]
        have hW4 : 1 ≤ W ^ 4 := by
          calc
            1 = 1 * 1 := by ring
            _ ≤ W ^ 2 * W ^ 2 := mul_le_mul hWsq hWsq (by norm_num) (sq_nonneg W)
            _ = W ^ 4 := by ring
        have hXover : X / W ^ 4 ≤ X := by
          apply (div_le_iff₀ (by positivity : 0 < W ^ 4)).2
          nlinarith [mul_nonneg (by linarith : 0 ≤ X) (sub_nonneg.mpr hW4)]
        exact hH12.trans (hH2.trans hXover)) hB hsupport hbound
    let w2 := mellinWindowData FractionalPrimes.polynomialKernelRho
      X H2 B a hX (by
        have hx : 0 < X := by linarith [hX]
        have hH1pos : 0 < H1 := lt_of_lt_of_le (Real.rpow_pos_of_pos hx _) hH1
        exact lt_of_lt_of_le hH1pos hH12) (by
        have hWsq : 1 ≤ W ^ 2 := by nlinarith [sq_nonneg (W - 2)]
        have hW4 : 1 ≤ W ^ 4 := by
          calc
            1 = 1 * 1 := by ring
            _ ≤ W ^ 2 * W ^ 2 := mul_le_mul hWsq hWsq (by norm_num) (sq_nonneg W)
            _ = W ^ 4 := by ring
        have hXover : X / W ^ 4 ≤ X := by
          apply (div_le_iff₀ (by positivity : 0 < W ^ 4)).2
          nlinarith [mul_nonneg (by linarith : 0 ≤ X) (sub_nonneg.mpr hW4)]
        exact le_trans hH2 hXover) hB hsupport hbound
    let T0 := X / H1
    T0 ≥ W ∧ ‖w1.N_H - w2.N_H‖ ≤
      128 * (1 + FractionalPrimes.polynomialKernelM1) *
        (B / W ^ 2 +
          ((1 + Real.log W) / Real.sqrt X) *
            dirichletMeanEnvelope w1 T0 W) := by
  let hH1pos : 0 < H1 := by
    have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.2 (by linarith [hX])
    have hsqrtEq : Real.sqrt X = Real.rpow X (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow X
    rw [hsqrtEq] at hsqrt
    exact lt_of_lt_of_le hsqrt hH1
  let hH2pos : 0 < H2 := lt_of_lt_of_le hH1pos hH12
  let hXpos : 0 < X := by linarith [hX]
  let hWpos : 0 < W := by linarith [hW]
  let hW2sqrt := shortLong_squareWindow_le_sqrt hX hW hWX
  let hsqrtEq : Real.sqrt X = Real.rpow X (1 / 2 : ℝ) := Real.sqrt_eq_rpow X
  have hH1sqrt : Real.sqrt X ≤ H1 := by rw [hsqrtEq]; exact hH1
  have hW2H1 : W ^ 2 ≤ H1 := le_trans hW2sqrt hH1sqrt
  have hWsq : 1 ≤ W ^ 2 := by nlinarith [sq_nonneg (W - 2)]
  have hW4 : 1 ≤ W ^ 4 := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ W ^ 2 * W ^ 2 := mul_le_mul hWsq hWsq (by norm_num) (sq_nonneg W)
      _ = W ^ 4 := by ring
  have hW4pos : 0 < W ^ 4 := by positivity
  have hW2pos : 0 < W ^ 2 := by positivity
  have hW2pow : W ^ 2 ≤ W ^ 4 := by
    calc
      W ^ 2 = W ^ 2 * 1 := by ring
      _ ≤ W ^ 2 * W ^ 2 := mul_le_mul_of_nonneg_left
        (by nlinarith [hW]) (by positivity)
      _ = W ^ 4 := by ring
  have hInvPow : 1 / W ^ 4 ≤ 1 / W ^ 2 := by
    apply (div_le_div_iff₀ hW4pos hW2pos).2
    simpa using hW2pow
  have hXover : X / W ^ 4 ≤ X := by
    apply (div_le_iff₀ hW4pos).2
    nlinarith [mul_nonneg hXpos.le (sub_nonneg.mpr hW4)]
  have hH2X : H2 ≤ X := le_trans hH2 hXover
  have hH1X : H1 ≤ X := le_trans hH12 hH2X
  let w1 : MellinWindowData := mellinWindowData
    FractionalPrimes.polynomialKernelRho X H1 B a hX hH1pos hH1X hB hsupport hbound
  let w2 : MellinWindowData := mellinWindowData
    FractionalPrimes.polynomialKernelRho X H2 B a hX hH2pos hH2X hB hsupport hbound
  let T0 : ℝ := X / H1
  let T : ℝ := T0 * W ^ 4
  let I : Set ℝ := Set.Icc (-T) T
  let L : Set ℝ := Set.Icc (-W) W
  let Q : Set ℝ := I \ L
  let E : Set ℝ := {t : ℝ | W ≤ |t| ∧ |t| ≤ T}
  let F : ℝ → ℂ := fun t =>
    FractionalPrimes.polynomialKernelRhoAngularFourier (t / T)
  let f1 : ℝ → ℂ := fun t => w1.A_X t * w1.K_H t * F t
  let f2 : ℝ → ℂ := fun t => w2.A_X t * w2.K_H t * F t
  let f : ℝ → ℂ := fun t => w1.A_X t * (w1.K_H t - w2.K_H t) * F t
  let g : ℝ → ℝ := fun t => ‖f t‖
  let m : ℝ → ℝ := fun t =>
    ‖w1.A_X t‖ * min 1 (T0 / |t|)
  have hT0pos : 0 < T0 := by dsimp [T0]; positivity
  have hT0W4 : W ^ 4 ≤ T0 := by
    dsimp [T0]
    apply (le_div_iff₀ hH1pos).2
    calc
      W ^ 4 * H1 ≤ W ^ 4 * H2 := mul_le_mul_of_nonneg_left hH12 (by positivity)
      _ = H2 * W ^ 4 := by ring
      _ ≤ X := (le_div_iff₀ hW4pos).1 hH2
  have hWleW4 : W ≤ W ^ 4 := by nlinarith [hW]
  have hT0W : W ≤ T0 := le_trans hWleW4 hT0W4
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hTW : W ≤ T := by
    dsimp [T]
    have hT0nonneg : 0 ≤ T0 := le_of_lt hT0pos
    have hW4one : 1 ≤ W ^ 4 := hW4
    nlinarith [mul_nonneg hT0nonneg (sub_nonneg.mpr hW4one), hT0W]
  have hT0cap : T0 ≤ T0 * W ^ 4 := by
    nlinarith [mul_nonneg (le_of_lt hT0pos) (sub_nonneg.mpr hW4)]
  have hAcont : Continuous w1.A_X := by
    simpa [w1] using mellinWindowData_A_X_continuous
      FractionalPrimes.polynomialKernelRho X H1 B a hX hH1pos hH1X hB hsupport hbound
  have hDnonneg : 0 ≤ dirichletMeanEnvelope w1 T0 W := by
    obtain ⟨Umax, hUmax, hmaxval, hmax⟩ :=
      dirichletMeanEnvelope_hasMaximum w1 hAcont hW hT0W
    have hTailnonneg : 0 ≤ dirichletAbsoluteTailIntegral w1 W T0 := by
      rw [dirichletAbsoluteTailIntegral_eq_intervalIntegrals w1 hAcont hWpos hT0W]
      exact add_nonneg
        (intervalIntegral.integral_nonneg hT0W (fun t _ => norm_nonneg (w1.A_X t)))
        (intervalIntegral.integral_nonneg (by linarith) (fun t _ => norm_nonneg (w1.A_X t)))
    have hObj : dirichletMeanEnvelopeObjective w1 T0 W T0 =
        dirichletAbsoluteTailIntegral w1 W T0 := by
      simp [dirichletMeanEnvelopeObjective, div_self hT0pos.ne']
    have hT0mem : T0 ∈ Set.Icc T0 (T0 * W ^ 4) := ⟨le_rfl, hT0cap⟩
    calc
      0 ≤ dirichletAbsoluteTailIntegral w1 W T0 := hTailnonneg
      _ = dirichletMeanEnvelopeObjective w1 T0 W T0 := hObj.symm
      _ ≤ dirichletMeanEnvelope w1 T0 W := hmax T0 hT0mem
  have hM1nonneg : 0 ≤ FractionalPrimes.polynomialKernelM1 := by
    unfold FractionalPrimes.polynomialKernelM1
    exact integral_nonneg fun u =>
      mul_nonneg (abs_nonneg u) (FractionalPrimes.polynomialKernelRho_nonneg u)
  have hkernelCont1 : Continuous (fun t : ℝ => w1.K_H t) := by
    change Continuous (fun t : ℝ => normalizedMellinWindowKernel X H1 t)
    exact shortLong_normalizedKernel_continuous X H1 hH1pos
  have hkernelCont2 : Continuous (fun t : ℝ => w2.K_H t) := by
    change Continuous (fun t : ℝ => normalizedMellinWindowKernel X H2 t)
    exact shortLong_normalizedKernel_continuous X H2 hH2pos
  have hFourierCont : Continuous F := by
    dsimp [F]
    exact shortLong_angularFourier_continuous.comp (by fun_prop)
  have hAeq : w1.A_X = w2.A_X := by
    funext t
    rfl
  have hf1cont : Continuous f1 := by
    dsimp [f1]
    exact (hAcont.mul hkernelCont1).mul hFourierCont
  have hf2cont : Continuous f2 := by
    dsimp [f2]
    exact (hAcont.mul hkernelCont2).mul hFourierCont
  have hfcont : Continuous f := by
    dsimp [f]
    exact (hAcont.mul (hkernelCont1.sub hkernelCont2)).mul hFourierCont
  have hgcont : Continuous g := by
    dsimp [g]
    exact continuous_norm.comp hfcont
  have hIcompact : IsCompact I := by simpa [I] using isCompact_Icc
  have hImeas : MeasurableSet I := hIcompact.isClosed.measurableSet
  have hIntgI : IntegrableOn g I := hgcont.continuousOn.integrableOn_compact hIcompact
  have hIntf1 : IntegrableOn f1 I := hf1cont.continuousOn.integrableOn_compact hIcompact
  have hIntf2 : IntegrableOn f2 I := hf2cont.continuousOn.integrableOn_compact hIcompact
  have hLsubsetI : L ⊆ I := by
    exact Set.Icc_subset_Icc (by linarith [hTW]) (by linarith [hTW])
  have hIunion : I = L ∪ Q := by
    ext t
    constructor
    · intro ht
      by_cases hLt : t ∈ L
      · exact Or.inl hLt
      · exact Or.inr ⟨ht, hLt⟩
    · intro ht
      rcases ht with hLt | hQt
      · exact hLsubsetI hLt
      · exact hQt.1
  have hLQdisjoint : Disjoint L Q := by
    rw [Set.disjoint_left]
    intro t htL htQ
    exact htQ.2 htL
  have hLmeas : MeasurableSet L := measurableSet_Icc
  have hQmeas : MeasurableSet Q := measurableSet_Icc.diff measurableSet_Icc
  have hIntgL : IntegrableOn g L := hIntgI.mono_set hLsubsetI
  have hQsubsetI : Q ⊆ I := by
    intro t ht
    exact ht.1
  have hIntgQ : IntegrableOn g Q := hIntgI.mono_set hQsubsetI
  have hsplit :
      (∫ t in I, g t) = (∫ t in L, g t) + (∫ t in Q, g t) := by
    rw [hIunion, setIntegral_union hLQdisjoint hQmeas hIntgL hIntgQ]
  have hAlim := mellinWindowData_A_X_norm_le
    FractionalPrimes.polynomialKernelRho X H1 B a hX hH1pos hH1X hB hsupport hbound
  have hH2ratio : H2 / X ≤ 1 / W ^ 4 := by
    apply (div_le_div_iff₀ hXpos hW4pos).2
    calc
      H2 * W ^ 4 ≤ X := (le_div_iff₀ hW4pos).1 hH2
      _ = 1 * X := by ring
  have hScale := shortLong_sqrt_kernel_identity hXpos
  have hLowPoint (t : ℝ) (ht : t ∈ L) :
      g t ≤ (5 * B / W ^ 4) * (1 + W) := by
    have habs : |t| ≤ W := abs_le.mpr (Set.mem_Icc.mp ht)
    have hwin := normalizedWindowKernelBounds X H1 H2 t hXpos hH1pos hH12 hH2X
    rcases hwin with ⟨_, _, _, _, hsm, _⟩
    have hKsm : ‖w1.K_H t - w2.K_H t‖ ≤
        H2 * ((1 + |t|) * X ^ ((-3 / 2 : ℝ))) := by
      rw [mellinWindowData_K_H_eq_normalized
        FractionalPrimes.polynomialKernelRho X H1 B a hX hH1pos hH1X hB
        hsupport hbound t,
        mellinWindowData_K_H_eq_normalized
        FractionalPrimes.polynomialKernelRho X H2 B a hX hH2pos hH2X hB
        hsupport hbound t]
      exact hsm
    have hFbound : ‖F t‖ ≤ 1 := by
      dsimp [F]
      exact FractionalPrimes.polynomialKernelRhoAngularFourier_norm_le_one _
    have hprod :
        ‖w1.A_X t‖ * ‖w1.K_H t - w2.K_H t‖ ≤
          (5 * B * Real.sqrt X) * (H2 * ((1 + |t|) * X ^ ((-3 / 2 : ℝ)))) := by
      exact mul_le_mul (hAlim t) hKsm (norm_nonneg _) (by positivity)
    have hprodF :
        ‖w1.A_X t‖ * ‖w1.K_H t - w2.K_H t‖ * ‖F t‖ ≤
          (5 * B * Real.sqrt X) * (H2 * ((1 + |t|) * X ^ ((-3 / 2 : ℝ)))) := by
      calc
        _ ≤ ((5 * B * Real.sqrt X) *
              (H2 * ((1 + |t|) * X ^ ((-3 / 2 : ℝ)))) * ‖F t‖) :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
        _ ≤ (5 * B * Real.sqrt X) *
              (H2 * ((1 + |t|) * X ^ ((-3 / 2 : ℝ)))) * 1 :=
          mul_le_mul_of_nonneg_left hFbound (by positivity)
        _ = _ := by ring
    have hfactor :
        (5 * B * Real.sqrt X) * (H2 * ((1 + |t|) * X ^ ((-3 / 2 : ℝ)))) =
          (5 * B * (H2 / X)) * (1 + |t|) := by
      calc
        _ = (5 * B * H2 * (1 + |t|)) *
              (Real.sqrt X * X ^ ((-3 / 2 : ℝ))) := by ring
        _ = (5 * B * H2 * (1 + |t|)) * (1 / X) :=
          congrArg (fun z : ℝ => (5 * B * H2 * (1 + |t|)) * z) hScale
        _ = (5 * B * (H2 / X)) * (1 + |t|) := by ring
    have hcoeff : 5 * B * (H2 / X) ≤ 5 * B / W ^ 4 := by
      calc
        5 * B * (H2 / X) ≤ 5 * B * (1 / W ^ 4) :=
          mul_le_mul_of_nonneg_left hH2ratio (by positivity)
        _ = 5 * B / W ^ 4 := by ring
    have habsbound : 1 + |t| ≤ 1 + W := by linarith
    have hpoint :
        ‖w1.A_X t‖ * ‖w1.K_H t - w2.K_H t‖ * ‖F t‖ = g t := by
      simp [g, f, norm_mul]
    rw [← hpoint]
    calc
      ‖w1.A_X t‖ * ‖w1.K_H t - w2.K_H t‖ * ‖F t‖ ≤
          (5 * B * Real.sqrt X) * (H2 * ((1 + |t|) * X ^ ((-3 / 2 : ℝ)))) := hprodF
      _ = (5 * B * (H2 / X)) * (1 + |t|) := hfactor
      _ ≤ (5 * B / W ^ 4) * (1 + |t|) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ ≤ (5 * B / W ^ 4) * (1 + W) :=
        mul_le_mul_of_nonneg_left habsbound (by positivity)
  have hconstL : IntegrableOn (fun _ : ℝ => (5 * B / W ^ 4) * (1 + W)) L :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hLowIcc :
      (∫ t in L, g t) ≤ (5 * B / W ^ 4) * (1 + W) * (2 * W) := by
    calc
      (∫ t in L, g t) ≤ (∫ t in L, (5 * B / W ^ 4) * (1 + W)) := by
        apply setIntegral_mono_on hIntgL hconstL hLmeas
        intro t ht
        exact hLowPoint t ht
      _ = (5 * B / W ^ 4) * (1 + W) * (2 * W) := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith : -W ≤ W),
          intervalIntegral.integral_const]
        simp
        ring
  have hLow : (∫ t in L, g t) ≤ 15 * B / W ^ 2 := by
    have hgeom : 2 * W * (1 + W) ≤ 3 * W ^ 2 := by nlinarith [hW]
    calc
      (∫ t in L, g t) ≤ (5 * B / W ^ 4) * (1 + W) * (2 * W) := hLowIcc
      _ = (5 * B / W ^ 4) * (2 * W * (1 + W)) := by ring
      _ ≤ (5 * B / W ^ 4) * (3 * W ^ 2) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = 15 * B / W ^ 2 := by field_simp [hWpos.ne']; ring
  have hEeq : E = Set.Icc W T ∪ Set.Icc (-T) (-W) :=
    shortLong_absTail_eq_union hWpos
  have hEcompact : IsCompact E := by
    rw [hEeq]
    exact isCompact_Icc.union isCompact_Icc
  have hEmeas : MeasurableSet E := hEcompact.isClosed.measurableSet
  have hQsubsetE : Q ⊆ E := by
    intro t ht
    have hI' := Set.mem_Icc.mp ht.1
    have htupper : |t| ≤ T := abs_le.mpr hI'
    have htlower : W ≤ |t| := by
      by_contra hnot
      have htlt : |t| < W := lt_of_not_ge hnot
      have htL : t ∈ L := by
        change -W ≤ t ∧ t ≤ W
        exact abs_le.mp htlt.le
      exact ht.2 htL
    exact ⟨htlower, htupper⟩
  have hdivCont : ContinuousOn (fun t : ℝ => T0 / |t|) E := by
    refine continuousOn_const.div continuous_abs.continuousOn ?_
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le hWpos ht.1)
  have hdivRestrict : Continuous (fun t : E => T0 / |(t : ℝ)|) := by
    exact continuousOn_iff_continuous_domRestrict.mp hdivCont
  have hminRestrict : Continuous (fun t : E => min 1 (T0 / |(t : ℝ)|)) :=
    continuous_const.min hdivRestrict
  have hminCont : ContinuousOn (fun t : ℝ => min 1 (T0 / |t|)) E :=
    continuousOn_iff_continuous_domRestrict.mpr hminRestrict
  have hmCont : ContinuousOn m E := by
    dsimp [m]
    exact (continuous_norm.comp hAcont).continuousOn.mul hminCont
  have hmIntE : IntegrableOn m E := hmCont.integrableOn_compact hEcompact
  have hmNonnegE : 0 ≤ᵐ[volume.restrict E] m := by
    apply ae_of_all
    intro t
    dsimp [m]
    apply mul_nonneg (norm_nonneg _)
    exact le_min (by positivity) (div_nonneg (le_of_lt hT0pos) (abs_nonneg _))
  have hQsubsetAe : (Q : Set ℝ) ≤ᵐ[volume] E := by
    filter_upwards with t ht
    exact hQsubsetE ht
  have hCnonneg : 0 ≤ 6 / Real.sqrt X := by positivity
  have hmajorIntE : IntegrableOn (fun t : ℝ => (6 / Real.sqrt X) * m t) E :=
    hmIntE.const_mul (6 / Real.sqrt X)
  have hmajorNonnegE :
      0 ≤ᵐ[volume.restrict E] (fun t : ℝ => (6 / Real.sqrt X) * m t) := by
    filter_upwards [hmNonnegE] with t ht
    exact mul_nonneg hCnonneg ht
  have hmajorIntQ : IntegrableOn (fun t : ℝ => (6 / Real.sqrt X) * m t) Q :=
    hmajorIntE.mono_set hQsubsetE
  have hQpoint (t : ℝ) (ht : t ∈ Q) :
      g t ≤ (6 / Real.sqrt X) * m t := by
    have htE := hQsubsetE ht
    have htne : t ≠ 0 := by
      intro hz
      subst t
      change W ≤ |(0 : ℝ)| ∧ |(0 : ℝ)| ≤ T at htE
      rw [abs_zero] at htE
      linarith
    have hwin := normalizedWindowKernelBounds X H1 H2 t hXpos hH1pos hH12 hH2X
    rcases hwin with ⟨_, _, _, _, _, htail⟩
    have hKtail0 : ‖normalizedMellinWindowKernel X H1 t -
        normalizedMellinWindowKernel X H2 t‖ ≤
        (6 / Real.sqrt X) * min 1 (T0 / |t|) := by
      simpa [T0, htne] using htail
    have hKtail : ‖w1.K_H t - w2.K_H t‖ ≤
        (6 / Real.sqrt X) * min 1 (T0 / |t|) := by
      rw [mellinWindowData_K_H_eq_normalized
        FractionalPrimes.polynomialKernelRho X H1 B a hX hH1pos hH1X hB
        hsupport hbound t,
        mellinWindowData_K_H_eq_normalized
        FractionalPrimes.polynomialKernelRho X H2 B a hX hH2pos hH2X hB
        hsupport hbound t]
      exact hKtail0
    have hFbound : ‖F t‖ ≤ 1 := by
      dsimp [F]
      exact FractionalPrimes.polynomialKernelRhoAngularFourier_norm_le_one _
    have hprod :
        ‖w1.A_X t‖ * ‖w1.K_H t - w2.K_H t‖ * ‖F t‖ ≤
          ‖w1.A_X t‖ * ((6 / Real.sqrt X) * min 1 (T0 / |t|)) := by
      calc
        _ ≤ (‖w1.A_X t‖ * ((6 / Real.sqrt X) * min 1 (T0 / |t|))) * ‖F t‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hKtail (norm_nonneg _)) (norm_nonneg _)
        _ ≤ ‖w1.A_X t‖ * ((6 / Real.sqrt X) * min 1 (T0 / |t|)) * 1 :=
          mul_le_mul_of_nonneg_left hFbound (by positivity)
        _ = _ := by ring
    have hnormEq :
        ‖w1.A_X t‖ * ‖w1.K_H t - w2.K_H t‖ * ‖F t‖ = g t := by
      simp [g, f, norm_mul]
    rw [← hnormEq]
    simpa [m, mul_assoc, mul_left_comm, mul_comm] using hprod
  have hQle1 : (∫ t in Q, g t) ≤
      ∫ t in Q, (6 / Real.sqrt X) * m t := by
    apply setIntegral_mono_on hIntgQ hmajorIntQ hQmeas
    intro t ht
    exact hQpoint t ht
  have hQle2 : (∫ t in Q, (6 / Real.sqrt X) * m t) ≤
      ∫ t in E, (6 / Real.sqrt X) * m t :=
    setIntegral_mono_set hmajorIntE hmajorNonnegE hQsubsetAe
  have hdyadic := dyadicMellinIntegral w1 hAcont hW hT0W
  have hDyadicE :
      (∫ t in E, m t) ≤ (3 + 12 * Real.log W) *
        dirichletMeanEnvelope w1 T0 W := by
    simpa [m, E, T] using hdyadic
  have hlognonneg : 0 ≤ Real.log W := Real.log_nonneg (by linarith [hW])
  have hlogfactor : 3 + 12 * Real.log W ≤ 16 * (1 + Real.log W) := by
    nlinarith
  have hHigh :
      (∫ t in Q, g t) ≤
        96 * ((1 + Real.log W) / Real.sqrt X) *
          dirichletMeanEnvelope w1 T0 W := by
    calc
      (∫ t in Q, g t) ≤ (∫ t in E, (6 / Real.sqrt X) * m t) := le_trans hQle1 hQle2
      _ = (6 / Real.sqrt X) * (∫ t in E, m t) := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ (6 / Real.sqrt X) *
          ((3 + 12 * Real.log W) * dirichletMeanEnvelope w1 T0 W) :=
        mul_le_mul_of_nonneg_left hDyadicE hCnonneg
      _ ≤ (6 / Real.sqrt X) *
          (16 * (1 + Real.log W) * dirichletMeanEnvelope w1 T0 W) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hlogfactor hDnonneg) hCnonneg
      _ = 96 * ((1 + Real.log W) / Real.sqrt X) *
          dirichletMeanEnvelope w1 T0 W := by ring
  have htotalint :
      (∫ t in I, g t) ≤ 15 * B / W ^ 2 +
        96 * ((1 + Real.log W) / Real.sqrt X) *
          dirichletMeanEnvelope w1 T0 W := by
    rw [hsplit]
    exact add_le_add hLow hHigh
  have hform1 : w1.S_H_T T = ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ t in I, w1.A_X t * w1.K_H t * F t := by
    exact smoothedMellinIdentity_formula X H1 B T a hX hH1pos hH1X hB
      hsupport hbound hTpos
  have hform2 : w2.S_H_T T = ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ t in I, w2.A_X t * w2.K_H t * F t := by
    exact smoothedMellinIdentity_formula X H2 B T a hX hH2pos hH2X hB
      hsupport hbound hTpos
  have hIntDiff :
      (∫ t in I, f1 t) - (∫ t in I, f2 t) = ∫ t in I, f t := by
    rw [← integral_sub hIntf1 hIntf2]
    apply setIntegral_congr_fun hImeas
    intro t ht
    dsimp [f1, f2, f, F]
    rw [hAeq]
    ring
  have hformDiff : w1.S_H_T T - w2.S_H_T T =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ t in I, f t := by
    rw [hform1, hform2, ← smul_sub, hIntDiff]
  have hScalar : ‖((2 * Real.pi)⁻¹ : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    change (2 * Real.pi)⁻¹ ≤ 1
    apply (inv_le_one₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hNormInt : ‖∫ t in I, f t‖ ≤ ∫ t in I, g t :=
    norm_integral_le_integral_norm f
  have hGnonneg : 0 ≤ ∫ t in I, g t :=
    setIntegral_nonneg hImeas (fun t _ => norm_nonneg (f t))
  have hSmoothed :
      ‖w1.S_H_T T - w2.S_H_T T‖ ≤
        15 * B / W ^ 2 +
          96 * ((1 + Real.log W) / Real.sqrt X) *
            dirichletMeanEnvelope w1 T0 W := by
    rw [hformDiff, norm_smul]
    calc
      ‖((2 * Real.pi)⁻¹ : ℝ)‖ * ‖∫ t in I, f t‖ ≤
          1 * (∫ t in I, g t) :=
        mul_le_mul hScalar hNormInt (norm_nonneg _) (by norm_num)
      _ = ∫ t in I, g t := by ring
      _ ≤ 15 * B / W ^ 2 +
          96 * ((1 + Real.log W) / Real.sqrt X) *
            dirichletMeanEnvelope w1 T0 W := htotalint
  have hM1nonneg' : 0 ≤ FractionalPrimes.polynomialKernelM1 := hM1nonneg
  have hTdef : T = T0 * W ^ 4 := rfl
  have hratio1 : X / (H1 * T) = 1 / W ^ 4 := by
    rw [hTdef]
    dsimp [T0]
    field_simp [hXpos.ne', hH1pos.ne', hW4pos.ne']
  have hratio2 : X / (H2 * T) ≤ 1 / W ^ 4 := by
    rw [hTdef]
    dsimp [T0]
    have hEq : X / (H2 * ((X / H1) * W ^ 4)) =
        H1 / (H2 * W ^ 4) := by
      field_simp [hXpos.ne', hH1pos.ne', hH2pos.ne', hW4pos.ne']
    rw [hEq]
    apply (div_le_div_iff₀ (by positivity : 0 < H2 * W ^ 4) hW4pos).2
    simpa using mul_le_mul_of_nonneg_right hH12 hW4pos.le
  have hmain1 : 32 * B * FractionalPrimes.polynomialKernelM1 * X /
        (H1 * T) ≤ 32 * B * FractionalPrimes.polynomialKernelM1 / W ^ 2 := by
    calc
      _ = (32 * B * FractionalPrimes.polynomialKernelM1) *
          (X / (H1 * T)) := by ring
      _ = (32 * B * FractionalPrimes.polynomialKernelM1) * (1 / W ^ 4) := by rw [hratio1]
      _ ≤ (32 * B * FractionalPrimes.polynomialKernelM1) * (1 / W ^ 2) :=
        mul_le_mul_of_nonneg_left hInvPow (by positivity)
      _ = _ := by ring
  have hmain2 : 32 * B * FractionalPrimes.polynomialKernelM1 * X /
        (H2 * T) ≤ 32 * B * FractionalPrimes.polynomialKernelM1 / W ^ 2 := by
    calc
      _ = (32 * B * FractionalPrimes.polynomialKernelM1) *
          (X / (H2 * T)) := by ring
      _ ≤ (32 * B * FractionalPrimes.polynomialKernelM1) * (1 / W ^ 4) :=
        mul_le_mul_of_nonneg_left hratio2 (by positivity)
      _ ≤ (32 * B * FractionalPrimes.polynomialKernelM1) * (1 / W ^ 2) :=
        mul_le_mul_of_nonneg_left hInvPow (by positivity)
      _ = _ := by ring
  have hinvH1 : 1 / H1 ≤ 1 / W ^ 2 := by
    apply (div_le_div_iff₀ hH1pos hW2pos).2
    simpa using hW2H1
  have hH2geW2 : W ^ 2 ≤ H2 := le_trans hW2H1 hH12
  have hinvH2 : 1 / H2 ≤ 1 / W ^ 2 := by
    apply (div_le_div_iff₀ hH2pos hW2pos).2
    simpa using hH2geW2
  have herr1 := smoothedMellinIdentity_endpoint X H1 B T a hX hH1pos hH1X hB
    hsupport hbound hTpos
  have herr2 := smoothedMellinIdentity_endpoint X H2 B T a hX hH2pos hH2X hB
    hsupport hbound hTpos
  have herrsum :
      (32 * B * FractionalPrimes.polynomialKernelM1 * X / (H1 * T) + 8 * B / H1) +
      (32 * B * FractionalPrimes.polynomialKernelM1 * X / (H2 * T) + 8 * B / H2) ≤
        (64 * FractionalPrimes.polynomialKernelM1 + 16) * B / W ^ 2 := by
    calc
      _ ≤ (32 * B * FractionalPrimes.polynomialKernelM1 / W ^ 2 + 8 * B / W ^ 2) +
            (32 * B * FractionalPrimes.polynomialKernelM1 / W ^ 2 + 8 * B / W ^ 2) :=
        add_le_add
          (add_le_add hmain1 (by
            calc
              8 * B / H1 = (8 * B) * (1 / H1) := by ring
              _ ≤ (8 * B) * (1 / W ^ 2) :=
                mul_le_mul_of_nonneg_left hinvH1 (by positivity)
              _ = 8 * B / W ^ 2 := by ring))
          (add_le_add hmain2 (by
            calc
              8 * B / H2 = (8 * B) * (1 / H2) := by ring
              _ ≤ (8 * B) * (1 / W ^ 2) :=
                mul_le_mul_of_nonneg_left hinvH2 (by positivity)
              _ = 8 * B / W ^ 2 := by ring))
      _ = (64 * FractionalPrimes.polynomialKernelM1 + 16) * B / W ^ 2 := by ring
  have hNtriangle :
      ‖w1.N_H - w2.N_H‖ ≤
        ‖w1.N_H - w1.S_H_T T‖ +
          ‖w1.S_H_T T - w2.S_H_T T‖ +
            ‖w2.S_H_T T - w2.N_H‖ := by
    have hdecomp : w1.N_H - w2.N_H =
        (w1.N_H - w1.S_H_T T) +
          ((w1.S_H_T T - w2.S_H_T T) + (w2.S_H_T T - w2.N_H)) := by ring
    rw [hdecomp]
    calc
      _ ≤ ‖w1.N_H - w1.S_H_T T‖ +
          ‖(w1.S_H_T T - w2.S_H_T T) + (w2.S_H_T T - w2.N_H)‖ := norm_add_le _ _
      _ ≤ ‖w1.N_H - w1.S_H_T T‖ +
          (‖w1.S_H_T T - w2.S_H_T T‖ + ‖w2.S_H_T T - w2.N_H‖) :=
        add_le_add (le_refl _) (norm_add_le _ _)
      _ = _ := by ring
  have herr2rev : ‖w2.S_H_T T - w2.N_H‖ = ‖w2.N_H - w2.S_H_T T‖ := by
    rw [← norm_neg, neg_sub]
  have hNbound :
      ‖w1.N_H - w2.N_H‖ ≤
        (64 * FractionalPrimes.polynomialKernelM1 + 31) * B / W ^ 2 +
          96 * ((1 + Real.log W) / Real.sqrt X) *
            dirichletMeanEnvelope w1 T0 W := by
    calc
      _ ≤ ‖w1.N_H - w1.S_H_T T‖ +
            ‖w1.S_H_T T - w2.S_H_T T‖ +
              ‖w2.S_H_T T - w2.N_H‖ := hNtriangle
      _ ≤ (32 * B * FractionalPrimes.polynomialKernelM1 * X / (H1 * T) + 8 * B / H1) +
            (15 * B / W ^ 2 +
              96 * ((1 + Real.log W) / Real.sqrt X) *
                dirichletMeanEnvelope w1 T0 W) +
            (32 * B * FractionalPrimes.polynomialKernelM1 * X / (H2 * T) + 8 * B / H2) := by
          rw [herr2rev]
          exact add_le_add (add_le_add (herr1) hSmoothed) herr2
      _ ≤ (64 * FractionalPrimes.polynomialKernelM1 + 16) * B / W ^ 2 +
            (15 * B / W ^ 2 +
              96 * ((1 + Real.log W) / Real.sqrt X) *
                dirichletMeanEnvelope w1 T0 W) := by
          calc
            _ = ((32 * B * FractionalPrimes.polynomialKernelM1 * X /
                  (H1 * T) + 8 * B / H1) +
                (32 * B * FractionalPrimes.polynomialKernelM1 * X /
                  (H2 * T) + 8 * B / H2)) +
                (15 * B / W ^ 2 +
                  96 * ((1 + Real.log W) / Real.sqrt X) *
                    dirichletMeanEnvelope w1 T0 W) := by ring
            _ ≤ ((64 * FractionalPrimes.polynomialKernelM1 + 16) * B / W ^ 2) +
                (15 * B / W ^ 2 +
                  96 * ((1 + Real.log W) / Real.sqrt X) *
                    dirichletMeanEnvelope w1 T0 W) :=
              add_le_add herrsum le_rfl
      _ = (64 * FractionalPrimes.polynomialKernelM1 + 31) * B / W ^ 2 +
            96 * ((1 + Real.log W) / Real.sqrt X) *
              dirichletMeanEnvelope w1 T0 W := by ring
  have hBterm : 0 ≤ B / W ^ 2 := by positivity
  have hDterm : 0 ≤ ((1 + Real.log W) / Real.sqrt X) *
      dirichletMeanEnvelope w1 T0 W := by
    apply mul_nonneg
    · apply div_nonneg
      · have hlog : 0 ≤ Real.log W := Real.log_nonneg (by linarith [hW])
        linarith
      · exact Real.sqrt_nonneg _
    · exact hDnonneg
  have hC1 : 64 * FractionalPrimes.polynomialKernelM1 + 31 ≤
      128 * (1 + FractionalPrimes.polynomialKernelM1) := by
    nlinarith [hM1nonneg']
  have hC2 : 96 ≤ 128 * (1 + FractionalPrimes.polynomialKernelM1) := by
    nlinarith [hM1nonneg']
  refine ⟨hT0W, ?_⟩
  calc
    ‖w1.N_H - w2.N_H‖ ≤
        (64 * FractionalPrimes.polynomialKernelM1 + 31) * B / W ^ 2 +
          96 * ((1 + Real.log W) / Real.sqrt X) *
            dirichletMeanEnvelope w1 T0 W := hNbound
    _ ≤ 128 * (1 + FractionalPrimes.polynomialKernelM1) * (B / W ^ 2) +
          128 * (1 + FractionalPrimes.polynomialKernelM1) *
            (((1 + Real.log W) / Real.sqrt X) *
              dirichletMeanEnvelope w1 T0 W) := by
      exact add_le_add
        (calc
          (64 * FractionalPrimes.polynomialKernelM1 + 31) * B / W ^ 2 =
              (64 * FractionalPrimes.polynomialKernelM1 + 31) * (B / W ^ 2) := by ring
          _ ≤ 128 * (1 + FractionalPrimes.polynomialKernelM1) * (B / W ^ 2) :=
            mul_le_mul_of_nonneg_right hC1 hBterm)
        (calc
          96 * ((1 + Real.log W) / Real.sqrt X) *
              dirichletMeanEnvelope w1 T0 W =
              96 * (((1 + Real.log W) / Real.sqrt X) *
                dirichletMeanEnvelope w1 T0 W) := by ring
          _ ≤ 128 * (1 + FractionalPrimes.polynomialKernelM1) *
              (((1 + Real.log W) / Real.sqrt X) *
                dirichletMeanEnvelope w1 T0 W) :=
            mul_le_mul_of_nonneg_right hC2 hDterm)
    _ = 128 * (1 + FractionalPrimes.polynomialKernelM1) *
        (B / W ^ 2 + ((1 + Real.log W) / Real.sqrt X) *
          dirichletMeanEnvelope w1 T0 W) := by ring

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.mellinWindowData_A_X_norm_le
#print axioms FractionalPrimes.Literature.Polynomial.shortLongTransferBoundedCoefficients

