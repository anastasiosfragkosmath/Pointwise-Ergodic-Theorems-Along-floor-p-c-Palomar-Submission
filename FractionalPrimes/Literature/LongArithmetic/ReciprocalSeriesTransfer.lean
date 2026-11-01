module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.Deriv
public import FractionalPrimes.Literature.LongArithmetic.CesaroPerron
public import FractionalPrimes.Literature.LongArithmetic.ContourTransfer
public import FractionalPrimes.Literature.LongArithmetic.ReciprocalKernelBounds
public import FractionalPrimes.Literature.LongArithmetic.ReciprocalSeriesTransferScalar
public import FractionalPrimes.Literature.LongArithmetic.ReciprocalSeriesNormBound

@[expose] public section

open Set
open MeasureTheory
open scoped Interval

namespace FractionalPrimes.Literature.LongArithmetic

/-- The smoothed Perron kernel is holomorphic on the positive real half-plane;
the only possible poles are at `0` and `-1`. -/
theorem transferKernel_differentiableOn_pos
    {x Δ : ℝ} (hΔ : 0 < Δ) :
    DifferentiableOn ℂ (transferKernel x Δ) {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  have hs0 : s ≠ 0 := by
    intro h
    have : s.re = 0 := by rw [h]; simp
    linarith
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hr : s.re + 1 = 0 := by
      have hr := congrArg Complex.re h
      simpa using hr
    linarith
  have hden : (Δ : ℂ) * s * (s + 1) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hΔ.ne') hs0
    · exact hs1
  have hnum : DifferentiableAt ℂ
      (fun z : ℂ =>
        Complex.exp ((z + 1) * (Real.log (x + Δ) : ℂ)) -
          Complex.exp ((z + 1) * (Real.log x : ℂ))) s := by
    fun_prop
  have hdenAt : DifferentiableAt ℂ
      (fun z : ℂ => (Δ : ℂ) * z * (z + 1)) s := by
    fun_prop
  have hquot := hnum.div hdenAt hden
  change DifferentiableWithinAt ℂ
    (fun z : ℂ =>
      (Complex.exp ((z + 1) * (Real.log (x + Δ) : ℂ)) -
        Complex.exp ((z + 1) * (Real.log x : ℂ))) /
          ((Δ : ℂ) * z * (z + 1))) {s : ℂ | 0 < s.re} s
  exact hquot.differentiableWithinAt

/-- On the open positive half-plane, the kernel has the regularity required
by the contour-displacement theorem. -/
theorem transferKernel_contDiffOn_pos
    {x Δ : ℝ} (hΔ : 0 < Δ) :
    ContDiffOn ℂ 1 (transferKernel x Δ) {s : ℂ | 0 < s.re} := by
  exact (transferKernel_differentiableOn_pos hΔ).contDiffOn
    (isOpen_lt continuous_const Complex.continuous_re)

/-- Multiplying the analytic extension by the Perron kernel preserves the
regularity needed for the contour displacement on any positive-half-plane
subdomain. -/
theorem transferProduct_contDiffOn_pos
    {F : ℂ → ℂ} {U : Set ℂ} {x Δ : ℝ} (hΔ : 0 < Δ)
    (hU : U ⊆ {s : ℂ | 0 < s.re})
    (hF : ContDiffOn ℂ 1 F U) :
    ContDiffOn ℂ 1 (fun s => F s * transferKernel x Δ s) U := by
  exact hF.mul ((transferKernel_contDiffOn_pos hΔ).mono hU)

/-- A rectangle whose left edge is positive lies in the regularity half-plane
of the kernel. -/
theorem transferRectangle_subset_pos
    {u v T : ℝ} (hu : 0 < u) (huv : u ≤ v) (hT : 0 ≤ T) :
    ([[u, v]] ×ℂ [[-T, T]]) ⊆ {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs' : s.re ∈ Set.Icc u v ∧ s.im ∈ Set.Icc (-T) T := by
    simpa [Set.uIcc_of_le huv, Set.uIcc_of_le (show -T ≤ T by linarith),
      Complex.mem_reProdIm] using hs
  change 0 < s.re
  exact lt_of_lt_of_le hu hs'.1.1

/-- The chosen right edge `v = 1 + 1/log x` satisfies the exact exponential
growth identity used on the horizontal contour edges. -/
theorem transferAbscissa_rpow_bound
    {x σ : ℝ} (hx : 3 ≤ x) (hσ : σ ≤ 1 + 1 / Real.log x) :
    x ^ (σ + 1) ≤ Real.exp 1 * x ^ 2 := by
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hxne : x ≠ 1 := by linarith
  have hexp : x ^ (Real.log x)⁻¹ = Real.exp 1 :=
    Real.rpow_inv_log hxpos hxne
  have hexp' : x ^ (1 / Real.log x) = Real.exp 1 := by
    simpa [one_div] using hexp
  have hσ' : σ + 1 ≤ (1 + 1 / Real.log x) + 1 := by linarith
  calc
    x ^ (σ + 1) ≤ x ^ ((1 + 1 / Real.log x) + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hσ'
    _ = x ^ 2 * x ^ (1 / Real.log x) := by
      rw [show (1 + 1 / Real.log x) + 1 = 2 + 1 / Real.log x by ring,
        Real.rpow_add hxpos]
      simp
    _ = Real.exp 1 * x ^ 2 := by rw [hexp']; ring

/-- One horizontal side of the rectangle contributes at most
`32 e M x^2/(Δ T^2)`, with the pointwise bound on the extension supplied by
the user of this helper. -/
theorem transferKernel_horizontal_integral_bound
    {F : ℂ → ℂ} {x Δ u v T M t : ℝ}
    (hx : 3 ≤ x) (hΔ : 0 < Δ) (hΔx : Δ ≤ x)
    (huv : u < v) (hwidth : v - u ≤ 2)
    (hright : v = 1 + 1 / Real.log x)
    (hulo : 1 / 2 ≤ u) (hvhi : v ≤ 2) (hT : 2 ≤ T) (hM : 0 ≤ M)
    (ht : t = T ∨ t = -T)
    (hF : ∀ σ ∈ Set.Icc u v, ‖F ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ M) :
    ‖∫ σ in u..v,
      F ((σ : ℂ) + Complex.I * (t : ℂ)) *
        transferKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      32 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) := by
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have ht_abs : 1 ≤ |t| := by
    rcases ht with h | h
    · subst t
      simpa [abs_of_nonneg hTpos.le] using hT1
    · subst t
      simpa [abs_neg, abs_of_nonneg hTpos.le] using hT1
  have ht_sq : t ^ 2 = T ^ 2 := by
    rcases ht with h | h
    · rw [h]
    · rw [h]
      ring
  have hdenpos : 0 < Δ * t ^ 2 := by rw [ht_sq]; positivity
  have hσpower (σ : ℝ) (hσ : σ ∈ Set.Icc u v) :
      x ^ (σ + 1) ≤ Real.exp 1 * x ^ 2 := by
    apply transferAbscissa_rpow_bound hx
    calc
      σ ≤ v := hσ.2
      _ = 1 + 1 / Real.log x := hright
  have hpoint : ∀ σ ∈ Ι u v,
      ‖F ((σ : ℂ) + Complex.I * (t : ℂ)) *
        transferKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
          16 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) := by
    intro σ hσ
    have hσIoc : σ ∈ Set.Ioc u v := by
      simpa [Set.uIoc_of_le huv.le] using hσ
    have hσIcc : σ ∈ Set.Icc u v := Set.Ioc_subset_Icc_self hσIoc
    have hσlo : 1 / 2 ≤ σ := hulo.trans hσIcc.1
    have hσhi : σ ≤ 2 := hσIcc.2.trans hvhi
    have hkernel := transferKernel_norm_le_of_one_le_abs
      hxpos hΔ hΔx hσlo hσhi ht_abs
    have hkernel' :
        ‖transferKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
          16 * Real.exp 1 * x ^ 2 / (Δ * T ^ 2) := by
      calc
        _ ≤ 16 * x ^ (σ + 1) / (Δ * t ^ 2) := hkernel
        _ = 16 * x ^ (σ + 1) / (Δ * T ^ 2) := by rw [ht_sq]
        _ ≤ 16 * (Real.exp 1 * x ^ 2) / (Δ * T ^ 2) := by
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left (hσpower σ hσIcc) (by norm_num)
          · positivity
        _ = 16 * Real.exp 1 * x ^ 2 / (Δ * T ^ 2) := by ring
    rw [norm_mul]
    calc
      ‖F ((σ : ℂ) + Complex.I * (t : ℂ))‖ *
          ‖transferKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
        M * (16 * Real.exp 1 * x ^ 2 / (Δ * T ^ 2)) :=
          mul_le_mul (hF σ hσIcc) hkernel' (norm_nonneg _) hM
      _ = 16 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) := by ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hlen : |v - u| ≤ 2 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ v - u)]
    exact hwidth
  calc
    _ ≤ (16 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2)) * |v - u| := hnorm
    _ ≤ (16 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2)) * 2 :=
      mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = 32 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) := by ring

/-- The Dirichlet series times the Perron kernel is continuous on every
vertical line to the right of `1`, for either orientation of the imaginary
coordinate. -/
theorem transferRightLine_continuous
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {x Δ ε : ℝ} (hx : 3 ≤ x) (hΔ : 0 < Δ) :
    Continuous (fun t : ℝ =>
      perronDirichletSeries a
        (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)) *
      transferKernel x Δ
        (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))) := by
  let v : ℝ := 1 + 1 / Real.log x
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hv : 1 < v := by
    dsimp [v]
    have : 0 < 1 / Real.log x := one_div_pos.mpr hlogpos
    linarith
  have hcoef : ∀ n, n ≠ 0 → ‖perronCoefficient a n‖ ≤ 1 := by
    intro n hn
    simp [perronCoefficient, hn, ha n (Nat.pos_of_ne_zero hn)]
  have habsc : LSeries.abscissaOfAbsConv (perronCoefficient a) ≤ (1 : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_le_const
    exact ⟨1, hcoef⟩
  have hLdomain (t : ℝ) :
      LSeries.abscissaOfAbsConv (perronCoefficient a) <
        (((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)).re : EReal) := by
    calc
      LSeries.abscissaOfAbsConv (perronCoefficient a) ≤ (1 : EReal) := habsc
      _ < (v : EReal) := by exact_mod_cast hv
      _ = (((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)).re : EReal) := by
        simp [Complex.add_re, Complex.mul_re]
  have hLcont : Continuous (fun t : ℝ =>
      perronDirichletSeries a ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))) := by
    apply continuousOn_univ.mp
    change ContinuousOn
      (fun t : ℝ => LSeries (perronCoefficient a)
        ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))) Set.univ
    exact (LSeries_differentiableOn (perronCoefficient a)).continuousOn.comp
      (by fun_prop) (by intro t ht; exact hLdomain t)
  have hKcont : Continuous (fun t : ℝ =>
      transferKernel x Δ ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))) := by
    apply continuousOn_univ.mp
    exact (transferKernel_contDiffOn_pos hΔ).continuousOn.comp
      (by fun_prop) (by
        intro t ht
        change 0 < (((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)).re)
        simpa using lt_trans zero_lt_one hv)
  have hcont := hLcont.mul hKcont
  convert hcont using 1 <;> funext t <;> rfl

/-- The right-edge Perron integrand is absolutely integrable on the upper
tail. Its majorant is the exact `t⁻²` decay used in `lal:contour-transfer`.
-/
theorem transferRightLine_upperTail_integrable
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {x Δ T : ℝ} (hx : 3 ≤ x) (hΔ : 0 < Δ) (hΔx : Δ ≤ x)
    (hT : 1 ≤ T) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    IntegrableOn
      (fun t : ℝ => perronDirichletSeries a
          (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)) *
        transferKernel x Δ
          (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)))
      (Set.Ioi T) ∧
    ‖∫ t in Set.Ioi T, perronDirichletSeries a
        (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)) *
      transferKernel x Δ
        (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))‖ ≤
      16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T) := by
  let v : ℝ := 1 + 1 / Real.log x
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogge : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hx)
  have hv : 1 < v := by
    dsimp [v]
    have : 0 < 1 / Real.log x := one_div_pos.mpr hlogpos
    linarith
  have hσlo : 1 / 2 ≤ v := by
    dsimp [v]
    have hrecip : 0 < 1 / Real.log x := one_div_pos.mpr hlogpos
    linarith
  have hσhi : v ≤ 2 := by
    dsimp [v]
    have hinv : 1 / Real.log x ≤ 1 := (div_le_one hlogpos).2 hlogge
    linarith
  have hcoef : ∀ n, n ≠ 0 → ‖perronCoefficient a n‖ ≤ 1 := by
    intro n hn
    simp [perronCoefficient, hn, ha n (Nat.pos_of_ne_zero hn)]
  have habsc : LSeries.abscissaOfAbsConv (perronCoefficient a) ≤ (1 : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_le_const
    exact ⟨1, hcoef⟩
  have hLdomain (t : ℝ) :
      LSeries.abscissaOfAbsConv (perronCoefficient a) <
        (((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)).re : EReal) := by
    calc
      LSeries.abscissaOfAbsConv (perronCoefficient a) ≤ (1 : EReal) := habsc
      _ < (v : EReal) := by exact_mod_cast hv
      _ = (((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)).re : EReal) := by
        simp [Complex.add_re, Complex.mul_re]
  have hLcont : Continuous (fun t : ℝ =>
      perronDirichletSeries a ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))) := by
    apply continuousOn_univ.mp
    change ContinuousOn
      (fun t : ℝ => LSeries (perronCoefficient a)
        ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))) Set.univ
    exact (LSeries_differentiableOn (perronCoefficient a)).continuousOn.comp
      (by fun_prop) (by intro t ht; exact hLdomain t)
  have hKcont : Continuous (fun t : ℝ =>
      transferKernel x Δ ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))) := by
    apply continuousOn_univ.mp
    exact (transferKernel_contDiffOn_pos hΔ).continuousOn.comp
      (by fun_prop) (by
        intro t ht
        change 0 < (((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)).re)
        simpa using lt_trans zero_lt_one hv)
  have hcont : Continuous (fun t : ℝ =>
      perronDirichletSeries a ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)) *
        transferKernel x Δ ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))) := hLcont.mul hKcont
  have hseries (t : ℝ) :
      ‖perronDirichletSeries a ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))‖ ≤
        1 + Real.log x := by
    calc
      _ ≤ 1 + 1 / (v - 1) := by
        simpa [perronDirichletSeries] using
          (LSeries_norm_le_integral_test (f := perronCoefficient a) hcoef
            (v := v) (t := ε * t) hv)
      _ = 1 + Real.log x := by
        have hv' : v - 1 = 1 / Real.log x := by dsimp [v]; ring
        rw [hv']
        field_simp [ne_of_gt hlogpos]
  have hpow : x ^ (v + 1) ≤ Real.exp 1 * x ^ 2 := by
    exact transferAbscissa_rpow_bound hx le_rfl
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioi T) :
      ‖perronDirichletSeries a ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)) *
        transferKernel x Δ ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))‖ ≤
          (16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / Δ) * t ^ (-2 : ℝ) := by
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have htpos : 0 < t := lt_trans hTpos ht
    have hεabs : |ε * t| = |t| := by rcases hε with h | h <;> simp [h]
    have hεsq : (ε * t) ^ 2 = t ^ 2 := by rcases hε with h | h <;> simp [h]
    have htabs : 1 ≤ |t| := by
      rw [abs_of_pos htpos]
      exact le_trans hT ht.le
    have hkernel := transferKernel_norm_le_of_one_le_abs
      (t := ε * t) hxpos hΔ hΔx hσlo hσhi (by simpa [hεabs] using htabs)
    have hkernel' :
        ‖transferKernel x Δ ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))‖ ≤
          (16 * Real.exp 1 * x ^ 2 / Δ) * t ^ (-2 : ℝ) := by
      have htpow : t ^ (-2 : ℝ) = 1 / t ^ 2 := by
        have htpow' : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
          rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num]
          rw [Real.rpow_neg htpos.le (2 : ℝ)]
          rw [show (2 : ℝ) = (2 : ℕ) by norm_num]
          rw [Real.rpow_natCast]
        simpa [one_div] using htpow'
      calc
        _ ≤ 16 * x ^ (v + 1) / (Δ * t ^ 2) := by simpa [hεsq] using hkernel
        _ ≤ 16 * (Real.exp 1 * x ^ 2) / (Δ * t ^ 2) := by
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hpow (by norm_num)
          · positivity
        _ = (16 * Real.exp 1 * x ^ 2 / Δ) * t ^ (-2 : ℝ) := by
          rw [htpow]
          field_simp
    rw [norm_mul]
    calc
      _ ≤ (1 + Real.log x) *
            ((16 * Real.exp 1 * x ^ 2 / Δ) * t ^ (-2 : ℝ)) :=
        mul_le_mul (hseries t) hkernel' (norm_nonneg _) (by positivity)
      _ = (16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / Δ) * t ^ (-2 : ℝ) := by ring
  have hmajor : IntegrableOn (fun t : ℝ =>
      (16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / Δ) * t ^ (-2 : ℝ))
      (Set.Ioi T) := by
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have h := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hTpos
    exact h.const_mul (16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / Δ)
  have hline : IntegrableOn (fun t : ℝ =>
      perronDirichletSeries a ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)) *
        transferKernel x Δ ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))) (Set.Ioi T) := by
    apply hmajor.mono'
    · exact hcont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpoint t ht
  have hmajorInt :
      ∫ t in Set.Ioi T,
        (16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / Δ) * t ^ (-2 : ℝ) =
          16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T) := by
    have hpowInt : ∫ t in Set.Ioi T, t ^ (-2 : ℝ) = 1 / T := by
      rw [integral_Ioi_rpow_of_lt (a := -2) (by norm_num) (lt_of_lt_of_le zero_lt_one hT)]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      simp [one_div]
    calc
      _ = (16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / Δ) *
          ∫ t in Set.Ioi T, t ^ (-2 : ℝ) := by rw [integral_const_mul]
      _ = _ := by rw [hpowInt]; ring
  have hnormIntegral :
      ‖∫ t in Set.Ioi T,
          perronDirichletSeries a ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)) *
            transferKernel x Δ ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))‖ ≤
        16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T) := by
    calc
      _ ≤ ∫ t in Set.Ioi T,
          ‖perronDirichletSeries a ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ)) *
            transferKernel x Δ ((v : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioi T,
          (16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / Δ) * t ^ (-2 : ℝ) := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun t => norm_nonneg _)
          · exact hmajor
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact hpoint t ht
      _ = 16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T) := hmajorInt
  exact ⟨by simpa [v] using hline, by simpa [v] using hnormIntegral⟩

/-- Reflection identifies the left tail of the original right Perron line
with the negative orientation of the upper-tail estimate. -/
theorem transferRightLine_lowerTail_integrable_bound
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {x Δ T : ℝ} (hx : 3 ≤ x) (hΔ : 0 < Δ) (hΔx : Δ ≤ x)
    (hT : 1 ≤ T) :
    IntegrableOn
      (fun t : ℝ => perronDirichletSeries a
          (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
        transferKernel x Δ
          (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)))
      (Set.Iic (-T)) ∧
    ‖∫ t in Set.Iic (-T), perronDirichletSeries a
        (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
      transferKernel x Δ
        (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ ≤
      16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T) := by
  let f : ℝ → ℂ := fun t => perronDirichletSeries a
      (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
    transferKernel x Δ
      (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))
  have hminus := transferRightLine_upperTail_integrable ha hx hΔ hΔx hT
    (ε := -1) (Or.inr rfl)
  have hminusInt : IntegrableOn (fun t : ℝ => f (-t)) (Set.Ioi T) := by
    simpa [f] using hminus.1
  have hminusIci : IntegrableOn (fun t : ℝ => f (-t)) (Set.Ici T) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (f := fun t : ℝ => f (-t))
      (μ := volume) (by finiteness)).2 hminusInt
  have hpreimage : Neg.neg ⁻¹' Set.Iic (-T) = Set.Ici T := by
    ext t
    simp [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici, neg_le_neg_iff]
  let hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hleft : IntegrableOn f (Set.Iic (-T)) := by
    have hcomp : IntegrableOn (f ∘ Neg.neg) (Neg.neg ⁻¹' Set.Iic (-T)) := by
      rw [hpreimage]
      simpa [Function.comp_def] using hminusIci
    exact (hmp.integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding).mp hcomp
  have hreflect :
      ∫ t in Set.Iic (-T), f t = ∫ t in Set.Ioi T, f (-t) := by
    have hindicator :
        (fun t : ℝ => (Set.Iic (-T)).indicator f (-t)) =
          (Set.Ici T).indicator (fun t : ℝ => f (-t)) := by
      funext t
      by_cases ht : T ≤ t
      · have hneg : -t ≤ -T := neg_le_neg ht
        simp [Set.indicator, Set.mem_Iic, Set.mem_Ici, ht, hneg]
      · have hneg : ¬ -t ≤ -T := by
          intro h
          exact ht (neg_le_neg_iff.mp h)
        simp [Set.indicator, Set.mem_Iic, Set.mem_Ici, ht, hneg]
    calc
      _ = ∫ t : ℝ, (Set.Iic (-T)).indicator f t := by
        rw [integral_indicator measurableSet_Iic]
      _ = ∫ t : ℝ, (Set.Iic (-T)).indicator f (-t) := by
        symm
        exact hmp.integral_comp (Homeomorph.neg ℝ).measurableEmbedding _
      _ = ∫ t : ℝ, (Set.Ici T).indicator (fun t : ℝ => f (-t)) t := by
        rw [hindicator]
      _ = ∫ t in Set.Ici T, f (-t) := by
        rw [integral_indicator measurableSet_Ici]
      _ = ∫ t in Set.Ioi T, f (-t) := integral_Ici_eq_integral_Ioi
  have hbound :
      ‖∫ t in Set.Ioi T, f (-t)‖ ≤
        16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T) := by
    simpa [f] using hminus.2
  constructor
  · simpa [f] using hleft
  · rw [hreflect]
    exact hbound

/-- Quantitative transfer of the sharp coefficient sum from the right Perron
line to the left side of an analytic rectangle. This is the exact theorem
`lal:contour-transfer`, with the extension and bound hypotheses stated on an
open neighbourhood and the closed rectangle, respectively. -/
private theorem transfer_norm_add_sub_le (z w q : ℂ) :
    ‖z + (w - q)‖ ≤ ‖z‖ + ‖w‖ + ‖q‖ := by
  calc
    ‖z + (w - q)‖ ≤ ‖z‖ + ‖w - q‖ := norm_add_le _ _
    _ ≤ ‖z‖ + (‖w‖ + ‖q‖) := by gcongr; exact norm_sub_le w q
    _ = ‖z‖ + ‖w‖ + ‖q‖ := by ring

 theorem reciprocalSeriesTransfer
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {x Δ T δ M : ℝ}
    (hx : 3 ≤ x) (hΔ : 0 < Δ) (hΔx : Δ ≤ x) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) (hM : 0 ≤ M)
    {F : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U)
    (hUrect : ([[1 - δ, 1 + 1 / Real.log x]] ×ℂ [[-T, T]]) ⊆ U)
    (hF : ContDiffOn ℂ 1 F U)
    (hFseries : ∀ s : ℂ, 1 < s.re → F s = perronDirichletSeries a s)
    (hFbound : ∀ s ∈ ([[1 - δ, 1 + 1 / Real.log x]] ×ℂ [[-T, T]]),
      ‖F s‖ ≤ M) :
    ‖cesaroPerronSharpSum a x‖ ≤
      Δ + 1 + 128 * Real.exp 1 *
        (M * x ^ (1 - δ) * (1 + Real.log T) +
          M * x ^ 2 / (Δ * T ^ 2) +
          (1 + Real.log x) * x ^ 2 / (Δ * T)) := by
  let u : ℝ := 1 - δ
  let v : ℝ := 1 + 1 / Real.log x
  let rect : Set ℂ := ([[u, v]] ×ℂ [[-T, T]])
  let G : ℂ → ℂ := fun s => F s * transferKernel x Δ s
  let f : ℝ → ℂ := fun t => perronDirichletSeries a
      ((v : ℂ) + Complex.I * (t : ℂ)) *
    transferKernel x Δ ((v : ℂ) + Complex.I * (t : ℂ))
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogge : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hx)
  have hTpos : 0 < T := by linarith
  have hTnegT : -T ≤ T := by linarith
  have huHalf : 1 / 2 ≤ u := by dsimp [u]; linarith
  have huPos : 0 < u := by linarith
  have hvOne : 1 < v := by
    dsimp [v]
    have hrecip : 0 < 1 / Real.log x := one_div_pos.mpr hlogpos
    linarith
  have hvTwo : v ≤ 2 := by
    dsimp [v]
    have hrecip : 1 / Real.log x ≤ 1 := (div_le_one hlogpos).2 hlogge
    linarith
  have huv : u < v := by linarith
  have hwidth : v - u ≤ 2 := by
    have hrecip : 1 / Real.log x ≤ 1 := (div_le_one hlogpos).2 hlogge
    dsimp [u, v]
    linarith [hδhi]
  have hFrect : rect ⊆ U := by
    simpa [rect, u, v] using hUrect
  have hrectPos : rect ⊆ {s : ℂ | 0 < s.re} :=
    transferRectangle_subset_pos huPos huv.le hTpos.le
  let V : Set ℂ := U ∩ {s : ℂ | 0 < s.re}
  have hVopen : IsOpen V := by
    exact hUopen.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hVrect : rect ⊆ V := by
    intro s hs
    exact ⟨hFrect hs, hrectPos hs⟩
  have hFV : ContDiffOn ℂ 1 F V := hF.mono Set.inter_subset_left
  have hVpos : V ⊆ {s : ℂ | 0 < s.re} := Set.inter_subset_right
  have hG : ContDiffOn ℂ 1 G V := by
    simpa [G] using transferProduct_contDiffOn_pos hΔ hVpos hFV
  have hdisp := rectangleDisplacement huv hTpos hVopen hVrect hG

  have hlineMem {σ t : ℝ} (hσ : σ ∈ Set.Icc u v)
      (ht : t ∈ Set.Icc (-T) T) :
      ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ rect := by
    apply Complex.mem_reProdIm.mpr
    constructor
    · have hre : (((σ : ℂ) + (t : ℂ) * Complex.I).re) = σ := by simp
      rw [hre]
      simpa [rect, Set.uIcc_of_le huv.le] using hσ
    · have him : (((σ : ℂ) + (t : ℂ) * Complex.I).im) = t := by simp
      rw [him]
      simpa [rect, Set.uIcc_of_le hTnegT] using ht
  have hlineMemI (σ t : ℝ) (hσ : σ ∈ Set.Icc u v)
      (ht : t ∈ Set.Icc (-T) T) :
      ((σ : ℂ) + Complex.I * (t : ℂ)) ∈ rect := by
    have h := hlineMem hσ ht
    convert h using 1
    congr 1
    ring
  have hFline (σ t : ℝ) (hσ : σ ∈ Set.Icc u v)
      (ht : t ∈ Set.Icc (-T) T) :
      ‖F ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ M :=
    hFbound _ (hlineMemI σ t hσ ht)

  have hTop :
      ‖∫ σ in u..v,
          F ((σ : ℂ) + Complex.I * (T : ℂ)) *
            transferKernel x Δ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
        32 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) := by
    apply transferKernel_horizontal_integral_bound hx hΔ hΔx huv hwidth rfl
      huHalf hvTwo hT hM (Or.inl rfl)
    intro σ hσ
    exact hFline σ T hσ ⟨by linarith, le_rfl⟩
  have hBottomCore :
      ‖∫ σ in u..v,
          F ((σ : ℂ) + Complex.I * ((-T : ℝ) : ℂ)) *
            transferKernel x Δ ((σ : ℂ) + Complex.I * ((-T : ℝ) : ℂ))‖ ≤
        32 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) := by
    exact transferKernel_horizontal_integral_bound hx hΔ hΔx huv hwidth rfl
      huHalf hvTwo hT hM (Or.inr rfl) (fun σ hσ =>
        hFline σ (-T) hσ ⟨le_rfl, by linarith⟩)
  have hBottom :
      ‖∫ σ in u..v,
          F ((σ : ℂ) + Complex.I * (-T : ℂ)) *
            transferKernel x Δ ((σ : ℂ) + Complex.I * (-T : ℂ))‖ ≤
        32 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) := by
    simpa only [Complex.ofReal_neg] using hBottomCore
  have hTopG :
      ‖∫ σ in u..v, G ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        32 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) := by
    simpa [G, mul_comm] using hTop
  have hBottomG :
      ‖∫ σ in u..v, G ((σ : ℂ) + (-T : ℂ) * Complex.I)‖ ≤
        32 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) := by
    simpa [G, mul_comm] using hBottom

  have hlineCont : Continuous (fun t : ℝ => (u : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hlineMapsV : Set.MapsTo (fun t : ℝ => (u : ℂ) + (t : ℂ) * Complex.I)
      (Set.Icc (-T) T) V := by
    intro t ht
    exact hVrect (hlineMem (σ := u) ⟨le_rfl, huv.le⟩ ht)
  have hGlineCont : ContinuousOn (fun t : ℝ => G ((u : ℂ) + (t : ℂ) * Complex.I))
      (Set.Icc (-T) T) :=
    hG.continuousOn.comp hlineCont.continuousOn hlineMapsV
  have hKlineCont : ContinuousOn
      (fun t : ℝ => transferKernel x Δ ((u : ℂ) + (t : ℂ) * Complex.I))
      (Set.Icc (-T) T) :=
    (transferKernel_contDiffOn_pos hΔ).continuousOn.comp hlineCont.continuousOn
      (by
        intro t ht
        exact hrectPos (hlineMem (σ := u) ⟨le_rfl, huv.le⟩ ht))
  have hGlineInt : IntervalIntegrable
      (fun t : ℝ => ‖G ((u : ℂ) + (t : ℂ) * Complex.I)‖)
      volume (-T) T :=
    hGlineCont.norm.intervalIntegrable_of_Icc hTnegT
  have hKlineInt : IntervalIntegrable
      (fun t : ℝ => ‖transferKernel x Δ ((u : ℂ) + (t : ℂ) * Complex.I)‖)
      volume (-T) T :=
    hKlineCont.norm.intervalIntegrable_of_Icc hTnegT
  have hGpoint (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      ‖G ((u : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        M * ‖transferKernel x Δ ((u : ℂ) + (t : ℂ) * Complex.I)‖ := by
    have hFleft : ‖F ((u : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M :=
      hFbound _ (hlineMem (σ := u) ⟨le_rfl, huv.le⟩ ht)
    change ‖F ((u : ℂ) + (t : ℂ) * Complex.I) *
      transferKernel x Δ ((u : ℂ) + (t : ℂ) * Complex.I)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul hFleft le_rfl (norm_nonneg _) hM
  have hGintLe :
      ∫ t in -T..T, ‖G ((u : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        M * ∫ t in -T..T,
          ‖transferKernel x Δ ((u : ℂ) + (t : ℂ) * Complex.I)‖ := by
    calc
      _ ≤ ∫ t in -T..T,
          M * ‖transferKernel x Δ ((u : ℂ) + (t : ℂ) * Complex.I)‖ :=
        intervalIntegral.integral_mono_on hTnegT hGlineInt
          (hKlineInt.const_mul M) (fun t ht => hGpoint t ht)
      _ = M * ∫ t in -T..T,
          ‖transferKernel x Δ ((u : ℂ) + (t : ℂ) * Complex.I)‖ :=
        intervalIntegral.integral_const_mul M _
  have hKlineEq :
      ∫ t in -T..T, ‖transferKernel x Δ ((u : ℂ) + (t : ℂ) * Complex.I)‖ =
        ∫ t in -T..T, ‖transferKernel x Δ ((u : ℂ) + Complex.I * (t : ℂ))‖ := by
    apply intervalIntegral.integral_congr
    intro t ht
    congr 1
    congr 1
    ring
  have hKvert := transferKernel_vertical_integral_bound hxpos hΔ hΔx huHalf
    (by linarith : u ≤ 2) hT
  have hleftVertical :
      ‖∫ t in -T..T, G ((u : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        16 * M * x ^ u * (1 + Real.log T) := by
    calc
      _ ≤ ∫ t in -T..T,
          ‖G ((u : ℂ) + (t : ℂ) * Complex.I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hTnegT
      _ ≤ M * ∫ t in -T..T,
          ‖transferKernel x Δ ((u : ℂ) + (t : ℂ) * Complex.I)‖ := hGintLe
      _ = M * ∫ t in -T..T,
          ‖transferKernel x Δ ((u : ℂ) + Complex.I * (t : ℂ))‖ := by rw [hKlineEq]
      _ ≤ M * (16 * x ^ u * (1 + Real.log T)) := by
        exact mul_le_mul_of_nonneg_left hKvert hM
      _ = 16 * M * x ^ u * (1 + Real.log T) := by ring

  have hFseriesLine (t : ℝ) :
      F ((v : ℂ) + Complex.I * (t : ℂ)) =
        perronDirichletSeries a ((v : ℂ) + Complex.I * (t : ℂ)) := by
    apply hFseries
    have : 1 < ((v : ℂ) + Complex.I * (t : ℂ)).re := by simpa using hvOne
    exact this
  have hRightMiddle :
      ∫ t in -T..T, G ((v : ℂ) + (t : ℂ) * Complex.I) =
        ∫ t in -T..T, f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change F ((v : ℂ) + (t : ℂ) * Complex.I) *
        transferKernel x Δ ((v : ℂ) + (t : ℂ) * Complex.I) =
      perronDirichletSeries a ((v : ℂ) + Complex.I * (t : ℂ)) *
        transferKernel x Δ ((v : ℂ) + Complex.I * (t : ℂ))
    rw [show (v : ℂ) + (t : ℂ) * Complex.I =
      (v : ℂ) + Complex.I * (t : ℂ) by ring, hFseriesLine t]
  have hContourMiddle :
      ‖∫ t in -T..T, f t‖ ≤
        16 * M * x ^ u * (1 + Real.log T) +
          64 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) := by
    have hdisp' :
        Complex.I • (∫ t in -T..T, G ((v : ℂ) + (t : ℂ) * Complex.I)) -
          Complex.I • (∫ t in -T..T, G ((u : ℂ) + (t : ℂ) * Complex.I)) =
        (∫ σ in u..v, G ((σ : ℂ) + (T : ℂ) * Complex.I)) -
          (∫ σ in u..v, G ((σ : ℂ) + (-T : ℂ) * Complex.I)) := by
      simpa [G] using hdisp
    have hrel :
        Complex.I • (∫ t in -T..T, G ((v : ℂ) + (t : ℂ) * Complex.I)) =
          Complex.I • (∫ t in -T..T, G ((u : ℂ) + (t : ℂ) * Complex.I)) +
            (∫ σ in u..v, G ((σ : ℂ) + (T : ℂ) * Complex.I)) -
              (∫ σ in u..v, G ((σ : ℂ) + (-T : ℂ) * Complex.I)) := by
      linear_combination hdisp'
    have hnormRel :
        ‖∫ t in -T..T, G ((v : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          ‖∫ t in -T..T, G ((u : ℂ) + (t : ℂ) * Complex.I)‖ +
            ‖∫ σ in u..v, G ((σ : ℂ) + (T : ℂ) * Complex.I)‖ +
              ‖∫ σ in u..v, G ((σ : ℂ) + (-T : ℂ) * Complex.I)‖ := by
      have hnormI (z : ℂ) : ‖Complex.I • z‖ = ‖z‖ := by simp
      calc
        _ = ‖Complex.I • (∫ t in -T..T,
              G ((v : ℂ) + (t : ℂ) * Complex.I))‖ := (hnormI _).symm
        _ = ‖Complex.I • (∫ t in -T..T,
              G ((u : ℂ) + (t : ℂ) * Complex.I)) +
              ((∫ σ in u..v, G ((σ : ℂ) + (T : ℂ) * Complex.I)) -
                (∫ σ in u..v, G ((σ : ℂ) + (-T : ℂ) * Complex.I)))‖ := by
          rw [hrel]
          congr 1
          abel
        _ ≤ ‖Complex.I • (∫ t in -T..T,
              G ((u : ℂ) + (t : ℂ) * Complex.I))‖ +
              ‖∫ σ in u..v, G ((σ : ℂ) + (T : ℂ) * Complex.I)‖ +
                ‖∫ σ in u..v, G ((σ : ℂ) + (-T : ℂ) * Complex.I)‖ := by
          exact transfer_norm_add_sub_le _ _ _
        _ = _ := by rw [hnormI]
    calc
      _ = ‖∫ t in -T..T, G ((v : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [hRightMiddle]
      _ ≤ _ := by
        calc
          _ ≤ ‖∫ t in -T..T, G ((u : ℂ) + (t : ℂ) * Complex.I)‖ +
                ‖∫ σ in u..v, G ((σ : ℂ) + (T : ℂ) * Complex.I)‖ +
                  ‖∫ σ in u..v, G ((σ : ℂ) + (-T : ℂ) * Complex.I)‖ := hnormRel
          _ ≤ 16 * M * x ^ u * (1 + Real.log T) +
                64 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) := by
            calc
              _ = ‖∫ t in -T..T, G ((u : ℂ) + (t : ℂ) * Complex.I)‖ +
                    (‖∫ σ in u..v, G ((σ : ℂ) + (T : ℂ) * Complex.I)‖ +
                      ‖∫ σ in u..v, G ((σ : ℂ) + (-T : ℂ) * Complex.I)‖) := by abel
              _ ≤ 16 * M * x ^ u * (1 + Real.log T) +
                    (32 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) +
                      32 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2)) :=
                add_le_add hleftVertical (add_le_add hTopG hBottomG)
              _ = 16 * M * x ^ u * (1 + Real.log T) +
                    64 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) := by ring

  have hplus := transferRightLine_upperTail_integrable ha hx hΔ hΔx
    (by linarith : 1 ≤ T) (ε := 1) (Or.inl rfl)
  have hminus := transferRightLine_lowerTail_integrable_bound ha hx hΔ hΔx
    (by linarith : 1 ≤ T)
  have hplusInt : IntegrableOn f (Set.Ioi T) := by
    simpa [f, v, mul_comm] using hplus.1
  have hplusBound : ‖∫ t in Set.Ioi T, f t‖ ≤
      16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T) := by
    simpa [f, v, mul_comm] using hplus.2
  have hminusInt : IntegrableOn f (Set.Iic (-T)) := by
    simpa [f, v] using hminus.1
  have hminusBound : ‖∫ t in Set.Iic (-T), f t‖ ≤
      16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T) := by
    simpa [f, v] using hminus.2
  have hseriesLineCont : Continuous f := by
    simpa [f, v, mul_comm] using
      (transferRightLine_continuous ha hx hΔ (ε := 1))
  have hmidInt : IntegrableOn f (Set.Ioc (-T) T) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hTnegT]
    exact hseriesLineCont.intervalIntegrable (-T) T
  have hrightIoi : IntegrableOn f (Set.Ioi (-T)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hTnegT]
    exact hmidInt.union hplusInt
  have hsplitMid := intervalIntegral.integral_interval_add_Ioi
    (f := f) hrightIoi hplusInt
  have hsplitWhole := intervalIntegral.integral_Iic_add_Ioi
    (f := f) hminusInt hrightIoi
  have hwholeEq :
      (∫ t : ℝ, f t) =
        (∫ t in Set.Iic (-T), f t) +
          (∫ t in -T..T, f t) + (∫ t in Set.Ioi T, f t) := by
    calc
      _ = (∫ t in Set.Iic (-T), f t) + (∫ t in Set.Ioi (-T), f t) :=
        hsplitWhole.symm
      _ = (∫ t in Set.Iic (-T), f t) +
          ((∫ t in -T..T, f t) + (∫ t in Set.Ioi T, f t)) := by rw [← hsplitMid]
      _ = _ := by abel
  have hwholeBound :
      ‖∫ t : ℝ, f t‖ ≤
        16 * M * x ^ u * (1 + Real.log T) +
          64 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) +
          32 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T) := by
    rw [hwholeEq]
    calc
      _ ≤ ‖∫ t in Set.Iic (-T), f t‖ +
            ‖∫ t in -T..T, f t‖ + ‖∫ t in Set.Ioi T, f t‖ := by
        calc
          _ ≤ ‖(∫ t in Set.Iic (-T), f t) + (∫ t in -T..T, f t)‖ +
                ‖∫ t in Set.Ioi T, f t‖ := norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by
        calc
          _ = ‖∫ t in -T..T, f t‖ +
                (‖∫ t in Set.Iic (-T), f t‖ + ‖∫ t in Set.Ioi T, f t‖) := by ring
          _ ≤ (16 * M * x ^ u * (1 + Real.log T) +
                64 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2)) +
                (16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T) +
                  16 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T)) :=
              add_le_add hContourMiddle (add_le_add hminusBound hplusBound)
          _ = _ := by ring

  have hnormFactor : ‖(↑((2 * Real.pi : ℝ)⁻¹) : ℂ)‖ = (2 * Real.pi : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (inv_pos.mpr Real.two_pi_pos))]
  have hfactorLe : (2 * Real.pi : ℝ)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ Real.two_pi_pos).2
    have hpi : 3 < Real.pi := Real.pi_gt_three
    linarith
  have hidentity : cesaroPerronSmoothedSum a x Δ =
      (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) * ∫ t : ℝ, f t := by
    simpa only [f, transferKernel, cesaroPerronKernel] using
      (cesaroPerronIdentity ha hxpos hΔ hvOne)
  have hlogTnonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
  have hA0 : 0 ≤ M * x ^ (1 - δ) * (1 + Real.log T) := by positivity
  have hB0 : 0 ≤ M * x ^ 2 / (Δ * T ^ 2) := by positivity
  have hC0 : 0 ≤ (1 + Real.log x) * x ^ 2 / (Δ * T) := by positivity
  have hsmoothedBound :
      ‖cesaroPerronSmoothedSum a x Δ‖ ≤
        16 * M * x ^ (1 - δ) * (1 + Real.log T) +
          64 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) +
          32 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T) := by
    rw [hidentity, norm_mul, hnormFactor]
    calc
      (2 * Real.pi : ℝ)⁻¹ * ‖∫ t : ℝ, f t‖ ≤
          1 * ‖∫ t : ℝ, f t‖ := mul_le_mul_of_nonneg_right hfactorLe (norm_nonneg _)
      _ ≤ _ := by simpa [u] using hwholeBound
  have hlargeConstant :
      16 * (M * x ^ (1 - δ) * (1 + Real.log T)) +
        64 * Real.exp 1 * (M * x ^ 2 / (Δ * T ^ 2)) +
        32 * Real.exp 1 * ((1 + Real.log x) * x ^ 2 / (Δ * T)) ≤
        128 * Real.exp 1 *
          (M * x ^ (1 - δ) * (1 + Real.log T) +
            M * x ^ 2 / (Δ * T ^ 2) +
            (1 + Real.log x) * x ^ 2 / (Δ * T)) := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hcoeffA : (16 : ℝ) ≤ 128 * Real.exp 1 := by
      calc
        (16 : ℝ) ≤ 128 := by norm_num
        _ = (128 : ℝ) * 1 := by ring
        _ ≤ (128 : ℝ) * Real.exp 1 := mul_le_mul_of_nonneg_left he (by norm_num)
    have hcoeffB : 64 * Real.exp 1 ≤ 128 * Real.exp 1 :=
      mul_le_mul_of_nonneg_right (by norm_num : (64 : ℝ) ≤ 128) (Real.exp_nonneg 1)
    have hcoeffC : 32 * Real.exp 1 ≤ 128 * Real.exp 1 :=
      mul_le_mul_of_nonneg_right (by norm_num : (32 : ℝ) ≤ 128) (Real.exp_nonneg 1)
    have htermA := mul_le_mul_of_nonneg_right hcoeffA hA0
    have htermB := mul_le_mul_of_nonneg_right hcoeffB hB0
    have htermC := mul_le_mul_of_nonneg_right hcoeffC hC0
    calc
      _ = 16 * (M * x ^ (1 - δ) * (1 + Real.log T)) +
          (64 * Real.exp 1 * (M * x ^ 2 / (Δ * T ^ 2)) +
            32 * Real.exp 1 * ((1 + Real.log x) * x ^ 2 / (Δ * T))) := by ring
      _ ≤ 128 * Real.exp 1 * (M * x ^ (1 - δ) * (1 + Real.log T)) +
          (128 * Real.exp 1 * (M * x ^ 2 / (Δ * T ^ 2)) +
            128 * Real.exp 1 * ((1 + Real.log x) * x ^ 2 / (Δ * T))) :=
        add_le_add htermA (add_le_add htermB htermC)
      _ = _ := by ring
  have herr := cesaroPerronSmoothedSum_error ha hxpos hΔ
  have herrRev :
      ‖cesaroPerronSharpSum a x - cesaroPerronSmoothedSum a x Δ‖ ≤ Δ + 1 := by
    simpa only [norm_sub_rev] using herr
  calc
    ‖cesaroPerronSharpSum a x‖ ≤
        ‖cesaroPerronSharpSum a x - cesaroPerronSmoothedSum a x Δ‖ +
          ‖cesaroPerronSmoothedSum a x Δ‖ := by
      calc
        _ = ‖(cesaroPerronSharpSum a x - cesaroPerronSmoothedSum a x Δ) +
              cesaroPerronSmoothedSum a x Δ‖ := by
          exact congrArg norm (sub_add_cancel _ _).symm
        _ ≤ _ := norm_add_le _ _
    _ ≤ Δ + 1 +
        (16 * M * x ^ (1 - δ) * (1 + Real.log T) +
          64 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) +
          32 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T)) :=
      add_le_add herrRev hsmoothedBound
    _ ≤ _ := by
      have hlargeConstant' :
          16 * M * x ^ (1 - δ) * (1 + Real.log T) +
            64 * Real.exp 1 * M * x ^ 2 / (Δ * T ^ 2) +
            32 * Real.exp 1 * (1 + Real.log x) * x ^ 2 / (Δ * T) ≤
          128 * Real.exp 1 *
            (M * x ^ (1 - δ) * (1 + Real.log T) +
              M * x ^ 2 / (Δ * T ^ 2) +
              (1 + Real.log x) * x ^ 2 / (Δ * T)) := by
        simpa [mul_assoc, mul_div_assoc] using hlargeConstant
      exact add_le_add_right hlargeConstant' (Δ + 1)

end FractionalPrimes.Literature.LongArithmetic

end
