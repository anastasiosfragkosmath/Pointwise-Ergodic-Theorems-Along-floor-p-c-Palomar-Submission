module

public import FractionalPrimes.Literature.LongArithmetic.IntegrableFourierInversion
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.NumberTheory.LSeries.Basic

@[expose] public section

open MeasureTheory Set
open scoped FourierTransform

namespace FractionalPrimes.Literature.LongArithmetic

/-- Coefficients indexed by positive integers, represented by a natural
sequence with its zeroth term discarded as in Mathlib's `LSeries`. -/
def perronCoefficient (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else a n

noncomputable def perronDirichletSeries (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  LSeries (perronCoefficient a) s

/-- The Cesàro-smoothed Perron kernel from `lal:cesaro-perron`. -/
noncomputable def cesaroPerronKernel (x Δ : ℝ) (s : ℂ) : ℂ :=
  (Complex.exp ((s + 1) * (Real.log (x + Δ) : ℂ)) -
    Complex.exp ((s + 1) * (Real.log x : ℂ))) /
      ((Δ : ℂ) * s * (s + 1))

/-- The exact sharp-plus-triangular sum in the approved `lal:cesaro-perron`
statement. -/
noncomputable def cesaroPerronSharpSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), a n

noncomputable def cesaroPerronEdgeSum (a : ℕ → ℂ) (x Δ : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc (1 : ℕ) (Nat.floor (x + Δ)) : Finset ℕ).filter
      (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + Δ),
    (((x + Δ - (n : ℝ)) / Δ) : ℝ) * a n

noncomputable def cesaroPerronSmoothedSum (a : ℕ → ℂ) (x Δ : ℝ) : ℂ :=
  cesaroPerronSharpSum a x + cesaroPerronEdgeSum a x Δ

/-- The coefficient of `a n` in the finite smoothed sum. -/
noncomputable def cesaroPerronWeight (x Δ : ℝ) (n : ℕ) : ℂ :=
  if 0 < (n : ℝ) ∧ (n : ℝ) ≤ x then 1
  else if x < (n : ℝ) ∧ (n : ℝ) ≤ x + Δ then
    ↑((x + Δ - (n : ℝ)) / Δ)
  else 0

theorem perronDirichletSeries_summable
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {σ t : ℝ} (hσ : 1 < σ) :
    LSeriesSummable (perronCoefficient a) ((σ : ℂ) + Complex.I * (t : ℂ)) := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
  · intro n hn
    simp [perronCoefficient, hn, ha n (Nat.pos_of_ne_zero hn)]
  · simpa using hσ

/-- The logarithmic-variable function used to derive the smoothed Perron
kernel from Fourier inversion. -/
noncomputable def perronAuxiliaryFunction (σ u : ℝ) : ℂ :=
  Complex.exp (-(σ : ℂ) * ((max u 0 : ℝ) : ℂ)) *
    (1 - Complex.exp (-((max u 0 : ℝ) : ℂ)))

private noncomputable def perronAuxiliaryOnPositive (σ u : ℝ) : ℂ :=
  Complex.exp (-(σ : ℂ) * (u : ℂ)) -
    Complex.exp (-((σ + 1 : ℝ) : ℂ) * (u : ℂ))

private theorem perronAuxiliary_eq_indicator (σ : ℝ) :
    perronAuxiliaryFunction σ = (Ioi 0).indicator (perronAuxiliaryOnPositive σ) := by
  funext u
  by_cases hu : 0 < u
  · simp only [perronAuxiliaryFunction, max_eq_left hu.le,
      indicator_of_mem (show u ∈ Ioi 0 from hu), perronAuxiliaryOnPositive]
    calc
      Complex.exp (-(σ : ℂ) * (u : ℂ)) *
          (1 - Complex.exp (-(u : ℂ))) =
        Complex.exp (-(σ : ℂ) * (u : ℂ)) -
          Complex.exp (-(σ : ℂ) * (u : ℂ)) * Complex.exp (-(u : ℂ)) := by
            rw [mul_sub, mul_one]
      _ = Complex.exp (-(σ : ℂ) * (u : ℂ)) -
          Complex.exp (-(σ : ℂ) * (u : ℂ) + -(u : ℂ)) := by
            rw [Complex.exp_add]
      _ = Complex.exp (-(σ : ℂ) * (u : ℂ)) -
          Complex.exp (-((σ + 1 : ℝ) : ℂ) * (u : ℂ)) := by
            congr 2
            push_cast
            ring
  · have hu' : u ≤ 0 := le_of_not_gt hu
    by_cases hzero : u = 0
    · subst u
      simp [perronAuxiliaryFunction]
    · have hneg : u < 0 := lt_of_le_of_ne hu' hzero
      simp [perronAuxiliaryFunction, hu, max_eq_right hu']

private theorem integrable_perronAuxiliaryFunction {σ : ℝ} (hσ : 0 < σ) :
    Integrable (perronAuxiliaryFunction σ) := by
  rw [perronAuxiliary_eq_indicator]
  rw [integrable_indicator_iff measurableSet_Ioi]
  have h₁ : IntegrableOn
      (fun u : ℝ => Complex.exp (-(σ : ℂ) * (u : ℂ))) (Ioi 0) := by
    exact integrableOn_exp_mul_complex_Ioi (a := -(σ : ℂ)) (by simp [hσ]) 0
  have h₂ : IntegrableOn
      (fun u : ℝ => Complex.exp (-((σ + 1 : ℝ) : ℂ) * (u : ℂ))) (Ioi 0) := by
    apply integrableOn_exp_mul_complex_Ioi
      (a := -((σ + 1 : ℝ) : ℂ)) (c := 0)
    have hreal : - (σ + 1) < 0 := by linarith
    simpa using hreal
  convert h₁.sub h₂ using 1
  ext u
  simp only [perronAuxiliaryOnPositive]
  congr 1

private theorem continuousAt_perronAuxiliaryFunction (σ v : ℝ) :
    ContinuousAt (perronAuxiliaryFunction σ) v := by
  unfold perronAuxiliaryFunction
  fun_prop

private theorem angularFourierTransform_perronAuxiliary
    {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    angularFourierTransform (perronAuxiliaryFunction σ) t =
      (↑σ + Complex.I * (t : ℂ))⁻¹ -
        (↑(σ + 1) + Complex.I * (t : ℂ))⁻¹ := by
  have hfun : (fun u : ℝ => perronAuxiliaryFunction σ u *
      Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ))) =
      (Ioi 0).indicator (fun u : ℝ => perronAuxiliaryOnPositive σ u *
        Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ))) := by
    funext u
    rw [perronAuxiliary_eq_indicator]
    by_cases hu : u ∈ Ioi 0 <;> simp [hu]
  rw [angularFourierTransform, hfun, integral_indicator measurableSet_Ioi]
  have h₁ : IntegrableOn
      (fun u : ℝ => Complex.exp (-((σ : ℂ) + Complex.I * (t : ℂ)) * (u : ℂ)))
      (Ioi 0) := by
    apply integrableOn_exp_mul_complex_Ioi (a := -((σ : ℂ) + Complex.I * (t : ℂ))) (c := 0)
    have hre : (-((σ : ℂ) + Complex.I * (t : ℂ))).re = -σ := by simp
    rw [hre]
    exact neg_lt_zero.mpr hσ
  have h₂ : IntegrableOn
      (fun u : ℝ => Complex.exp
        (-(((σ + 1 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (u : ℂ)))
      (Ioi 0) := by
    apply integrableOn_exp_mul_complex_Ioi
      (a := -(((σ + 1 : ℝ) : ℂ) + Complex.I * (t : ℂ))) (c := 0)
    have hre : (-(((σ + 1 : ℝ) : ℂ) + Complex.I * (t : ℂ))).re = -(σ + 1) := by simp
    rw [hre]
    linarith
  have hformula : ∀ u : ℝ,
      perronAuxiliaryOnPositive σ u * Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ)) =
        Complex.exp (-((σ : ℂ) + Complex.I * (t : ℂ)) * (u : ℂ)) -
          Complex.exp (-(((σ + 1 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (u : ℂ)) := by
    intro u
    unfold perronAuxiliaryOnPositive
    rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring
  have hsplit :
      (∫ u : ℝ in Ioi 0, perronAuxiliaryOnPositive σ u *
        Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ))) =
      (∫ u : ℝ in Ioi 0,
        Complex.exp (-((σ : ℂ) + Complex.I * (t : ℂ)) * (u : ℂ))) -
        ∫ u : ℝ in Ioi 0,
          Complex.exp (-(((σ + 1 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (u : ℂ)) := by
    rw [integral_congr_ae]
    · exact integral_sub h₁ h₂
    · filter_upwards with u
      exact hformula u
  rw [hsplit]
  have hI₁ := integral_exp_mul_complex_Ioi
    (a := -((σ : ℂ) + Complex.I * (t : ℂ)))
    (by have hre : (-((σ : ℂ) + Complex.I * (t : ℂ))).re = -σ := by simp
        rw [hre]
        exact neg_lt_zero.mpr hσ) 0
  have hI₂ := integral_exp_mul_complex_Ioi
    (a := -(((σ + 1 : ℝ) : ℂ) + Complex.I * (t : ℂ))) (by
      have hre : (-(((σ + 1 : ℝ) : ℂ) + Complex.I * (t : ℂ))).re = -(σ + 1) := by simp
      rw [hre]
      linarith) 0
  rw [hI₁, hI₂]
  simp [mul_zero, Complex.exp_zero, div_eq_mul_inv]
  have hdA : -(Complex.I * (t : ℂ)) + -(↑σ : ℂ) =
      -((↑σ : ℂ) + Complex.I * (t : ℂ)) := by ring
  have hdB : -(Complex.I * (t : ℂ)) + ((-1 : ℂ) + -(↑σ : ℂ)) =
      -(↑σ + 1 + Complex.I * (t : ℂ)) := by
    ring_nf
  rw [hdA, hdB]
  simp only [inv_neg, neg_neg, sub_eq_add_neg]

private theorem perronRational_eq_productInverse
    {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (↑σ + Complex.I * (t : ℂ))⁻¹ -
        (↑(σ + 1) + Complex.I * (t : ℂ))⁻¹ =
      ((↑σ + Complex.I * (t : ℂ)) *
        (↑(σ + 1) + Complex.I * (t : ℂ)))⁻¹ := by
  have hA : (↑σ + Complex.I * (t : ℂ)) ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp at hr
    linarith
  have hB : (↑(σ + 1) + Complex.I * (t : ℂ)) ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp at hr
    linarith
  have hBcast : (↑(σ + 1) : ℂ) + Complex.I * (t : ℂ) =
      ↑σ + 1 + Complex.I * (t : ℂ) := by
    push_cast
    ring
  have hB' : (↑σ + 1 + Complex.I * (t : ℂ)) ≠ 0 := by
    rw [← hBcast]
    exact hB
  rw [hBcast]
  field_simp [hA, hB']
  ring_nf

private theorem integrable_perronRationalKernel
    {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t : ℝ =>
      ((↑σ + Complex.I * (t : ℂ)) *
        (↑(σ + 1) + Complex.I * (t : ℂ)))⁻¹) := by
  let c : ℝ := min σ 1
  have hcpos : 0 < c := by
    dsimp [c]
    exact lt_min hσ zero_lt_one
  have hcσ : c ≤ σ := min_le_left _ _
  have hc1 : c ≤ 1 := min_le_right _ _
  have hc2σ : c ^ 2 ≤ σ ^ 2 := by nlinarith
  have hc21 : c ^ 2 ≤ 1 := by nlinarith
  have hbaseA (t : ℝ) : c ^ 2 * (1 + t ^ 2) ≤ σ ^ 2 + t ^ 2 := by
    calc
      c ^ 2 * (1 + t ^ 2) = c ^ 2 + c ^ 2 * t ^ 2 := by ring
      _ ≤ σ ^ 2 + t ^ 2 := by
        have hct : c ^ 2 * t ^ 2 ≤ t ^ 2 := by
          simpa using mul_le_mul_of_nonneg_right hc21 (sq_nonneg t)
        exact add_le_add hc2σ hct
  have hbaseB (t : ℝ) : 1 + t ^ 2 ≤ (σ + 1) ^ 2 + t ^ 2 := by
    nlinarith [sq_nonneg (σ + 1 - 1)]
  have hnormA (t : ℝ) :
      c * Real.sqrt (1 + t ^ 2) ≤ ‖(↑σ : ℂ) + (t : ℂ) * Complex.I‖ := by
    rw [Complex.norm_add_mul_I]
    apply le_of_sq_le_sq ?_ (Real.sqrt_nonneg _)
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    nlinarith [hbaseA t]
  have hnormB (t : ℝ) :
      Real.sqrt (1 + t ^ 2) ≤ ‖(↑(σ + 1) : ℂ) + (t : ℂ) * Complex.I‖ := by
    rw [Complex.norm_add_mul_I]
    apply le_of_sq_le_sq ?_ (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    nlinarith [hbaseB t]
  have hdenom (t : ℝ) :
      c * (1 + t ^ 2) ≤
        ‖(↑σ : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖(↑(σ + 1) : ℂ) + (t : ℂ) * Complex.I‖ := by
    calc
      c * (1 + t ^ 2) =
          c * Real.sqrt (1 + t ^ 2) ^ 2 := by
        congr 1
        exact (Real.sq_sqrt (show 0 ≤ 1 + t ^ 2 by positivity)).symm
      _ = (c * Real.sqrt (1 + t ^ 2)) * Real.sqrt (1 + t ^ 2) := by ring
      _ ≤ _ := mul_le_mul (hnormA t) (hnormB t)
        (Real.sqrt_nonneg _) (norm_nonneg _)
  have hmajor : Integrable (fun t : ℝ => c⁻¹ * (1 + t ^ 2)⁻¹) := by
    simpa [mul_comm] using integrable_inv_one_add_sq.const_mul c⁻¹
  apply hmajor.mono'
  · fun_prop
  · filter_upwards with t
    have hdenpos : 0 < c * (1 + t ^ 2) := by positivity
    calc
      ‖((↑σ + Complex.I * (t : ℂ)) *
          (↑(σ + 1) + Complex.I * (t : ℂ)))⁻¹‖ =
        (‖(↑σ : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖(↑(σ + 1) : ℂ) + (t : ℂ) * Complex.I‖)⁻¹ := by
            simp [mul_comm]
      _ ≤ (c * (1 + t ^ 2))⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hdenpos (hdenom t)
      _ = c⁻¹ * (1 + t ^ 2)⁻¹ := by
        field_simp [ne_of_gt hcpos]

private theorem integrable_angularFourierTransform_perronAuxiliary
    {σ : ℝ} (hσ : 0 < σ) :
    Integrable (angularFourierTransform (perronAuxiliaryFunction σ)) := by
  have hfun : angularFourierTransform (perronAuxiliaryFunction σ) =
      fun t : ℝ =>
        ((↑σ + Complex.I * (t : ℂ)) *
          (↑(σ + 1) + Complex.I * (t : ℂ)))⁻¹ := by
    funext t
    rw [angularFourierTransform_perronAuxiliary hσ t,
      perronRational_eq_productInverse hσ t]
  rw [hfun]
  exact integrable_perronRationalKernel hσ

/-- The approved `lal:lone-inversion` kernel route, specialized to the
one-sided exponential used in the smoothed Perron identity. -/
theorem perronAuxiliary_fourierInversion
    {σ v : ℝ} (hσ : 0 < σ) :
    perronAuxiliaryFunction σ v =
      (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∫ t : ℝ, angularFourierTransform (perronAuxiliaryFunction σ) t *
          Complex.exp (Complex.I * (t : ℂ) * (v : ℂ)) := by
  exact integrableFourierInversion (integrable_perronAuxiliaryFunction hσ)
    (integrable_angularFourierTransform_perronAuxiliary hσ)
    (continuousAt_perronAuxiliaryFunction σ v)

#print axioms perronAuxiliary_fourierInversion

noncomputable def perronVerticalKernel (σ y t : ℝ) : ℂ :=
  Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Real.log y : ℂ)) *
    ((↑σ + Complex.I * (t : ℂ)) *
      (↑(σ + 1) + Complex.I * (t : ℂ)))⁻¹

/-- The scalar Perron kernel identity obtained by applying the approved
angular Fourier inversion lemma to its one-sided exponential. -/
theorem cesaroPerronKernelIdentity
    {σ y : ℝ} (hσ : 0 < σ) (hy : 0 < y) :
    (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∫ t : ℝ, perronVerticalKernel σ y t =
      if 1 ≤ y then (↑(1 - y⁻¹) : ℂ) else 0 := by
  have hInv := perronAuxiliary_fourierInversion (σ := σ) (v := Real.log y) hσ
  have hInv' : perronAuxiliaryFunction σ (Real.log y) =
      (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∫ t : ℝ,
          ((↑σ + Complex.I * (t : ℂ)) *
            (↑(σ + 1) + Complex.I * (t : ℂ)))⁻¹ *
              Complex.exp (Complex.I * (t : ℂ) * (Real.log y : ℂ)) := by
    simpa only [angularFourierTransform_perronAuxiliary hσ,
      perronRational_eq_productInverse hσ, mul_comm] using hInv
  have hintegral :
      (∫ t : ℝ, perronVerticalKernel σ y t) =
        Complex.exp ((σ : ℂ) * (Real.log y : ℂ)) *
          ∫ t : ℝ,
            ((↑σ + Complex.I * (t : ℂ)) *
              (↑(σ + 1) + Complex.I * (t : ℂ)))⁻¹ *
                Complex.exp (Complex.I * (t : ℂ) * (Real.log y : ℂ)) := by
    calc
      (∫ t : ℝ, perronVerticalKernel σ y t) =
          ∫ t : ℝ, Complex.exp ((σ : ℂ) * (Real.log y : ℂ)) *
            (((↑σ + Complex.I * (t : ℂ)) *
              (↑(σ + 1) + Complex.I * (t : ℂ)))⁻¹ *
                Complex.exp (Complex.I * (t : ℂ) * (Real.log y : ℂ))) := by
          apply integral_congr_ae
          filter_upwards with t
          unfold perronVerticalKernel
          rw [add_mul, Complex.exp_add]
          ring
      _ = _ := by rw [integral_const_mul]
  rw [hintegral]
  calc
    (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        (Complex.exp ((σ : ℂ) * (Real.log y : ℂ)) *
          ∫ t : ℝ,
            ((↑σ + Complex.I * (t : ℂ)) *
              (↑(σ + 1) + Complex.I * (t : ℂ)))⁻¹ *
                Complex.exp (Complex.I * (t : ℂ) * (Real.log y : ℂ))) =
      Complex.exp ((σ : ℂ) * (Real.log y : ℂ)) *
        perronAuxiliaryFunction σ (Real.log y) := by
          calc
            _ = Complex.exp ((σ : ℂ) * (Real.log y : ℂ)) *
                ((↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
                  ∫ t : ℝ,
                    ((↑σ + Complex.I * (t : ℂ)) *
                      (↑(σ + 1) + Complex.I * (t : ℂ)))⁻¹ *
                        Complex.exp (Complex.I * (t : ℂ) * (Real.log y : ℂ))) := by ring
            _ = _ := by rw [hInv']
    _ = if 1 ≤ y then (↑(1 - y⁻¹) : ℂ) else 0 := by
      by_cases hle : 1 ≤ y
      · have hlog : 0 ≤ Real.log y := (Real.log_nonneg_iff hy).2 hle
        have hcancel :
            Complex.exp ((σ : ℂ) * (Real.log y : ℂ)) *
              Complex.exp ((-(σ : ℂ)) * (Real.log y : ℂ)) = 1 := by
          rw [← Complex.exp_add]
          rw [show (σ : ℂ) * (Real.log y : ℂ) +
              (-(σ : ℂ)) * (Real.log y : ℂ) = 0 by ring, Complex.exp_zero]
        have hlogexp : Complex.exp (-(Real.log y : ℂ)) = (↑(y⁻¹) : ℂ) := by
          rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hy]
        rw [if_pos hle, perronAuxiliaryFunction, max_eq_left hlog]
        calc
          Complex.exp ((σ : ℂ) * (Real.log y : ℂ)) *
              (Complex.exp ((-(σ : ℂ)) * (Real.log y : ℂ)) *
                (1 - Complex.exp (-(Real.log y : ℂ)))) =
            1 - Complex.exp (-(Real.log y : ℂ)) := by
              rw [← mul_assoc, hcancel]
              simp
          _ = (↑(1 - y⁻¹) : ℂ) := by rw [hlogexp]; push_cast; ring
      · have hlog : Real.log y < 0 := (Real.log_neg_iff hy).2 (lt_of_not_ge hle)
        rw [if_neg hle, perronAuxiliaryFunction, max_eq_right hlog.le]
        simp

private theorem integrable_perronVerticalKernel
    {σ y : ℝ} (hσ : 0 < σ) (hy : 0 < y) :
    Integrable (perronVerticalKernel σ y) := by
  let phase : ℝ → ℂ := fun t =>
    Complex.exp (Complex.I * (t : ℂ) * (Real.log y : ℂ))
  let rational : ℝ → ℂ := fun t =>
    ((↑σ + Complex.I * (t : ℂ)) *
      (↑(σ + 1) + Complex.I * (t : ℂ)))⁻¹
  have hphase : AEStronglyMeasurable phase := by fun_prop
  have hphase_bound : ∀ᵐ t : ℝ, ‖phase t‖ ≤ 1 := by
    filter_upwards with t
    simp [phase, Complex.norm_exp]
  have hmul := (integrable_perronRationalKernel hσ).bdd_mul hphase hphase_bound
  have hrewrite : perronVerticalKernel σ y = fun t : ℝ =>
      Complex.exp ((σ : ℂ) * (Real.log y : ℂ)) * (phase t * rational t) := by
    funext t
    simp only [perronVerticalKernel, phase, rational]
    rw [add_mul, Complex.exp_add]
    ring
  rw [hrewrite]
  exact hmul.const_mul (Complex.exp ((σ : ℂ) * (Real.log y : ℂ)))

private theorem cesaroPerronKernelLine_eq
    {x Δ σ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) (hσ : 0 < σ) (t : ℝ) :
    cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ)) =
      (((↑(x + Δ) : ℂ) * perronVerticalKernel σ (x + Δ) t) -
        (↑x : ℂ) * perronVerticalKernel σ x t) / (Δ : ℂ) := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hX : Complex.exp ((s + 1) * (Real.log (x + Δ) : ℂ)) =
      (↑(x + Δ) : ℂ) * Complex.exp (s * (Real.log (x + Δ) : ℂ)) := by
    rw [show (s + 1) * (Real.log (x + Δ) : ℂ) =
      s * (Real.log (x + Δ) : ℂ) + (Real.log (x + Δ) : ℂ) by ring,
      Complex.exp_add]
    rw [← Complex.ofReal_exp, Real.exp_log (by linarith : 0 < x + Δ)]
    ring
  have hxexp : Complex.exp ((s + 1) * (Real.log x : ℂ)) =
      (↑x : ℂ) * Complex.exp (s * (Real.log x : ℂ)) := by
    rw [show (s + 1) * (Real.log x : ℂ) =
      s * (Real.log x : ℂ) + (Real.log x : ℂ) by ring,
      Complex.exp_add]
    rw [← Complex.ofReal_exp, Real.exp_log hx]
    ring
  have hden : (s * (s + 1)) =
      ((↑σ + Complex.I * (t : ℂ)) *
        (↑(σ + 1) + Complex.I * (t : ℂ))) := by
    dsimp [s]
    push_cast
    ring
  have hs : s ≠ 0 := by
    intro hs0
    have hreal := congrArg Complex.re hs0
    simp [s] at hreal
    linarith
  have hs1 : s + 1 ≠ 0 := by
    intro hs0
    have hreal := congrArg Complex.re hs0
    simp [s] at hreal
    linarith
  rw [cesaroPerronKernel]
  simp only [perronVerticalKernel]
  dsimp [s] at hX hxexp hden ⊢
  rw [hX, hxexp, ← hden]
  field_simp [ne_of_gt hΔ, hs, hs1]

private theorem integrable_cesaroPerronKernelLine
    {x Δ σ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) (hσ : 0 < σ) :
    Integrable (fun t : ℝ =>
      cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))) := by
  have hrewrite : (fun t : ℝ =>
      cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))) =
      fun t => (((↑(x + Δ) : ℂ) * perronVerticalKernel σ (x + Δ) t) -
        (↑x : ℂ) * perronVerticalKernel σ x t) / (Δ : ℂ) := by
    funext t
    exact cesaroPerronKernelLine_eq hx hΔ hσ t
  rw [hrewrite]
  have htop := (integrable_perronVerticalKernel hσ (by linarith : 0 < x + Δ)).const_mul
    (↑(x + Δ) : ℂ)
  have hbot := (integrable_perronVerticalKernel hσ hx).const_mul (↑x : ℂ)
  have hsub := htop.sub hbot
  simpa [div_eq_mul_inv, mul_assoc] using hsub.mul_const (Δ : ℂ)⁻¹

private noncomputable def perronLineTerm (a : ℕ → ℂ) (x Δ σ : ℝ)
    (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (perronCoefficient a) ((σ : ℂ) + Complex.I * (t : ℂ)) n *
    cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))

private noncomputable def perronTermNormBound (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ‖a n‖ / (n : ℝ) ^ σ

private theorem perronLineTerm_norm_eq
    {a : ℕ → ℂ} {σ : ℝ} (hσ : 0 < σ) (n : ℕ) (t : ℝ) :
    ‖LSeries.term (perronCoefficient a) ((σ : ℂ) + Complex.I * (t : ℂ)) n‖ =
      perronTermNormBound a σ n := by
  by_cases hn : n = 0
  · simp [hn, perronTermNormBound]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hre : ((σ : ℂ) + Complex.I * (t : ℂ)).re = σ := by simp
    rw [LSeries.norm_term_eq]
    simp only [hn, if_false, perronCoefficient]
    rw [hre]
    simp [perronTermNormBound, hn]

private theorem integrable_perronLineTerm
    {a : ℕ → ℂ} {x Δ σ : ℝ}
    (hx : 0 < x) (hΔ : 0 < Δ) (hσ : 1 < σ) (n : ℕ) :
    Integrable (perronLineTerm a x Δ σ n) := by
  have hK := integrable_cesaroPerronKernelLine hx hΔ (by linarith : 0 < σ)
  have hbound (t : ℝ) :
      ‖perronLineTerm a x Δ σ n t‖ ≤
        perronTermNormBound a σ n *
          ‖cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
    simp only [perronLineTerm, norm_mul]
    rw [perronLineTerm_norm_eq (a := a) (by linarith : 0 < σ) n t]
  have hmajor := hK.norm.const_mul (perronTermNormBound a σ n)
  apply hmajor.mono'
  · by_cases hn : n = 0
    · subst n
      change AEStronglyMeasurable (fun t : ℝ =>
        LSeries.term (perronCoefficient a) ((σ : ℂ) + Complex.I * (t : ℂ)) 0 *
          cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ)))
      simp only [LSeries.term_zero, zero_mul]
      fun_prop
    · change AEStronglyMeasurable (fun t : ℝ =>
        LSeries.term (perronCoefficient a) ((σ : ℂ) + Complex.I * (t : ℂ)) n *
          cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ)))
      have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hscont : Continuous (fun t : ℝ =>
          (σ : ℂ) + Complex.I * (t : ℂ)) := by fun_prop
      have hpowcont : Continuous (fun t : ℝ =>
          (n : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ))) :=
        hscont.const_cpow (Or.inl hncast)
      have hpowne (t : ℝ) :
          (n : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 0 :=
        (Complex.cpow_ne_zero_iff).2 (Or.inl hncast)
      have hquot : Continuous (fun t : ℝ =>
          a n / (n : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ))) :=
        continuous_const.div₀ hpowcont hpowne
      have hprod := hquot.aestronglyMeasurable.mul hK.aestronglyMeasurable
      convert hprod using 1
      ext t
      simp [LSeries.term_of_ne_zero hn, perronCoefficient, hn]
  · filter_upwards with t
    exact hbound t

private theorem perronTermNormBound_le
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    perronTermNormBound a σ n ≤ 1 / (n : ℝ) ^ σ := by
  by_cases hn : n = 0
  · have hzero : (0 : ℝ) ^ σ = 0 := Real.zero_rpow (ne_of_gt hσ)
    simp [perronTermNormBound, hn, hzero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    simp [perronTermNormBound, hn]
    have hp : 0 < (n : ℝ) ^ σ :=
      Real.rpow_pos_of_pos (by exact_mod_cast hnpos) σ
    simpa [one_div] using (div_le_div_iff_of_pos_right hp).2 (ha n hnpos)

private theorem perronLineTerm_integral_norm_summable
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {x Δ σ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖perronLineTerm a x Δ σ n t‖) := by
  have hK := integrable_cesaroPerronKernelLine hx hΔ (by linarith : 0 < σ)
  let C : ℝ := ∫ t : ℝ,
    ‖cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))‖
  have hC : 0 ≤ C := by
    dsimp [C]
    exact integral_nonneg (fun t => norm_nonneg _)
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ σ) :=
    Real.summable_one_div_nat_rpow.mpr hσ
  have hscaled : Summable (fun n : ℕ => (1 / (n : ℝ) ^ σ) * C) :=
    hbase.mul_right C
  apply Summable.of_nonneg_of_le
  · intro n
    exact integral_nonneg (fun t => norm_nonneg _)
  · intro n
    have hterm := integrable_perronLineTerm (a := a) hx hΔ hσ n
    have hKnorm := hK.norm.const_mul (perronTermNormBound a σ n)
    have hpoint (t : ℝ) :
        ‖perronLineTerm a x Δ σ n t‖ ≤
          perronTermNormBound a σ n *
            ‖cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
      simp only [perronLineTerm, norm_mul]
      rw [perronLineTerm_norm_eq (a := a) (by linarith : 0 < σ) n t]
    have hInt := integral_mono_ae hterm.norm hKnorm (ae_of_all _ hpoint)
    calc
      (∫ t : ℝ, ‖perronLineTerm a x Δ σ n t‖) ≤
          perronTermNormBound a σ n * C := by
            dsimp [C] at *
            simpa [integral_const_mul] using hInt
      _ ≤ (1 / (n : ℝ) ^ σ) * C :=
            mul_le_mul_of_nonneg_right
              (perronTermNormBound_le ha (by linarith : 0 < σ) n) hC
  · simpa [C] using hscaled

private theorem integral_tsum_perronLineTerm
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {x Δ σ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) (hσ : 1 < σ) :
    ∫ t : ℝ, perronDirichletSeries a ((σ : ℂ) + Complex.I * (t : ℂ)) *
        cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ)) =
      ∑' n : ℕ, ∫ t : ℝ, perronLineTerm a x Δ σ n t := by
  have hsum := perronLineTerm_integral_norm_summable ha hx hΔ hσ
  symm
  rw [integral_tsum_of_summable_integral_norm
      (fun n => integrable_perronLineTerm hx hΔ hσ n) hsum]
  apply integral_congr_ae
  filter_upwards with t
  have hDir := perronDirichletSeries_summable (a := a) ha (t := t) hσ
  change (∑' n : ℕ,
      LSeries.term (perronCoefficient a) ((σ : ℂ) + Complex.I * (t : ℂ)) n *
        cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))) =
      (∑' n : ℕ, LSeries.term (perronCoefficient a)
        ((σ : ℂ) + Complex.I * (t : ℂ)) n) *
          cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))
  exact hDir.tsum_mul_right _

private theorem exp_neg_log_mul_perronVerticalKernel
    {n y σ : ℝ} (hn : 0 < n) (hy : 0 < y) (t : ℝ) :
    Complex.exp (-((σ : ℂ) + Complex.I * (t : ℂ)) * (Real.log n : ℂ)) *
        perronVerticalKernel σ y t =
      perronVerticalKernel σ (y / n) t := by
  have hn' : n ≠ 0 := ne_of_gt hn
  have hy' : y ≠ 0 := ne_of_gt hy
  have hlog : (Real.log (y / n) : ℂ) =
      (Real.log y : ℂ) - (Real.log n : ℂ) := by
    exact_mod_cast Real.log_div hy' hn'
  have hexp :
      Complex.exp (-((σ : ℂ) + Complex.I * (t : ℂ)) * (Real.log n : ℂ)) *
        Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Real.log y : ℂ)) =
      Complex.exp (((σ : ℂ) + Complex.I * (t : ℂ)) * (Real.log (y / n) : ℂ)) := by
    rw [← Complex.exp_add]
    rw [hlog]
    congr 1
    ring
  unfold perronVerticalKernel
  rw [← mul_assoc, hexp]

private theorem perronLineTerm_eq_ratioKernels
    {a : ℕ → ℂ} {x Δ σ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) (hσ : 1 < σ)
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    perronLineTerm a x Δ σ n t =
      (a n / (Δ : ℂ)) *
        ((↑(x + Δ) : ℂ) * perronVerticalKernel σ ((x + Δ) / n) t -
          (↑x : ℂ) * perronVerticalKernel σ (x / n) t) := by
  have hterm :
      LSeries.term (perronCoefficient a) ((σ : ℂ) + Complex.I * (t : ℂ)) n =
        a n * Complex.exp (-((σ : ℂ) + Complex.I * (t : ℂ)) * (Real.log n : ℂ)) := by
    have hzero : perronCoefficient a 0 = 0 := by simp [perronCoefficient]
    have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    rw [LSeries.term_def₀ hzero]
    simp only [perronCoefficient, if_neg (Nat.ne_of_gt hn)]
    rw [Complex.cpow_def_of_ne_zero hncast, Complex.natCast_log]
    congr 1
    ring_nf
  rw [perronLineTerm, hterm, cesaroPerronKernelLine_eq hx hΔ (by linarith : 0 < σ) t]
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have htop := exp_neg_log_mul_perronVerticalKernel
    (σ := σ) hnreal (by linarith : 0 < x + Δ) t
  have hbottom := exp_neg_log_mul_perronVerticalKernel (σ := σ) hnreal hx t
  calc
    _ = (a n / (Δ : ℂ)) *
          ((↑(x + Δ) : ℂ) *
              (Complex.exp (-((σ : ℂ) + Complex.I * (t : ℂ)) * (Real.log n : ℂ)) *
                perronVerticalKernel σ (x + Δ) t) -
            (↑x : ℂ) *
              (Complex.exp (-((σ : ℂ) + Complex.I * (t : ℂ)) * (Real.log n : ℂ)) *
                perronVerticalKernel σ x t)) := by
      field_simp [ne_of_gt hΔ]
    _ = _ := by rw [htop, hbottom]

private theorem perronLineTerm_integral_eq_weight
    {a : ℕ → ℂ} {x Δ σ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) (hσ : 1 < σ)
    (n : ℕ) :
    (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∫ t : ℝ, perronLineTerm a x Δ σ n t =
      a n * cesaroPerronWeight x Δ n := by
  by_cases hn : n = 0
  · subst n
    simp only [perronLineTerm, LSeries.term_zero, zero_mul, integral_zero, mul_zero]
    have hxnot : ¬x < 0 := not_lt.mpr hx.le
    simp [cesaroPerronWeight, hxnot]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hσpos : 0 < σ := by linarith
    have hXpos : 0 < x + Δ := by linarith
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    have hΔC : (Δ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hΔ)
    have hXC : ((x + Δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hXpos)
    have hXsumC : (↑x + ↑Δ : ℂ) ≠ 0 := by simpa using hXC
    have hVtop := integrable_perronVerticalKernel hσpos (div_pos hXpos hnreal)
    have hVbottom := integrable_perronVerticalKernel hσpos (div_pos hx hnreal)
    have hfun : (fun t : ℝ => perronLineTerm a x Δ σ n t) =
        fun t => (a n / (Δ : ℂ)) *
          ((↑(x + Δ) : ℂ) * perronVerticalKernel σ ((x + Δ) / n) t -
            (↑x : ℂ) * perronVerticalKernel σ (x / n) t) := by
      funext t
      exact perronLineTerm_eq_ratioKernels hx hΔ hσ hnpos t
    have hIntegral :
        (∫ t : ℝ, perronLineTerm a x Δ σ n t) =
          (a n / (Δ : ℂ)) *
            ((↑(x + Δ) : ℂ) *
                (∫ t : ℝ, perronVerticalKernel σ ((x + Δ) / n) t) -
              (↑x : ℂ) *
                (∫ t : ℝ, perronVerticalKernel σ (x / n) t)) := by
      have hsub :
          (∫ t : ℝ, (↑(x + Δ) : ℂ) * perronVerticalKernel σ ((x + Δ) / n) t -
              (↑x : ℂ) * perronVerticalKernel σ (x / n) t) =
            (↑(x + Δ) : ℂ) *
                (∫ t : ℝ, perronVerticalKernel σ ((x + Δ) / n) t) -
              (↑x : ℂ) *
                (∫ t : ℝ, perronVerticalKernel σ (x / n) t) := by
        have htopInt :
            (∫ u : ℝ, perronVerticalKernel σ ((x + Δ) / n) u) =
              (∫ t : ℝ, perronVerticalKernel σ ((x + Δ) / n) t) := by
          apply integral_congr_ae
          filter_upwards with t
          rfl
        have hbottomInt :
            (∫ u : ℝ, perronVerticalKernel σ (x / n) u) =
              (∫ t : ℝ, perronVerticalKernel σ (x / n) t) := by
          apply integral_congr_ae
          filter_upwards with t
          rfl
        calc
          _ = (∫ t : ℝ, (↑(x + Δ) : ℂ) *
                perronVerticalKernel σ ((x + Δ) / n) t) -
              ∫ t : ℝ, (↑x : ℂ) * perronVerticalKernel σ (x / n) t :=
                integral_sub (hVtop.const_mul (↑(x + Δ) : ℂ))
                  (hVbottom.const_mul (↑x : ℂ))
          _ = (↑(x + Δ) : ℂ) *
                (∫ t : ℝ, perronVerticalKernel σ ((x + Δ) / n) t) -
              (↑x : ℂ) * (∫ t : ℝ, perronVerticalKernel σ (x / n) t) := by
                rw [integral_const_mul, integral_const_mul, htopInt, hbottomInt]
      calc
        _ = ∫ t : ℝ, (a n / (Δ : ℂ)) *
              ((↑(x + Δ) : ℂ) * perronVerticalKernel σ ((x + Δ) / n) t -
                (↑x : ℂ) * perronVerticalKernel σ (x / n) t) := by
              apply integral_congr_ae
              filter_upwards with t
              exact congrFun hfun t
        _ = (a n / (Δ : ℂ)) *
              ∫ t : ℝ, (↑(x + Δ) : ℂ) * perronVerticalKernel σ ((x + Δ) / n) t -
                (↑x : ℂ) * perronVerticalKernel σ (x / n) t := integral_const_mul _ _
        _ = _ := congrArg (fun z : ℂ => (a n / (Δ : ℂ)) * z) hsub
    have htop := cesaroPerronKernelIdentity hσpos (div_pos hXpos hnreal)
      (σ := σ) (y := (x + Δ) / n)
    have hbottom := cesaroPerronKernelIdentity hσpos (div_pos hx hnreal)
      (σ := σ) (y := x / n)
    have htop' : (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∫ t : ℝ, perronVerticalKernel σ ((x + Δ) / n) t =
          if (n : ℝ) ≤ x + Δ then
            (↑(1 - (n : ℝ) / (x + Δ)) : ℂ) else 0 := by
      simpa [one_le_div₀ hnreal, inv_div] using htop
    have hbottom' : (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∫ t : ℝ, perronVerticalKernel σ (x / n) t =
          if (n : ℝ) ≤ x then (↑(1 - (n : ℝ) / x) : ℂ) else 0 := by
      simpa [one_le_div₀ hnreal, inv_div] using hbottom
    rw [hIntegral]
    have hreduce :
        (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
            ((a n / (Δ : ℂ)) *
              ((↑(x + Δ) : ℂ) *
                  (∫ t : ℝ, perronVerticalKernel σ ((x + Δ) / n) t) -
                (↑x : ℂ) *
                  (∫ t : ℝ, perronVerticalKernel σ (x / n) t))) =
          (a n / (Δ : ℂ)) *
            ((↑(x + Δ) : ℂ) *
                ((↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
                  ∫ t : ℝ, perronVerticalKernel σ ((x + Δ) / n) t) -
              (↑x : ℂ) *
                ((↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
                  ∫ t : ℝ, perronVerticalKernel σ (x / n) t)) := by
      simp only [mul_sub]
      ring_nf
    rw [hreduce, htop', hbottom']
    by_cases hnx : (n : ℝ) ≤ x <;> by_cases hN : (n : ℝ) ≤ x + Δ
    · simp [cesaroPerronWeight, hnreal, hnx, hN]
      field_simp [hΔC, hxC, hXC, hXsumC]
      ring_nf
    · exfalso
      have hle : x ≤ x + Δ := by linarith
      linarith
    · simp [cesaroPerronWeight, hnreal, hnx, hN]
      have hxn : x < (n : ℝ) := lt_of_not_ge hnx
      simp [hxn, cesaroPerronWeight, hnreal, hnx, hN] <;>
        field_simp [hΔC, hxC, hXC, hXsumC] <;> ring_nf
    · have hnotx : ¬(0 < (n : ℝ) ∧ (n : ℝ) ≤ x) := by
        exact fun h => hnx h.2
      have hnotedge : ¬(x < (n : ℝ) ∧ (n : ℝ) ≤ x + Δ) := by
        exact fun h => hN h.2
      simp [cesaroPerronWeight, hnx, hN, hnotx, hnotedge]

private theorem cesaroPerron_weight_tsum
    (a : ℕ → ℂ) {x Δ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) :
    (∑' n : ℕ, a n * cesaroPerronWeight x Δ n) =
      ∑ n ∈ Finset.Icc 1 (Nat.floor (x + Δ)),
        a n * cesaroPerronWeight x Δ n := by
  classical
  apply tsum_eq_sum (s := Finset.Icc 1 (Nat.floor (x + Δ)))
  intro n hn
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  rcases hn with hnzero | hnlarge
  · have hn0 : n = 0 := by omega
    subst n
    have hw : cesaroPerronWeight x Δ 0 = 0 := by
      simp [cesaroPerronWeight, not_lt.mpr hx.le]
    simp [hw]
  · have hcast : (Nat.floor (x + Δ) : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hnlarge)
    have hlarge : x + Δ < (n : ℝ) := by
      exact (Nat.lt_floor_add_one (x + Δ)).trans_le (by simpa using hcast)
    have hw : cesaroPerronWeight x Δ n = 0 := by
      have hxn : x < (n : ℝ) := by linarith
      simp [cesaroPerronWeight, hxn, not_le_of_gt hlarge]
    simp [hw]

private theorem cesaroPerronSmoothedSum_eq_weightSum
    (a : ℕ → ℂ) {x Δ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) :
    cesaroPerronSmoothedSum a x Δ =
      ∑ n ∈ Finset.Icc 1 (Nat.floor (x + Δ)),
        a n * cesaroPerronWeight x Δ n := by
  classical
  let P : ℕ → Prop := fun n => (n : ℝ) ≤ x
  have hMleN : Nat.floor x ≤ Nat.floor (x + Δ) :=
    Nat.floor_mono (by linarith)
  have hsharp : Finset.Icc 1 (Nat.floor x) =
      (Finset.Icc 1 (Nat.floor (x + Δ))).filter P := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨hn1, hnx⟩
      refine ⟨⟨hn1, Nat.le_trans hnx hMleN⟩, ?_⟩
      exact (Nat.le_floor_iff' (by omega)).mp hnx
    · rintro ⟨⟨hn1, hnN⟩, hnx⟩
      exact ⟨hn1, (Nat.le_floor_iff' (by omega)).mpr hnx⟩
  have hedge :
      (Finset.Icc 1 (Nat.floor (x + Δ))).filter (fun n : ℕ => ¬ P n) =
        (Finset.Icc 1 (Nat.floor (x + Δ))).filter
          (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + Δ) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hnmem, hnnot⟩
      have hnIcc := Finset.mem_Icc.mp hnmem
      have hnN := hnIcc.2
      have hnupper : (n : ℝ) ≤ x + Δ :=
        (Nat.le_floor_iff' (by omega : n ≠ 0)).mp hnN
      exact ⟨hnmem, lt_of_not_ge hnnot, hnupper⟩
    · rintro ⟨hnmem, hnx, hnupper⟩
      exact ⟨hnmem, not_le_of_gt hnx⟩
  have hsharpSum :
      (∑ n ∈ (Finset.Icc 1 (Nat.floor (x + Δ))).filter P, a n) =
        ∑ n ∈ (Finset.Icc 1 (Nat.floor (x + Δ))).filter P,
          a n * cesaroPerronWeight x Δ n := by
    apply Finset.sum_congr rfl
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnmem, hnx⟩
    have hnIcc := Finset.mem_Icc.mp hnmem
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    change (n : ℝ) ≤ x at hnx
    have hw : cesaroPerronWeight x Δ n = 1 := by
      simp [cesaroPerronWeight, hnpos, hnx]
    rw [hw, mul_one]
  have hedgeSum :
      (∑ n ∈ (Finset.Icc 1 (Nat.floor (x + Δ))).filter (fun n : ℕ => ¬ P n),
          (↑((x + Δ - (n : ℝ)) / Δ) : ℂ) * a n) =
        ∑ n ∈ (Finset.Icc 1 (Nat.floor (x + Δ))).filter (fun n : ℕ => ¬ P n),
          a n * cesaroPerronWeight x Δ n := by
    apply Finset.sum_congr rfl
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnmem, hnnot⟩
    have hnIcc := Finset.mem_Icc.mp hnmem
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    change ¬((n : ℝ) ≤ x) at hnnot
    have hnx : x < (n : ℝ) := lt_of_not_ge hnnot
    have hnupper : (n : ℝ) ≤ x + Δ :=
      (Nat.le_floor_iff' (by omega : n ≠ 0)).mp hnIcc.2
    have hw : cesaroPerronWeight x Δ n =
        ↑((x + Δ - (n : ℝ)) / Δ) := by
      simp [cesaroPerronWeight, hnpos, hnx, hnupper]
    rw [hw]
    ring
  change (∑ n ∈ Finset.Icc 1 (Nat.floor x), a n) +
      ∑ n ∈ (Finset.Icc 1 (Nat.floor (x + Δ))).filter
          (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + Δ),
          (↑((x + Δ - (n : ℝ)) / Δ) : ℂ) * a n = _
  rw [hsharp, ← hedge, hsharpSum, hedgeSum]
  exact (Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 (Nat.floor (x + Δ))) P
    (fun n => a n * cesaroPerronWeight x Δ n))

private theorem cesaroPerronEdge_card_le {x Δ : ℝ}
    (hx : 0 < x) (hΔ : 0 < Δ) :
    ((Finset.Icc 1 (Nat.floor (x + Δ))).filter
      (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + Δ)).card ≤ Δ + 1 := by
  classical
  let M := Nat.floor x
  let N := Nat.floor (x + Δ)
  let E := (Finset.Icc 1 N).filter
    (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + Δ)
  have hMN : M ≤ N := Nat.floor_mono (by linarith)
  have hsubset : E ⊆ Finset.Ioc M N := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hnx, hnupper⟩
    have hnM : (M : ℝ) < (n : ℝ) :=
      (Nat.floor_le (le_of_lt hx)).trans_lt hnx
    have hnM' : M < n := by exact_mod_cast hnM
    exact Finset.mem_Ioc.mpr ⟨hnM', (Finset.mem_Icc.mp hnIcc).2⟩
  have hcardNat : E.card ≤ N - M := by
    calc
      E.card ≤ (Finset.Ioc M N).card := Finset.card_le_card hsubset
      _ = N - M := Nat.card_Ioc M N
  have hcardR : (E.card : ℝ) ≤ (N : ℝ) - (M : ℝ) := by
    have hcast : (E.card : ℝ) ≤ ((N - M : ℕ) : ℝ) := by exact_mod_cast hcardNat
    rw [Nat.cast_sub hMN] at hcast
    exact hcast
  have hN : (N : ℝ) ≤ x + Δ := Nat.floor_le (by linarith)
  have hM : x - 1 < (M : ℝ) := Nat.sub_one_lt_floor x
  linarith

private theorem cesaroPerronEdgeTerm_norm_le_one {a : ℕ → ℂ}
    (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {x Δ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) {n : ℕ}
    (hnx : x < (n : ℝ)) (hnupper : (n : ℝ) ≤ x + Δ) :
    ‖(↑((x + Δ - (n : ℝ)) / Δ) : ℂ) * a n‖ ≤ 1 := by
  have hnpos : 0 < n := by exact_mod_cast (lt_trans hx hnx)
  let r : ℝ := (x + Δ - (n : ℝ)) / Δ
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (by linarith) hΔ.le
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_one₀ hΔ).2
    linarith
  calc
    ‖(↑r : ℂ) * a n‖ = ‖(↑r : ℂ)‖ * ‖a n‖ := norm_mul _ _
    _ = r * ‖a n‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    _ ≤ 1 * 1 := mul_le_mul hr1 (ha n hnpos) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem cesaroPerronSmoothedSum_error {a : ℕ → ℂ}
    (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {x Δ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) :
    ‖cesaroPerronSmoothedSum a x Δ - cesaroPerronSharpSum a x‖ ≤ Δ + 1 := by
  classical
  rw [cesaroPerronSmoothedSum]
  simp only [add_sub_cancel_left]
  unfold cesaroPerronEdgeSum
  let E := (Finset.Icc 1 (Nat.floor (x + Δ))).filter
    (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + Δ)
  calc
    ‖∑ n ∈ E, (↑((x + Δ - (n : ℝ)) / Δ) : ℂ) * a n‖ ≤
        ∑ n ∈ E, ‖(↑((x + Δ - (n : ℝ)) / Δ) : ℂ) * a n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ E, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rcases Finset.mem_filter.mp hn with ⟨_, ⟨hnx, hnupper⟩⟩
      exact cesaroPerronEdgeTerm_norm_le_one ha hx hΔ hnx hnupper
    _ = E.card := by simp [E]
    _ ≤ Δ + 1 := cesaroPerronEdge_card_le hx hΔ

/-- Exact smoothed Perron inversion for bounded coefficients. This is the
identity in blueprint element `lal:cesaro-perron`; the separate error theorem
below records the endpoint count. -/
theorem cesaroPerronIdentity {a : ℕ → ℂ}
    (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {x Δ σ : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) (hσ : 1 < σ) :
    cesaroPerronSmoothedSum a x Δ =
      (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
        ∫ t : ℝ, perronDirichletSeries a ((σ : ℂ) + Complex.I * (t : ℂ)) *
          cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ)) := by
  calc
    cesaroPerronSmoothedSum a x Δ =
        ∑ n ∈ Finset.Icc 1 (Nat.floor (x + Δ)),
          a n * cesaroPerronWeight x Δ n :=
      cesaroPerronSmoothedSum_eq_weightSum a hx hΔ
    _ = ∑' n : ℕ, a n * cesaroPerronWeight x Δ n :=
      (cesaroPerron_weight_tsum a hx hΔ).symm
    _ = ∑' n : ℕ,
          (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
            ∫ t : ℝ, perronLineTerm a x Δ σ n t := by
      apply tsum_congr
      intro n
      exact (perronLineTerm_integral_eq_weight hx hΔ hσ n).symm
    _ = (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
          ∑' n : ℕ, ∫ t : ℝ, perronLineTerm a x Δ σ n t := tsum_mul_left
    _ = (↑((2 * Real.pi : ℝ)⁻¹) : ℂ) *
          ∫ t : ℝ, perronDirichletSeries a ((σ : ℂ) + Complex.I * (t : ℂ)) *
            cesaroPerronKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ)) := by
      rw [← integral_tsum_perronLineTerm ha hx hΔ hσ]

#print axioms perronLineTerm_integral_eq_weight
#print axioms cesaroPerronIdentity
#print axioms cesaroPerronSmoothedSum_error

end FractionalPrimes.Literature.LongArithmetic

end
