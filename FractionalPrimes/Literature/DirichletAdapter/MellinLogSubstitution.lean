module

public import FractionalPrimes.Literature.DirichletAdapter.MellinComplexification
public import FractionalPrimes.Literature.Twisted.SmoothDyadicQuadratureDerivative
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The exact positive-line substitution `x = N * exp w` for complex integrals. -/

@[expose] public section

open MeasureTheory
open scoped FourierTransform

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The phase identity needed after logarithmic substitution. -/
theorem real_exp_cpow (w : ℝ) (s : ℂ) :
    (Real.exp w : ℂ) ^ s = Complex.exp ((w : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_ne_zero w))]
  rw [← Complex.ofReal_log (Real.exp_pos w).le, Real.log_exp]

/-- The Jacobian and the source power combine into the exact Mellin
amplitude and oscillatory phase. -/
theorem exp_twist_weight (w t H : ℝ) :
    (Real.exp w : ℂ) *
        ((Real.exp w : ℂ) ^ Twisted.smoothDyadicTwistExponent t * (H : ℂ)) =
      Complex.exp (-(t : ℂ) * Complex.I * (w : ℂ)) *
        ((Real.exp (w / 2) * H : ℝ) : ℂ) := by
  rw [real_exp_cpow, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  have hexp : (w : ℂ) + (w : ℂ) * Twisted.smoothDyadicTwistExponent t =
      ((w / 2 : ℝ) : ℂ) + (-(t : ℂ) * Complex.I * (w : ℂ)) := by
    simp only [Twisted.smoothDyadicTwistExponent, Complex.ofReal_div,
      Complex.ofReal_ofNat]
    ring
  rw [hexp, Complex.exp_add, ← Complex.ofReal_exp]
  push_cast
  ring

/-- Pointwise form of the source profile after `x = N exp w`. -/
theorem smoothDyadicQuadratureSource_log_phase
    (N t w : ℝ) (p : ℝ × ℝ × ℝ) (hN : 0 < N) :
    Real.exp w • Twisted.smoothDyadicQuadratureSource N t p (N * Real.exp w) =
      (N : ℂ) ^ Twisted.smoothDyadicTwistExponent t *
        Complex.exp (-(t : ℂ) * Complex.I * (w : ℂ)) *
          (Twisted.smoothDyadicMellinH p w : ℂ) := by
  have hx : 0 < N * Real.exp w := mul_pos hN (Real.exp_pos w)
  have hquot : N * Real.exp w / N = Real.exp w := by
    field_simp [ne_of_gt hN]
  rw [Twisted.smoothDyadicQuadratureSource, if_pos hx, hquot]
  rw [show ((N * Real.exp w : ℝ) : ℂ) =
      (N : ℂ) * (Real.exp w : ℂ) by push_cast; rfl]
  rw [Complex.mul_cpow_ofReal_nonneg hN.le (Real.exp_pos w).le]
  rw [RCLike.real_smul_eq_coe_mul]
  change (Real.exp w : ℂ) *
      ((N : ℂ) ^ Twisted.smoothDyadicTwistExponent t *
        (Real.exp w : ℂ) ^ Twisted.smoothDyadicTwistExponent t *
        (Twisted.smoothDyadicH p.1 p.2.1 p.2.2 (Real.exp w) : ℂ)) = _
  rw [Twisted.smoothDyadicMellinH]
  convert congrArg ((N : ℂ) ^ Twisted.smoothDyadicTwistExponent t * ·)
    (exp_twist_weight w t
      (Twisted.smoothDyadicH p.1 p.2.1 p.2.2 (Real.exp w))) using 1 <;> ring

/-- Mathlib's `2π` Fourier convention matches the Mellin oscillation
at frequency `t/(2π)`. -/
theorem mellin_phase_eq_fourier_kernel (w t : ℝ) :
    Complex.exp (((-2 * Real.pi * w * (t / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-(t : ℂ) * Complex.I * (w : ℂ)) := by
  congr 1
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

/-- An arbitrary real Mellin amplitude with the paper's phase is exactly
Mathlib's Fourier transform at `t/(2π)`. -/
theorem mellin_phase_integral_eq_fourier (M : ℝ → ℝ) (t : ℝ) :
    (∫ w : ℝ, Complex.exp (-(t : ℂ) * Complex.I * (w : ℂ)) * (M w : ℂ) ∂volume) =
      𝓕 (fun w : ℝ => (M w : ℂ)) (t / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1
  funext w
  rw [mellin_phase_eq_fourier_kernel]
  simp only [smul_eq_mul]

/-- Logarithmic substitution with a positive scale. The Jacobian is
`N * exp w`; no integrability hypothesis is needed for the identity of
Bochner integrals. -/
theorem integral_Ioi_zero_eq_scaled_log_integral
    (f : ℝ → ℂ) (N : ℝ) (hN : 0 < N) :
    (∫ x in Set.Ioi (0 : ℝ), f x ∂volume) =
      N • ∫ w : ℝ, Real.exp w • f (N * Real.exp w) ∂volume := by
  have hlog := MeasureTheory.integral_comp_exp (fun u : ℝ => f (N * u))
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi' f 0 hN
  simpa only [mul_zero] using hscale.symm.trans (congrArg (fun z : ℂ => N • z) hlog.symm)

/-- The same substitution for a function extended by zero to the
nonpositive half-line. -/
theorem integral_eq_scaled_log_integral_of_nonpos_eq_zero
    (f : ℝ → ℂ) (N : ℝ) (hN : 0 < N)
    (hzero : ∀ x : ℝ, x ≤ 0 → f x = 0) :
    (∫ x : ℝ, f x ∂volume) =
      N • ∫ w : ℝ, Real.exp w • f (N * Real.exp w) ∂volume := by
  rw [← integral_Ioi_zero_eq_scaled_log_integral f N hN]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
  intro x hx
  exact hzero x (le_of_not_gt hx)

/-- Exact logarithmic substitution for the blueprint's literal
zero-extended oscillatory source. -/
theorem smoothDyadicQuadratureSource_log_substitution
    (N t : ℝ) (p : ℝ × ℝ × ℝ) (hN : 0 < N) :
    (∫ x : ℝ, Twisted.smoothDyadicQuadratureSource N t p x ∂volume) =
      N • ∫ w : ℝ, Real.exp w •
        Twisted.smoothDyadicQuadratureSource N t p (N * Real.exp w) ∂volume := by
  apply integral_eq_scaled_log_integral_of_nonpos_eq_zero _ N hN
  intro x hx
  simp [Twisted.smoothDyadicQuadratureSource, not_lt.mpr hx]

/-- The exact Mellin/Fourier identity for the paper's zero-extended
oscillatory source, including its complex scale factor. -/
theorem smoothDyadicQuadratureSource_integral_eq_fourier
    (N t : ℝ) (p : ℝ × ℝ × ℝ) (hN : 0 < N) :
    (∫ x : ℝ, Twisted.smoothDyadicQuadratureSource N t p x ∂volume) =
      N • ((N : ℂ) ^ Twisted.smoothDyadicTwistExponent t *
        𝓕 (fun w : ℝ => (Twisted.smoothDyadicMellinH p w : ℂ))
          (t / (2 * Real.pi))) := by
  rw [smoothDyadicQuadratureSource_log_substitution N t p hN]
  simp_rw [smoothDyadicQuadratureSource_log_phase N t _ p hN]
  rw [← mellin_phase_integral_eq_fourier (Twisted.smoothDyadicMellinH p) t]
  congr 1
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

#print axioms integral_Ioi_zero_eq_scaled_log_integral
#print axioms real_exp_cpow
#print axioms exp_twist_weight
#print axioms smoothDyadicQuadratureSource_log_phase
#print axioms mellin_phase_eq_fourier_kernel
#print axioms mellin_phase_integral_eq_fourier
#print axioms smoothDyadicQuadratureSource_integral_eq_fourier
#print axioms smoothDyadicQuadratureSource_log_substitution

end FractionalPrimes.Literature.DirichletAdapter

end
