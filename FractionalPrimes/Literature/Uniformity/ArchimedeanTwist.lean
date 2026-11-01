module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Archimedean multiplicative twists

The phase and its derivative are prepared for the `lu:elementary-growth`
variation estimate.  The frequency and logarithm conventions match the
approved blueprint exactly.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

/-- The archimedean twist `exp(i T log x)` used in `lu:elementary-growth`. -/
noncomputable def archimedeanTwist (T x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (T : ℂ) * (Real.log x : ℂ))

/-- The archimedean twist has unit modulus on the positive real axis. -/
theorem norm_archimedeanTwist_eq_one (T x : ℝ) :
    ‖archimedeanTwist T x‖ = 1 := by
  rw [archimedeanTwist, Complex.norm_exp]
  have hre : (Complex.I * (T : ℂ) * (Real.log x : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

/-- Derivative of the archimedean twist at a nonzero real point. -/
theorem hasDerivAt_archimedeanTwist {T x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => archimedeanTwist T y)
      (archimedeanTwist T x *
        (Complex.I * (T : ℂ) * ((x⁻¹ : ℝ) : ℂ))) x := by
  have hlog : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
    (Real.hasDerivAt_log hx).ofReal_comp
  have harg : HasDerivAt
      (fun y : ℝ => Complex.I * (T : ℂ) * (Real.log y : ℂ))
      (Complex.I * (T : ℂ) * ((x⁻¹ : ℝ) : ℂ)) x := by
    simpa only [Function.comp_def] using hlog.const_mul (Complex.I * (T : ℂ))
  have hexp := (Complex.hasDerivAt_exp _).comp x harg
  simpa [archimedeanTwist, Function.comp_def] using hexp

/-- Pointwise derivative magnitude of the twist on the positive real axis. -/
theorem norm_deriv_archimedeanTwist_le {T x : ℝ} (hx : 0 < x) :
    ‖deriv (fun y : ℝ => archimedeanTwist T y) x‖ ≤ |T| / x := by
  have hderiv := (hasDerivAt_archimedeanTwist (T := T) (x := x) hx.ne').deriv
  rw [hderiv, norm_mul, norm_archimedeanTwist_eq_one, one_mul]
  calc
    ‖Complex.I * (T : ℂ) * ((x⁻¹ : ℝ) : ℂ)‖ = |T| * x⁻¹ := by
      simp [Complex.norm_I, abs_of_pos hx]
    _ ≤ |T| / x := by rw [div_eq_mul_inv]

/-- Smoothness of the twist on any compact positive real interval. -/
theorem contDiffOn_archimedeanTwist {T u v : ℝ} (hu : 0 < u) :
    ContDiffOn ℝ 1 (fun x : ℝ => archimedeanTwist T x) (Set.Icc u v) := by
  have hpos : Set.Icc u v ⊆ ({0} : Set ℝ)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (lt_of_lt_of_le hu hx.1)
  have hlog : ContDiffOn ℝ 1 Real.log (Set.Icc u v) :=
    Real.contDiffOn_log.mono hpos
  have hlogC : ContDiffOn ℝ 1 (fun x : ℝ => (Real.log x : ℂ)) (Set.Icc u v) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hlog
  have harg : ContDiffOn ℝ 1
      (fun x : ℝ => Complex.I * (T : ℂ) * (Real.log x : ℂ)) (Set.Icc u v) := by
    simpa only [smul_eq_mul] using hlogC.const_smul (Complex.I * (T : ℂ))
  simpa [archimedeanTwist] using harg.cexp

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.norm_archimedeanTwist_eq_one
#print axioms FractionalPrimes.Literature.Uniformity.hasDerivAt_archimedeanTwist
#print axioms FractionalPrimes.Literature.Uniformity.norm_deriv_archimedeanTwist_le
#print axioms FractionalPrimes.Literature.Uniformity.contDiffOn_archimedeanTwist
