module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

open MeasureTheory

namespace FractionalPrimes

open scoped ComplexConjugate

/-- The angular Fourier transform used by the polynomial major-arc blueprint.
This normalization has no `2 * π` in the exponential. -/
noncomputable def polynomialAngularFourier (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ u : ℝ, f u * Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ))

/-- The angular Fourier transform is bounded by the `L¹` mass of its input.
For a nonnegative normalized real kernel this is the blueprint's bound
`|F rho| ≤ 1`. -/
theorem norm_polynomialAngularFourier_le_integral_norm
    (f : ℝ → ℂ) (t : ℝ) :
    ‖polynomialAngularFourier f t‖ ≤ ∫ u : ℝ, ‖f u‖ := by
  let phase : ℝ → ℂ := fun u => Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ))
  have hphase (u : ℝ) : ‖phase u‖ = 1 := by
    dsimp [phase]
    rw [show -Complex.I * (t : ℂ) * (u : ℂ) =
        (-(t * u) : ℝ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hnorm : ‖∫ u : ℝ, f u * phase u‖ ≤
      ∫ u : ℝ, ‖f u * phase u‖ := norm_integral_le_integral_norm _
  unfold polynomialAngularFourier
  calc
    _ = ‖∫ u : ℝ, f u * phase u‖ := by rfl
    _ ≤ ∫ u : ℝ, ‖f u * phase u‖ := hnorm
    _ = ∫ u : ℝ, ‖f u‖ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [norm_mul, hphase, mul_one]

/-- The dilation of a real kernel used in `lup:kernel-properties`. -/
def polynomialKernelDilation (T : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  T * f (T * u)

/-- Angular Fourier transform scales exactly under the blueprint's kernel
dilation `rho_T(u) = T * rho(T*u)`. This is stated for arbitrary complex
kernels, so it applies without changing the blueprint's fixed cutoff once
its inverse transform has been encoded. -/
theorem polynomialAngularFourier_dilation
    (f : ℝ → ℂ) (T t : ℝ) (hT : 0 < T) :
    polynomialAngularFourier (fun u => (T : ℂ) * f (T * u)) t =
      polynomialAngularFourier f (t / T) := by
  let g : ℝ → ℂ := fun u => f u *
    Complex.exp (-Complex.I * ((t / T : ℝ) : ℂ) * (u : ℂ))
  have hchange : (∫ u : ℝ, g (T * u)) =
      (T⁻¹ : ℝ) • ∫ u : ℝ, g u := by
    rw [Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.mpr hT)]
  unfold polynomialAngularFourier
  change ∫ u : ℝ,
      (T : ℂ) * f (T * u) * Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ)) = _
  have hphase (u : ℝ) :
      Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ)) =
        Complex.exp (-Complex.I * ((t / T : ℝ) : ℂ) * ((T * u : ℝ) : ℂ)) := by
    congr 1
    push_cast
    field_simp [ne_of_gt hT]
  calc
    _ = ∫ u : ℝ, (T : ℂ) * g (T * u) := by
      apply integral_congr_ae
      filter_upwards with u
      dsimp [g]
      rw [← hphase u]
      ring
    _ = (T : ℂ) * ∫ u : ℝ, g (T * u) := by
      rw [integral_const_mul]
    _ = (T : ℂ) * ((T⁻¹ : ℝ) • ∫ u : ℝ, g u) := by rw [hchange]
    _ = ∫ u : ℝ, g u := by
      have hcast : (T : ℂ) * (T⁻¹ : ℂ) = 1 := by
        exact_mod_cast (mul_inv_cancel₀ hT.ne' : T * T⁻¹ = 1)
      rw [Complex.real_smul]
      rw [Complex.ofReal_inv]
      change (T : ℂ) * ((T : ℂ)⁻¹ * (∫ u : ℝ, g u)) = _
      rw [← mul_assoc, hcast, one_mul]
    _ = polynomialAngularFourier f (t / T) := rfl

/-- The first absolute moment scales by `1/T` for the exact positive dilation
used in `lup:kernel-properties`. -/
theorem integral_abs_mul_polynomialKernelDilation
    (f : ℝ → ℝ) (T : ℝ) (hT : 0 < T) :
    (∫ u : ℝ, |u| * polynomialKernelDilation T f u) =
      T⁻¹ * ∫ u : ℝ, |u| * f u := by
  let g : ℝ → ℝ := fun u => |u| * f u
  have hchange : (∫ u : ℝ, g (T * u)) =
      (T⁻¹ : ℝ) • ∫ u : ℝ, g u := by
    rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hT)]
  simp only [polynomialKernelDilation]
  calc
    _ = ∫ u : ℝ, g (T * u) := by
      apply integral_congr_ae
      filter_upwards with u
      dsimp [g]
      rw [abs_mul, abs_of_pos hT]
      ring
    _ = T⁻¹ * ∫ u : ℝ, g u := by
      rw [hchange]
      simp only [smul_eq_mul]
    _ = T⁻¹ * ∫ u : ℝ, |u| * f u := rfl

end FractionalPrimes
