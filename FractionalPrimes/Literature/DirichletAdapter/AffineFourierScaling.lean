module

public import FractionalPrimes.Literature.DirichletAdapter.CompactSmoothPoisson
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Fourier scaling for the residue-lattice function. -/

@[expose] public section

open MeasureTheory Real
open scoped FourierTransform

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The positive real scaling law with the exact `1/q` Fourier normalization. -/
theorem fourier_comp_mul_pos (F : ℝ → ℂ) (q ξ : ℝ) (hq : 0 < q) :
    𝓕 (fun x : ℝ => F (q * x)) ξ =
      q⁻¹ • 𝓕 F (ξ / q) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  let g : ℝ → ℂ := fun y => (𝐞 (-(y * (ξ / q)))) • F y
  have hg (x : ℝ) :
      (𝐞 (-(x * ξ))) • F (q * x) = g (q * x) := by
    simp only [g]
    congr 1
    field_simp
  simp_rw [hg]
  rw [Measure.integral_comp_mul_left g q]
  simpa only [abs_of_pos hq, inv_inv, g] using
    (show |q⁻¹| • ∫ y : ℝ, g y = q⁻¹ • ∫ y : ℝ, g y from by
      rw [abs_of_pos (inv_pos.mpr hq)])

#print axioms fourier_comp_mul_pos

/-- Translation contributes the positive Fourier character of the shift. -/
theorem fourier_comp_add_right (F : ℝ → ℂ) (b ξ : ℝ) :
    𝓕 (fun x : ℝ => F (x + b)) ξ =
      (𝐞 (b * ξ)) • 𝓕 F ξ := by
  simpa only [Function.comp_def, Real.fourier_real_eq,
    Fourier.fourierIntegral, VectorFourier.fourierIntegral,
    LinearMap.mul, LinearMap.mk₂_apply] using
    congrFun (Fourier.fourierIntegral_comp_add_right Real.fourierChar volume F b) ξ

#print axioms fourier_comp_add_right

/-- The exact phase and normalization for `x ↦ F(b+q*x)`.
The phase has the positive sign from the blueprint. -/
theorem fourier_comp_residue_affine
    (F : ℝ → ℂ) (q b ξ : ℝ) (hq : 0 < q) :
    𝓕 (fun x : ℝ => F (b + q * x)) ξ =
      q⁻¹ • ((𝐞 (b * (ξ / q))) • 𝓕 F (ξ / q)) := by
  calc
    𝓕 (fun x : ℝ => F (b + q * x)) ξ =
        q⁻¹ • 𝓕 (fun y : ℝ => F (y + b)) (ξ / q) := by
          simpa only [add_comm] using
            fourier_comp_mul_pos (fun y : ℝ => F (y + b)) q ξ hq
    _ = q⁻¹ • ((𝐞 (b * (ξ / q))) • 𝓕 F (ξ / q)) := by
          rw [fourier_comp_add_right]

#print axioms fourier_comp_residue_affine

end FractionalPrimes.Literature.DirichletAdapter

end
