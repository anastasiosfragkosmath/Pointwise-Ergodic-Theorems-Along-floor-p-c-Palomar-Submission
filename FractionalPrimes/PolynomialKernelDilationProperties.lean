module

public import FractionalPrimes.PolynomialKernelAngularFourierProperties
public import FractionalPrimes.PolynomialKernelScaling

@[expose] public section

open MeasureTheory

namespace FractionalPrimes

/-- The exact positive dilation `rho_T(u) = T * rho(T*u)` from
`lup:kernel-properties`. -/
noncomputable def polynomialKernelRhoT (T u : ℝ) : ℝ :=
  T * polynomialKernelRho (T * u)

/-- The angular Fourier transform of the blueprint's dilated kernel has the
exact rescaling `F_ang rho_T(t) = F_ang rho(t/T)`. -/
theorem polynomialKernelRhoT_angularFourier (T t : ℝ) (hT : 0 < T) :
    polynomialAngularFourier (fun u => (polynomialKernelRhoT T u : ℂ)) t =
      polynomialKernelRhoAngularFourier (t / T) := by
  have h := polynomialAngularFourier_dilation
    (fun u => (polynomialKernelRho u : ℂ)) T t hT
  simpa [polynomialKernelRhoT, polynomialKernelRhoAngularFourier] using h

/-- The first absolute moment of the exact dilation is `M₁/T`. -/
theorem polynomialKernelRhoT_firstMoment (T : ℝ) (hT : 0 < T) :
    (∫ u : ℝ, |u| * polynomialKernelRhoT T u) =
      polynomialKernelM1 / T := by
  calc
    (∫ u : ℝ, |u| * polynomialKernelRhoT T u) =
        T⁻¹ * polynomialKernelM1 := by
      simpa [polynomialKernelRhoT, polynomialKernelDilation,
        polynomialKernelM1] using
          (integral_abs_mul_polynomialKernelDilation
            polynomialKernelRho T hT)
    _ = polynomialKernelM1 / T := by
      rw [div_eq_mul_inv]
      ring

end FractionalPrimes
