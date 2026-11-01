module

public import Mathlib.Analysis.PSeries

public import FractionalPrimes.Literature.DirichletAdapter.FourierDerivativeDecay
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.Deriv.Support

/-! Poisson summation for the compact smooth functions used in residue quadrature. -/

@[expose] public section

open scoped FourierTransform ContDiff SchwartzMap
open MeasureTheory

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The Mathlib Schwartz-space Poisson formula, specialized to a compact smooth function. -/
theorem compactSmooth_poisson
    (F : ℝ → ℂ) (hcompact : HasCompactSupport F)
    (hsmooth : ContDiff ℝ ∞ F) (x : ℝ) :
    ∑' n : ℤ, F (x + n) =
      ∑' n : ℤ, 𝓕 F (n : ℝ) * fourier n (x : UnitAddCircle) := by
  have hfun : (hcompact.toSchwartzMap hsmooth : ℝ → ℂ) = F := rfl
  simpa only [SchwartzMap.fourier_coe, hfun] using
    SchwartzMap.tsum_eq_tsum_fourier (hcompact.toSchwartzMap hsmooth) x

#print axioms compactSmooth_poisson

/-- Integer samples of the Fourier transform of a compact smooth function
form an absolutely summable series. -/
theorem compactSmooth_fourier_int_summable
    (F : ℝ → ℂ) (hcompact : HasCompactSupport F)
    (hsmooth : ContDiff ℝ ∞ F) :
    Summable (fun k : ℤ => 𝓕 F (k : ℝ)) := by
  let S : 𝓢(ℝ, ℂ) := hcompact.toSchwartzMap hsmooth
  have hS : (S : ℝ → ℂ) = F := rfl
  have hsum : Summable (fun k : ℤ => 𝓕 S (k : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 S).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  simpa only [SchwartzMap.fourier_coe, hS] using hsum

#print axioms compactSmooth_fourier_int_summable

/-- All ordinary derivatives of a compact smooth function are integrable. -/
theorem compactSmooth_iteratedDeriv_integrable
    (F : ℝ → ℂ) (hcompact : HasCompactSupport F)
    (hsmooth : ContDiff ℝ ∞ F) (n : ℕ) :
    Integrable (iteratedDeriv n F) volume := by
  have hsupport : ∀ m : ℕ, HasCompactSupport (iteratedDeriv m F) := by
    intro m
    induction m with
    | zero => simpa only [iteratedDeriv_zero] using hcompact
    | succ m ih => simpa only [iteratedDeriv_succ] using ih.deriv
  exact (hsmooth.continuous_iteratedDeriv n (by simp)).integrable_of_hasCompactSupport
    (hsupport n)

#print axioms compactSmooth_iteratedDeriv_integrable

end FractionalPrimes.Literature.DirichletAdapter

end
