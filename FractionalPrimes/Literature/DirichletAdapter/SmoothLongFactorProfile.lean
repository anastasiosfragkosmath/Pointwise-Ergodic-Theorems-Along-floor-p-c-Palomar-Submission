module

public import FractionalPrimes.Literature.Uniformity.SmoothHeathBrownRetention
public import FractionalPrimes.Literature.Polynomial.PolynomialSmoothMeanDecay
public import FractionalPrimes.Literature.Twisted.SmoothDyadicQuadratureDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Exact source-profile identification for the non-Möbius smooth
Heath--Brown factor selected in the long-factor branch. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- The `a` profile parameter for a free factor: `(1,0)` for a theta factor,
and the normalized logarithm of its scale for the unique logarithmic factor. -/
noncomputable def smoothHeathBrownFreeFactorProfileA
    {X : ℝ} (f : SmoothHeathBrownFactor X) : ℝ :=
  match f with
  | .theta _ => 1
  | .logarithm _ =>
      Real.log (smoothHeathBrownFactorScale f) / (4 * Real.log X)
  | .mobius _ => 0

/-- The `b` profile parameter for a free factor; it is nonzero only for the
normalized logarithmic factor. -/
noncomputable def smoothHeathBrownFreeFactorProfileB
    {X : ℝ} (f : SmoothHeathBrownFactor X) : ℝ :=
  match f with
  | .theta _ => 0
  | .logarithm _ => 1 / (4 * Real.log X)
  | .mobius _ => 0

/-- The exact profile point for a fixed product `m` of the other factors. -/
noncomputable def smoothHeathBrownFreeFactorProfileParameters
    (X : ℝ) (m : ℕ) {X' : ℝ} (f : SmoothHeathBrownFactor X') : ℝ × ℝ × ℝ :=
  ((m : ℝ) * smoothHeathBrownFactorScale f / X,
    smoothHeathBrownFreeFactorProfileA f,
    smoothHeathBrownFreeFactorProfileB f)

/-- The discrete coefficient of a non-Möbius free factor, with the sole
logarithm normalized exactly as in the source proof. -/
noncomputable def smoothHeathBrownFreeFactorCoefficient
    {X : ℝ} (f : SmoothHeathBrownFactor X) (n : ℕ) : ℝ :=
  match f with
  | .theta j => smoothHeathBrownThetaFactor j n
  | .logarithm j =>
      smoothHeathBrownLogFactor j n / (4 * Real.log X)
  | .mobius _ => 0

/-- At every positive integer, the smooth profile is exactly the normalized
free Heath--Brown factor multiplied by the outer cutoff at the full product
`m*n`. This is the source's `H_{v,a,b}(n/N)` identity. -/
theorem smoothHeathBrown_freeFactor_profile_sample
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m n : ℕ) (hn : 0 < n) :
    smoothDyadicH
        ((m : ℝ) * smoothHeathBrownFactorScale f / X)
        (smoothHeathBrownFreeFactorProfileA f)
        (smoothHeathBrownFreeFactorProfileB f)
        ((n : ℝ) / smoothHeathBrownFactorScale f) =
      smoothHeathBrownFreeFactorCoefficient f n *
        polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) := by
  have hXpos : 0 < X := by linarith
  have hXlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hNpos : 0 < smoothHeathBrownFactorScale f :=
    lt_of_lt_of_le (by norm_num) (smoothHeathBrownFactorScale_ge_one f)
  have hu : 0 < (n : ℝ) / smoothHeathBrownFactorScale f :=
    div_pos (by exact_mod_cast hn) hNpos
  have harg :
      ((m : ℝ) * smoothHeathBrownFactorScale f / X) *
          ((n : ℝ) / smoothHeathBrownFactorScale f) =
        ((m * n : ℕ) : ℝ) / X := by
    field_simp [hXpos.ne', hNpos.ne']
    exact (Nat.cast_mul m n).symm
  cases f with
  | theta j =>
      rw [smoothDyadicH, if_pos hu, harg]
      simp [smoothHeathBrownFreeFactorProfileA,
        smoothHeathBrownFreeFactorProfileB,
        smoothHeathBrownFreeFactorCoefficient,
        smoothHeathBrownFactorScale, smoothHeathBrownThetaFactor,
        hn.ne']
  | logarithm j =>
      have hlogdiv :
          Real.log ((n : ℝ) / smoothHeathBrownFactorScale
              (SmoothHeathBrownFactor.logarithm j)) =
            Real.log (n : ℝ) - Real.log
              (smoothHeathBrownFactorScale (SmoothHeathBrownFactor.logarithm j)) :=
        Real.log_div (by positivity) hNpos.ne'
      have hlogweight :
          smoothHeathBrownFreeFactorProfileA (SmoothHeathBrownFactor.logarithm j) +
              smoothHeathBrownFreeFactorProfileB
                (SmoothHeathBrownFactor.logarithm j) *
                Real.log ((n : ℝ) / smoothHeathBrownFactorScale
                  (SmoothHeathBrownFactor.logarithm j)) =
            Real.log (n : ℝ) / (4 * Real.log X) := by
        unfold smoothHeathBrownFreeFactorProfileA
          smoothHeathBrownFreeFactorProfileB
        rw [hlogdiv]
        field_simp [hXlog.ne']
        ring
      rw [smoothDyadicH, if_pos hu, harg]
      rw [hlogweight]
      simp [smoothHeathBrownFreeFactorCoefficient,
        smoothHeathBrownLogFactor, ArithmeticFunction.log_apply,
        smoothHeathBrownFactorScale, hn.ne']
      ring
  | mobius j => exact (hfree j rfl).elim

#print axioms smoothHeathBrown_freeFactor_profile_sample

/-- The literal zero-extended quadrature profile vanishes at every
nonpositive real input, so it can be reindexed onto the natural residue
lattice. -/
theorem smoothHeathBrown_freeFactorSource_eq_zero_of_nonpos
    (N t : ℝ) (p : ℝ × ℝ × ℝ) {x : ℝ} (hx : x ≤ 0) :
    smoothDyadicQuadratureSource N t p x = 0 := by
  simp [smoothDyadicQuadratureSource, not_lt.mpr hx]

#print axioms smoothHeathBrown_freeFactorSource_eq_zero_of_nonpos

/-- The discrete factor expression, with the source cutoff and Mellin phase,
is the sample of the literal zero-extended profile. -/
theorem smoothHeathBrown_freeFactorSource_sample
    {X : ℝ} (hX : 3 ≤ X) (f : SmoothHeathBrownFactor X)
    (hfree : ∀ j : SmoothHeathBrownScaleIndex X, f ≠ .mobius j)
    (m n : ℕ) (hn : 0 < n) (t : ℝ) :
    smoothDyadicQuadratureSource
        (smoothHeathBrownFactorScale f) t
        (smoothHeathBrownFreeFactorProfileParameters X m f)
        (n : ℝ) =
      (n : ℂ) ^ smoothDyadicTwistExponent t *
        (((smoothHeathBrownFreeFactorCoefficient f n *
          polynomialOuterCutoff (((m * n : ℕ) : ℝ) / X) : ℝ) : ℂ)) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [smoothDyadicQuadratureSource, if_pos hnreal]
  simp only [smoothHeathBrownFreeFactorProfileParameters]
  rw [smoothHeathBrown_freeFactor_profile_sample hX f hfree m n hn]
  simp only [Complex.ofReal_natCast]

#print axioms smoothHeathBrown_freeFactorSource_sample

end FractionalPrimes.Literature.DirichletAdapter

end
