module

public import FractionalPrimes.Literature.Polynomial.PolynomialMonomialToBinomial

/-!
# Binomial coefficients and the centered coefficient seminorm

This file provides the manifest-facing interface for blueprint item
`lu:binomial-data`.  Its implementation is the already checked iterated
forward-difference construction used by the scalar inverse theorems.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open FractionalPrimes.Literature.Polynomial

/-- The `j`th Newton coefficient `(Δ^j P)(M)` at an integral centre. -/
noncomputable def binomialPolynomialCoefficient
    (d : ℕ) (P : Polynomial ℝ) (M : ℤ) (j : ℕ) : ℝ :=
  polynomialBinomialCoefficient d P M j

/-- The exact centered binomial coefficient seminorm from blueprint item
`lu:binomial-data`; the constant coefficient is omitted and the value at
degree zero is zero. -/
noncomputable def binomialCoefficientNorm
    (d : ℕ) (P : Polynomial ℝ) (M : ℤ) (H : ℝ) : ℝ :=
  polynomialBinomialCoefficientNorm d P M H

theorem binomialPolynomialCoefficient_eq_iteratedForwardDifference
    (d : ℕ) (P : Polynomial ℝ) (M : ℤ) (j : ℕ) :
    binomialPolynomialCoefficient d P M j =
      (iteratedPolynomialForwardDifference j P).eval (M : ℝ) := by
  simpa [binomialPolynomialCoefficient] using
    polynomialBinomialCoefficient_eq_centeredDifference d P M j

@[simp]
theorem binomialCoefficientNorm_zero
    (P : Polynomial ℝ) (M : ℤ) (H : ℝ) :
    binomialCoefficientNorm 0 P M H = 0 := by
  simp [binomialCoefficientNorm]

theorem binomialCoefficientNorm_eq_polynomialBinomialCoefficientNorm
    (d : ℕ) (P : Polynomial ℝ) (M : ℤ) (H : ℝ) :
    binomialCoefficientNorm d P M H =
      polynomialBinomialCoefficientNorm d P M H := rfl

#print axioms binomialPolynomialCoefficient
#print axioms binomialCoefficientNorm
#print axioms binomialPolynomialCoefficient_eq_iteratedForwardDifference

end FractionalPrimes.Literature.Uniformity

