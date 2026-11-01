module

public import FractionalPrimes.Literature.Uniformity.ArithmeticTypes
public import FractionalPrimes.Literature.Uniformity.BinomialCoefficientNorm
public import FractionalPrimes.Literature.Polynomial.PolynomialDilationConcatenation
public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearCommonCentre

/-!
# Quantitative arithmetic inverse tasks

This file formalizes the proposition `INV` in blueprint item
`lu:inverse-tasks`.  It records the three ordinary-correlation clauses with
one common pair of constants; their discharge is deliberately left to the
subsequent Type-I, Type-I₂, and Type-II theorems.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The common real budget `K_d δ^{-c_d}` used by all three inverse clauses. -/
def arithmeticInverseBudget (K c : ℕ) (δ : ℝ) : ℝ :=
  (K : ℝ) * (δ⁻¹) ^ c

/-- The Type-I clause of `INV`, with the constants `K_d,c_d` specified. -/
def typeIInverseTaskClause (d K c : ℕ) : Prop :=
  ∀ (X H : ℤ) (P : Polynomial ℝ) (δ A_I : ℝ)
      (f : ComplexPositiveIntegerFunction),
    3 ≤ X → 2 ≤ H → H ≤ X →
    P.natDegree ≤ d →
    0 < δ → δ < min (1 / 2) ((Real.log (X : ℝ))⁻¹) →
    typeIFunction δ A_I f →
    δ * (H : ℝ) ≤ typeIScalarPhaseCorrelation f P (X : ℝ) (H : ℝ) →
    (H : ℝ) ≤ arithmeticInverseBudget K c δ * A_I ∨
      ∃ r : ℤ, 1 ≤ r ∧
        (r : ℝ) ≤ arithmeticInverseBudget K c δ ∧
        binomialCoefficientNorm d (Polynomial.C (r : ℝ) * P) X (H : ℝ) ≤
          arithmeticInverseBudget K c δ

/-- The Type-I₂ clause of `INV`, with the constants `K_d,c_d` specified. -/
def typeI2InverseTaskClause (d K c : ℕ) : Prop :=
  ∀ (X H : ℤ) (P : Polynomial ℝ) (δ A_I2 : ℝ)
      (f : ComplexPositiveIntegerFunction),
    3 ≤ X → 2 ≤ H → H ≤ X →
    P.natDegree ≤ d →
    0 < δ → δ < min (1 / 2) ((Real.log (X : ℝ))⁻¹) →
    typeI2Function δ A_I2 f →
    δ * (H : ℝ) ≤ typeIScalarPhaseCorrelation f P (X : ℝ) (H : ℝ) →
    (H : ℝ) ≤ arithmeticInverseBudget K c δ *
          Real.rpow (X : ℝ) (1 / 3 : ℝ) *
          Real.rpow A_I2 (2 / 3 : ℝ) ∨
      ∃ r : ℤ, 1 ≤ r ∧
        (r : ℝ) ≤ arithmeticInverseBudget K c δ ∧
        binomialCoefficientNorm d (Polynomial.C (r : ℝ) * P) X (H : ℝ) ≤
          arithmeticInverseBudget K c δ

/-- The Type-II coefficient-recurrence clause of `INV`, with the constants
`K_d,c_d` specified.  The canonical centered coefficients are those of
`P(X+t)`; the degree hypothesis makes the coefficient at `d+1` zero. -/
def typeIIInverseTaskClause (d K c : ℕ) : Prop :=
  ∀ (X H : ℤ) (P : Polynomial ℝ) (δ Aminus Aplus : ℝ)
      (f : ComplexPositiveIntegerFunction),
    3 ≤ X → 2 ≤ H → H ≤ X →
    P.natDegree ≤ d →
    0 < δ → δ < min (1 / 2) ((Real.log (X : ℝ))⁻¹) →
    typeIIFunction δ Aminus Aplus f →
    δ * (H : ℝ) ≤ typeIScalarPhaseCorrelation f P (X : ℝ) (H : ℝ) →
    (H : ℝ) ≤ arithmeticInverseBudget K c δ *
          max Aplus ((X : ℝ) / Aminus) ∨
      ∃ Q : ℕ, 1 ≤ Q ∧
        (Q : ℝ) ≤ arithmeticInverseBudget K c δ ∧
        ∀ j, 1 ≤ j → j ≤ d →
          realDistanceToIntegers
              ((Q : ℝ) * bilinearDerivativeCoefficient (X : ℝ)
                (fun i => (phaseCenteredAt P X).coeff i) j) ≤
            arithmeticInverseBudget K c δ * (X : ℝ) /
              (H : ℝ) ^ (j + 1)

/-- All three arithmetic inverse clauses with one specified pair of constants. -/
def arithmeticInverseTasksWithConstants (d K c : ℕ) : Prop :=
  2 ≤ K ∧ 1 ≤ c ∧
    typeIInverseTaskClause d K c ∧
    typeI2InverseTaskClause d K c ∧
    typeIIInverseTaskClause d K c

/-- The exact proposition `INV` from blueprint item `lu:inverse-tasks`. -/
def arithmeticInverseTasks : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∃ K c : ℕ, arithmeticInverseTasksWithConstants d K c

#print arithmeticInverseTasks
#print axioms arithmeticInverseTasks

end

end FractionalPrimes.Literature.Uniformity

