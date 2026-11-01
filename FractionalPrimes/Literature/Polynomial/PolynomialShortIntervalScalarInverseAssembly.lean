module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalConditionalReal
public import FractionalPrimes.Literature.Uniformity.ScalarInverseClauses

/-!
# Discharging the global scalar inverse premise

The conditional integer and real short-interval packages already accept the
exact global inverse task `arithmeticInverseTasks`. This module supplies its
checked proof `scalarInverseClauses`, leaving the approved restricted PMA and
PTW contracts as explicit premises. No stronger unrestricted task is used.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Centres
open scoped BigOperators

/-- Conditional integer uniformity assuming only the two outstanding
restricted analytic tasks. The global scalar inverse task is discharged by
`scalarInverseClauses`. -/
theorem conditionalIntegerUniformityOfPMAandPTW
    (d : ℕ) (A η : ℝ) (hA : 0 < A) (hη : 0 < η)
    (hηmax : η < 3 / 16)
    (hPMA : polynomialMajorArcTask)
    (hPTW : restrictedPolynomialTwistedTask) :
    ∃ C : ℝ, 0 < C ∧
      ∀ X H : ℕ, 3 ≤ X →
        (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ) →
        (H : ℝ) ≤ (X : ℝ) ^ (1 - η) →
        ∀ P : Polynomial ℝ, P.natDegree ≤ d →
          ‖∑ n ∈ Finset.Ioc X (X + H),
              (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ +
            ‖∑ n ∈ Finset.Ioc X (X + H),
              ((paperLambda (n : ℤ) : ℂ) -
                (paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℂ)) *
                unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
            C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
  exact conditionalIntegerUniformityOfScalarTasks d A η hA hη hηmax
    hPMA scalarInverseClauses hPTW

/-- The integer-sum premise for the real-centred package, with the same
restricted PMA/PTW hypotheses and the checked global inverse task. -/
theorem conditionalIntegerPremiseOfPMAandPTW
    (k : ℕ) (A : ℝ) (hA : 0 < A)
    (hPMA : polynomialMajorArcTask)
    (hPTW : restrictedPolynomialTwistedTask) :
    ∀ η : ℝ, 0 < η → η < 3 / 16 →
      ∃ Cint : ℝ, 0 < Cint ∧
        ∀ P : Polynomial ℝ, P.natDegree ≤ k →
          ∀ M L : ℕ, 3 ≤ M →
            (M : ℝ) ^ (5 / 8 + η) ≤ (L : ℝ) →
            (L : ℝ) ≤ (M : ℝ) ^ (1 - η) →
              ‖integerToRealMobiusPhaseSum P M L‖ +
                ‖integerToRealLambdaModelPhaseSum P M L‖ ≤
                Cint * (L : ℝ) * (Real.log (M : ℝ)) ^ (-A : ℝ) := by
  exact conditionalIntegerPremiseOfScalarTasks k A hA hPMA
    scalarInverseClauses hPTW

/-- Conditional real-centred short-interval uniformity assuming only the
restricted PMA and PTW contracts. The integer result uses the proved scalar
inverse task, and the real-centre transfer is unchanged. -/
theorem conditionalRealUniformityOfPMAandPTW
    (k : ℕ) (A : ℝ) (hA : 0 < A)
    (hPMA : polynomialMajorArcTask)
    (hPTW : restrictedPolynomialTwistedTask)
    (ε : ℝ) (hε : 0 < ε) (hεtop : ε < 3 / 16) :
    ∃ Cint : ℝ, 0 < Cint ∧
      ∀ P : Polynomial ℝ, P.natDegree ≤ k →
        ∀ X H : ℝ,
          3 ≤ X →
          X ^ (5 / 8 + ε) ≤ H →
          H ≤ X ^ (1 - ε) →
            ‖∑ n ∈ realIntegerInterval X H,
                (paperMu n : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ +
              ‖realCenterLambdaModelPhaseSum P X H‖ ≤
              integerToRealUniformityConstant A ε Cint * H *
                (Real.log X) ^ (-A : ℝ) := by
  exact conditionalRealUniformityOfScalarTasks k A hA hPMA
    scalarInverseClauses hPTW ε hε hεtop

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.conditionalIntegerUniformityOfPMAandPTW
#print axioms FractionalPrimes.Literature.Polynomial.conditionalIntegerPremiseOfPMAandPTW
#print axioms FractionalPrimes.Literature.Polynomial.conditionalRealUniformityOfPMAandPTW
