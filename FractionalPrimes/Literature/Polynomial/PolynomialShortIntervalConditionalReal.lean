module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalConditionalInteger
public import FractionalPrimes.Literature.Polynomial.PolynomialIntegerToRealUniformity

/-!
# Real-centred consequence of the conditional scalar tasks

This module adapts the checked natural-Ioc conditional integer theorem to the
exact integer-sum premise of `uniformityRealOfInteger`, then applies the
source-faithful centre-transfer theorem without changing any task hypotheses.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open scoped BigOperators
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Centres

/-- Reorder the exact conditional integer estimate into the hypothesis
shape used by the centre-transfer theorem and convert natural-Ioc sums to
the matching integer-Ioc sums. The interval endpoints and location-dependent
Cramér model are unchanged. -/
theorem conditionalIntegerPremiseOfScalarTasks
    (k : ℕ) (A : ℝ) (hA : 0 < A)
    (hPMA : polynomialMajorArcTask)
    (hInv : arithmeticInverseTasks)
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
  intro η hη hηtop
  obtain ⟨Cint, hCint, hBound⟩ :=
    conditionalIntegerUniformityOfScalarTasks k A η hA hη hηtop
      hPMA hInv hPTW
  refine ⟨Cint, hCint, ?_⟩
  intro P hP M L hM hLower hUpper
  have hNatBound := hBound M L hM hLower hUpper P hP
  have hMuSum :
      (∑ n ∈ Finset.Ioc M (M + L),
        (FractionalPrimes.paperMu (n : ℤ) : ℂ) *
          FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))) =
        integerToRealMobiusPhaseSum P M L := by
    unfold integerToRealMobiusPhaseSum
    exact cramerShortInterval_sum_nat_eq_int M L (fun n : ℤ =>
      (FractionalPrimes.paperMu n : ℂ) *
        FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ)))
  have hLambdaSum :
      (∑ n ∈ Finset.Ioc M (M + L),
        ((FractionalPrimes.paperLambda (n : ℤ) : ℂ) -
          (FractionalPrimes.paperShortBlockCramerWeight
            (M : ℝ) (n : ℤ) : ℂ)) *
          FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))) =
        integerToRealLambdaModelPhaseSum P M L := by
    calc
      _ = ∑ n ∈ Finset.Ioc (M : ℤ) ((M + L : ℕ) : ℤ),
          ((FractionalPrimes.paperLambda n : ℂ) -
            (FractionalPrimes.paperShortBlockCramerWeight
              (M : ℝ) n : ℂ)) *
            FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ)) :=
        cramerShortInterval_sum_nat_eq_int M L (fun n : ℤ =>
          ((FractionalPrimes.paperLambda n : ℂ) -
            (FractionalPrimes.paperShortBlockCramerWeight
              (M : ℝ) n : ℂ)) *
            FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ)))
      _ = integerToRealLambdaModelPhaseSum P M L := by
        unfold integerToRealLambdaModelPhaseSum
        apply Finset.sum_congr rfl
        intro n hn
        simp [FractionalPrimes.paperShortBlockCramerWeight]
  simpa only [hMuSum, hLambdaSum] using hNatBound

/-- The exact conditional real-centred conclusion obtained by composing the
restricted scalar-task integer theorem with `lc:integer-to-real`. -/
theorem conditionalRealUniformityOfScalarTasks
    (k : ℕ) (A : ℝ) (hA : 0 < A)
    (hPMA : polynomialMajorArcTask)
    (hInv : arithmeticInverseTasks)
    (hPTW : restrictedPolynomialTwistedTask)
    (ε : ℝ) (hε : 0 < ε) (hεtop : ε < 3 / 16) :
    ∃ Cint : ℝ, 0 < Cint ∧
      ∀ P : Polynomial ℝ, P.natDegree ≤ k →
        ∀ X H : ℝ,
          3 ≤ X →
          X ^ (5 / 8 + ε) ≤ H →
          H ≤ X ^ (1 - ε) →
            ‖∑ n ∈ FractionalPrimes.realIntegerInterval X H,
                (FractionalPrimes.paperMu n : ℂ) *
                  FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ +
              ‖realCenterLambdaModelPhaseSum P X H‖ ≤
              integerToRealUniformityConstant A ε Cint * H *
                (Real.log X) ^ (-A : ℝ) := by
  exact uniformityRealOfInteger k A hA
    (conditionalIntegerPremiseOfScalarTasks k A hA hPMA hInv hPTW)
    ε hε hεtop

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.conditionalIntegerPremiseOfScalarTasks
#print axioms FractionalPrimes.Literature.Polynomial.conditionalRealUniformityOfScalarTasks
