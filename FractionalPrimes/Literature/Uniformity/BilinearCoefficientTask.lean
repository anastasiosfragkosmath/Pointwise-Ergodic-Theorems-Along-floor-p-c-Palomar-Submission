module

public import FractionalPrimes.Literature.Polynomial.PolynomialBilinearCoefficientInverse

/-!
# Nondegenerate coefficient-norm bilinear task

This file formalizes blueprint nodes `lu:bilinear-task` and
`lu:bilinear-discharge`.  The first definition records the exact proposition;
the discharge uses the explicit constants from `lbi:budgets` and the checked
nondegenerate bilinear inverse theorem.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The bilinear coefficient conclusion with specified constants `K,c`.
This separate predicate makes the phrase “with the exact constants” available
to downstream Type-II reductions without unpacking an existential witness. -/
def bilinearCoefficientTaskWithConstants (d K c : ℕ) : Prop :=
  2 ≤ K ∧ 1 ≤ c ∧
    ∀ (X₀ : ℤ) (H M ρ : ℝ),
      3 ≤ (X₀ : ℝ) →
      2 ≤ H → H ≤ (X₀ : ℝ) → 2 ≤ M →
      0 < ρ → ρ < 1 / 2 →
      (K : ℝ) * (ρ⁻¹) ^ c * max ((X₀ : ℝ) / M) M ≤ H →
      ∀ (α β : ℕ → ℂ) (ν : ℕ → ℝ),
        ν (d + 1) = 0 →
        0 < bilinearU ((X₀ : ℝ) / M) α * bilinearV M β →
        ρ * H *
              (bilinearU ((X₀ : ℝ) / M) α * bilinearV M β) ≤
            ‖bilinearS (X₀ : ℝ) H M α β
              (bilinearCenteredPhase (X₀ : ℝ) d ν)‖ →
        ∃ Q : ℕ, 1 ≤ Q ∧
          (Q : ℝ) ≤ (K : ℝ) * (ρ⁻¹) ^ c ∧
          ∀ j, 1 ≤ j → j ≤ d →
            realDistanceToIntegers
                ((Q : ℝ) *
                  bilinearDerivativeCoefficient (X₀ : ℝ) ν j) ≤
              (K : ℝ) * (ρ⁻¹) ^ c *
                (X₀ : ℝ) / H ^ (j + 1)

/-- The exact existential proposition `BIL_d` from blueprint item
`lu:bilinear-task`. -/
def bilinearCoefficientTask (d : ℕ) : Prop :=
  ∃ K c : ℕ, bilinearCoefficientTaskWithConstants d K c

/-- The specified-constant form of the scalar bilinear discharge. -/
theorem bilinearCoefficientBound_exactConstants (d : ℕ) (hd : 1 ≤ d) :
    bilinearCoefficientTaskWithConstants d
      (bilinearInverseConstant d) (bilinearInverseExponent d) := by
  refine ⟨bilinearInverseConstant_ge_two d,
    bilinearInverseExponent_ge_one d hd, ?_⟩
  intro X₀ H M ρ hX hH hHX hM hρ hρhalf hlength α β ν hνtop hUV hlarge
  exact bilinearCoefficientInverse d hd X₀ H M ρ hX hH hHX hM hρ hρhalf
    hlength α β ν hνtop hUV hlarge

/-- The proposition `BIL_d` holds for every `d≥1`, with witnesses exactly the
constants defined in blueprint item `lbi:budgets`. -/
theorem bilinearCoefficientBound (d : ℕ) (hd : 1 ≤ d) :
    bilinearCoefficientTask d := by
  exact ⟨bilinearInverseConstant d, bilinearInverseExponent d,
    bilinearCoefficientBound_exactConstants d hd⟩

#print axioms bilinearCoefficientTask
#print axioms bilinearCoefficientBound_exactConstants
#print axioms bilinearCoefficientBound

end

end FractionalPrimes.Literature.Uniformity

