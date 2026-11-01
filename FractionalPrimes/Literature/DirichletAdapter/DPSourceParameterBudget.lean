module
public import FractionalPrimes.Literature.DirichletAdapter.DPSourceComponentLogEnvelope
public import FractionalPrimes.Literature.Polynomial.DirichletMeanConstants
public import Mathlib.Tactic
@[expose] public section

/-!
# Explicit parameter budget for the source DP implication

This file checks the numerical choices stated in blueprint `lda:dp-from-muf`
against the exact hypotheses of `smoothHeathBrownDPSourceComponent_logEnvelope`.
-/

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.DirichletMean
noncomputable section

/-- The logarithmic budget `p` in blueprint `lda:dp-from-muf`. -/
def dpSourceBudgetP : ℕ := b 20 + 3 * 2 ^ 20 + 100

/-- The source budget `S=A+20B+p+10`. -/
def dpSourceBudgetS (A B : ℝ) : ℝ :=
  A + 20 * B + (dpSourceBudgetP : ℝ) + 10

/-- The source smoothing exponent `κ=32S`. -/
def dpSourceBudgetKappa (A B : ℝ) : ℝ := 32 * dpSourceBudgetS A B

/-- All numeric hypotheses required by the checked DP component log-envelope
theorem follow from the exact source choices `p=b₂₀+3·2²⁰+100`,
`S=A+20B+p+10`, `κ=32S`, and `D≥128S`.  The natural exponent is chosen as
`floor(8/η)+1`, so it is strictly above the source threshold. -/
theorem dpSourceParameterBudget
    {A B η D : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hη : 0 < η) (hηsmall : η < 3 / 16)
    (hD : 128 * dpSourceBudgetS A B ≤ D) :
    ∃ j : ℕ,
      8 / η < (j : ℝ) ∧
      2 ≤ j ∧
      0 < dpSourceBudgetKappa A B ∧
      2 * dpSourceBudgetKappa A B + 10 ≤ D ∧
      16 * (((A + 22) + 20 * B) +
        (smoothHeathBrownDPBlockLogExponent : ℝ)) ≤
          dpSourceBudgetKappa A B ∧
      ((A + 22) + 20 * B) +
        (smoothHeathBrownDPBlockLogExponent : ℝ) ≤ D ∧
      (A + 22) ≤ D * ((j : ℝ) - 1) ∧
      8 ≤ (j : ℝ) * η := by
  let M : ℝ := (smoothHeathBrownDPBlockLogExponent : ℝ)
  have hpM : (dpSourceBudgetP : ℝ) = M + 100 := by
    change ((b 20 + 3 * 2 ^ 20 + 100 : ℕ) : ℝ) =
      ((b 20 + 3 * 2 ^ 20 : ℕ) : ℝ) + 100
    push_cast
    ring
  have hSrepr : dpSourceBudgetS A B = ((A + 22) + 20 * B) + M + 88 := by
    dsimp [dpSourceBudgetS]
    rw [hpM]
    ring
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hSpos : 0 < dpSourceBudgetS A B := by
    rw [hSrepr]
    nlinarith [hA, hB, hMnonneg]
  have hKpos : 0 < dpSourceBudgetKappa A B := by
    unfold dpSourceBudgetKappa
    positivity
  let j : ℕ := Nat.floor (8 / η) + 1
  have hjstrict : 8 / η < (j : ℝ) := by
    dsimp [j]
    simpa [Nat.cast_add] using Nat.lt_floor_add_one (8 / η)
  have hratio : (1 : ℝ) < 8 / η := by
    rw [lt_div_iff₀ hη]
    nlinarith [hηsmall]
  have hjtwo : 2 ≤ j := by
    have hjreal : (1 : ℝ) < (j : ℝ) := hratio.trans hjstrict
    exact_mod_cast (show 1 < j by exact_mod_cast hjreal)
  have hκabs :
      16 * (((A + 22) + 20 * B) + M) ≤ dpSourceBudgetKappa A B := by
    rw [dpSourceBudgetKappa, hSrepr]
    nlinarith [hA, hB, hMnonneg]
  have hsourceLog_leS :
      ((A + 22) + 20 * B) + M ≤ dpSourceBudgetS A B := by
    rw [hSrepr]
    nlinarith
  have hDabs : ((A + 22) + 20 * B) + M ≤ D := by
    calc
      _ ≤ dpSourceBudgetS A B := hsourceLog_leS
      _ ≤ 128 * dpSourceBudgetS A B := by nlinarith [hSpos]
      _ ≤ D := hD
  have hDpos : 0 < D := by
    have hpos : 0 < 128 * dpSourceBudgetS A B := by positivity
    exact hpos.trans_le hD
  have htwoK : 2 * dpSourceBudgetKappa A B + 10 ≤ D := by
    calc
      2 * dpSourceBudgetKappa A B + 10 =
          64 * dpSourceBudgetS A B + 10 := by
            simp [dpSourceBudgetKappa]
            ring
      _ ≤ 128 * dpSourceBudgetS A B := by
        rw [hSrepr]
        nlinarith [hA, hB, hMnonneg]
      _ ≤ D := hD
  have hA22leD : A + 22 ≤ D := by
    have hMnonneg' : 0 ≤ (smoothHeathBrownDPBlockLogExponent : ℝ) := by
      positivity
    have hBnonneg : 0 ≤ 20 * B := by positivity
    linarith [hDabs, hMnonneg', hBnonneg]
  have hjminus : (1 : ℝ) ≤ (j : ℝ) - 1 := by
    have hjreal : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjtwo
    linarith
  have hDtail : A + 22 ≤ D * ((j : ℝ) - 1) := by
    calc
      A + 22 ≤ D := hA22leD
      _ = D * 1 := by ring
      _ ≤ D * ((j : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hjminus hDpos.le
  have hjη : 8 ≤ (j : ℝ) * η := by
    have hprod : 8 < (j : ℝ) * η := (div_lt_iff₀ hη).mp hjstrict
    exact le_of_lt hprod
  refine ⟨j, hjstrict, hjtwo, hKpos, htwoK, ?_, ?_, hDtail, hjη⟩
  · simpa only [M] using hκabs
  · simpa only [M] using hDabs

#print axioms dpSourceParameterBudget

end
end FractionalPrimes.Literature.DirichletAdapter
