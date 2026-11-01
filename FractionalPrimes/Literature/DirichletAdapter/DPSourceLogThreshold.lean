module
public import FractionalPrimes.Literature.DirichletAdapter.DPSourceParameterBudget
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
public import Mathlib.Tactic
@[expose] public section

/-!
# Explicit large-X threshold for the source DP envelope

The threshold below directly enforces the source's fixed lower scale, the
logarithm lower bound, and the `A+22` logarithmic absorption hypothesis.  The
window lower condition `2≤W` is handled separately from the window relation
`W≤X/H`, which still depends on the source interval parameters.
-/

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.DirichletMean
noncomputable section

/-- A concrete threshold for the source DP logarithmic side conditions. -/
noncomputable def dpSourceLogThreshold (A : ℝ) : ℝ :=
  max ((2 : ℝ) ^ 35)
    (max (Real.exp 2) ((logAbsorptionM 1 (A + 22)) ^ 2))

/-- Every `X` beyond the displayed threshold satisfies the fixed source scale,
`1≤log X`, and the exact logarithmic absorption condition required by the DP
component theorem. -/
theorem dpSourceLogThreshold_spec (A : ℝ) :
    3 ≤ dpSourceLogThreshold A ∧
      ∀ X : ℝ, dpSourceLogThreshold A ≤ X →
        (2 : ℝ) ^ 35 ≤ X ∧
        1 ≤ Real.log X ∧
        2 ≤ Real.log X ∧
        2 * Real.log (logAbsorptionM 1 (A + 22)) ≤ Real.log X := by
  let M : ℝ := logAbsorptionM 1 (A + 22)
  have hMone : 1 ≤ M := by
    dsimp [M]
    exact one_le_logAbsorptionM
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hMone
  have hPowerBound : (2 : ℝ) ^ 35 ≤ dpSourceLogThreshold A :=
    le_max_left _ _
  have hExpInner : Real.exp 2 ≤ max (Real.exp 2) (M ^ 2) := le_max_left _ _
  have hExpBound : Real.exp 2 ≤ dpSourceLogThreshold A :=
    hExpInner.trans (le_max_right _ _)
  have hMInner : M ^ 2 ≤ max (Real.exp 2) (M ^ 2) := le_max_right _ _
  have hMBound : M ^ 2 ≤ dpSourceLogThreshold A :=
    hMInner.trans (le_max_right _ _)
  have hthree : (3 : ℝ) ≤ (2 : ℝ) ^ 35 := by norm_num
  refine ⟨hthree.trans hPowerBound, ?_⟩
  intro X hX
  have hPowerX : (2 : ℝ) ^ 35 ≤ X := hPowerBound.trans hX
  have hExpX : Real.exp 2 ≤ X := hExpBound.trans hX
  have hMX : M ^ 2 ≤ X := hMBound.trans hX
  have hlogTwo : 2 ≤ Real.log X := by
    calc
      2 = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos 2) hExpX
  have hlogMpow : Real.log (M ^ 2) = 2 * Real.log M := by
    rw [Real.log_pow]
    norm_num
  have hlogM : 2 * Real.log M ≤ Real.log X := by
    calc
      2 * Real.log M = Real.log (M ^ 2) := hlogMpow.symm
      _ ≤ Real.log X := Real.log_le_log (pow_pos hMpos 2) hMX
  refine ⟨hPowerX, ?_, hlogTwo, ?_⟩
  · linarith
  · simpa only [M] using hlogM

/-- The source choice `W=(log X)^D` satisfies its lower side condition
`2≤W` once the `D≥128S` parameter budget and the explicit log threshold hold. -/
theorem dpSourceLogWindow_lower_bound_of_parameterBudget
    {A B D : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hD : 128 * dpSourceBudgetS A B ≤ D) :
    ∀ X : ℝ, dpSourceLogThreshold A ≤ X →
      2 ≤ (Real.log X) ^ D := by
  have hpNat : 100 ≤ dpSourceBudgetP := by
    change 100 ≤ b 20 + 3 * 2 ^ 20 + 100
    omega
  have hpReal : (100 : ℝ) ≤ (dpSourceBudgetP : ℝ) := by
    exact_mod_cast hpNat
  have hSone : 1 ≤ dpSourceBudgetS A B := by
    unfold dpSourceBudgetS
    nlinarith [hA, hB, hpReal]
  have hDone : 1 ≤ D := by
    nlinarith [hD, hSone]
  have hDnonneg : 0 ≤ D := le_trans (by norm_num) hDone
  intro X hX
  rcases (dpSourceLogThreshold_spec A).2 X hX with
    ⟨_, _, hlogTwo, _⟩
  calc
    2 = (2 : ℝ) ^ (1 : ℝ) := by simp
    _ ≤ (2 : ℝ) ^ D :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hDone
    _ ≤ (Real.log X) ^ D :=
      Real.rpow_le_rpow (by norm_num) hlogTwo hDnonneg

#print axioms dpSourceLogThreshold_spec
#print axioms dpSourceLogWindow_lower_bound_of_parameterBudget

end
end FractionalPrimes.Literature.DirichletAdapter
