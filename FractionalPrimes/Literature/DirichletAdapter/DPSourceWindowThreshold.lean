module
public import FractionalPrimes.Literature.DirichletAdapter.DPSourceLogThreshold
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
public import Mathlib.Tactic
@[expose] public section

/-!
# Explicit source window threshold for the DP task

The original scalar DP task requires `2 ≤ W ≤ X^(1/100)` and
`W ≤ T₀`, where `W=(log X)^D` and `T₀=X/H`.  The source interval
hypothesis `H ≤ X^(1-η)` gives `X^η ≤ T₀`.  This file chooses a concrete
threshold that makes both logarithmic-power comparisons hold and then
derives `W ≤ T₀` from that exact H hypothesis.
-/

namespace FractionalPrimes.Literature.DirichletAdapter

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.DirichletMean
noncomputable section

/-- A threshold simultaneously enforcing the earlier component logarithmic
absorption condition and the two source window upper bounds. -/
noncomputable def dpSourceWindowThreshold (A η D : ℝ) : ℝ :=
  max (dpSourceLogThreshold A)
    (max
      (Real.exp (200 * Real.log (logAbsorptionM (1 / 100) D)))
      (Real.exp ((2 / η) * Real.log (logAbsorptionM η D))))

/-- Above the displayed threshold, the source window `W=(log X)^D` lies below
both `X^(1/100)` and `X^η`, and all logarithmic side conditions from the
component threshold hold. -/
theorem dpSourceWindowThreshold_spec
    {A B η D : ℝ} (hA : 0 < A) (hB : 0 < B) (hη : 0 < η)
    (hD : 128 * dpSourceBudgetS A B ≤ D) :
    3 ≤ dpSourceWindowThreshold A η D ∧
      ∀ X : ℝ, dpSourceWindowThreshold A η D ≤ X →
        1 ≤ Real.log X ∧
        2 ≤ Real.log X ∧
        2 * Real.log (logAbsorptionM 1 (A + 22)) ≤ Real.log X ∧
        2 ≤ (Real.log X) ^ D ∧
        (Real.log X) ^ D ≤ X ^ (1 / 100 : ℝ) ∧
        (Real.log X) ^ D ≤ X ^ η := by
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
  have hbase : 3 ≤ dpSourceLogThreshold A :=
    (dpSourceLogThreshold_spec A).1
  have hbaseLe : dpSourceLogThreshold A ≤ dpSourceWindowThreshold A η D :=
    le_max_left _ _
  have h100Le :
      Real.exp (200 * Real.log (logAbsorptionM (1 / 100) D)) ≤
        dpSourceWindowThreshold A η D := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hηLe :
      Real.exp ((2 / η) * Real.log (logAbsorptionM η D)) ≤
        dpSourceWindowThreshold A η D := by
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hthresholdThree : 3 ≤ dpSourceWindowThreshold A η D :=
    hbase.trans hbaseLe
  refine ⟨hthresholdThree, ?_⟩
  intro X hX
  have hbaseX : dpSourceLogThreshold A ≤ X := hbaseLe.trans hX
  rcases (dpSourceLogThreshold_spec A).2 X hbaseX with
    ⟨_, hlogOne, hlogTwo, hAbsorb⟩
  have hXone : 1 ≤ X := by linarith
  have hExp100X :
      Real.exp (200 * Real.log (logAbsorptionM (1 / 100) D)) ≤ X :=
    h100Le.trans hX
  have hExπηX :
      Real.exp ((2 / η) * Real.log (logAbsorptionM η D)) ≤ X :=
    hηLe.trans hX
  have hlarge100 :
      (2 / (1 / 100 : ℝ)) * Real.log (logAbsorptionM (1 / 100) D) ≤
        Real.log X := by
    calc
      (2 / (1 / 100 : ℝ)) * Real.log (logAbsorptionM (1 / 100) D) =
          200 * Real.log (logAbsorptionM (1 / 100) D) := by norm_num
      _ = Real.log
          (Real.exp (200 * Real.log (logAbsorptionM (1 / 100) D))) :=
            (Real.log_exp _).symm
      _ ≤ Real.log X :=
        Real.log_le_log (Real.exp_pos _) hExp100X
  have hlarge100' :
      (2 / (1 / 100 : ℝ)) * Real.log
          (1 * logAbsorptionM (1 / 100) D) ≤ Real.log X := by
    simpa only [one_mul] using hlarge100
  have hlargeη :
      (2 / η) * Real.log (logAbsorptionM η D) ≤ Real.log X := by
    calc
      (2 / η) * Real.log (logAbsorptionM η D) =
          Real.log (Real.exp ((2 / η) * Real.log (logAbsorptionM η D))) :=
            (Real.log_exp _).symm
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos _) hExπηX
  have hlargeη' :
      (2 / η) * Real.log (1 * logAbsorptionM η D) ≤ Real.log X := by
    simpa only [one_mul] using hlargeη
  have hpow100 : (Real.log X) ^ D ≤ X ^ (1 / 100 : ℝ) := by
    have h := log_absorption_bound
      (a := (1 / 100 : ℝ)) (b := D) (K := 1) (X := X)
      (by norm_num) hDnonneg (by norm_num) hXone hlarge100'
    simpa only [one_mul] using h
  have hpowη : (Real.log X) ^ D ≤ X ^ η := by
    have h := log_absorption_bound
      (a := η) (b := D) (K := 1) (X := X)
      hη hDnonneg (by norm_num) hXone hlargeη'
    simpa only [one_mul] using h
  have hWtwo : 2 ≤ (Real.log X) ^ D :=
    dpSourceLogWindow_lower_bound_of_parameterBudget hA hB hD X hbaseX
  exact ⟨hlogOne, hlogTwo, hAbsorb, hWtwo, hpow100, hpowη⟩

/-- The exact natural-parameter source H hypotheses imply the complete DP
window side conditions, including `W≤T₀=X/H`.  The intermediate `W≤X^η`
records precisely where the upper bound on H is used. -/
theorem dpSourceWindowThreshold_source_conditions
    {A B η D : ℝ} (hA : 0 < A) (hB : 0 < B) (hη : 0 < η)
    (hη₃ : η < 3 / 16)
    (hD : 128 * dpSourceBudgetS A B ≤ D)
    {X H : ℕ}
    (hX : dpSourceWindowThreshold A η D ≤ (X : ℝ))
    (hHlower : (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ))
    (hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - η)) :
    3 ≤ (X : ℝ) ∧
      1 ≤ Real.log (X : ℝ) ∧
      2 * Real.log (logAbsorptionM 1 (A + 22)) ≤ Real.log (X : ℝ) ∧
      let W : ℝ := (Real.log (X : ℝ)) ^ D
      2 ≤ W ∧
        W ≤ (X : ℝ) ^ (1 / 100 : ℝ) ∧
        W ≤ (X : ℝ) ^ η ∧
        W ≤ (X : ℝ) / (H : ℝ) := by
  have hbaseThree : 3 ≤ dpSourceLogThreshold A :=
    (dpSourceLogThreshold_spec A).1
  have hbaseLe : dpSourceLogThreshold A ≤ dpSourceWindowThreshold A η D :=
    le_max_left _ _
  have hXthree : 3 ≤ (X : ℝ) :=
    (hbaseThree.trans hbaseLe).trans hX
  rcases (dpSourceWindowThreshold_spec hA hB hη hD).2 (X : ℝ) hX with
    ⟨hlogOne, _, hAbsorb, hWtwo, hW100, hWη⟩
  have hXpos : 0 < (X : ℝ) := by linarith
  have hHpos : 0 < (H : ℝ) := by
    have hbasePow : 0 < (X : ℝ) ^ ((5 / 8 : ℝ) + η) :=
      Real.rpow_pos_of_pos hXpos _
    exact lt_of_lt_of_le hbasePow hHlower
  have hWleT₀ : (Real.log (X : ℝ)) ^ D ≤ (X : ℝ) / (H : ℝ) := by
    have hpowNonneg : 0 ≤ (X : ℝ) ^ η :=
      Real.rpow_nonneg hXpos.le _
    have hprod : (X : ℝ) ^ η * (H : ℝ) ≤ (X : ℝ) := by
      calc
        (X : ℝ) ^ η * (H : ℝ) ≤
            (X : ℝ) ^ η * (X : ℝ) ^ (1 - η) :=
          mul_le_mul_of_nonneg_left hHupper hpowNonneg
        _ = (X : ℝ) ^ (η + (1 - η)) :=
          (Real.rpow_add hXpos η (1 - η)).symm
        _ = (X : ℝ) := by
          rw [show η + (1 - η) = 1 by ring, Real.rpow_one]
    have hpowLeT₀ : (X : ℝ) ^ η ≤ (X : ℝ) / (H : ℝ) :=
      (le_div_iff₀ hHpos).2 hprod
    exact hWη.trans hpowLeT₀
  refine ⟨hXthree, hlogOne, hAbsorb, ?_⟩
  simpa only using ⟨hWtwo, hW100, hWη, hWleT₀⟩

#print axioms dpSourceWindowThreshold_spec
#print axioms dpSourceWindowThreshold_source_conditions

end
end FractionalPrimes.Literature.DirichletAdapter
