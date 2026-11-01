module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open Real

/-- The explicit constant in the logarithmic absorption part of
`lu:elementary-growth`. -/
noncomputable def logAbsorptionM (a b : ℝ) : ℝ :=
  if b = 0 then 1 else max 1 ((2 * b / (a * Real.exp 1)) ^ b)

theorem one_le_logAbsorptionM {a b : ℝ} :
    1 ≤ logAbsorptionM a b := by
  by_cases hb : b = 0
  · simp [logAbsorptionM, hb]
  · simp [logAbsorptionM, hb]

/-- For nonnegative `t`, the exact auxiliary power bound used in the
blueprint's explicit logarithmic absorption argument. -/
theorem rpow_le_logAbsorptionM_mul_exp {a b t : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    t ^ b ≤ logAbsorptionM a b * Real.exp (a * t / 2) := by
  by_cases hb0 : b = 0
  · have ht_exp_nonneg : 0 ≤ a * t / 2 := by positivity
    calc
      t ^ b = 1 := by simp [hb0]
      _ ≤ Real.exp (a * t / 2) := by
        nlinarith [Real.add_one_le_exp (a * t / 2)]
      _ = logAbsorptionM a b * Real.exp (a * t / 2) := by
        simp [logAbsorptionM, hb0]
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    let q : ℝ := 2 * b / a
    let z : ℝ := t / q
    let C : ℝ := (q / Real.exp 1) ^ b
    have hqpos : 0 < q := by
      dsimp [q]
      positivity
    have hznonneg : 0 ≤ z := by
      dsimp [z]
      exact div_nonneg ht hqpos.le
    by_cases ht0 : t = 0
    · simp [ht0, hbpos.ne', logAbsorptionM]
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hzpos : 0 < z := by
        dsimp [z]
        exact div_pos htpos hqpos
      have ht_eq : t = q * z := by
        dsimp [z]
        symm
        exact mul_div_cancel₀ t hqpos.ne'
      have hscale : a * t / 2 = b * z := by
        dsimp [q, z]
        field_simp [ha.ne', hbpos.ne']
      have hlogt : Real.log t = Real.log q + Real.log z := by
        rw [ht_eq, Real.log_mul hqpos.ne' hzpos.ne']
      have hlogz := Real.log_le_sub_one_of_pos hzpos
      have hCpos : 0 < C := by
        dsimp [C]
        exact Real.rpow_pos_of_pos (div_pos hqpos (Real.exp_pos 1)) b
      have hlogC : Real.log C = b * (Real.log q - 1) := by
        dsimp [C]
        rw [Real.log_rpow (div_pos hqpos (Real.exp_pos 1)) b,
          Real.log_div hqpos.ne' (Real.exp_ne_zero 1), Real.log_exp]
      have hCeq : C = (2 * b / (a * Real.exp 1)) ^ b := by
        dsimp [C, q]
        congr 1
        field_simp [ha.ne', (Real.exp_pos 1).ne']
      have hCle : C ≤ logAbsorptionM a b := by
        simp [logAbsorptionM, hb0, hCeq]
      have hlogpower : b * Real.log t ≤ Real.log C + a * t / 2 := by
        rw [hlogt, hlogC]
        have hmul := mul_le_mul_of_nonneg_left hlogz hb
        nlinarith [hmul, hscale]
      calc
        t ^ b = Real.exp (Real.log t * b) := Real.rpow_def_of_pos htpos b
        _ ≤ Real.exp (Real.log C + a * t / 2) :=
          Real.exp_le_exp.mpr (by nlinarith [hlogpower])
        _ = C * Real.exp (a * t / 2) := by
          rw [Real.exp_add, Real.exp_log hCpos]
        _ ≤ logAbsorptionM a b * Real.exp (a * t / 2) :=
          mul_le_mul_of_nonneg_right hCle (Real.exp_nonneg _)

/-- The explicit logarithmic absorption inequality in `lu:elementary-growth`.
The standing scale hypothesis `1 ≤ X` is the one in that blueprint lemma. -/
theorem log_absorption_bound {a b K X : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hK : 1 ≤ K) (hX : 1 ≤ X)
    (hlarge : (2 / a) * Real.log (K * logAbsorptionM a b) ≤ Real.log X) :
    K * (Real.log X) ^ b ≤ X ^ a := by
  have hXpos : 0 < X := by linarith
  have hM : 1 ≤ logAbsorptionM a b := one_le_logAbsorptionM
  have hKMpos : 0 < K * logAbsorptionM a b := by positivity
  have hKMlog : 0 ≤ Real.log (K * logAbsorptionM a b) :=
    (Real.log_nonneg_iff hKMpos).2 (by nlinarith [hK, hM])
  have ht : 0 ≤ Real.log X := by
    have hcoef : 0 ≤ (2 / a) * Real.log (K * logAbsorptionM a b) :=
      mul_nonneg (by positivity) hKMlog
    exact hcoef.trans hlarge
  have hhalf : Real.log (K * logAbsorptionM a b) ≤ a * Real.log X / 2 := by
    have hcoef : (a / 2) * (2 / a) = 1 := by
      field_simp [ha.ne']
    calc
      Real.log (K * logAbsorptionM a b) =
          (a / 2) * ((2 / a) * Real.log (K * logAbsorptionM a b)) := by
        rw [← mul_assoc, hcoef, one_mul]
      _ ≤ (a / 2) * Real.log X :=
        mul_le_mul_of_nonneg_left hlarge (by positivity)
      _ = a * Real.log X / 2 := by ring
  have hKMexp : K * logAbsorptionM a b ≤
      Real.exp (a * Real.log X / 2) := by
    have h := Real.exp_le_exp.mpr hhalf
    simpa only [Real.exp_log hKMpos] using h
  have hpow := rpow_le_logAbsorptionM_mul_exp ha hb ht
  have hresult : K * (Real.log X) ^ b ≤ Real.exp (a * Real.log X) := by
    calc
      K * (Real.log X) ^ b ≤
          K * (logAbsorptionM a b * Real.exp (a * Real.log X / 2)) :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
      _ = (K * logAbsorptionM a b) * Real.exp (a * Real.log X / 2) := by ring
      _ ≤ Real.exp (a * Real.log X / 2) * Real.exp (a * Real.log X / 2) :=
        mul_le_mul_of_nonneg_right hKMexp (Real.exp_nonneg _)
      _ = Real.exp (a * Real.log X) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    K * (Real.log X) ^ b ≤ Real.exp (a * Real.log X) := hresult
    _ = X ^ a := by
      rw [Real.rpow_def_of_pos hXpos a]
      congr 1
      ring

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.log_absorption_bound
