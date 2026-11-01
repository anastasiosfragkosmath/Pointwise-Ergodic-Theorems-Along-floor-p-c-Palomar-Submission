module

public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTransferAssembly
public import Mathlib.Tactic

/-! Finite compatibility of the source PTW character/allocation window with
the full-frequency envelope window used by absolute Mellin transfer. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Uniformity

/-- Explicit eventual-X threshold ensuring that every frequency interval in
the absolute-transfer envelope also lies in the source character/allocation
window. The two exponential terms provide `X^eta ≥ 2` and absorb the exact
factor `(log X)^(40a)` into `X^(eta/2)`. -/
noncomputable def selectedMobiusPTWSourceWindowThreshold
    (a eta : ℝ) : ℝ :=
  max (selectedMobiusPTWTransferGrowthThreshold a eta)
    (max (Real.exp (Real.log 2 / eta))
      (Real.exp ((2 / (eta / 2)) *
        Real.log (logAbsorptionM (eta / 2) (40 * a)))))

set_option maxHeartbeats 3000000 in
private theorem selectedMobiusPTWTransferW_four
    {X a : ℝ} (hlog : 0 ≤ Real.log X) :
    selectedMobiusPTWTransferW X a ^ 4 = (Real.log X) ^ (40 * a) := by
  rw [selectedMobiusPTWTransferW,
    (Real.rpow_mul_natCast hlog (10 * a) 4).symm]
  congr 1
  ring

set_option maxHeartbeats 3000000 in
/-- On the exact absolute-transfer envelope interval, the source hypotheses
`U ≤ X^(3/8-eps)` and separated-frequency bounds hold with
`eps=eta/2`. Thus the already checked selected Möbius source integral may be
applied at every envelope frequency. This is parameter bookkeeping only; it
does not identify the source character/allocation integrand with a full
frequency polynomial. -/
theorem selectedMobiusPTWSourceWindow_compatible
    {a eta X H T U : ℝ}
    (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (heta0 : 0 < eta) (heta : eta < 3 / 16)
    (hX : selectedMobiusPTWSourceWindowThreshold a eta ≤ X)
    (hHpos : 0 < H)
    (hHlower : X ^ (5 / 8 + eta) ≤ H)
    (hHupper : H ≤ X ^ (1 - eta))
    (hTlower : (X / H) * (Real.log X) ^ (50 * a) ≤ |T|)
    (hTupper : |T| ≤ X ^ a)
    (hU : U ∈ Set.Icc (X / H)
      ((X / H) * selectedMobiusPTWTransferW X a ^ 4)) :
    2 ≤ U ∧
      U ≤ X ^ (3 / 8 - eta / 2) ∧
      ∀ t ∈ Set.Icc (-U) U,
        (Real.log X) ^ (45 * a) ≤ |T - t| ∧
          |T - t| ≤ X ^ (a + 1) := by
  have hXold : selectedMobiusPTWTransferGrowthThreshold a eta ≤ X :=
    (le_max_left _ _).trans hX
  have hXeta : Real.exp (Real.log 2 / eta) ≤ X :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXabsorb :
      Real.exp ((2 / (eta / 2)) *
        Real.log (logAbsorptionM (eta / 2) (40 * a))) ≤ X :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hgrowth :=
    selectedMobiusPTWTransferGrowth_of_threshold ha heta0 hXold
  have hX120 : (2 : ℝ) ^ 120 ≤ X := hgrowth.2.1
  have hXpos : 0 < X := by linarith [hX120]
  have hXone : 1 ≤ X := by linarith [hX120]
  have hlog2 : 2 ≤ Real.log X := hgrowth.1
  have hLone : 1 ≤ Real.log X := by linarith
  have hLpos : 0 < Real.log X := by linarith
  have hLnonneg : 0 ≤ Real.log X := by linarith
  have ha2 : 2 ≤ a := by
    have h2nat : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
    have h2 : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast h2nat
    exact h2.trans ha
  have hEtaAbsorbLog :
      (2 / (eta / 2)) *
        Real.log (logAbsorptionM (eta / 2) (40 * a)) ≤ Real.log X := by
    have hle :
        Real.exp ((2 / (eta / 2)) *
          Real.log (logAbsorptionM (eta / 2) (40 * a))) ≤
        Real.exp (Real.log X) := by
      simpa [Real.exp_log hXpos] using hXabsorb
    exact Real.exp_le_exp.mp hle
  have hlogpow := log_absorption_bound
    (a := eta / 2) (b := 40 * a) (K := 1) (X := X)
    (by positivity) (by positivity) (by norm_num) hXone
    (by simpa [one_mul] using hEtaAbsorbLog)
  have hlogpow' : (Real.log X) ^ (40 * a) ≤ X ^ (eta / 2) := by
    simpa [one_mul] using hlogpow
  have hXeta2 : 2 ≤ X ^ eta := by
    have hlogBase : Real.log 2 / eta ≤ Real.log X := by
      have hle : Real.exp (Real.log 2 / eta) ≤ Real.exp (Real.log X) := by
        simpa [Real.exp_log hXpos] using hXeta
      exact Real.exp_le_exp.mp hle
    have hmul' : Real.log 2 ≤ Real.log X * eta := by
      exact (div_le_iff₀ heta0).mp hlogBase
    have hmul : Real.log 2 ≤ eta * Real.log X := by
      nlinarith [hmul']
    calc
      2 = Real.exp (Real.log 2) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp (eta * Real.log X) := Real.exp_le_exp.mpr hmul
      _ = X ^ eta := by
        rw [Real.rpow_def_of_pos hXpos]
        congr 1
        ring
  have hratioLower : X ^ eta ≤ X / H := by
    apply (le_div_iff₀ hHpos).2
    have hpow : X ^ eta * X ^ (1 - eta) = X := by
      calc
        X ^ eta * X ^ (1 - eta) = X ^ (eta + (1 - eta)) :=
          (Real.rpow_add hXpos eta (1 - eta)).symm
        _ = X := by simp
    calc
      X ^ eta * H ≤ X ^ eta * X ^ (1 - eta) :=
        mul_le_mul_of_nonneg_left hHupper (Real.rpow_nonneg hXpos.le _)
      _ = X := hpow
  have hratioUpper : X / H ≤ X ^ (3 / 8 - eta) := by
    apply (div_le_iff₀ hHpos).2
    have hpow : X ^ (3 / 8 - eta) * X ^ (5 / 8 + eta) = X := by
      calc
        X ^ (3 / 8 - eta) * X ^ (5 / 8 + eta) =
            X ^ ((3 / 8 - eta) + (5 / 8 + eta)) :=
          (Real.rpow_add hXpos (3 / 8 - eta) (5 / 8 + eta)).symm
        _ = X := by norm_num
    calc
      X = X ^ (3 / 8 - eta) * X ^ (5 / 8 + eta) := hpow.symm
      _ ≤ X ^ (3 / 8 - eta) * H :=
        mul_le_mul_of_nonneg_left hHlower
          (Real.rpow_nonneg hXpos.le _)
  have hT0ge2 : 2 ≤ X / H := le_trans hXeta2 hratioLower
  have hUlower : 2 ≤ U := le_trans hT0ge2 hU.1
  have hW4 : selectedMobiusPTWTransferW X a ^ 4 =
      (Real.log X) ^ (40 * a) :=
    selectedMobiusPTWTransferW_four hLnonneg
  have hUupper : U ≤ X ^ (3 / 8 - eta / 2) := by
    calc
      U ≤ (X / H) * selectedMobiusPTWTransferW X a ^ 4 := hU.2
      _ ≤ X ^ (3 / 8 - eta) * (Real.log X) ^ (40 * a) := by
        rw [hW4]
        exact mul_le_mul_of_nonneg_right hratioUpper
          (Real.rpow_nonneg hLnonneg _)
      _ ≤ X ^ (3 / 8 - eta) * X ^ (eta / 2) :=
        mul_le_mul_of_nonneg_left hlogpow'
          (Real.rpow_nonneg hXpos.le _)
      _ = X ^ (3 / 8 - eta / 2) := by
        rw [← Real.rpow_add hXpos]
        congr 1
        ring
  have hLpow45nonneg : 0 ≤ (Real.log X) ^ (45 * a) :=
    Real.rpow_nonneg hLnonneg _
  have hLpow50 : 1 ≤ (Real.log X) ^ (50 * a) :=
    Real.one_le_rpow hLone (by positivity)
  have hLpow40 : 0 ≤ (Real.log X) ^ (40 * a) :=
    Real.rpow_nonneg hLnonneg _
  have hT0ge1 : 1 ≤ X / H := le_trans (by norm_num) hT0ge2
  have hpowNeg : (Real.log X) ^ (-(5 * a)) ≤ 1 := by
    rw [Real.rpow_neg hLpos.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hLone (by positivity))
  have hpowPos : 2 ≤ (Real.log X) ^ (5 * a) := by
    have hexp : (1 : ℝ) ≤ 5 * a := by nlinarith [ha2]
    have h := Real.rpow_le_rpow_of_exponent_le hLone hexp
    rw [Real.rpow_one] at h
    exact le_trans hlog2 h
  have hpowGap :
      (Real.log X) ^ (50 * a) - (Real.log X) ^ (40 * a) ≥
        (Real.log X) ^ (45 * a) := by
    have hfact50 :
        (Real.log X) ^ (45 * a) * (Real.log X) ^ (5 * a) =
          (Real.log X) ^ (50 * a) := by
      calc
        _ = (Real.log X) ^ (45 * a + 5 * a) :=
          (Real.rpow_add hLpos (45 * a) (5 * a)).symm
        _ = _ := by congr 1 <;> ring
    have hfact40 :
        (Real.log X) ^ (45 * a) * (Real.log X) ^ (-(5 * a)) =
          (Real.log X) ^ (40 * a) := by
      calc
        _ = (Real.log X) ^ (45 * a + -(5 * a)) :=
          (Real.rpow_add hLpos (45 * a) (-(5 * a))).symm
        _ = _ := by congr 1 <;> ring
    rw [← hfact50, ← hfact40]
    calc
      (Real.log X) ^ (45 * a) * (Real.log X) ^ (5 * a) -
          (Real.log X) ^ (45 * a) * (Real.log X) ^ (-(5 * a)) =
        (Real.log X) ^ (45 * a) *
          ((Real.log X) ^ (5 * a) - (Real.log X) ^ (-(5 * a))) := by ring
      _ ≥ (Real.log X) ^ (45 * a) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) hLpow45nonneg
      _ = (Real.log X) ^ (45 * a) := by ring
  have hXpowA_nonneg : 0 ≤ X ^ a := Real.rpow_nonneg hXpos.le _
  have hUleXa : U ≤ X ^ a := by
    have hexp : 3 / 8 - eta / 2 ≤ a := by linarith [ha2]
    exact hUupper.trans
      (Real.rpow_le_rpow_of_exponent_le hXone hexp)
  have htwoXa : 2 * X ^ a ≤ X ^ (a + 1) := by
    calc
      2 * X ^ a ≤ X * X ^ a := by nlinarith [hXone, hXpowA_nonneg]
      _ = X ^ a * X := by ring
      _ = X ^ a * X ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = X ^ (a + 1) := (Real.rpow_add hXpos a 1).symm
  refine ⟨hUlower, hUupper, ?_⟩
  intro t ht
  have htabs : |t| ≤ U := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hTdiffLower :
      (Real.log X) ^ (45 * a) ≤ |T - t| := by
    have htriangle : |T| - |t| ≤ |T - t| := by
      nlinarith [abs_sub_abs_le_abs_sub T t]
    have hfactor :
        (X / H) * ((Real.log X) ^ (50 * a) -
          (Real.log X) ^ (40 * a)) ≤ |T| - |t| := by
      have huT : |t| ≤ (X / H) * (Real.log X) ^ (40 * a) := by
        calc
          |t| ≤ U := htabs
          _ ≤ (X / H) * selectedMobiusPTWTransferW X a ^ 4 := hU.2
          _ = (X / H) * (Real.log X) ^ (40 * a) := by rw [hW4]
      calc
        _ = (X / H) * (Real.log X) ^ (50 * a) -
            (X / H) * (Real.log X) ^ (40 * a) := by ring
        _ ≤ |T| - (X / H) * (Real.log X) ^ (40 * a) :=
          sub_le_sub_right hTlower _
        _ ≤ |T| - |t| := by linarith [huT]
    have hgapNonneg : 0 ≤ (Real.log X) ^ (50 * a) -
        (Real.log X) ^ (40 * a) :=
      le_trans hLpow45nonneg hpowGap
    have hscale : (Real.log X) ^ (45 * a) ≤
        (X / H) * ((Real.log X) ^ (50 * a) -
          (Real.log X) ^ (40 * a)) := by
      calc
        _ ≤ 1 * ((Real.log X) ^ (50 * a) -
            (Real.log X) ^ (40 * a)) := by rw [one_mul]; exact hpowGap
        _ ≤ (X / H) * ((Real.log X) ^ (50 * a) -
            (Real.log X) ^ (40 * a)) :=
          mul_le_mul_of_nonneg_right hT0ge1 hgapNonneg
    exact le_trans hscale (le_trans hfactor htriangle)
  have htriangleUpper : |T - t| ≤ |T| + |t| := by
    calc
      |T - t| = |T + -t| := by congr 1 <;> ring
      _ ≤ |T| + |-t| := abs_add_le _ _
      _ = |T| + |t| := by simp
  have hTdiffUpper : |T - t| ≤ X ^ (a + 1) := by
    calc
      |T - t| ≤ |T| + |t| := htriangleUpper
      _ ≤ X ^ a + X ^ a := add_le_add hTupper (htabs.trans hUleXa)
      _ = 2 * X ^ a := by ring
      _ ≤ X ^ (a + 1) := htwoXa
  exact ⟨hTdiffLower, hTdiffUpper⟩

#print axioms selectedMobiusPTWSourceWindow_compatible

end FractionalPrimes.Literature.DirichletMean

end
