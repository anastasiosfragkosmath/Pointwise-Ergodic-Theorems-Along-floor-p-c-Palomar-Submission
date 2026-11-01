module

public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWSourceWindow
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
public import Mathlib.Tactic

/-! Numerical facts for applying the selected full-frequency estimate at a
local prefix length `m` while the phase range is normalized by the macro
length `H`. The extra `42*a` threshold accounts for the loss
`m ≥ H (log X)^(-2a)` in the local frequency window. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Uniformity

/-- The source window threshold augmented by the exact `42*a` logarithmic
absorption needed when the Mellin window is based on a local prefix length
`m ≥ H (log X)^(-2a)`. -/
noncomputable def selectedMobiusPTWLocalPrefixWindowThreshold
    (a eta : ℝ) : ℝ :=
  max (selectedMobiusPTWSourceWindowThreshold a eta)
    (Real.exp ((2 / (eta / 2)) *
      Real.log (logAbsorptionM (eta / 2) (42 * a))))

private theorem selectedMobiusPTWLocalPrefixTransferW_four
    {X a : ℝ} (hlog : 0 ≤ Real.log X) :
    selectedMobiusPTWTransferW X a ^ 4 = (Real.log X) ^ (40 * a) := by
  rw [selectedMobiusPTWTransferW,
    (Real.rpow_mul_natCast hlog (10 * a) 4).symm]
  congr 1
  ring

/-- The exact frequency and source-range conditions for a local prefix.
The long-frequency lower bound is stated at the macro length `H`, while
the Mellin window uses `m`; the assumption `H (log X)^(-2a) ≤ m` bridges
these conventions without changing the source range. -/
theorem selectedMobiusPTWLocalPrefixWindowFacts
    {a eta X H m U T : ℝ}
    (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (heta0 : 0 < eta) (heta : eta < 3 / 16)
    (hX : selectedMobiusPTWLocalPrefixWindowThreshold a eta ≤ X)
    (hHlower : X ^ (5 / 8 + eta) ≤ H)
    (hHupper : H ≤ X ^ (1 - eta))
    (hmlower : H * (Real.log X) ^ (-2 * a) ≤ m)
    (hmupper : m ≤ H)
    (hTlower : (X / H) * (Real.log X) ^ (50 * a) ≤ |T|)
    (hTupper : |T| ≤ X ^ a)
    (hU : U ∈ Set.Icc (X / m)
      ((X / m) * selectedMobiusPTWTransferW X a ^ 4)) :
    0 < m ∧ m ≤ X ∧ 2 ≤ U ∧
      U ≤ X ^ (3 / 8 - eta / 2) ∧
      ∀ t ∈ Set.Icc (-U) U,
        (Real.log X) ^ (45 * a) ≤ |T - t| ∧
          |T - t| ≤ X ^ (a + 1) := by
  have hSourceWindow : selectedMobiusPTWSourceWindowThreshold a eta ≤ X :=
    (le_max_left _ _).trans hX
  have h42Threshold : Real.exp ((2 / (eta / 2)) *
      Real.log (logAbsorptionM (eta / 2) (42 * a))) ≤ X :=
    (le_max_right _ _).trans hX
  have hGrowthThreshold : selectedMobiusPTWTransferGrowthThreshold a eta ≤ X :=
    (le_max_left _ _).trans hSourceWindow
  have hGrowth := selectedMobiusPTWTransferGrowth_of_threshold ha heta0
    hGrowthThreshold
  have hlog2 : 2 ≤ Real.log X := hGrowth.1
  have hX120 : (2 : ℝ) ^ 120 ≤ X := hGrowth.2.1
  have hXpos : 0 < X := by positivity
  have hlogpos : 0 < Real.log X := by linarith
  have hlognonneg : 0 ≤ Real.log X := hlogpos.le
  have hXone : 1 ≤ X := by
    have hOne : (1 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hOne.trans hX120
  have ha2 : 2 ≤ a := by
    have hTwoNat : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
    have hTwo : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast hTwoNat
    exact hTwo.trans ha
  have hlogone : 1 ≤ Real.log X := by linarith
  have hL42 : (Real.log X) ^ (42 * a) ≤ X ^ (eta / 2) := by
    have hAbsorbLog :
        (2 / (eta / 2)) *
          Real.log (logAbsorptionM (eta / 2) (42 * a)) ≤ Real.log X := by
      have hExp : Real.exp ((2 / (eta / 2)) *
          Real.log (logAbsorptionM (eta / 2) (42 * a))) ≤
          Real.exp (Real.log X) := by
        simpa [Real.exp_log hXpos] using h42Threshold
      exact Real.exp_le_exp.mp hExp
    have hBound := log_absorption_bound
      (a := eta / 2) (b := 42 * a) (K := 1) (X := X)
      (by positivity) (by positivity) (by norm_num) hXone
      (by simpa [one_mul] using hAbsorbLog)
    simpa [one_mul] using hBound
  have hWone : 1 ≤ selectedMobiusPTWTransferW X a := by
    change 1 ≤ (Real.log X) ^ (10 * a)
    exact Real.one_le_rpow hlogone (by positivity)
  have hW4 : 1 ≤ selectedMobiusPTWTransferW X a ^ 4 := one_le_pow₀ hWone
  have hHpos : 0 < H := by
    have hpow : 0 < X ^ (5 / 8 + eta) := Real.rpow_pos_of_pos hXpos _
    exact lt_of_lt_of_le hpow hHlower
  have hHleX : H ≤ X := by
    have hexp : (1 - eta : ℝ) ≤ 1 := by linarith
    have hpow : X ^ (1 - eta) ≤ X ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hXone hexp
    simpa only [Real.rpow_one] using hHupper.trans hpow
  have hcutoffPos : 0 < H * (Real.log X) ^ (-2 * a) :=
    mul_pos hHpos (Real.rpow_pos_of_pos hlogpos _)
  have hmpos : 0 < m := lt_of_lt_of_le hcutoffPos hmlower
  have hmleX : m ≤ X := hmupper.trans hHleX
  have hXoverHpos : 0 < X / H := div_pos hXpos hHpos
  have hXoverHge2 : 2 ≤ X / H := by
    have hUmacro : X / H ∈ Set.Icc (X / H)
        ((X / H) * selectedMobiusPTWTransferW X a ^ 4) := by
      refine ⟨le_rfl, ?_⟩
      calc
        X / H = (X / H) * 1 := by ring
        _ ≤ (X / H) * selectedMobiusPTWTransferW X a ^ 4 :=
          mul_le_mul_of_nonneg_left hW4 hXoverHpos.le
    exact (selectedMobiusPTWSourceWindow_compatible
      ha heta0 heta hSourceWindow hHpos hHlower hHupper hTlower hTupper
      hUmacro).1
  have hL8a : 2 ≤ (Real.log X) ^ (8 * a) := by
    have hexp : (1 : ℝ) ≤ 8 * a := by nlinarith
    calc
      2 ≤ Real.log X := hlog2
      _ = (Real.log X) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (Real.log X) ^ (8 * a) :=
        Real.rpow_le_rpow_of_exponent_le hlogone hexp
  have hL5a : 2 ≤ (Real.log X) ^ (5 * a) := by
    have hexp : (1 : ℝ) ≤ 5 * a := by nlinarith
    calc
      2 ≤ Real.log X := hlog2
      _ = (Real.log X) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (Real.log X) ^ (5 * a) :=
        Real.rpow_le_rpow_of_exponent_le hlogone hexp
  have hTimeRatio : X / m ≤ (X / H) * (Real.log X) ^ (2 * a) := by
    have hInv :
        1 / m ≤ (Real.log X) ^ (2 * a) / H := by
      have hInvCut : 1 / (H * (Real.log X) ^ (-2 * a)) =
          (Real.log X) ^ (2 * a) / H := by
        rw [show (-2 * a : ℝ) = -(2 * a) by ring,
          Real.rpow_neg hlogpos.le]
        field_simp
      calc
        1 / m ≤ 1 / (H * (Real.log X) ^ (-2 * a)) :=
          one_div_le_one_div_of_le hcutoffPos hmlower
        _ = (Real.log X) ^ (2 * a) / H := hInvCut
    calc
      X / m = X * (1 / m) := by ring
      _ ≤ X * ((Real.log X) ^ (2 * a) / H) :=
        mul_le_mul_of_nonneg_left hInv hXpos.le
      _ = (X / H) * (Real.log X) ^ (2 * a) := by ring
  have hWfour := selectedMobiusPTWLocalPrefixTransferW_four
    (X := X) (a := a) hlognonneg
  have hLocalUpper : U ≤ (X / H) * (Real.log X) ^ (42 * a) := by
    have hUupper : U ≤ (X / m) * (Real.log X) ^ (40 * a) := by
      simpa only [hWfour] using hU.2
    have hmul :
        (X / m) * (Real.log X) ^ (40 * a) ≤
          ((X / H) * (Real.log X) ^ (2 * a)) *
            (Real.log X) ^ (40 * a) :=
      mul_le_mul_of_nonneg_right hTimeRatio
        (Real.rpow_nonneg hlognonneg _)
    calc
      U ≤ (X / m) * (Real.log X) ^ (40 * a) := hUupper
      _ ≤ ((X / H) * (Real.log X) ^ (2 * a)) *
            (Real.log X) ^ (40 * a) := hmul
      _ = (X / H) * (Real.log X) ^ (42 * a) := by
        calc
          _ = (X / H) *
              ((Real.log X) ^ (2 * a) * (Real.log X) ^ (40 * a)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hlogpos]
            congr 2
            ring
  have hUbound : U ≤ X ^ (3 / 8 - eta / 2) := by
    have hratio : X / H ≤ X ^ (3 / 8 - eta) := by
      apply (div_le_iff₀ hHpos).2
      have hprod : X ^ (3 / 8 - eta) * X ^ (5 / 8 + eta) = X := by
        calc
          X ^ (3 / 8 - eta) * X ^ (5 / 8 + eta) =
              X ^ ((3 / 8 - eta) + (5 / 8 + eta)) :=
            (Real.rpow_add hXpos _ _).symm
          _ = X := by
            have hsum : (3 / 8 - eta) + (5 / 8 + eta) = (1 : ℝ) := by ring
            rw [hsum, Real.rpow_one]
      calc
        X = X ^ (3 / 8 - eta) * X ^ (5 / 8 + eta) := hprod.symm
        _ ≤ X ^ (3 / 8 - eta) * H :=
          mul_le_mul_of_nonneg_left hHlower
            (Real.rpow_nonneg hXpos.le _)
    have hXpow :
        X ^ (3 / 8 - eta) * X ^ (eta / 2) =
          X ^ (3 / 8 - eta / 2) := by
      calc
        X ^ (3 / 8 - eta) * X ^ (eta / 2) =
            X ^ ((3 / 8 - eta) + eta / 2) :=
          (Real.rpow_add hXpos _ _).symm
        _ = X ^ (3 / 8 - eta / 2) := by congr 1 <;> ring
    calc
      U ≤ (X / H) * (Real.log X) ^ (42 * a) := hLocalUpper
      _ ≤ X ^ (3 / 8 - eta) * X ^ (eta / 2) :=
        mul_le_mul hratio hL42 (Real.rpow_nonneg hlognonneg _)
          (Real.rpow_nonneg hXpos.le _)
      _ = X ^ (3 / 8 - eta / 2) := hXpow
  have hL42to50 : (Real.log X) ^ (42 * a) ≤
      (1 / 2) * (Real.log X) ^ (50 * a) := by
    have hpow : (Real.log X) ^ (42 * a) *
        (Real.log X) ^ (8 * a) = (Real.log X) ^ (50 * a) := by
      calc
        _ = (Real.log X) ^ ((42 * a) + (8 * a)) :=
          (Real.rpow_add hlogpos _ _).symm
        _ = _ := by congr 1 <;> ring
    rw [← hpow]
    have hfactor := mul_le_mul_of_nonneg_left hL8a
      (Real.rpow_nonneg hlognonneg (42 * a))
    nlinarith
  have hLocalTime : U ≤ (1 / 2) * |T| := by
    calc
      U ≤ (X / H) * (Real.log X) ^ (42 * a) := hLocalUpper
      _ ≤ (X / H) * ((1 / 2) * (Real.log X) ^ (50 * a)) :=
        mul_le_mul_of_nonneg_left hL42to50 hXoverHpos.le
      _ = (1 / 2) * ((X / H) * (Real.log X) ^ (50 * a)) := by ring
      _ ≤ (1 / 2) * |T| := mul_le_mul_of_nonneg_left hTlower (by norm_num)
  have hL45to50 : (Real.log X) ^ (45 * a) ≤
      (1 / 2) * (Real.log X) ^ (50 * a) := by
    have hpow : (Real.log X) ^ (45 * a) *
        (Real.log X) ^ (5 * a) = (Real.log X) ^ (50 * a) := by
      calc
        _ = (Real.log X) ^ ((45 * a) + (5 * a)) :=
          (Real.rpow_add hlogpos _ _).symm
        _ = _ := by congr 1 <;> ring
    rw [← hpow]
    have hfactor := mul_le_mul_of_nonneg_left hL5a
      (Real.rpow_nonneg hlognonneg (45 * a))
    nlinarith
  have hSeparationLow :
      (Real.log X) ^ (45 * a) ≤ (1 / 2) * |T| := by
    calc
      (Real.log X) ^ (45 * a) ≤
          (1 / 2) * (Real.log X) ^ (50 * a) := hL45to50
      _ = 1 * ((1 / 2) * (Real.log X) ^ (50 * a)) := by ring
      _ ≤ (X / H) * ((1 / 2) * (Real.log X) ^ (50 * a)) :=
        mul_le_mul_of_nonneg_right (by linarith : 1 ≤ X / H)
          (by positivity)
      _ = (1 / 2) * ((X / H) * (Real.log X) ^ (50 * a)) := by ring
      _ ≤ (1 / 2) * |T| := mul_le_mul_of_nonneg_left hTlower (by norm_num)
  have hXtwo : 2 ≤ X := by
    have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact htwo.trans hX120
  have hTa : 0 ≤ X ^ a := Real.rpow_nonneg hXpos.le _
  have hReciprocal : 1 / H ≤ 1 / m :=
    one_div_le_one_div_of_le hmpos hmupper
  have hXoverm : X / H ≤ X / m := by
    calc
      X / H = X * (1 / H) := by ring
      _ ≤ X * (1 / m) := mul_le_mul_of_nonneg_left hReciprocal hXpos.le
      _ = X / m := by ring
  refine ⟨hmpos, hmleX, hXoverHge2.trans (hXoverm.trans hU.1), hUbound, ?_⟩
  · intro t ht
    have htAbs : |t| ≤ U := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have htriLow : |T| ≤ |T - t| + |t| := by
      calc
        |T| = |(T - t) + t| := by congr 1 <;> ring
        _ ≤ |T - t| + |t| := abs_add_le _ _
    have htriHigh : |T - t| ≤ |T| + |t| := by
      have h := abs_add_le T (-t)
      simpa [sub_eq_add_neg, abs_neg, add_comm] using h
    have hLow : (Real.log X) ^ (45 * a) ≤ |T - t| := by
      linarith only [hSeparationLow, hLocalTime, htAbs, htriLow]
    have htHalf : |t| ≤ (1 / 2) * |T| :=
      htAbs.trans hLocalTime
    have hTscale : (3 / 2) * |T| ≤ 2 * X ^ a := by
      calc
        (3 / 2) * |T| ≤ (3 / 2) * X ^ a := by
          nlinarith only [hTupper]
        _ ≤ 2 * X ^ a := by nlinarith only [hTa]
    have hHigh : |T - t| ≤ 2 * X ^ a := by
      calc
        |T - t| ≤ |T| + |t| := htriHigh
        _ ≤ (3 / 2) * |T| := by linarith only [htHalf]
        _ ≤ 2 * X ^ a := hTscale
    have hXrpow : X ^ (a + 1) = X ^ a * X := by
      rw [Real.rpow_add hXpos, Real.rpow_one]
    have hfinal : 2 * X ^ a ≤ X ^ (a + 1) := by
      calc
        2 * X ^ a ≤ X * X ^ a :=
          mul_le_mul_of_nonneg_right hXtwo hTa
        _ = X ^ a * X := by ring
        _ = X ^ (a + 1) := hXrpow.symm
    exact ⟨hLow, hHigh.trans hfinal⟩

#print axioms selectedMobiusPTWLocalPrefixWindowFacts

end FractionalPrimes.Literature.DirichletMean

end
