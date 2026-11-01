module

public import FractionalPrimes.Literature.Twisted.SelectedComponentMass
public import FractionalPrimes.Literature.Uniformity.ElementaryGrowthPackage

/-!
# Short prefixes and frequency separation

This module formalizes the approved prefix and frequency range statement.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

noncomputable section

def prefixTwistBeta : ℕ := 2 ^ 180 + 1

noncomputable def prefixTwistMassScale : ℝ :=
  (2 : ℝ) ^ 90 * (2 + 22 * Real.log 2) ^ prefixTwistBeta

noncomputable def prefixTwistPowerThreshold (a : ℝ) : ℝ :=
  (2 * prefixTwistMassScale) ^ (1 / (a - (prefixTwistBeta : ℝ)))

noncomputable def prefixTwistAbsorptionThreshold (a eta : ℝ) : ℝ :=
  (2 / ((1 / 8 + eta) / 2)) *
    Real.log (prefixTwistMassScale *
      logAbsorptionM ((1 / 8 + eta) / 2)
        (a + (prefixTwistBeta : ℝ)))

noncomputable def prefixTwistHalfPowerThreshold (eta : ℝ) : ℝ :=
  (2 / (1 / 8 + eta)) * Real.log 2

noncomputable def prefixTwistLogThreshold (a eta : ℝ) : ℝ :=
  max 2 (max (prefixTwistPowerThreshold a)
    (max (prefixTwistAbsorptionThreshold a eta)
      (prefixTwistHalfPowerThreshold eta)))

noncomputable def prefixTwistRangeThreshold (a eta : ℝ) : ℝ :=
  max ((2 : ℝ) ^ 120) (Real.exp (prefixTwistLogThreshold a eta))

private theorem prefixTwist_massScale_ge_one :
    1 ≤ prefixTwistMassScale := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold prefixTwistMassScale
  have hbase : 1 ≤ 2 + 22 * Real.log 2 := by nlinarith
  have hpow : 1 ≤ (2 + 22 * Real.log 2) ^ prefixTwistBeta :=
    one_le_pow₀ hbase
  nlinarith

private theorem selectedComponentK_le_massScale_log_power
    {X : ℝ} (hX : (2 : ℝ) ^ 120 ≤ X)
    (hlog : 2 ≤ Real.log X) :
    selectedComponentK X ≤
      prefixTwistMassScale * (Real.log X) ^ (prefixTwistBeta : ℝ) := by
  have hXpos : 0 < X := by positivity
  have hell0 : 0 ≤ Real.log X := by linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogZ : Real.log ((2 : ℝ) ^ 22 * X) =
      22 * Real.log 2 + Real.log X := by
    rw [Real.log_mul (by positivity) hXpos.ne', Real.log_pow]
    push_cast
    ring
  have hZbound :
      1 + Real.log ((2 : ℝ) ^ 22 * X) ≤
        (2 + 22 * Real.log 2) * Real.log X := by
    rw [hlogZ]
    nlinarith
  have hZ0 : 0 ≤ 1 + Real.log ((2 : ℝ) ^ 22 * X) := by
    rw [hlogZ]
    positivity
  have hpow := pow_le_pow_left₀ hZ0 hZbound prefixTwistBeta
  calc
    selectedComponentK X =
        (2 : ℝ) ^ 90 *
          (1 + Real.log ((2 : ℝ) ^ 22 * X)) ^ prefixTwistBeta := rfl
    _ ≤ (2 : ℝ) ^ 90 *
          ((2 + 22 * Real.log 2) * Real.log X) ^ prefixTwistBeta :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = prefixTwistMassScale * (Real.log X) ^ (prefixTwistBeta : ℝ) := by
      rw [mul_pow]
      simp [prefixTwistMassScale, Real.rpow_natCast]
      ring

private theorem prefixTwistMassConditions_of_large
    {a eta X H : ℝ}
    (ha : (prefixTwistBeta : ℝ) < a) (heta : 0 < eta)
    (hXlarge : prefixTwistRangeThreshold a eta ≤ X)
    (hHlo : X ^ (5 / 8 + eta) ≤ H) :
    selectedComponentK X ≤ (1 / 2) * (Real.log X) ^ a ∧
      selectedComponentK X * Real.sqrt X ≤
        (1 / 2) * H * (Real.log X) ^ (-a) := by
  have hX120 : (2 : ℝ) ^ 120 ≤ X := le_trans (le_max_left _ _) hXlarge
  have hXpos : 0 < X := by positivity
  have hloglarge : prefixTwistLogThreshold a eta ≤ Real.log X := by
    have hexpX : Real.exp (prefixTwistLogThreshold a eta) ≤ X :=
      (le_max_right _ _).trans hXlarge
    have hcmp : Real.exp (prefixTwistLogThreshold a eta) ≤
        Real.exp (Real.log X) := by simpa [Real.exp_log hXpos] using hexpX
    exact Real.exp_le_exp.mp hcmp
  have hloglarge' : max 2 (max (prefixTwistPowerThreshold a)
      (max (prefixTwistAbsorptionThreshold a eta)
        (prefixTwistHalfPowerThreshold eta))) ≤ Real.log X := hloglarge
  have hell : 2 ≤ Real.log X := (le_max_left _ _).trans hloglarge'
  have hlogpos : 0 < Real.log X := by linarith
  have hX1 : 1 ≤ X := by
    have h120 : (1 : ℝ) ≤ 2 ^ 120 := by norm_num
    exact h120.trans hX120
  have hHpos : 0 < H := by
    have hpow : 0 < X ^ (5 / 8 + eta) := Real.rpow_pos_of_pos hXpos _
    exact lt_of_lt_of_le hpow hHlo
  have hKscale := selectedComponentK_le_massScale_log_power hX120 hell
  have hmassScale1 : 1 ≤ prefixTwistMassScale := prefixTwist_massScale_ge_one
  have hM1 : prefixTwistPowerThreshold a ≤ Real.log X := by
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans hloglarge')
  have hdpos : 0 < a - (prefixTwistBeta : ℝ) := sub_pos.mpr ha
  have hpowM1 : 2 * prefixTwistMassScale ≤
      (Real.log X) ^ (a - (prefixTwistBeta : ℝ)) := by
    have hmassScalePos : 0 < prefixTwistMassScale :=
      lt_of_lt_of_le (by norm_num) hmassScale1
    have hpowbase : 0 < 2 * prefixTwistMassScale :=
      mul_pos (by norm_num) hmassScalePos
    have hroot :
        (2 * prefixTwistMassScale) ^
          (1 / (a - (prefixTwistBeta : ℝ))) ≤ Real.log X := by
      exact hM1
    calc
      2 * prefixTwistMassScale =
          ((2 * prefixTwistMassScale) ^
            (1 / (a - (prefixTwistBeta : ℝ)))) ^
              (a - (prefixTwistBeta : ℝ)) := by
        rw [← Real.rpow_mul hpowbase.le]
        have he : (1 / (a - (prefixTwistBeta : ℝ))) *
            (a - (prefixTwistBeta : ℝ)) = 1 := by
          field_simp
        rw [he, Real.rpow_one]
      _ ≤ (Real.log X) ^ (a - (prefixTwistBeta : ℝ)) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hpowbase.le _) hroot hdpos.le
  have hsmallK : selectedComponentK X ≤
      (1 / 2) * (Real.log X) ^ a := by
    have hKcoeff : prefixTwistMassScale ≤
        (1 / 2) * (Real.log X) ^ (a - (prefixTwistBeta : ℝ)) := by
      nlinarith
    calc
      selectedComponentK X ≤ prefixTwistMassScale *
          (Real.log X) ^ (prefixTwistBeta : ℝ) := hKscale
      _ ≤ (1 / 2) * (Real.log X) ^
          (a - (prefixTwistBeta : ℝ)) *
            (Real.log X) ^ (prefixTwistBeta : ℝ) :=
        mul_le_mul_of_nonneg_right hKcoeff
          (Real.rpow_nonneg hlogpos.le _)
      _ = (1 / 2) * (Real.log X) ^ a := by
        have hpow : (Real.log X) ^ (a - (prefixTwistBeta : ℝ)) *
            (Real.log X) ^ (prefixTwistBeta : ℝ) = (Real.log X) ^ a := by
          calc
            _ = (Real.log X) ^
                ((a - (prefixTwistBeta : ℝ)) + (prefixTwistBeta : ℝ)) :=
              (Real.rpow_add hlogpos _ _).symm
            _ = (Real.log X) ^ a := by congr 1 <;> ring
        calc
          _ = (1 / 2) * ((Real.log X) ^
              (a - (prefixTwistBeta : ℝ)) *
                (Real.log X) ^ (prefixTwistBeta : ℝ)) := by ring
          _ = (1 / 2) * (Real.log X) ^ a :=
            congrArg (fun y : ℝ => (1 / 2) * y) hpow
  have hcpos : 0 < (1 / 8 + eta) := by linarith
  have heps : 0 < (1 / 8 + eta) / 2 := by positivity
  have hbabs : 0 ≤ a + (prefixTwistBeta : ℝ) := by
    have hb : 0 ≤ (prefixTwistBeta : ℝ) := by positivity
    linarith
  have hM2 : prefixTwistAbsorptionThreshold a eta ≤ Real.log X := by
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hloglarge'))
  have hlogAbs := log_absorption_bound
    (a := (1 / 8 + eta) / 2) (b := a + (prefixTwistBeta : ℝ))
    (K := prefixTwistMassScale) (X := X)
    heps hbabs hmassScale1 hX1 (by
      change prefixTwistAbsorptionThreshold a eta ≤ Real.log X
      exact hM2)
  have hM3 : prefixTwistHalfPowerThreshold eta ≤ Real.log X := by
    exact (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hloglarge'))
  have hpowTwo : 2 ≤ X ^ ((1 / 8 + eta) / 2) := by
    have hscaled : Real.log 2 ≤
        ((1 / 8 + eta) / 2) * Real.log X := by
      have hmul := mul_le_mul_of_nonneg_left hM3
        (by positivity : 0 ≤ (1 / 8 + eta) / 2)
      dsimp [prefixTwistHalfPowerThreshold] at hmul
      field_simp at hmul ⊢
      nlinarith
    rw [Real.rpow_def_of_pos hXpos]
    calc
      2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log X * ((1 / 8 + eta) / 2)) :=
        Real.exp_le_exp.mpr (by nlinarith [hscaled])
  have hsumExp : (1 / 8 + eta) / 2 + (1 / 8 + eta) / 2 =
      1 / 8 + eta := by ring
  have hpowSquare :
      X ^ ((1 / 8 + eta) / 2) * X ^ ((1 / 8 + eta) / 2) =
        X ^ (1 / 8 + eta) := by
    rw [← Real.rpow_add hXpos, hsumExp]
  have hhalfPower : X ^ ((1 / 8 + eta) / 2) ≤
      (1 / 2) * X ^ (1 / 8 + eta) := by
    have hnonneg : 0 ≤ X ^ ((1 / 8 + eta) / 2) :=
      Real.rpow_nonneg hXpos.le _
    rw [← hpowSquare]
    nlinarith
  have hKell : selectedComponentK X * (Real.log X) ^ a ≤
      prefixTwistMassScale * (Real.log X) ^
        (a + (prefixTwistBeta : ℝ)) := by
    calc
      selectedComponentK X * (Real.log X) ^ a ≤
          prefixTwistMassScale * (Real.log X) ^
            (prefixTwistBeta : ℝ) * (Real.log X) ^ a :=
        mul_le_mul_of_nonneg_right hKscale (Real.rpow_nonneg hlogpos.le _)
      _ = prefixTwistMassScale * (Real.log X) ^
          (a + (prefixTwistBeta : ℝ)) := by
        have hpow : (Real.log X) ^ (prefixTwistBeta : ℝ) *
            (Real.log X) ^ a = (Real.log X) ^
              (a + (prefixTwistBeta : ℝ)) := by
          calc
            _ = (Real.log X) ^
                ((prefixTwistBeta : ℝ) + a) :=
              (Real.rpow_add hlogpos _ _).symm
            _ = (Real.log X) ^ (a + (prefixTwistBeta : ℝ)) := by
              congr 1 <;> ring
        calc
          _ = prefixTwistMassScale *
              ((Real.log X) ^ (prefixTwistBeta : ℝ) * (Real.log X) ^ a) := by ring
          _ = prefixTwistMassScale * (Real.log X) ^
              (a + (prefixTwistBeta : ℝ)) := by rw [hpow]
  have hKpower : selectedComponentK X * (Real.log X) ^ a ≤
      X ^ ((1 / 8 + eta) / 2) := hKell.trans hlogAbs
  have hKhalf : selectedComponentK X * (Real.log X) ^ a ≤
      (1 / 2) * X ^ (1 / 8 + eta) := hKpower.trans hhalfPower
  have hsqrt : Real.sqrt X = X ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow X
  have hsumPower : (1 / 8 + eta) + (1 / 2 : ℝ) = 5 / 8 + eta := by ring
  have hXproduct : X ^ (1 / 8 + eta) * Real.sqrt X =
      X ^ (5 / 8 + eta) := by
    rw [hsqrt]
    calc
      X ^ (1 / 8 + eta) * X ^ (1 / 2 : ℝ) =
          X ^ ((1 / 8 + eta) + (1 / 2 : ℝ)) :=
        (Real.rpow_add hXpos _ _).symm
      _ = X ^ (5 / 8 + eta) := by congr 1
  have hcancel : (Real.log X) ^ a * (Real.log X) ^ (-a) = 1 := by
    calc
      _ = (Real.log X) ^ (a + (-a)) :=
        (Real.rpow_add hlogpos _ _).symm
      _ = 1 := by simp
  have hmassSecond : selectedComponentK X * Real.sqrt X ≤
      (1 / 2) * H * (Real.log X) ^ (-a) := by
    have hfactor : selectedComponentK X * Real.sqrt X =
        (selectedComponentK X * (Real.log X) ^ a) *
          (Real.sqrt X * (Real.log X) ^ (-a)) := by
      calc
        _ = selectedComponentK X * Real.sqrt X * 1 := by ring
        _ = selectedComponentK X * Real.sqrt X *
            ((Real.log X) ^ a * (Real.log X) ^ (-a)) := by rw [hcancel]
        _ = _ := by ring
    calc
      selectedComponentK X * Real.sqrt X = _ := hfactor
      _ ≤ ((1 / 2) * X ^ (1 / 8 + eta)) *
          (Real.sqrt X * (Real.log X) ^ (-a)) :=
        mul_le_mul_of_nonneg_right hKhalf
          (mul_nonneg (Real.sqrt_nonneg X)
            (Real.rpow_nonneg hlogpos.le _))
      _ = (1 / 2) * X ^ (5 / 8 + eta) *
          (Real.log X) ^ (-a) := by
        calc
          _ = ((1 / 2) * (X ^ (1 / 8 + eta) * Real.sqrt X)) *
              (Real.log X) ^ (-a) := by ring
          _ = _ := by rw [hXproduct]
      _ ≤ (1 / 2) * H * (Real.log X) ^ (-a) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hHlo (by norm_num))
          (Real.rpow_nonneg hlogpos.le _)
  exact ⟨hsmallK, hmassSecond⟩

private theorem selectedComponentK_nonneg {X : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) : 0 ≤ selectedComponentK X := by
  have hXpos : 0 < X := by positivity
  have hZ1 : 1 ≤ (2 : ℝ) ^ 22 * X := by nlinarith [hX]
  have hlogZ : 0 ≤ Real.log ((2 : ℝ) ^ 22 * X) := Real.log_nonneg hZ1
  unfold selectedComponentK
  positivity

private theorem selectedComponentShortPrefixBound
    {X H a x h : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (hell : 2 ≤ Real.log X)
    (hHpos : 0 < H)
    (hKsmall : selectedComponentK X ≤ (1 / 2) * (Real.log X) ^ a)
    (hKsqrt : selectedComponentK X * Real.sqrt X ≤
      (1 / 2) * H * (Real.log X) ^ (-a))
    (hprefix : h ≤ H * (Real.log X) ^ (-2 * a))
    (f : ℕ → ℝ) (w : ℕ → ℂ)
    (hmass : (∑ n ∈ selectedPositiveInterval x h,
        ‖(f n : ℂ) * w n‖) ≤
          selectedComponentK X * (h + selectedComponentH0 X)) :
    ‖∑ n ∈ selectedPositiveInterval x h, (f n : ℂ) * w n‖ ≤
      H * (Real.log X) ^ (-a) := by
  have hXpos : 0 < X := by positivity
  have hlogpos : 0 < Real.log X := by linarith
  have hK0 : 0 ≤ selectedComponentK X := selectedComponentK_nonneg hX
  have hh0 : selectedComponentH0 X ≤ Real.sqrt X :=
    selectedComponentH0_le_sqrt hX
  have hnorm : ‖∑ n ∈ selectedPositiveInterval x h, (f n : ℂ) * w n‖ ≤
      ∑ n ∈ selectedPositiveInterval x h, ‖(f n : ℂ) * w n‖ := norm_sum_le _ _
  have hmassBound : selectedComponentK X * (h + selectedComponentH0 X) ≤
      H * (Real.log X) ^ (-a) := by
    have hfirst : selectedComponentK X * h ≤
        selectedComponentK X * (H * (Real.log X) ^ (-2 * a)) :=
      mul_le_mul_of_nonneg_left hprefix hK0
    have hsecond : selectedComponentK X * selectedComponentH0 X ≤
        selectedComponentK X * Real.sqrt X :=
      mul_le_mul_of_nonneg_left hh0 hK0
    have hrpow : (Real.log X) ^ a * (Real.log X) ^ (-2 * a) =
        (Real.log X) ^ (-a) := by
      calc
        _ = (Real.log X) ^ (a + (-2 * a)) :=
          (Real.rpow_add hlogpos _ _).symm
        _ = (Real.log X) ^ (-a) := by congr 1 <;> ring
    have hKfirst : selectedComponentK X *
        (H * (Real.log X) ^ (-2 * a)) ≤
          (1 / 2) * H * (Real.log X) ^ (-a) := by
      calc
        _ ≤ ((1 / 2) * (Real.log X) ^ a) *
            (H * (Real.log X) ^ (-2 * a)) :=
          mul_le_mul_of_nonneg_right hKsmall
            (mul_nonneg hHpos.le (Real.rpow_nonneg hlogpos.le _))
        _ = (1 / 2) * H * (Real.log X) ^ (-a) := by
          calc
            _ = (1 / 2) * H *
                ((Real.log X) ^ a * (Real.log X) ^ (-2 * a)) := by ring
            _ = (1 / 2) * H * (Real.log X) ^ (-a) := by rw [hrpow]
    calc
      selectedComponentK X * (h + selectedComponentH0 X) =
          selectedComponentK X * h +
            selectedComponentK X * selectedComponentH0 X := by ring
      _ ≤ selectedComponentK X *
            (H * (Real.log X) ^ (-2 * a)) +
          selectedComponentK X * Real.sqrt X := add_le_add hfirst hsecond
      _ ≤ (1 / 2) * H * (Real.log X) ^ (-a) +
            (1 / 2) * H * (Real.log X) ^ (-a) :=
        add_le_add hKfirst hKsqrt
      _ = H * (Real.log X) ^ (-a) := by ring
  exact hnorm.trans (hmass.trans hmassBound)

private theorem twistFrequencySeparation
    {X H a h T t : ℝ}
    (hX : (2 : ℝ) ^ 120 ≤ X) (hell : 2 ≤ Real.log X)
    (ha : 1 ≤ a) (hHpos : 0 < H) (hHhi : H ≤ X)
    (hlong : H * (Real.log X) ^ (-2 * a) ≤ h)
    (hTlo : (X / H) * (Real.log X) ^ (50 * a) ≤ |T|)
    (hThi : |T| ≤ X ^ a)
    (ht : |t| ≤ (X / h) * ((Real.log X) ^ (10 * a)) ^ 4) :
    |T - t| ≥ (1 / 2) * |T| ∧
      (1 / 2) * |T| ≥ (Real.log X) ^ (45 * a) ∧
      |T - t| ≤ 2 * X ^ a ∧ 2 * X ^ a ≤ X ^ (a + 1) := by
  have hXpos : 0 < X := by positivity
  have hlogpos : 0 < Real.log X := by linarith
  have hlog1 : 1 ≤ Real.log X := by linarith
  have hHratio : 1 ≤ X / H := (le_div_iff₀ hHpos).2 (by simpa using hHhi)
  have hratioPos : 0 < X / H := by positivity
  have hcutpos : 0 < H * (Real.log X) ^ (-2 * a) := by
    exact mul_pos hHpos (Real.rpow_pos_of_pos hlogpos _)
  have hhpos : 0 < h := lt_of_lt_of_le hcutpos hlong
  have hW4 : ((Real.log X) ^ (10 * a)) ^ 4 =
      (Real.log X) ^ (40 * a) := by
    calc
      ((Real.log X) ^ (10 * a)) ^ 4 =
          (Real.log X) ^ ((10 * a) * 4) :=
        (Real.rpow_mul_natCast hlogpos.le (10 * a) 4).symm
      _ = (Real.log X) ^ (40 * a) := by congr 1 <;> ring
  have hinvCut : 1 / (H * (Real.log X) ^ (-2 * a)) =
      (Real.log X) ^ (2 * a) / H := by
    have hexp : (-2 * a : ℝ) = -(2 * a) := by ring
    rw [hexp, Real.rpow_neg hlogpos.le]
    field_simp
  have hinv : 1 / h ≤ (Real.log X) ^ (2 * a) / H := by
    calc
      1 / h ≤ 1 / (H * (Real.log X) ^ (-2 * a)) :=
        one_div_le_one_div_of_le hcutpos hlong
      _ = (Real.log X) ^ (2 * a) / H := hinvCut
  have hXdiv : X / h ≤ (X / H) * (Real.log X) ^ (2 * a) := by
    calc
      X / h = X * (1 / h) := by ring
      _ ≤ X * ((Real.log X) ^ (2 * a) / H) :=
        mul_le_mul_of_nonneg_left hinv hXpos.le
      _ = (X / H) * (Real.log X) ^ (2 * a) := by ring
  have htimeBase : |t| ≤ (X / H) * (Real.log X) ^ (42 * a) := by
    have htime := ht
    rw [hW4] at htime
    calc
      |t| ≤ (X / h) * (Real.log X) ^ (40 * a) := htime
      _ ≤ ((X / H) * (Real.log X) ^ (2 * a)) *
          (Real.log X) ^ (40 * a) :=
        mul_le_mul_of_nonneg_right hXdiv (Real.rpow_nonneg hlogpos.le _)
      _ = (X / H) * (Real.log X) ^ (42 * a) := by
        calc
          _ = (X / H) *
              ((Real.log X) ^ (2 * a) * (Real.log X) ^ (40 * a)) := by ring
          _ = (X / H) * (Real.log X) ^ (42 * a) := by
            have hpow : (Real.log X) ^ (2 * a) *
                (Real.log X) ^ (40 * a) = (Real.log X) ^ (42 * a) := by
              calc
                _ = (Real.log X) ^ ((2 * a) + (40 * a)) :=
                  (Real.rpow_add hlogpos _ _).symm
                _ = (Real.log X) ^ (42 * a) := by congr 1 <;> ring
            rw [hpow]
  have hpow8 : 2 ≤ (Real.log X) ^ (8 * a) := by
    have hexp : 1 ≤ 8 * a := by nlinarith
    calc
      2 ≤ Real.log X := hell
      _ = (Real.log X) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (Real.log X) ^ (8 * a) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 hexp
  have hpow42to50 : (Real.log X) ^ (42 * a) ≤
      (1 / 2) * (Real.log X) ^ (50 * a) := by
    have hpow : (Real.log X) ^ (42 * a) *
        (Real.log X) ^ (8 * a) = (Real.log X) ^ (50 * a) := by
      calc
        _ = (Real.log X) ^ ((42 * a) + (8 * a)) :=
          (Real.rpow_add hlogpos _ _).symm
        _ = (Real.log X) ^ (50 * a) := by congr 1 <;> ring
    rw [← hpow]
    have hfactor := mul_le_mul_of_nonneg_left hpow8
      (Real.rpow_nonneg hlogpos.le (42 * a))
    nlinarith
  have htsmall : |t| ≤ (1 / 2) * |T| := by
    calc
      |t| ≤ (X / H) * (Real.log X) ^ (42 * a) := htimeBase
      _ ≤ (X / H) * ((1 / 2) * (Real.log X) ^ (50 * a)) :=
        mul_le_mul_of_nonneg_left hpow42to50 hratioPos.le
      _ = (1 / 2) * ((X / H) * (Real.log X) ^ (50 * a)) := by ring
      _ ≤ (1 / 2) * |T| := mul_le_mul_of_nonneg_left hTlo (by norm_num)
  have hpow5 : 2 ≤ (Real.log X) ^ (5 * a) := by
    have hexp : 1 ≤ 5 * a := by nlinarith
    calc
      2 ≤ Real.log X := hell
      _ = (Real.log X) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (Real.log X) ^ (5 * a) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 hexp
  have hpow45to50 : (Real.log X) ^ (45 * a) ≤
      (1 / 2) * (Real.log X) ^ (50 * a) := by
    have hpow : (Real.log X) ^ (45 * a) *
        (Real.log X) ^ (5 * a) = (Real.log X) ^ (50 * a) := by
      calc
        _ = (Real.log X) ^ ((45 * a) + (5 * a)) :=
          (Real.rpow_add hlogpos _ _).symm
        _ = (Real.log X) ^ (50 * a) := by congr 1 <;> ring
    rw [← hpow]
    have hfactor := mul_le_mul_of_nonneg_left hpow5
      (Real.rpow_nonneg hlogpos.le (45 * a))
    nlinarith
  have hTlarge : (Real.log X) ^ (45 * a) ≤ (1 / 2) * |T| := by
    calc
      (Real.log X) ^ (45 * a) ≤ (1 / 2) *
          (Real.log X) ^ (50 * a) := hpow45to50
      _ = 1 * ((1 / 2) * (Real.log X) ^ (50 * a)) := by ring
      _ ≤ (X / H) * ((1 / 2) * (Real.log X) ^ (50 * a)) :=
        mul_le_mul_of_nonneg_right hHratio
          (by positivity : 0 ≤ (1 / 2) * (Real.log X) ^ (50 * a))
      _ = (1 / 2) * ((X / H) * (Real.log X) ^ (50 * a)) := by ring
      _ ≤ (1 / 2) * |T| := mul_le_mul_of_nonneg_left hTlo (by norm_num)
  have htriLo : |T| ≤ |T - t| + |t| := by
    calc
      |T| = |(T - t) + t| := by congr 1 <;> ring
      _ ≤ |T - t| + |t| := abs_add_le _ _
  have htriHi : |T - t| ≤ |T| + |t| := by
    have h := abs_add_le T (-t)
    simpa [sub_eq_add_neg, abs_neg, add_comm] using h
  have hTpos : 0 < X ^ a := Real.rpow_pos_of_pos hXpos a
  have hlowBound : (1 / 2) * |T| ≤ |T - t| := by
    nlinarith
  have hupperBound : |T - t| ≤ 2 * X ^ a := by
    nlinarith
  have hXtwo : 2 ≤ X := by
    have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact hpow.trans hX
  have hXrpow : X ^ (a + 1) = X ^ a * X := by
    rw [Real.rpow_add hXpos, Real.rpow_one]
  have hfinal : 2 * X ^ a ≤ X ^ (a + 1) := by
    calc
      2 * X ^ a ≤ X * X ^ a :=
        mul_le_mul_of_nonneg_right hXtwo (Real.rpow_nonneg hXpos.le a)
      _ = X ^ a * X := by ring
      _ = X ^ (a + 1) := hXrpow.symm
  exact ⟨hlowBound, hTlarge, hupperBound, hfinal⟩

private theorem prefixTwist_X_pos_of_mass_conditions
    {X H a : ℝ} (hell : 2 ≤ Real.log X) (hHhi : H ≤ X)
    (hKsqrt : selectedComponentK X * Real.sqrt X ≤
      (1 / 2) * H * (Real.log X) ^ (-a)) : 0 < X := by
  by_contra hnot
  have hXle : X ≤ 0 := le_of_not_gt hnot
  by_cases hXzero : X = 0
  · have hlogzero : Real.log X = 0 := by rw [hXzero]; simp
    linarith
  · have hXneg : X < 0 := lt_of_le_of_ne hXle hXzero
    have hsqrt : Real.sqrt X = 0 := Real.sqrt_eq_zero_of_nonpos hXle
    have hlogpos : 0 < Real.log X := by linarith
    have hweight : 0 < (Real.log X) ^ (-a) :=
      Real.rpow_pos_of_pos hlogpos _
    have hHnonneg : 0 ≤ H := by
      have h := hKsqrt
      rw [hsqrt] at h
      have hrhs : 0 ≤ (1 / 2) * H * (Real.log X) ^ (-a) := by simpa using h
      have hcoef : 0 < (1 / 2) * (Real.log X) ^ (-a) :=
        mul_pos (by norm_num) hweight
      nlinarith
    exact (not_le_of_gt hXneg) (hHnonneg.trans hHhi)

private theorem selectedComponentK_lower_of_log
    {X : ℝ} (hXpos : 0 < X) (hell : 2 ≤ Real.log X) :
    (2 : ℝ) ^ 90 ≤ selectedComponentK X := by
  have hXgt1 : 1 < X :=
    (Real.log_pos_iff hXpos.le).mp (by linarith)
  have hZ1 : 1 ≤ (2 : ℝ) ^ 22 * X := by
    have hpow : 1 ≤ (2 : ℝ) ^ 22 := by norm_num
    nlinarith
  have hlogZ : 0 ≤ Real.log ((2 : ℝ) ^ 22 * X) := Real.log_nonneg hZ1
  have hbase : 1 ≤ 1 + Real.log ((2 : ℝ) ^ 22 * X) := by linarith
  have hpow : 1 ≤ (1 + Real.log ((2 : ℝ) ^ 22 * X)) ^ prefixTwistBeta :=
    one_le_pow₀ hbase
  calc
    (2 : ℝ) ^ 90 = (2 : ℝ) ^ 90 * 1 := by ring
    _ ≤ (2 : ℝ) ^ 90 *
        (1 + Real.log ((2 : ℝ) ^ 22 * X)) ^ prefixTwistBeta :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = selectedComponentK X := rfl

private theorem prefixTwist_X_ge_component_threshold
    {X H a : ℝ} (hell : 2 ≤ Real.log X) (ha : 1 ≤ a)
    (hHhi : H ≤ X)
    (hKsqrt : selectedComponentK X * Real.sqrt X ≤
      (1 / 2) * H * (Real.log X) ^ (-a)) :
    (2 : ℝ) ^ 120 ≤ X := by
  have hXpos := prefixTwist_X_pos_of_mass_conditions hell hHhi hKsqrt
  have hlogpos : 0 < Real.log X := by linarith
  have hKlo := selectedComponentK_lower_of_log hXpos hell
  have hKpos : 0 < selectedComponentK X := lt_of_lt_of_le (by positivity) hKlo
  have hlog1 : 1 ≤ Real.log X := by linarith
  have hlogpow : 1 ≤ (Real.log X) ^ a :=
    Real.one_le_rpow hlog1 (by linarith)
  have hcancel : (Real.log X) ^ a * (Real.log X) ^ (-a) = 1 := by
    calc
      _ = (Real.log X) ^ (a + (-a)) :=
        (Real.rpow_add hlogpos _ _).symm
      _ = 1 := by simp
  have hcancel' : (Real.log X) ^ (-a) * (Real.log X) ^ a = 1 := by
    rw [mul_comm, hcancel]
  have hmassRight : (1 / 2) * H * (Real.log X) ^ (-a) ≤
      (1 / 2) * X * (Real.log X) ^ (-a) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hHhi (by norm_num))
      (Real.rpow_nonneg hlogpos.le _)
  have hmass : selectedComponentK X * Real.sqrt X ≤
      (1 / 2) * X * (Real.log X) ^ (-a) := hKsqrt.trans hmassRight
  have hmassScaled :
      (selectedComponentK X * Real.sqrt X) *
          (2 * (Real.log X) ^ a) ≤
        ((1 / 2) * X * (Real.log X) ^ (-a)) *
          (2 * (Real.log X) ^ a) :=
    mul_le_mul_of_nonneg_right hmass
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hlogpos.le _))
  have hmassCancel :
      ((1 / 2) * X * (Real.log X) ^ (-a)) *
          (2 * (Real.log X) ^ a) = X := by
    calc
      _ = X * ((Real.log X) ^ (-a) * (Real.log X) ^ a) := by ring
      _ = X := by rw [hcancel']; ring
  have hlargeProduct :
      2 * selectedComponentK X * Real.sqrt X * (Real.log X) ^ a ≤ X := by
    calc
      _ = (selectedComponentK X * Real.sqrt X) *
          (2 * (Real.log X) ^ a) := by ring
      _ ≤ _ := hmassScaled
      _ = X := hmassCancel
  have hcoeff : (2 : ℝ) ^ 91 ≤
      2 * selectedComponentK X * (Real.log X) ^ a := by
    calc
      (2 : ℝ) ^ 91 = 2 * (2 : ℝ) ^ 90 := by norm_num
      _ ≤ 2 * selectedComponentK X :=
        mul_le_mul_of_nonneg_left hKlo (by norm_num)
      _ = (2 * selectedComponentK X) * 1 := by ring
      _ ≤ (2 * selectedComponentK X) * (Real.log X) ^ a :=
        mul_le_mul_of_nonneg_left hlogpow (by positivity)
  have hsqrtPos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
  have hsqrtLarge : (2 : ℝ) ^ 91 * Real.sqrt X ≤ X := by
    calc
      _ ≤ (2 * selectedComponentK X * (Real.log X) ^ a) * Real.sqrt X :=
        mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg X)
      _ = 2 * selectedComponentK X * Real.sqrt X * (Real.log X) ^ a := by ring
      _ ≤ X := hlargeProduct
  have hdiv : (2 : ℝ) ^ 91 ≤ X / Real.sqrt X :=
    (le_div_iff₀ hsqrtPos).2 hsqrtLarge
  have hsqrtSq : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hXpos.le
  have hdivEq : X / Real.sqrt X = Real.sqrt X := by
    have hsq : Real.sqrt X * Real.sqrt X = X := by nlinarith [hsqrtSq]
    calc
      X / Real.sqrt X =
          (Real.sqrt X * Real.sqrt X) / Real.sqrt X := by rw [hsq]
      _ = Real.sqrt X := by field_simp [ne_of_gt hsqrtPos]
  rw [hdivEq] at hdiv
  calc
    (2 : ℝ) ^ 120 ≤ ((2 : ℝ) ^ 91) ^ 2 := by norm_num
    _ ≤ (Real.sqrt X) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg X)
      nlinarith
    _ = X := hsqrtSq

/-- The finite-X conditional clause of `ltw:prefix-twist-range`, under
exactly its two displayed mass assumptions. The component-mass cutoff
`X ≥ 2^120` follows from those assumptions and `H ≤ X`. -/
theorem prefixAndTwistSeparation_of_mass_conditions
    {a eta X H : ℝ}
    (hell : 2 ≤ Real.log X) (ha : 1 ≤ a) (_heta : 0 < eta)
    (hHlo : X ^ (5 / 8 + eta) ≤ H) (hHhi : H ≤ X)
    (hKsmall : selectedComponentK X ≤ (1 / 2) * (Real.log X) ^ a)
    (hKsqrt : selectedComponentK X * Real.sqrt X ≤
      (1 / 2) * H * (Real.log X) ^ (-a)) :
    (∀ ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X),
      ∀ T : ℝ, ∀ q b : ℕ, ∀ u : ℕ → ℂ, (∀ n, ‖u n‖ ≤ 1) →
        ∀ x h : ℝ, 0 ≤ h → h ≤ H * (Real.log X) ^ (-2 * a) →
          ‖∑ n ∈ selectedPositiveInterval x h,
            (mobiusDyadicComponent (dyadicMobiusCutoff X) ν n : ℂ) *
              selectedComponentModulatedWeight T q b u n‖ ≤
                H * (Real.log X) ^ (-a)) ∧
    (∀ ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X),
      ∀ T : ℝ, ∀ q b : ℕ, ∀ u : ℕ → ℂ, (∀ n, ‖u n‖ ≤ 1) →
        ∀ x h : ℝ, 0 ≤ h → h ≤ H * (Real.log X) ^ (-2 * a) →
          ‖∑ n ∈ selectedPositiveInterval x h,
            (vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n : ℂ) *
              selectedComponentModulatedWeight T q b u n‖ ≤
                H * (Real.log X) ^ (-a)) ∧
    (∀ h : ℝ, H * (Real.log X) ^ (-2 * a) ≤ h →
      ∀ T t : ℝ,
        (X / H) * (Real.log X) ^ (50 * a) ≤ |T| →
        |T| ≤ X ^ a →
        |t| ≤ (X / h) * ((Real.log X) ^ (10 * a)) ^ 4 →
          |T - t| ≥ (1 / 2) * |T| ∧
          (1 / 2) * |T| ≥ (Real.log X) ^ (45 * a) ∧
          |T - t| ≤ 2 * X ^ a ∧ 2 * X ^ a ≤ X ^ (a + 1)) := by
  have hXpos := prefixTwist_X_pos_of_mass_conditions hell hHhi hKsqrt
  have hX120 := prefixTwist_X_ge_component_threshold hell ha hHhi hKsqrt
  have hHpos : 0 < H := by
    have hpow : 0 < X ^ (5 / 8 + eta) := Real.rpow_pos_of_pos hXpos _
    exact lt_of_lt_of_le hpow hHlo
  refine ⟨?_, ?_, ?_⟩
  · intro ν hν T q b u hu x h hh hshort
    obtain ⟨hm, _⟩ := selectedComponentLocalMass_modulated
      X hX120 T q b u hu
    exact selectedComponentShortPrefixBound hX120 hell hHpos
      hKsmall hKsqrt hshort
      (fun n => mobiusDyadicComponent (dyadicMobiusCutoff X) ν n)
      (selectedComponentModulatedWeight T q b u)
      (hm ν hν x h hh)
  · intro ν hν T q b u hu x h hh hshort
    obtain ⟨_, hv⟩ := selectedComponentLocalMass_modulated
      X hX120 T q b u hu
    exact selectedComponentShortPrefixBound hX120 hell hHpos
      hKsmall hKsqrt hshort
      (fun n => vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n)
      (selectedComponentModulatedWeight T q b u)
      (hv ν hν x h hh)
  · intro h hlong T t hTlo hThi ht
    exact twistFrequencySeparation hX120 hell ha hHpos hHhi
      hlong hTlo hThi ht

/-- The eventual clause of `ltw:prefix-twist-range`, obtained by combining
the finite-X conditional theorem with the two explicit mass thresholds. -/
theorem prefixAndTwistSeparation
    {a eta X H : ℝ}
    (ha : (prefixTwistBeta : ℝ) < a) (heta : 0 < eta)
    (hXlarge : prefixTwistRangeThreshold a eta ≤ X)
    (hHlo : X ^ (5 / 8 + eta) ≤ H) (hHhi : H ≤ X) :
    selectedComponentK X ≤ (1 / 2) * (Real.log X) ^ a ∧
    selectedComponentK X * Real.sqrt X ≤
      (1 / 2) * H * (Real.log X) ^ (-a) ∧
    (∀ ν ∈ mobiusDyadicLabels X (dyadicMobiusCutoff X),
      ∀ T : ℝ, ∀ q b : ℕ, ∀ u : ℕ → ℂ, (∀ n, ‖u n‖ ≤ 1) →
        ∀ x h : ℝ, 0 ≤ h → h ≤ H * (Real.log X) ^ (-2 * a) →
          ‖∑ n ∈ selectedPositiveInterval x h,
            (mobiusDyadicComponent (dyadicMobiusCutoff X) ν n : ℂ) *
              selectedComponentModulatedWeight T q b u n‖ ≤
                H * (Real.log X) ^ (-a)) ∧
    (∀ ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X),
      ∀ T : ℝ, ∀ q b : ℕ, ∀ u : ℕ → ℂ, (∀ n, ‖u n‖ ≤ 1) →
        ∀ x h : ℝ, 0 ≤ h → h ≤ H * (Real.log X) ^ (-2 * a) →
          ‖∑ n ∈ selectedPositiveInterval x h,
            (vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n : ℂ) *
              selectedComponentModulatedWeight T q b u n‖ ≤
                H * (Real.log X) ^ (-a)) ∧
    (∀ h : ℝ, H * (Real.log X) ^ (-2 * a) ≤ h →
      ∀ T t : ℝ,
        (X / H) * (Real.log X) ^ (50 * a) ≤ |T| →
        |T| ≤ X ^ a →
        |t| ≤ (X / h) * ((Real.log X) ^ (10 * a)) ^ 4 →
          |T - t| ≥ (1 / 2) * |T| ∧
          (1 / 2) * |T| ≥ (Real.log X) ^ (45 * a) ∧
          |T - t| ≤ 2 * X ^ a ∧ 2 * X ^ a ≤ X ^ (a + 1)) := by
  have hX120 : (2 : ℝ) ^ 120 ≤ X := le_trans (le_max_left _ _) hXlarge
  have hXpos : 0 < X := by positivity
  have hell : 2 ≤ Real.log X := by
    have hloglarge : prefixTwistLogThreshold a eta ≤ Real.log X := by
      have hexpX : Real.exp (prefixTwistLogThreshold a eta) ≤ X :=
        (le_max_right _ _).trans hXlarge
      have hcmp : Real.exp (prefixTwistLogThreshold a eta) ≤
          Real.exp (Real.log X) := by simpa [Real.exp_log hXpos] using hexpX
      exact Real.exp_le_exp.mp hcmp
    have hloglarge' : max 2 (max (prefixTwistPowerThreshold a)
        (max (prefixTwistAbsorptionThreshold a eta)
          (prefixTwistHalfPowerThreshold eta))) ≤ Real.log X := hloglarge
    exact (le_max_left _ _).trans hloglarge'
  have ha1 : 1 ≤ a := by
    have hb : (1 : ℝ) ≤ (prefixTwistBeta : ℝ) := by
      norm_num [prefixTwistBeta]
    linarith
  have hmass := prefixTwistMassConditions_of_large
    ha heta hXlarge hHlo
  exact ⟨hmass.1, hmass.2,
    prefixAndTwistSeparation_of_mass_conditions
      hell ha1 heta hHlo hHhi hmass.1 hmass.2⟩

end

end FractionalPrimes.Literature.Twisted

#print axioms FractionalPrimes.Literature.Twisted.prefixAndTwistSeparation
#print axioms FractionalPrimes.Literature.Twisted.prefixAndTwistSeparation_of_mass_conditions
