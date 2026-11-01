module

public import FractionalPrimes.ArithmeticBasicsCore
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section
namespace FractionalPrimes
open Filter
open scoped Topology
noncomputable section

/-- The explicit slow scales in `er:mobius-dense`, including t₀=1. -/
def mobiusSlowScale (k : ℕ) : ℕ := Nat.floor ((2 : ℝ) ^ Real.sqrt (k : ℝ))

theorem mobiusSlowScale_zero : mobiusSlowScale 0 = 1 := by
  simp [mobiusSlowScale]

theorem mobiusSlowScale_pos (k : ℕ) : 0 < mobiusSlowScale k := by
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow (by norm_num) (Real.sqrt_nonneg _)

/-- The source logarithmic scale comparison, with the lower estimate stated
for the tail `k ≥ 4` where `sqrt k ≥ 2`. -/
theorem mobiusSlowScale_log_bounds {k : ℕ} (hk : 4 ≤ k) :
    (Real.log 2 / 2) * Real.sqrt (k : ℝ) ≤
        Real.log (mobiusSlowScale k : ℝ) ∧
      Real.log (mobiusSlowScale k : ℝ) ≤
        Real.log 2 * Real.sqrt (k : ℝ) := by
  have hpowOne : 1 ≤ (2 : ℝ) ^ Real.sqrt (k : ℝ) :=
    Real.one_le_rpow (by norm_num) (Real.sqrt_nonneg _)
  have hfloorLower : (2 : ℝ) ^ Real.sqrt (k : ℝ) / 2 ≤
      (mobiusSlowScale k : ℝ) := by
    simpa [mobiusSlowScale] using
      natFloor_half_le_of_one_le hpowOne
  have hfloorUpper : (mobiusSlowScale k : ℝ) ≤
      (2 : ℝ) ^ Real.sqrt (k : ℝ) := by
    simpa [mobiusSlowScale] using
      Nat.floor_le (show 0 ≤ (2 : ℝ) ^ Real.sqrt (k : ℝ) by positivity)
  have hfloorPos : 0 < (mobiusSlowScale k : ℝ) := by
    exact_mod_cast mobiusSlowScale_pos k
  have hhalfPos : 0 < (2 : ℝ) ^ Real.sqrt (k : ℝ) / 2 := by
    positivity
  have hlogLow := Real.log_le_log hhalfPos hfloorLower
  have hlogHigh := Real.log_le_log hfloorPos hfloorUpper
  have hlogHalf : Real.log ((2 : ℝ) ^ Real.sqrt (k : ℝ) / 2) =
      (Real.sqrt (k : ℝ) - 1) * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num),
      Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    ring
  have hlogPow : Real.log ((2 : ℝ) ^ Real.sqrt (k : ℝ)) =
      Real.log 2 * Real.sqrt (k : ℝ) := by
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    ring
  have hkreal : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hroot : 2 ≤ Real.sqrt (k : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · rw [hlogHalf] at hlogLow
    nlinarith
  · rw [hlogPow] at hlogHigh
    nlinarith

theorem mobiusSlowScale_monotone : Monotone mobiusSlowScale := by
  intro k l hkl
  apply Nat.floor_mono
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  exact Real.sqrt_le_sqrt (by exact_mod_cast hkl)

theorem tendsto_mobiusSlowScale : Tendsto mobiusSlowScale atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))

theorem tendsto_sqrt_nat_succ_sub :
    Tendsto (fun k : ℕ => Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ))
      atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun k : ℕ => Real.sqrt (k : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun k : ℕ =>
      Real.sqrt ((k + 1 : ℕ) : ℝ) + Real.sqrt (k : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun k => le_add_of_nonneg_left (Real.sqrt_nonneg _)) hsqrt
  have hi := tendsto_inv_atTop_zero.comp hsum
  apply hi.congr'
  exact Eventually.of_forall fun k => by
    dsimp only [Function.comp_apply]
    have hpos : (0 : ℝ) < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hnonneg := Real.sqrt_nonneg (k : ℝ)
    have hsq₁ := Real.sq_sqrt (show (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by positivity)
    have hsq₀ := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) by positivity)
    have hden : Real.sqrt ((k + 1 : ℕ) : ℝ) + Real.sqrt (k : ℝ) ≠ 0 := by positivity
    push_cast at hsq₁
    field_simp [hden]
    push_cast
    nlinarith only [hsq₁, hsq₀]

theorem mobiusSlowScale_relativeGap_tendsto_zero :
    Tendsto (fun k : ℕ =>
      ((mobiusSlowScale (k + 1) : ℝ) - mobiusSlowScale k) / mobiusSlowScale k)
      atTop (𝓝 0) := by
  let u : ℕ → ℝ := fun k => (2 : ℝ) ^ Real.sqrt (k : ℝ)
  have hu : Tendsto u atTop atTop :=
    (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hfloor : Tendsto (fun k : ℕ => (mobiusSlowScale k : ℝ) / u k) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hu
  have hfloorSucc := (tendsto_add_atTop_iff_nat 1).mpr hfloor
  have hratio : Tendsto (fun k : ℕ => u (k + 1) / u k) atTop (𝓝 1) := by
    have hpow : Tendsto (fun k : ℕ =>
        (2 : ℝ) ^ (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)))
        atTop (𝓝 1) := by
      change Tendsto
        ((fun x : ℝ => (2 : ℝ) ^ x) ∘
          (fun k : ℕ =>
            Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)))
        atTop (𝓝 1)
      simpa only [Real.rpow_zero] using (Real.continuous_const_rpow
        (by norm_num : (2 : ℝ) ≠ 0)).continuousAt.tendsto.comp
          tendsto_sqrt_nat_succ_sub
    apply hpow.congr'
    exact Eventually.of_forall fun k => by
      dsimp [u]
      exact Real.rpow_sub (by norm_num : (0 : ℝ) < 2) _ _
  have hrounded := (hfloorSucc.mul hratio).div hfloor (by norm_num : (1 : ℝ) ≠ 0)
  simp only [one_mul, div_one] at hrounded
  have hr : Tendsto (fun k : ℕ =>
      (mobiusSlowScale (k + 1) : ℝ) / mobiusSlowScale k) atTop (𝓝 1) := by
    apply hrounded.congr'
    exact Eventually.of_forall fun k => by
      dsimp only [Function.comp_apply, Pi.div_apply, Pi.mul_apply]
      have hu₀ : u k ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
      have hu₁ : u (k + 1) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
      have ht : (mobiusSlowScale k : ℝ) ≠ 0 := by exact_mod_cast (mobiusSlowScale_pos k).ne'
      field_simp [hu₀, hu₁, ht]
  have hz := hr.sub_const 1
  simp only [sub_self] at hz
  apply hz.congr'
  exact Eventually.of_forall fun k => by
    have ht : (mobiusSlowScale k : ℝ) ≠ 0 := by exact_mod_cast (mobiusSlowScale_pos k).ne'
    field_simp

#print axioms mobiusSlowScale_relativeGap_tendsto_zero
end
end FractionalPrimes
