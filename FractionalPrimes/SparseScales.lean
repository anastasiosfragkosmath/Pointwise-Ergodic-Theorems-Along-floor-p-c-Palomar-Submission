module

public import FractionalPrimes.Core
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Basic

/-!
# Sparse scales from the blueprint

This file formalizes the scale sequence used in the logarithmic perturbation
argument.  The summability estimates for the block errors are recorded in
subsequent lemmas; this first checkpoint proves the exact sequence's basic
growth and logarithmic comparison properties.
-/

public section

namespace FractionalPrimes

open scoped ENNReal

noncomputable section

/-- The exponent `q = min(p, 2)` in the sparse-scale construction. -/
@[expose] def sparseScaleQ (p : ℝ) : ℝ := min p 2

/-- Public equation for the mixed-norm exponent. -/
theorem sparseScaleQ_eq_min (p : ℝ) : sparseScaleQ p = min p 2 := rfl

/-- The conjugate exponent `q' = q / (q - 1)` used in the blueprint. -/
def sparseScaleQPrime (p : ℝ) : ℝ := sparseScaleQ p / (sparseScaleQ p - 1)

/-- The sparse-scale exponent `τ = 1 / (100 q')`. -/
def sparseScaleTau (p : ℝ) : ℝ := 1 / (100 * sparseScaleQPrime p)

/-- The real number whose natural floor gives the `k`th sparse scale. -/
def sparseScaleReal (p : ℝ) (k : ℕ) : ℝ :=
  Real.rpow 2 (Real.rpow (k : ℝ) (sparseScaleTau p))

/-- The sparse sequence `s_k = floor(2^(k^τ))` from the blueprint. -/
def sparseScale (p : ℝ) (k : ℕ) : ℕ := ⌊sparseScaleReal p k⌋₊

theorem sparseScaleQ_gt_one {p : ℝ} (hp : 1 < p) : 1 < sparseScaleQ p := by
  exact lt_min hp (by norm_num)

theorem sparseScaleTau_eq_on_domain {p : ℝ} (hp : 1 < p) :
    sparseScaleTau p = (sparseScaleQ p - 1) / (100 * sparseScaleQ p) := by
  unfold sparseScaleTau sparseScaleQPrime
  have hq0 : sparseScaleQ p ≠ 0 := ne_of_gt (lt_trans zero_lt_one (sparseScaleQ_gt_one hp))
  have hq1 : sparseScaleQ p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (sparseScaleQ_gt_one hp))
  field_simp

theorem sparseScaleTau_pos {p : ℝ} (hp : 1 < p) : 0 < sparseScaleTau p := by
  rw [sparseScaleTau_eq_on_domain hp]
  exact div_pos (sub_pos.mpr (sparseScaleQ_gt_one hp))
    (mul_pos (by norm_num) (lt_trans zero_lt_one (sparseScaleQ_gt_one hp)))

theorem sparseScaleTau_lt_one {p : ℝ} (hp : 1 < p) : sparseScaleTau p < 1 := by
  rw [sparseScaleTau_eq_on_domain hp]
  have hq := sparseScaleQ_gt_one hp
  have hq0 : 0 < sparseScaleQ p := lt_trans zero_lt_one hq
  apply (div_lt_one (mul_pos (by norm_num : (0 : ℝ) < 100) hq0)).2
  nlinarith

theorem sparseScaleReal_nonneg (p : ℝ) (k : ℕ) : 0 ≤ sparseScaleReal p k := by
  exact Real.rpow_nonneg (by norm_num) _

theorem sparseScale_monotone {p : ℝ} (hp : 1 < p) : Monotone (sparseScale p) := by
  intro k l hkl
  apply Nat.floor_mono
  unfold sparseScaleReal
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact Real.rpow_le_rpow (Nat.cast_nonneg k) (Nat.cast_le.mpr hkl)
    (le_of_lt (sparseScaleTau_pos hp))

theorem sparseScale_zero {p : ℝ} (hp : 1 < p) : sparseScale p 0 = 1 := by
  simp [sparseScale, sparseScaleReal,
    Real.zero_rpow (ne_of_gt (sparseScaleTau_pos hp))]

theorem sparseScaleReal_tendsto_atTop {p : ℝ} (hp : 1 < p) :
    Filter.Tendsto (sparseScaleReal p) (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ) := by
  have hpow : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ sparseScaleTau p)
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ) :=
    (tendsto_rpow_atTop (sparseScaleTau_pos hp)).comp
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto Nat.cast (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ))
  have hmul : Filter.Tendsto (fun k : ℕ => Real.log 2 * (k : ℝ) ^ sparseScaleTau p)
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ) :=
    hpow.const_mul_atTop (Real.log_pos (by norm_num))
  have hexp := Real.tendsto_exp_atTop.comp hmul
  apply hexp.congr' (Filter.Eventually.of_forall ?_)
  intro k
  simp [sparseScaleReal, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem sparseScale_tendsto_atTop {p : ℝ} (hp : 1 < p) :
    Filter.Tendsto (sparseScale p) (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℕ) := by
  change Filter.Tendsto (fun k : ℕ => ⌊sparseScaleReal p k⌋₊)
    (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℕ)
  exact tendsto_nat_floor_atTop.comp (sparseScaleReal_tendsto_atTop hp)

/-- The elementary floor lower bound used for the logarithmic scale estimate. -/
theorem floor_two_rpow_half_le {x : ℝ} (hx : 1 ≤ x) :
    Real.rpow 2 (x / 2) ≤ (⌊Real.rpow 2 x⌋₊ : ℝ) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hbase : 0 ≤ Real.rpow 2 x := Real.rpow_nonneg (by norm_num) _
  by_cases hx2 : x < 2
  · have htwo : (2 : ℝ) ≤ Real.rpow 2 x := by
      calc
        (2 : ℝ) = Real.rpow 2 1 := by norm_num
        _ ≤ Real.rpow 2 x := Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
    have hfloor : 2 ≤ ⌊Real.rpow 2 x⌋₊ := Nat.le_floor htwo
    have hhalf : Real.rpow 2 (x / 2) ≤ 2 := by
      have h_exp : x / 2 ≤ 1 := by linarith
      calc
        Real.rpow 2 (x / 2) ≤ Real.rpow 2 1 :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h_exp
        _ = 2 := by norm_num
    exact le_trans hhalf (by exact_mod_cast hfloor)
  · have hx2' : 2 ≤ x := le_of_not_gt hx2
    have hA : 1 ≤ Real.rpow 2 (x / 2) :=
      Real.one_le_rpow (by norm_num) (by linarith)
    have hdouble : 2 * Real.rpow 2 (x / 2) ≤ Real.rpow 2 x := by
      have hexp : x / 2 + 1 ≤ x := by linarith
      calc
        2 * Real.rpow 2 (x / 2) = Real.rpow 2 1 * Real.rpow 2 (x / 2) := by norm_num
        _ = Real.rpow 2 (1 + x / 2) :=
          (Real.rpow_add (by norm_num) 1 (x / 2)).symm
        _ = Real.rpow 2 (x / 2 + 1) := by congr 1; ring
        _ ≤ Real.rpow 2 x :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hsub : Real.rpow 2 (x / 2) ≤ Real.rpow 2 x - 1 := by nlinarith
    have hfloor : Real.rpow 2 x - 1 < (⌊Real.rpow 2 x⌋₊ : ℝ) :=
      Nat.sub_one_lt_floor (Real.rpow 2 x)
    linarith

theorem sparseScale_log_bounds {p : ℝ} (hp : 1 < p) {k : ℕ} (hk : 1 ≤ k) :
    (Real.log 2 / 2) * Real.rpow (k : ℝ) (sparseScaleTau p) ≤
        Real.log (sparseScale p k) ∧
      Real.log (sparseScale p k) ≤ Real.log 2 * Real.rpow (k : ℝ) (sparseScaleTau p) := by
  let x := Real.rpow (k : ℝ) (sparseScaleTau p)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow (by exact_mod_cast hk) (le_of_lt (sparseScaleTau_pos hp))
  have hfloorlo := floor_two_rpow_half_le hx
  have hfloorhi : (sparseScale p k : ℝ) ≤ Real.rpow 2 x :=
    Nat.floor_le (Real.rpow_nonneg (by norm_num) x)
  have hspos : 0 < sparseScale p k := by
    exact Nat.floor_pos.mpr (by
      calc
        (1 : ℝ) ≤ Real.rpow 2 x := Real.one_le_rpow (by norm_num) (le_trans (by norm_num) hx)
    )
  have hpowpos : 0 < Real.rpow 2 (x / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hscale_pos : (0 : ℝ) < sparseScale p k := Nat.cast_pos.mpr hspos
  constructor
  · have hlog := Real.log_le_log hpowpos hfloorlo
    have hlogpow : Real.log (Real.rpow 2 (x / 2)) = (x / 2) * Real.log 2 :=
      Real.log_rpow (by norm_num) _
    rw [hlogpow] at hlog
    have hlog' : (x / 2) * Real.log 2 ≤ Real.log (sparseScale p k) := by
      simpa [sparseScale, sparseScaleReal, x] using hlog
    calc
      (Real.log 2 / 2) * Real.rpow (k : ℝ) (sparseScaleTau p) =
          (x / 2) * Real.log 2 := by dsimp [x]; ring
      _ ≤ Real.log (sparseScale p k) := hlog'
  · have hlog := Real.log_le_log hscale_pos hfloorhi
    have hlogpow : Real.log (Real.rpow 2 x) = x * Real.log 2 :=
      Real.log_rpow (by norm_num) _
    rw [hlogpow] at hlog
    simpa [sparseScale, x, mul_comm] using hlog

/-- Concavity controls the increment of the inner power in the scale sequence. -/
theorem sparseScale_inner_increment_le {p : ℝ} (hp : 1 < p) {k : ℕ}
    (hk : 1 ≤ k) :
    Real.rpow ((k + 1 : ℕ) : ℝ) (sparseScaleTau p) -
        Real.rpow (k : ℝ) (sparseScaleTau p) ≤
      sparseScaleTau p * Real.rpow (k : ℝ) (sparseScaleTau p - 1) := by
  have hτ0 : 0 ≤ sparseScaleTau p := le_of_lt (sparseScaleTau_pos hp)
  have hτ1 : sparseScaleTau p ≤ 1 := (sparseScaleTau_lt_one hp).le
  have hconc := Real.concaveOn_rpow hτ0 hτ1
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hk0 : (k : ℝ) ∈ Set.Ici (0 : ℝ) := le_of_lt hkpos
  have hk1 : ((k + 1 : ℕ) : ℝ) ∈ Set.Ici (0 : ℝ) := by
    simp only [Set.mem_Ici]
    positivity
  have hstep : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hderiv := Real.hasDerivAt_rpow_const
    (x := (k : ℝ)) (p := sparseScaleTau p) (Or.inl hkpos.ne')
  have hslope := hconc.slope_le_of_hasDerivAt hk0 hk1 hstep hderiv
  have hgap : ((k + 1 : ℕ) : ℝ) - (k : ℝ) = 1 := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  simpa [slope, hgap, Nat.cast_add, Nat.cast_one] using hslope

/-- A secant increment bound for exponentials on a positive ray. -/
theorem exp_linear_increment_le {c x y : ℝ} (hxy : x ≤ y) :
    Real.exp (c * y) - Real.exp (c * x) ≤
      (y - x) * c * Real.exp (c * y) := by
  by_cases heq : x = y
  · subst y
    simp
  · have hxylt : x < y := lt_of_le_of_ne hxy heq
    have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => Real.exp (c * t)) := by
      convert convexOn_exp.comp_linearMap (LinearMap.mulRight ℝ c) using 1 <;>
        ext t <;> simp [LinearMap.mulRight_apply, mul_comm]
    have hderiv : HasDerivAt (fun t : ℝ => Real.exp (c * t))
        (Real.exp (c * y) * c) y := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_exp (c * y)).comp y (hasDerivAt_const_mul c)
    have hslope := hconv.slope_le_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y)
      hxylt hderiv
    have hdiv :
        (Real.exp (c * y) - Real.exp (c * x)) / (y - x) ≤
          Real.exp (c * y) * c := by
      simpa [slope, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hslope
    have hyx : 0 < y - x := sub_pos.mpr hxylt
    have hmul := (div_le_iff₀ hyx).mp hdiv
    nlinarith [hmul]

/-- The floor in `s_k` loses at most a factor of two when `k ≥ 1`. -/
theorem sparseScale_floor_half {p : ℝ} (hp : 1 < p) {k : ℕ} (hk : 1 ≤ k) :
    Real.rpow 2 (Real.rpow (k : ℝ) (sparseScaleTau p)) / 2 ≤
      (sparseScale p k : ℝ) := by
  let x := Real.rpow (k : ℝ) (sparseScaleTau p)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow (by exact_mod_cast hk)
      (le_of_lt (sparseScaleTau_pos hp))
  have ha : 2 ≤ Real.rpow 2 x := by
    calc
      (2 : ℝ) = Real.rpow 2 1 := by norm_num
      _ ≤ Real.rpow 2 x := Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
  have hfloor : Real.rpow 2 x - 1 < (⌊Real.rpow 2 x⌋₊ : ℝ) :=
    Nat.sub_one_lt_floor (Real.rpow 2 x)
  have hhalf : Real.rpow 2 x / 2 ≤ Real.rpow 2 x - 1 := by linarith
  change Real.rpow 2 x / 2 ≤ (⌊Real.rpow 2 x⌋₊ : ℝ)
  exact hhalf.trans hfloor.le

/-- Relative growth of consecutive sparse scales, including the floor error. -/
theorem sparseScale_relative_step_bound {p : ℝ} (hp : 1 < p) {k : ℕ}
    (hk : 1 ≤ k) :
    (((sparseScale p (k + 1) - sparseScale p k : ℕ) : ℝ) /
        (sparseScale p k : ℝ)) ≤
      4 * Real.log 2 * sparseScaleTau p *
          Real.rpow (k : ℝ) (sparseScaleTau p - 1) +
        2 / Real.rpow 2 (Real.rpow (k : ℝ) (sparseScaleTau p)) := by
  let a : ℝ := Real.rpow (k : ℝ) (sparseScaleTau p)
  let b : ℝ := Real.rpow ((k + 1 : ℕ) : ℝ) (sparseScaleTau p)
  let y : ℝ := Real.rpow 2 a
  let z : ℝ := Real.rpow 2 b
  let d : ℝ := b - a
  let t : ℝ := sparseScaleTau p * Real.rpow (k : ℝ) (sparseScaleTau p - 1)
  have hτpos : 0 < sparseScaleTau p := sparseScaleTau_pos hp
  have hτlt : sparseScaleTau p < 1 := sparseScaleTau_lt_one hp
  have hkreal : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpow : Real.rpow (k : ℝ) (sparseScaleTau p - 1) ≤ 1 := by
    calc
      Real.rpow (k : ℝ) (sparseScaleTau p - 1) ≤ Real.rpow (k : ℝ) 0 :=
        Real.rpow_le_rpow_of_exponent_le hkreal (by linarith)
      _ = 1 := Real.rpow_zero _
  have ht_nonneg : 0 ≤ t := mul_nonneg hτpos.le (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have ht_le_tau : t ≤ sparseScaleTau p := by
    simpa [t] using mul_le_mul_of_nonneg_left hkpow hτpos.le
  have hinner_mono : a ≤ b := by
    dsimp [a, b]
    exact Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast (Nat.le_succ k)) hτpos.le
  have hdelta : d ≤ t := by
    dsimp [d, a, b, t]
    exact sparseScale_inner_increment_le hp hk
  have hd_nonneg : 0 ≤ d := by dsimp [d]; linarith [hinner_mono]
  have hd_le_one : d ≤ 1 := by
    dsimp [d]
    linarith [hdelta, ht_le_tau, sparseScaleTau_lt_one hp]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hypos : 0 < y := by dsimp [y]; positivity
  have hz_le : z ≤ 2 * y := by
    change (2 : ℝ) ^ b ≤ 2 * (2 : ℝ) ^ a
    calc
      (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (a + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by dsimp [d] at hd_le_one; linarith)
      _ = (2 : ℝ) ^ (1 + a) := by congr 1; ring
      _ = (2 : ℝ) ^ 1 * (2 : ℝ) ^ a :=
        Real.rpow_add (x := (2 : ℝ)) (by norm_num) 1 a
      _ = (2 : ℝ) ^ a * 2 := by norm_num [mul_comm]
      _ = 2 * (2 : ℝ) ^ a := by ring
  have houter : z - y ≤ d * Real.log 2 * z := by
    change (2 : ℝ) ^ b - (2 : ℝ) ^ a ≤
      (b - a) * Real.log 2 * (2 : ℝ) ^ b
    rw [Real.rpow_def_of_pos (x := (2 : ℝ)) (by norm_num) b,
      Real.rpow_def_of_pos (x := (2 : ℝ)) (by norm_num) a]
    exact exp_linear_increment_le hinner_mono
  have houter_bound : z - y ≤ 2 * d * Real.log 2 * y := by
    calc
      z - y ≤ d * Real.log 2 * z := houter
      _ ≤ d * Real.log 2 * (2 * y) :=
        mul_le_mul_of_nonneg_left hz_le (mul_nonneg hd_nonneg hlog2.le)
      _ = 2 * d * Real.log 2 * y := by ring
  have hsle : sparseScale p k ≤ sparseScale p (k + 1) :=
    sparseScale_monotone hp (Nat.le_succ k)
  have hcast_sub :
      ((sparseScale p (k + 1) - sparseScale p k : ℕ) : ℝ) =
        (sparseScale p (k + 1) : ℝ) - (sparseScale p k : ℝ) := by
    rw [Nat.cast_sub hsle]
  have hfloor_next : (sparseScale p (k + 1) : ℝ) ≤ z := by
    dsimp [z, b]
    exact Nat.floor_le (sparseScaleReal_nonneg p (k + 1))
  have hfloor_cur : y - 1 < (sparseScale p k : ℝ) := by
    dsimp [y, a, sparseScale, sparseScaleReal]
    exact Nat.sub_one_lt_floor _
  have hfloor_diff :
      ((sparseScale p (k + 1) - sparseScale p k : ℕ) : ℝ) ≤ z - y + 1 := by
    rw [hcast_sub]
    linarith
  have hfloorhalf : y / 2 ≤ (sparseScale p k : ℝ) := by
    dsimp [y, a]
    exact sparseScale_floor_half hp hk
  have hcurpos : 0 < (sparseScale p k : ℝ) := by
    have : 0 < Real.rpow 2 a := by dsimp [a]; positivity
    have hle : 0 < Real.rpow 2 a / 2 := by positivity
    exact lt_of_lt_of_le hle hfloorhalf
  have hprod_step : 2 * d * Real.log 2 * y ≤
      (sparseScale p k : ℝ) *
        (4 * Real.log 2 * sparseScaleTau p * Real.rpow (k : ℝ)
          (sparseScaleTau p - 1)) := by
    have hleft := mul_le_mul_of_nonneg_right hdelta
      (show 0 ≤ 2 * Real.log 2 * y by positivity)
    have hright := mul_le_mul_of_nonneg_right hfloorhalf
      (show 0 ≤ 4 * Real.log 2 * t by positivity)
    calc
      2 * d * Real.log 2 * y = d * (2 * Real.log 2 * y) := by ring
      _ ≤ t * (2 * Real.log 2 * y) := hleft
      _ = y / 2 * (4 * Real.log 2 * t) := by ring
      _ ≤ (sparseScale p k : ℝ) * (4 * Real.log 2 * t) := hright
      _ = (sparseScale p k : ℝ) *
          (4 * Real.log 2 * sparseScaleTau p *
            Real.rpow (k : ℝ) (sparseScaleTau p - 1)) := by dsimp [t]; ring
  have hprod_floor : 1 ≤ (sparseScale p k : ℝ) * (2 / y) := by
    have hmul := mul_le_mul_of_nonneg_right hfloorhalf (show 0 ≤ 2 / y by positivity)
    have hyne : y ≠ 0 := ne_of_gt hypos
    have hcalc : y / 2 * (2 / y) = 1 := by field_simp [hyne]
    rw [hcalc] at hmul
    exact hmul
  have hbound_product :
      ((sparseScale p (k + 1) - sparseScale p k : ℕ) : ℝ) ≤
        (sparseScale p k : ℝ) *
          (4 * Real.log 2 * sparseScaleTau p * Real.rpow (k : ℝ)
              (sparseScaleTau p - 1) + 2 / y) := by
    calc
      ((sparseScale p (k + 1) - sparseScale p k : ℕ) : ℝ) ≤ z - y + 1 := hfloor_diff
      _ ≤ 2 * d * Real.log 2 * y + 1 := by linarith [houter_bound]
      _ ≤ _ := by
        have := add_le_add hprod_step hprod_floor
        nlinarith
  have hbound_product' :
      ((sparseScale p (k + 1) - sparseScale p k : ℕ) : ℝ) ≤
        (4 * Real.log 2 * sparseScaleTau p *
            Real.rpow (k : ℝ) (sparseScaleTau p - 1) + 2 / y) *
          (sparseScale p k : ℝ) := by
    simpa [mul_comm] using hbound_product
  have hratio := (div_le_iff₀ hcurpos).2 hbound_product'
  simpa [a, y] using hratio

/-- The finite logarithmic block error from the blueprint. -/
def sparseScaleBlockError (p : ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico (sparseScale p k) (sparseScale p (k + 1)),
    Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1)

private theorem sparseScaleBlockError_eq_sum_private (p : ℝ) (k : ℕ) :
    sparseScaleBlockError p k =
      ∑ m ∈ Finset.Ico (sparseScale p k) (sparseScale p (k + 1)),
        Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1) := rfl

/-- Public equation form of the finite logarithmic block error. -/
theorem sparseScaleBlockError_eq_sum (p : ℝ) (k : ℕ) :
    sparseScaleBlockError p k =
      ∑ m ∈ Finset.Ico (sparseScale p k) (sparseScale p (k + 1)),
        Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1) :=
  sparseScaleBlockError_eq_sum_private p k

/-- The one-step shifted logarithmic sum matching the finite consecutive
increment bound on a sparse block. -/
def sparseScaleShiftedBlockError (p : ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico (sparseScale p k) (sparseScale p (k + 1)),
    Real.log (2 * ((m : ℝ) + 1)) / ((m : ℝ) + 1)

/-- Shifting the logarithm from `m` to `m+1` costs at most a factor of two
on every sparse block, since all its indices are positive. -/
theorem sparseScaleShiftedBlockError_le
    {p : ℝ} (hp : 1 < p) (k : ℕ) :
    sparseScaleShiftedBlockError p k ≤ 2 * sparseScaleBlockError p k := by
  unfold sparseScaleShiftedBlockError sparseScaleBlockError
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hm1 : 1 ≤ m := by
    have hs : 1 ≤ sparseScale p k := by
      calc
        1 = sparseScale p 0 := (sparseScale_zero hp).symm
        _ ≤ sparseScale p k := sparseScale_monotone hp (Nat.zero_le k)
    exact hs.trans (Finset.mem_Ico.mp hm).1
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm1)
  have hmreal1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have harg : 0 < 2 * ((m : ℝ) + 1) := by positivity
  have harg' : 0 < 4 * (m : ℝ) := by positivity
  have harg_le : 2 * ((m : ℝ) + 1) ≤ 4 * (m : ℝ) := by nlinarith
  have hlogarg : 2 * (m : ℝ) ≤ 4 * (m : ℝ) := by nlinarith
  have hlogmono := Real.log_le_log harg harg_le
  have hlogsplit : Real.log (4 * (m : ℝ)) =
      Real.log 2 + Real.log (2 * (m : ℝ)) := by
    rw [show 4 * (m : ℝ) = 2 * (2 * (m : ℝ)) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hlog2le : Real.log 2 ≤ Real.log (2 * (m : ℝ)) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hlogle : Real.log (2 * ((m : ℝ) + 1)) ≤
      2 * Real.log (2 * (m : ℝ)) := by linarith [hlogmono, hlogsplit, hlog2le]
  have hden : 0 ≤ ((m : ℝ) + 1)⁻¹ := by positivity
  change Real.log (2 * ((m : ℝ) + 1)) / ((m : ℝ) + 1) ≤
    2 * (Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1))
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    Real.log (2 * ((m : ℝ) + 1)) * ((m : ℝ) + 1)⁻¹ ≤
        (2 * Real.log (2 * (m : ℝ))) * ((m : ℝ) + 1)⁻¹ :=
      mul_le_mul_of_nonneg_right hlogle hden
    _ = 2 * (Real.log (2 * (m : ℝ)) * ((m : ℝ) + 1)⁻¹) := by ring

/-- Reindex a finite consecutive-scale sum by its natural interval. -/
theorem sum_range_add_eq_sum_Ico {α : Type*} [AddCommMonoid α]
    (s t : ℕ) (f : ℕ → α) :
    (∑ i ∈ Finset.range (t - s), f (s + i)) =
      ∑ m ∈ Finset.Ico s t, f m := by
  rw [Finset.sum_Ico_eq_sum_range]

/-- Casting a consecutive natural index to the reals commutes with its
one-step shift. -/
theorem realCast_nat_add_succ (s i : ℕ) :
    (((s + i : ℕ) : ℝ) + 1) = (s : ℝ) + (i : ℝ) + 1 := by
  norm_cast

/-- The normalized logarithmic coefficient is unchanged when its natural
index is expanded as a block start plus an offset. -/
theorem normalizedLogCoeff_nat_add (s i : ℕ) :
    2 * Real.log (2 * (((s + i : ℕ) : ℝ) + 1)) /
        (((s + i : ℕ) : ℝ) + 1) =
      2 * Real.log (2 * ((s : ℝ) + (i : ℝ) + 1)) /
        ((s : ℝ) + (i : ℝ) + 1) := by
  rw [realCast_nat_add_succ]

/-- Convert the ENNReal sum of shifted logarithmic coefficients to the
corresponding real sum over the interval. -/
theorem ennreal_sum_normalizedLogCoeff_eq_ofReal
    {s t : ℕ} (hs : 1 ≤ s) :
    (∑ i ∈ Finset.range (t - s),
      ENNReal.ofReal
        (2 * Real.log (2 * (((s + i : ℕ) : ℝ) + 1)) /
          (((s + i : ℕ) : ℝ) + 1))) =
      ENNReal.ofReal
        (2 * ∑ m ∈ Finset.Ico s t,
          Real.log (2 * ((m : ℝ) + 1)) / ((m : ℝ) + 1)) := by
  have hnonneg : ∀ i ∈ Finset.range (t - s),
      0 ≤ 2 * Real.log (2 * (((s + i : ℕ) : ℝ) + 1)) /
        (((s + i : ℕ) : ℝ) + 1) := by
    intro i hi
    have hm : 1 ≤ s + i := by omega
    have hmreal : (1 : ℝ) ≤ ((s + i : ℕ) : ℝ) := by exact_mod_cast hm
    have hlog : 0 ≤ Real.log (2 * (((s + i : ℕ) : ℝ) + 1)) :=
      Real.log_nonneg (by nlinarith)
    positivity
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]
  congr 1
  calc
    (∑ i ∈ Finset.range (t - s),
        2 * Real.log (2 * (((s + i : ℕ) : ℝ) + 1)) /
          (((s + i : ℕ) : ℝ) + 1)) =
      2 * ∑ i ∈ Finset.range (t - s),
        Real.log (2 * (((s + i : ℕ) : ℝ) + 1)) /
          (((s + i : ℕ) : ℝ) + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = 2 * ∑ m ∈ Finset.Ico s t,
        Real.log (2 * ((m : ℝ) + 1)) / ((m : ℝ) + 1) := by
          exact congrArg (fun z : ℝ => 2 * z)
            (sum_range_add_eq_sum_Ico s t
              (fun m => Real.log (2 * ((m : ℝ) + 1)) / ((m : ℝ) + 1)))

/-- The normalized coefficient sum on the actual sparse block is controlled
by four times the summable block error. -/
theorem sparseScaleIncrementCoeffSum_le
    {p : ℝ} (hp : 1 < p) (k : ℕ) :
    (∑ i ∈ Finset.range
        (sparseScale p (k + 1) - sparseScale p k),
      ENNReal.ofReal
        (2 * Real.log (2 * (((sparseScale p k + i : ℕ) : ℝ) + 1)) /
          (((sparseScale p k + i : ℕ) : ℝ) + 1))) ≤
      ENNReal.ofReal (4 * sparseScaleBlockError p k) := by
  have hs : 1 ≤ sparseScale p k := by
    calc
      1 = sparseScale p 0 := (sparseScale_zero hp).symm
      _ ≤ sparseScale p k := sparseScale_monotone hp (Nat.zero_le k)
  have heq := ennreal_sum_normalizedLogCoeff_eq_ofReal
    (s := sparseScale p k) (t := sparseScale p (k + 1)) hs
  have heq' :
      (∑ i ∈ Finset.range
          (sparseScale p (k + 1) - sparseScale p k),
        ENNReal.ofReal
          (2 * Real.log (2 * (((sparseScale p k + i : ℕ) : ℝ) + 1)) /
            (((sparseScale p k + i : ℕ) : ℝ) + 1))) =
        ENNReal.ofReal (2 * sparseScaleShiftedBlockError p k) := by
    simpa [sparseScaleShiftedBlockError] using heq
  calc
    _ = ENNReal.ofReal (2 * sparseScaleShiftedBlockError p k) := heq'
    _ ≤ ENNReal.ofReal (4 * sparseScaleBlockError p k) :=
      ENNReal.ofReal_le_ofReal (by
        have hshift := sparseScaleShiftedBlockError_le hp k
        linarith)

/-- Bound a block error by its endpoint logarithm times the relative scale gap. -/
theorem sparseScaleBlockError_le_endpoint_log_mul_relative
    {p : ℝ} (hp : 1 < p) (k : ℕ) :
    sparseScaleBlockError p k ≤
      Real.log (2 * (sparseScale p (k + 1) : ℝ)) *
        (((sparseScale p (k + 1) - sparseScale p k : ℕ) : ℝ) /
          (sparseScale p k : ℝ)) := by
  let s := sparseScale p k
  let t := sparseScale p (k + 1)
  have hs_le_t : s ≤ t := sparseScale_monotone hp (Nat.le_succ k)
  have hmin : 1 ≤ s := by
    dsimp [s]
    calc
      1 = sparseScale p 0 := (sparseScale_zero hp).symm
      _ ≤ sparseScale p k := sparseScale_monotone hp (Nat.zero_le k)
  have hs_pos : 0 < (s : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hmin)
  have hterm : ∀ m ∈ Finset.Ico s t,
      Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1) ≤
        Real.log (2 * (t : ℝ)) / (s : ℝ) := by
    intro m hm
    rcases Finset.mem_Ico.mp hm with ⟨hsm, hmt⟩
    have hmmin : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (hmin.trans hsm)
    have hnumArgPos : 0 < 2 * (m : ℝ) := by positivity
    have hnumArgLe : 2 ≤ 2 * (m : ℝ) := by nlinarith
    have hnumNonneg : 0 ≤ Real.log (2 * (m : ℝ)) := by
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnumArgLe
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hnumArgUpper : 2 * (m : ℝ) ≤ 2 * (t : ℝ) := by
      have hmt' : (m : ℝ) ≤ (t : ℝ) := by exact_mod_cast (Nat.le_of_lt hmt)
      nlinarith
    have hnumUpper : Real.log (2 * (m : ℝ)) ≤ Real.log (2 * (t : ℝ)) :=
      Real.log_le_log hnumArgPos hnumArgUpper
    have hdenLe : (s : ℝ) ≤ (m : ℝ) + 1 := by
      exact_mod_cast (Nat.le_add_right_of_le hsm)
    exact div_le_div₀ (le_trans hnumNonneg hnumUpper) hnumUpper hs_pos hdenLe
  have hsum := Finset.sum_le_card_nsmul
    (Finset.Ico s t)
    (fun m : ℕ => Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1))
    (Real.log (2 * (t : ℝ)) / (s : ℝ)) hterm
  have hsum' : sparseScaleBlockError p k ≤
      (Finset.Ico s t).card • (Real.log (2 * (t : ℝ)) / (s : ℝ)) := by
    simpa [sparseScaleBlockError, s, t] using hsum
  have hcard : (Finset.Ico s t).card = t - s := Nat.card_Ico s t
  have hsum'' : sparseScaleBlockError p k ≤
      (Real.log (2 * (t : ℝ)) / (s : ℝ)) * ((t - s : ℕ) : ℝ) := by
    simpa [nsmul_eq_mul, hcard, mul_comm] using hsum'
  calc
    sparseScaleBlockError p k ≤
        (Real.log (2 * (t : ℝ)) / (s : ℝ)) * ((t - s : ℕ) : ℝ) := hsum''
    _ = Real.log (2 * (t : ℝ)) * ((t - s : ℕ) : ℝ) / (s : ℝ) := by ring
    _ = Real.log (2 * (sparseScale p (k + 1) : ℝ)) *
        (((sparseScale p (k + 1) - sparseScale p k : ℕ) : ℝ) /
          (sparseScale p k : ℝ)) := by
      dsimp [s, t]
      ring

/-- The final logarithmic series term from the sparse-scale lemma, zeroed off its stated range. -/
def sparseScaleLogInversePower (p : ℝ) (k : ℕ) : ℝ :=
  if 3 ≤ sparseScale p k then
    (Real.log (sparseScale p k : ℝ)) ^ (-(2 / sparseScaleTau p))
  else 0

/-- The logarithmic inverse-power series in the blueprint is summable. -/
theorem summable_sparseScaleLogInversePower {p : ℝ} (hp : 1 < p) :
    Summable (sparseScaleLogInversePower p) := by
  let τ := sparseScaleTau p
  let D := 2 / τ
  let c := Real.log 2 / 2
  have hτpos : 0 < τ := by dsimp [τ]; exact sparseScaleTau_pos hp
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hpow_summable : Summable (fun k : ℕ => (k : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hmajor : Summable (fun k : ℕ => c ^ (-D) * (k : ℝ) ^ (-2 : ℝ)) :=
    hpow_summable.mul_left (c ^ (-D))
  apply Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hmajor
  · by_cases hcond : 3 ≤ sparseScale p k
    · simp [sparseScaleLogInversePower, hcond]
      apply Real.rpow_nonneg
      exact le_of_lt (Real.log_pos (by
        have : 1 < (sparseScale p k : ℝ) := by exact_mod_cast (by omega : 1 < sparseScale p k)
        exact this))
    · simp [sparseScaleLogInversePower, hcond]
  · by_cases hcond : 3 ≤ sparseScale p k
    · have hk : 1 ≤ k := by
        by_contra h
        have hk0 : k = 0 := by omega
        subst k
        rw [sparseScale_zero hp] at hcond
        omega
      have hloglower := (sparseScale_log_bounds hp hk).1
      have hspos : 0 < (sparseScale p k : ℝ) := by
        exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (by omega : 1 ≤ sparseScale p k))
      have hlogpos : 0 < Real.log (sparseScale p k : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < sparseScale p k))
      have hbasepos : 0 < c * (k : ℝ) ^ τ := by
        dsimp [c]
        exact mul_pos hcpos (Real.rpow_pos_of_pos (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)) τ)
      have hnegative : -(D : ℝ) ≤ 0 := by linarith
      have hpow_le :
          (Real.log (sparseScale p k : ℝ)) ^ (-D) ≤
            (c * (k : ℝ) ^ τ) ^ (-D) := by
        exact Real.rpow_le_rpow_of_nonpos hbasepos hloglower hnegative
      have hexp : τ * (-D) = -2 := by
        dsimp [D]
        field_simp [ne_of_gt hτpos]
      have hmul :
          (c * (k : ℝ) ^ τ) ^ (-D) = c ^ (-D) * (k : ℝ) ^ (-2 : ℝ) := by
        rw [Real.mul_rpow hcpos.le (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le k)) τ)]
        rw [← Real.rpow_mul (by exact_mod_cast (Nat.zero_le k)) τ (-D), hexp]
      simpa [sparseScaleLogInversePower, hcond, τ, D, c] using hpow_le.trans_eq hmul
    · simp only [sparseScaleLogInversePower, ite_eq_right hcond]
      exact mul_nonneg (Real.rpow_nonneg hcpos.le _) (Real.rpow_nonneg (Nat.cast_nonneg k) _)

/-- The exponential floor error is eventually dominated by the scale power. -/
def sparseScaleExpDecayRatio (p : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) ^ (1 - sparseScaleTau p) /
    (2 : ℝ) ^ ((k : ℝ) ^ sparseScaleTau p)

theorem eventually_sparseScaleExpDecayRatio_le_one {p : ℝ} (hp : 1 < p) :
    ∀ᶠ k : ℕ in Filter.atTop, sparseScaleExpDecayRatio p k ≤ 1 := by
  let τ := sparseScaleTau p
  let s := (1 - τ) / τ
  have hτpos : 0 < τ := by dsimp [τ]; exact sparseScaleTau_pos hp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinner : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ τ)
      (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ) :=
    (tendsto_rpow_atTop hτpos).comp
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto Nat.cast (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ))
  have hdecay : Filter.Tendsto (fun x : ℝ => x ^ s * Real.exp (-Real.log 2 * x))
      (Filter.atTop : Filter ℝ) (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s (Real.log 2) hlog2
  have hseq := hdecay.comp hinner
  have hevent : ∀ᶠ k : ℕ in Filter.atTop,
      ((k : ℝ) ^ τ) ^ s * Real.exp (-Real.log 2 * (k : ℝ) ^ τ) < 1 := by
    exact hseq.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hevent, Filter.eventually_ge_atTop (1 : ℕ)] with k hkle hk
  have hexp : τ * s = 1 - τ := by
    dsimp [s]
    field_simp [ne_of_gt hτpos]
  have hpow : (k : ℝ) ^ (1 - τ) = ((k : ℝ) ^ τ) ^ s := by
    calc
      (k : ℝ) ^ (1 - τ) = (k : ℝ) ^ (τ * s) := by rw [hexp]
      _ = ((k : ℝ) ^ τ) ^ s := Real.rpow_mul (Nat.cast_nonneg k) τ s
  have hexp_inv : Real.exp (-Real.log 2 * (k : ℝ) ^ τ) =
      ((2 : ℝ) ^ ((k : ℝ) ^ τ))⁻¹ := by
    calc
      Real.exp (-Real.log 2 * (k : ℝ) ^ τ) =
          Real.exp (Real.log 2 * (-(k : ℝ) ^ τ)) := by congr 1; ring
      _ = (2 : ℝ) ^ (-(k : ℝ) ^ τ) :=
        (Real.rpow_def_of_pos (x := (2 : ℝ)) (by norm_num) _).symm
      _ = ((2 : ℝ) ^ ((k : ℝ) ^ τ))⁻¹ := Real.rpow_neg (by norm_num) _
  have heq : sparseScaleExpDecayRatio p k =
      ((k : ℝ) ^ τ) ^ s * Real.exp (-Real.log 2 * (k : ℝ) ^ τ) := by
    change (k : ℝ) ^ (1 - τ) / (2 : ℝ) ^ ((k : ℝ) ^ τ) =
      ((k : ℝ) ^ τ) ^ s * Real.exp (-Real.log 2 * (k : ℝ) ^ τ)
    rw [hpow, hexp_inv]
    simp [div_eq_mul_inv]
  rw [heq]
  exact hkle.le

/-- The endpoint logarithm of a sparse block is at most a constant times `k^τ`. -/
theorem sparseScale_endpoint_log_bound {p : ℝ} (hp : 1 < p) {k : ℕ}
    (hk : 1 ≤ k) :
    Real.log (2 * (sparseScale p (k + 1) : ℝ)) ≤
      3 * Real.log 2 * Real.rpow (k : ℝ) (sparseScaleTau p) := by
  have hτpos := sparseScaleTau_pos hp
  have hkreal : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hpow_ge_one : 1 ≤ Real.rpow (k : ℝ) (sparseScaleTau p) :=
    Real.one_le_rpow hkreal hτpos.le
  have hbase : ((k + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
    have hkcast : (1 : ℝ) ≤ (k : ℝ) := hkreal
    push_cast
    nlinarith
  have hpow_base : Real.rpow ((k + 1 : ℕ) : ℝ) (sparseScaleTau p) ≤
      Real.rpow (2 * (k : ℝ)) (sparseScaleTau p) :=
    Real.rpow_le_rpow (by positivity) hbase hτpos.le
  have hmul : Real.rpow (2 * (k : ℝ)) (sparseScaleTau p) =
      Real.rpow 2 (sparseScaleTau p) * Real.rpow (k : ℝ) (sparseScaleTau p) := by
    change (2 * (k : ℝ)) ^ sparseScaleTau p =
      (2 : ℝ) ^ sparseScaleTau p * (k : ℝ) ^ sparseScaleTau p
    exact Real.mul_rpow (by norm_num) (Nat.cast_nonneg k)
  have hpow_two : Real.rpow 2 (sparseScaleTau p) ≤ 2 := by
    calc
      Real.rpow 2 (sparseScaleTau p) ≤ Real.rpow 2 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (sparseScaleTau_lt_one hp).le
      _ = 2 := by norm_num
  have hpow_succ : Real.rpow ((k + 1 : ℕ) : ℝ) (sparseScaleTau p) ≤
      2 * Real.rpow (k : ℝ) (sparseScaleTau p) := by
    calc
      Real.rpow ((k + 1 : ℕ) : ℝ) (sparseScaleTau p) ≤
          Real.rpow (2 * (k : ℝ)) (sparseScaleTau p) := hpow_base
      _ = Real.rpow 2 (sparseScaleTau p) * Real.rpow (k : ℝ) (sparseScaleTau p) := hmul
      _ ≤ 2 * Real.rpow (k : ℝ) (sparseScaleTau p) :=
        mul_le_mul_of_nonneg_right hpow_two (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hk_succ : 1 ≤ k + 1 := by omega
  have hlog_succ := (sparseScale_log_bounds hp hk_succ).2
  have hspos : 0 < (sparseScale p (k + 1) : ℝ) := by
    have hmin : 1 ≤ sparseScale p (k + 1) := by
      calc
        1 = sparseScale p 0 := (sparseScale_zero hp).symm
        _ ≤ sparseScale p (k + 1) := sparseScale_monotone hp (Nat.zero_le _)
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hmin)
  have hlogmul : Real.log (2 * (sparseScale p (k + 1) : ℝ)) =
      Real.log 2 + Real.log (sparseScale p (k + 1) : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hspos.ne']
  rw [hlogmul]
  calc
    Real.log 2 + Real.log (sparseScale p (k + 1) : ℝ) ≤
        Real.log 2 + Real.log 2 *
          Real.rpow ((k + 1 : ℕ) : ℝ) (sparseScaleTau p) :=
      add_le_add (le_rfl) hlog_succ
    _ ≤ 3 * Real.log 2 * Real.rpow (k : ℝ) (sparseScaleTau p) := by
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), hpow_succ, hpow_ge_one]

/-- A two-term bound for the logarithmic block error. -/
theorem sparseScaleBlockError_le_two_term_bound
    {p : ℝ} (hp : 1 < p) {k : ℕ} (hk : 1 ≤ k) :
    sparseScaleBlockError p k ≤
      12 * (Real.log 2) ^ 2 * sparseScaleTau p *
          Real.rpow (k : ℝ) (2 * sparseScaleTau p - 1) +
        6 * Real.log 2 *
          (Real.rpow (k : ℝ) (sparseScaleTau p) /
            Real.rpow 2 (Real.rpow (k : ℝ) (sparseScaleTau p))) := by
  have hrelative := sparseScale_relative_step_bound hp hk
  have hendpoint := sparseScale_endpoint_log_bound hp hk
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htaupos : 0 < sparseScaleTau p := sparseScaleTau_pos hp
  have hkpow_nonneg : 0 ≤ Real.rpow (k : ℝ) (sparseScaleTau p) :=
    Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hdenpos : 0 < Real.rpow 2 (Real.rpow (k : ℝ) (sparseScaleTau p)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrel_nonneg : 0 ≤
      4 * Real.log 2 * sparseScaleTau p *
          Real.rpow (k : ℝ) (sparseScaleTau p - 1) +
        2 / Real.rpow 2 (Real.rpow (k : ℝ) (sparseScaleTau p)) := by
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hlog2pos.le) htaupos.le)
        (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    · exact div_nonneg (by norm_num) hdenpos.le
  have hstep := sparseScaleBlockError_le_endpoint_log_mul_relative hp k
  have hscale : 0 < (k : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hpow_add : Real.rpow (k : ℝ) (sparseScaleTau p) *
        Real.rpow (k : ℝ) (sparseScaleTau p - 1) =
      Real.rpow (k : ℝ) (2 * sparseScaleTau p - 1) := by
    change (k : ℝ) ^ sparseScaleTau p * (k : ℝ) ^ (sparseScaleTau p - 1) =
      (k : ℝ) ^ (2 * sparseScaleTau p - 1)
    calc
      (k : ℝ) ^ sparseScaleTau p * (k : ℝ) ^ (sparseScaleTau p - 1) =
          (k : ℝ) ^ (sparseScaleTau p + (sparseScaleTau p - 1)) :=
        (Real.rpow_add hscale (sparseScaleTau p) (sparseScaleTau p - 1)).symm
      _ = (k : ℝ) ^ (2 * sparseScaleTau p - 1) := by congr 1; ring
  calc
    sparseScaleBlockError p k ≤
        Real.log (2 * (sparseScale p (k + 1) : ℝ)) *
          (((sparseScale p (k + 1) - sparseScale p k : ℕ) : ℝ) /
            (sparseScale p k : ℝ)) := hstep
    _ ≤ 3 * Real.log 2 * Real.rpow (k : ℝ) (sparseScaleTau p) *
        (((sparseScale p (k + 1) - sparseScale p k : ℕ) : ℝ) /
          (sparseScale p k : ℝ)) :=
      mul_le_mul_of_nonneg_right hendpoint (by positivity)
    _ ≤ 3 * Real.log 2 * Real.rpow (k : ℝ) (sparseScaleTau p) *
        (4 * Real.log 2 * sparseScaleTau p *
            Real.rpow (k : ℝ) (sparseScaleTau p - 1) +
          2 / Real.rpow 2 (Real.rpow (k : ℝ) (sparseScaleTau p))) :=
      mul_le_mul_of_nonneg_left hrelative (by
        exact mul_nonneg (mul_nonneg (by norm_num) hlog2pos.le) hkpow_nonneg)
    _ = 12 * (Real.log 2) ^ 2 * sparseScaleTau p *
          Real.rpow (k : ℝ) (2 * sparseScaleTau p - 1) +
        6 * Real.log 2 *
          (Real.rpow (k : ℝ) (sparseScaleTau p) /
            Real.rpow 2 (Real.rpow (k : ℝ) (sparseScaleTau p))) := by
      calc
        _ = 12 * (Real.log 2) ^ 2 * sparseScaleTau p *
              (Real.rpow (k : ℝ) (sparseScaleTau p) *
                Real.rpow (k : ℝ) (sparseScaleTau p - 1)) +
            6 * Real.log 2 *
              (Real.rpow (k : ℝ) (sparseScaleTau p) /
                Real.rpow 2 (Real.rpow (k : ℝ) (sparseScaleTau p))) := by ring
        _ = _ := by rw [hpow_add]

/-- The full block error has the blueprint's polynomial decay, eventually in `k`. -/
def sparseScaleBlockConstant (p : ℝ) : ℝ :=
  12 * (Real.log 2) ^ 2 * sparseScaleTau p + 6 * Real.log 2

theorem eventually_sparseScaleBlockError_le_polynomial
    {p : ℝ} (hp : 1 < p) :
    ∀ᶠ k : ℕ in Filter.atTop,
      sparseScaleBlockError p k ≤
        sparseScaleBlockConstant p * Real.rpow (k : ℝ) (2 * sparseScaleTau p - 1) := by
  let τ := sparseScaleTau p
  let e := 2 * τ - 1
  let A := 12 * (Real.log 2) ^ 2 * τ
  let B := 6 * Real.log 2
  have hτpos : 0 < τ := by dsimp [τ]; exact sparseScaleTau_pos hp
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdecay := eventually_sparseScaleExpDecayRatio_le_one hp
  filter_upwards [hdecay, Filter.eventually_ge_atTop (1 : ℕ)] with k hdec hk
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hpow_product : (k : ℝ) ^ e * (k : ℝ) ^ (1 - τ) = (k : ℝ) ^ τ := by
    calc
      (k : ℝ) ^ e * (k : ℝ) ^ (1 - τ) = (k : ℝ) ^ (e + (1 - τ)) :=
        (Real.rpow_add hkpos e (1 - τ)).symm
      _ = (k : ℝ) ^ τ := by congr 1; dsimp [e, τ]; ring_nf
  have hterm :
      Real.rpow (k : ℝ) τ /
          Real.rpow 2 (Real.rpow (k : ℝ) τ) ≤
        Real.rpow (k : ℝ) e := by
    have hmul := mul_le_mul_of_nonneg_right hdec
      (Real.rpow_nonneg (Nat.cast_nonneg k) e)
    have hmul_eq : sparseScaleExpDecayRatio p k * Real.rpow (k : ℝ) e =
        Real.rpow (k : ℝ) τ /
          Real.rpow 2 (Real.rpow (k : ℝ) τ) := by
      change ((k : ℝ) ^ (1 - τ) / (2 : ℝ) ^ ((k : ℝ) ^ τ)) *
          (k : ℝ) ^ e = (k : ℝ) ^ τ / (2 : ℝ) ^ ((k : ℝ) ^ τ)
      have hnum : (k : ℝ) ^ (1 - τ) * (k : ℝ) ^ e = (k : ℝ) ^ τ := by
        calc
          (k : ℝ) ^ (1 - τ) * (k : ℝ) ^ e =
              (k : ℝ) ^ e * (k : ℝ) ^ (1 - τ) := by ring
          _ = (k : ℝ) ^ τ := hpow_product
      calc
        _ = ((k : ℝ) ^ (1 - τ) * (k : ℝ) ^ e) /
            ((2 : ℝ) ^ ((k : ℝ) ^ τ)) := by rw [div_mul_eq_mul_div]
        _ = (k : ℝ) ^ τ / (2 : ℝ) ^ ((k : ℝ) ^ τ) := by rw [hnum]
    change sparseScaleExpDecayRatio p k * Real.rpow (k : ℝ) e ≤
      1 * Real.rpow (k : ℝ) e at hmul
    rw [hmul_eq] at hmul
    simpa using hmul
  have herror := sparseScaleBlockError_le_two_term_bound hp hk
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hBterm := mul_le_mul_of_nonneg_left hterm hBnonneg
  change sparseScaleBlockError p k ≤
      A * Real.rpow (k : ℝ) e + B *
        (Real.rpow (k : ℝ) τ /
          Real.rpow 2 (Real.rpow (k : ℝ) τ)) at herror
  calc
    sparseScaleBlockError p k ≤
        A * Real.rpow (k : ℝ) e + B *
          (Real.rpow (k : ℝ) τ /
            Real.rpow 2 (Real.rpow (k : ℝ) τ)) := herror
    _ ≤ A * Real.rpow (k : ℝ) e + B * Real.rpow (k : ℝ) e :=
      add_le_add (le_rfl) hBterm
    _ = (A + B) * Real.rpow (k : ℝ) e := by ring
    _ = sparseScaleBlockConstant p *
        Real.rpow (k : ℝ) (2 * sparseScaleTau p - 1) := by
      dsimp [A, B, e, sparseScaleBlockConstant, τ]

/-- Each logarithmic block error is nonnegative. -/
theorem sparseScaleBlockError_nonneg {p : ℝ} (hp : 1 < p) (k : ℕ) :
    0 ≤ sparseScaleBlockError p k := by
  have hmin : 1 ≤ sparseScale p k := by
    calc
      1 = sparseScale p 0 := (sparseScale_zero hp).symm
      _ ≤ sparseScale p k := sparseScale_monotone hp (Nat.zero_le k)
  have hterm : ∀ m ∈ Finset.Ico (sparseScale p k) (sparseScale p (k + 1)),
      0 ≤ Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1) := by
    intro m hm
    rcases Finset.mem_Ico.mp hm with ⟨hsm, _⟩
    have hmmin : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (hmin.trans hsm)
    have harg : (2 : ℝ) ≤ 2 * (m : ℝ) := by
      calc
        (2 : ℝ) = 2 * 1 := by ring
        _ ≤ 2 * (m : ℝ) := mul_le_mul_of_nonneg_left hmmin (by norm_num)
    have hlog : 0 ≤ Real.log (2 * (m : ℝ)) := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) harg
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    exact div_nonneg hlog (by positivity)
  change 0 ≤ ∑ m ∈ Finset.Ico (sparseScale p k) (sparseScale p (k + 1)),
    Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1)
  exact Finset.sum_nonneg hterm

/-- A finite constant gives the blueprint's block-error power bound for every `k ≥ 1`. -/
theorem exists_sparseScaleBlockError_polynomial_bound {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      sparseScaleBlockError p k ≤
        C * Real.rpow (k : ℝ) (2 * sparseScaleTau p - 1) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_sparseScaleBlockError_le_polynomial hp)
  let e := 2 * sparseScaleTau p - 1
  let C₀ := sparseScaleBlockConstant p
  let term (k : ℕ) := sparseScaleBlockError p k / Real.rpow (k : ℝ) e
  let C := C₀ + ∑ k ∈ Finset.range N, term k
  have hτpos : 0 < sparseScaleTau p := sparseScaleTau_pos hp
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC₀ : 0 < C₀ := by
    dsimp [C₀, sparseScaleBlockConstant]
    positivity
  have hterm_nonneg (k : ℕ) : 0 ≤ term k := by
    dsimp [term]
    exact div_nonneg (sparseScaleBlockError_nonneg hp k)
      (Real.rpow_nonneg (Nat.cast_nonneg k) e)
  have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range N, term k :=
    Finset.sum_nonneg fun k _ => hterm_nonneg k
  refine ⟨C, ?_, fun k hk => ?_⟩
  · dsimp [C]
    linarith
  · by_cases hNk : N ≤ k
    · have htail := hN k hNk
      have hC₀le : C₀ ≤ C := by dsimp [C]; exact le_add_of_nonneg_right hsum_nonneg
      have hkpow : 0 ≤ Real.rpow (k : ℝ) e := Real.rpow_nonneg (Nat.cast_nonneg k) e
      calc
        sparseScaleBlockError p k ≤ C₀ * Real.rpow (k : ℝ) e := htail
        _ ≤ C * Real.rpow (k : ℝ) e :=
          mul_le_mul_of_nonneg_right hC₀le hkpow
    · have hkN : k < N := Nat.lt_of_not_ge hNk
      have hkpowpos : 0 < Real.rpow (k : ℝ) e := by
        exact Real.rpow_pos_of_pos (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)) e
      have hsumterm : term k ≤ ∑ j ∈ Finset.range N, term j :=
        Finset.single_le_sum (fun j _ => hterm_nonneg j) (Finset.mem_range.mpr hkN)
      have hratio : term k * Real.rpow (k : ℝ) e = sparseScaleBlockError p k := by
        dsimp [term]
        exact div_mul_cancel₀ _ (ne_of_gt hkpowpos)
      have hCsum : (∑ j ∈ Finset.range N, term j) ≤ C := by
        dsimp [C]
        exact le_add_of_nonneg_left hC₀.le
      calc
        sparseScaleBlockError p k = term k * Real.rpow (k : ℝ) e := hratio.symm
        _ ≤ (∑ j ∈ Finset.range N, term j) * Real.rpow (k : ℝ) e :=
          mul_le_mul_of_nonneg_right hsumterm hkpowpos.le
        _ ≤ C * Real.rpow (k : ℝ) e := mul_le_mul_of_nonneg_right hCsum hkpowpos.le

/-- The source exponent `q(2τ-1)` lies strictly below `-1`. -/
theorem sparseScaleBlockExponent_lt_neg_one {p : ℝ} (hp : 1 < p) :
    sparseScaleQ p * (2 * sparseScaleTau p - 1) < -1 := by
  have hq : 1 < sparseScaleQ p := sparseScaleQ_gt_one hp
  rw [sparseScaleTau_eq_on_domain hp]
  have hq0 : sparseScaleQ p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  field_simp [hq0]
  nlinarith

/-- The `q`th powers of the blueprint's logarithmic block errors are summable. -/
theorem summable_sparseScaleBlockError_q {p : ℝ} (hp : 1 < p) :
    Summable (fun k : ℕ =>
      (sparseScaleBlockError p k) ^ (sparseScaleQ p)) := by
  let q := sparseScaleQ p
  let τ := sparseScaleTau p
  let e := 2 * τ - 1
  let β := q * e
  let C := sparseScaleBlockConstant p
  have hqpos : 0 < q := lt_trans zero_lt_one (sparseScaleQ_gt_one hp)
  have hqnonneg : 0 ≤ q := hqpos.le
  have hτpos : 0 < τ := by dsimp [τ]; exact sparseScaleTau_pos hp
  have hCpos : 0 < C := by
    dsimp [C, sparseScaleBlockConstant]
    positivity
  have hβ : β < -1 := by
    simpa [β, q, e, τ] using sparseScaleBlockExponent_lt_neg_one hp
  have hseries : Summable (fun k : ℕ => C ^ q * (k : ℝ) ^ β) :=
    (Real.summable_nat_rpow.mpr hβ).mul_left (C ^ q)
  have hbound := eventually_sparseScaleBlockError_le_polynomial hp
  have hlarge := Filter.eventually_ge_atTop (1 : ℕ)
  have hboundC : ∀ᶠ k : ℕ in Filter.cofinite,
      sparseScaleBlockError p k ≤
        sparseScaleBlockConstant p * Real.rpow (k : ℝ) (2 * sparseScaleTau p - 1) := by
    rw [Nat.cofinite_eq_atTop]
    exact hbound
  have hlargeC : ∀ᶠ k : ℕ in Filter.cofinite, 1 ≤ k := by
    rw [Nat.cofinite_eq_atTop]
    exact hlarge
  apply Summable.of_norm_bounded_eventually hseries
  filter_upwards [hboundC, hlargeC] with k hblock hk
  have hmin : 1 ≤ sparseScale p k := by
    calc
      1 = sparseScale p 0 := (sparseScale_zero hp).symm
      _ ≤ sparseScale p k := sparseScale_monotone hp (Nat.zero_le k)
  have hblock_nonneg : 0 ≤ sparseScaleBlockError p k := by
    have hterm : ∀ m ∈ Finset.Ico (sparseScale p k) (sparseScale p (k + 1)),
        0 ≤ Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1) := by
      intro m hm
      rcases Finset.mem_Ico.mp hm with ⟨hsm, _⟩
      have hmmin : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (hmin.trans hsm)
      have hlog : 0 ≤ Real.log (2 * (m : ℝ)) := by
        have harg : (2 : ℝ) ≤ 2 * (m : ℝ) := by
          calc
            (2 : ℝ) = 2 * 1 := by ring
            _ ≤ 2 * (m : ℝ) := mul_le_mul_of_nonneg_left hmmin (by norm_num)
        have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) harg
        linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      exact div_nonneg hlog (by positivity)
    change 0 ≤ ∑ m ∈ Finset.Ico (sparseScale p k) (sparseScale p (k + 1)),
      Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1)
    exact Finset.sum_nonneg hterm
  have hpow_nonneg : 0 ≤ (sparseScaleBlockError p k) ^ q :=
    Real.rpow_nonneg hblock_nonneg q
  have hpow_le :
      (sparseScaleBlockError p k) ^ q ≤
        (C * Real.rpow (k : ℝ) e) ^ q :=
    Real.rpow_le_rpow hblock_nonneg hblock hqnonneg
  have hfactor : (C * Real.rpow (k : ℝ) e) ^ q = C ^ q * (k : ℝ) ^ β := by
    change (C * (k : ℝ) ^ e) ^ q = C ^ q * (k : ℝ) ^ β
    calc
      (C * (k : ℝ) ^ e) ^ q = C ^ q * ((k : ℝ) ^ e) ^ q :=
        Real.mul_rpow hCpos.le (Real.rpow_nonneg (Nat.cast_nonneg k) e)
      _ = C ^ q * (k : ℝ) ^ (e * q) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg k) e q]
      _ = C ^ q * (k : ℝ) ^ β := by
        congr 2
        dsimp [β, q]
        ring
  calc
    ‖(sparseScaleBlockError p k) ^ q‖ =
        (sparseScaleBlockError p k) ^ q := Real.norm_of_nonneg hpow_nonneg
    _ ≤ (C * Real.rpow (k : ℝ) e) ^ q := hpow_le
    _ = C ^ q * (k : ℝ) ^ β := hfactor

/-- The ENNReal `q`-power series of the sparse block coefficients is finite. -/
theorem ennreal_tsum_sparseScaleBlockCoefficient_q_lt_top
    {p : ℝ} (hp : 1 < p) :
    (∑' k, (ENNReal.ofReal (4 * sparseScaleBlockError p k)) ^
      sparseScaleQ p) < ⊤ := by
  have hqpos : 0 < sparseScaleQ p :=
    lt_trans zero_lt_one (sparseScaleQ_gt_one hp)
  have hqnonneg : 0 ≤ sparseScaleQ p := hqpos.le
  have hrealSeries : Summable (fun k : ℕ =>
      (4 * sparseScaleBlockError p k) ^ sparseScaleQ p) := by
    have hfactor : (fun k : ℕ =>
        (4 * sparseScaleBlockError p k) ^ sparseScaleQ p) =
        fun k => 4 ^ sparseScaleQ p *
          (sparseScaleBlockError p k) ^ sparseScaleQ p := by
      funext k
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
        (sparseScaleBlockError_nonneg hp k)]
    rw [hfactor]
    exact (summable_sparseScaleBlockError_q hp).mul_left
      (4 ^ sparseScaleQ p)
  have hrealNonneg : ∀ k : ℕ,
      0 ≤ (4 * sparseScaleBlockError p k) ^ sparseScaleQ p := by
    intro k
    exact Real.rpow_nonneg (mul_nonneg (by norm_num)
      (sparseScaleBlockError_nonneg hp k)) _
  calc
    (∑' k, (ENNReal.ofReal (4 * sparseScaleBlockError p k)) ^
        sparseScaleQ p) =
      ∑' k, ENNReal.ofReal
        ((4 * sparseScaleBlockError p k) ^ sparseScaleQ p) := by
          apply tsum_congr
          intro k
          rw [ENNReal.ofReal_rpow_of_nonneg
            (mul_nonneg (by norm_num) (sparseScaleBlockError_nonneg hp k))
            hqnonneg]
    _ = ENNReal.ofReal (∑' k,
        (4 * sparseScaleBlockError p k) ^ sparseScaleQ p) :=
      (ENNReal.ofReal_tsum_of_nonneg hrealNonneg hrealSeries).symm
    _ < ∞ := ENNReal.ofReal_lt_top

/-- Logarithmic decay along the sparse scales is summable, with the finitely
many scales below `3` controlled separately. This is the scalar summability
step used for the sparse subsequence perturbation in the blueprint. -/
theorem summable_sparseScale_error_of_log_decay {p : ℝ} (hp : 1 < p)
    (e : ℕ → ℝ) (B C : ℝ) (_hB : 0 ≤ B) (hC : 0 ≤ C)
    (he_nonneg : ∀ k, 0 ≤ e k)
    (he_small : ∀ k, sparseScale p k < 3 → e k ≤ B)
    (he_decay : ∀ k, 3 ≤ sparseScale p k →
      e k ≤ C * Real.log (sparseScale p k : ℝ) ^ (-(2 / sparseScaleTau p))) :
    Summable e := by
  classical
  let small : Set ℕ := {k | sparseScale p k < 3}
  have hscale_large : ∀ᶠ k : ℕ in Filter.atTop, 3 ≤ sparseScale p k :=
    (sparseScale_tendsto_atTop hp).eventually_ge_atTop 3
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hscale_large
  have hsmall_finite : small.Finite := by
    apply (Set.finite_Iio K).subset
    intro k hk
    simp only [small, Set.mem_ofPred_eq, Set.mem_Iio] at hk ⊢
    by_contra hKk
    have hlarge := hK k (le_of_not_gt hKk)
    omega
  have hfinite_sum : Summable (fun k : ℕ => if k ∈ small then B else 0) := by
    apply summable_of_ne_finset_zero (s := hsmall_finite.toFinset)
    intro k hk
    have hk_not : k ∉ small := by
      intro hmem
      exact hk (by simpa using hmem)
    simp [hk_not]
  have hbase_sum : Summable (fun k : ℕ => C * sparseScaleLogInversePower p k) :=
    (summable_sparseScaleLogInversePower hp).mul_left C
  have hmajor_sum : Summable (fun k : ℕ =>
      (if k ∈ small then B else 0) + C * sparseScaleLogInversePower p k) :=
    hfinite_sum.add hbase_sum
  have hbase_nonneg (k : ℕ) : 0 ≤ sparseScaleLogInversePower p k := by
    unfold sparseScaleLogInversePower
    split_ifs with hk
    · have hs : 1 < sparseScale p k := by omega
      have hlog : 0 < Real.log (sparseScale p k : ℝ) := by
        apply Real.log_pos
        exact_mod_cast hs
      exact Real.rpow_nonneg hlog.le _
    · positivity
  apply Summable.of_norm_bounded hmajor_sum
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (he_nonneg k)]
  by_cases hk : sparseScale p k < 3
  · have hsmall : k ∈ small := hk
    rw [ite_eq_left hsmall]
    exact (he_small k hk).trans (le_add_of_nonneg_right (mul_nonneg hC (hbase_nonneg k)))
  · have hklarge : 3 ≤ sparseScale p k := by omega
    have hbase_eq : sparseScaleLogInversePower p k =
        Real.log (sparseScale p k : ℝ) ^ (-(2 / sparseScaleTau p)) := by
      simp [sparseScaleLogInversePower, hklarge]
    have hnot_small : k ∉ small := by simpa [small] using hk
    rw [ite_eq_right hnot_small]
    calc
      e k ≤ C * Real.log (sparseScale p k : ℝ) ^ (-(2 / sparseScaleTau p)) :=
        he_decay k hklarge
      _ = C * sparseScaleLogInversePower p k := by rw [hbase_eq]
      _ ≤ 0 + C * sparseScaleLogInversePower p k := by simp

end

end FractionalPrimes

end
