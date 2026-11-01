module

public import FractionalPrimes.FiniteInterpolationSplit
public import FractionalPrimes.FiniteSupportLpNorm
public import FractionalPrimes.FiniteSupportLpGeneral
public import FractionalPrimes.InterpolationWeightedLayercake
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

@[expose] public section

/-!
# The strict-level estimate for MSZ strong interpolation

This module isolates the first distribution estimate in the approved
`lm:interpolation` proof. The finite low/high split uses the existing
source-faithful convention: strict super-threshold values are high, and
equality is low. The endpoint estimates are expressed using `eLpNorm`,
which retains the extended counting-measure `ℓᵖ` norm from `lm:spaces`.
-/

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory
open Filter
open Set
open scoped BigOperators ENNReal Topology

noncomputable section

private theorem eLpNorm_rpow_eq_sum_of_supported
    {p : ℝ} (hp : 0 < p) (s : Finset ℤ) (f : ℤ → ℂ)
    (hf : ∀ x ∉ s, f x = 0) :
    (eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p =
      ∑ x ∈ s, ‖f x‖ₑ ^ p := by
  have hpENN0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpENNTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hrep : f = fun x => if x ∈ s then f x else 0 := by
    funext x
    by_cases hx : x ∈ s
    · simp [hx]
    · simp [hx, hf x hx]
  calc
    (eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p =
        (eLpNorm (fun x => if x ∈ s then f x else 0)
          (ENNReal.ofReal p) Measure.count) ^ p := by
      conv_lhs => rw [hrep]
    _ = ((∑ x ∈ s, ‖f x‖ₑ ^ (ENNReal.ofReal p).toReal) ^
        (1 / (ENNReal.ofReal p).toReal)) ^ p := by
          rw [eLpNorm_finiteSupport_eq_sum_rpow hpENN0 hpENNTop]
    _ = ∑ x ∈ s, ‖f x‖ₑ ^ p := by
          rw [ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul,
            one_div_mul_cancel hp.ne', ENNReal.rpow_one]

private theorem finiteHighPart_eLpNorm_rpow
    {p : ℝ} (hp : 0 < p) (s : Finset ℤ) (c : ℝ) (f : ℤ → ℂ) :
    (eLpNorm (finiteHighPart s c f) (ENNReal.ofReal p) Measure.count) ^ p =
      ∑ x ∈ s.filter (fun x => c < ‖f x‖), ‖f x‖ₑ ^ p := by
  rw [eLpNorm_rpow_eq_sum_of_supported hp s (finiteHighPart s c f)
    (fun x hx => finiteHighPart_eq_zero_of_not_mem s c f hx)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : c < ‖f x‖
  · simp [finiteHighPart, hx, h]
  · simp [finiteHighPart, hx, h, ENNReal.zero_rpow_of_pos hp]

private theorem finiteLowPart_eLpNorm_rpow
    {p : ℝ} (hp : 0 < p) (s : Finset ℤ) (c : ℝ) (f : ℤ → ℂ) :
    (eLpNorm (finiteLowPart s c f) (ENNReal.ofReal p) Measure.count) ^ p =
      ∑ x ∈ s.filter (fun x => ‖f x‖ ≤ c), ‖f x‖ₑ ^ p := by
  rw [eLpNorm_rpow_eq_sum_of_supported hp s (finiteLowPart s c f)
    (fun x hx => finiteLowPart_eq_zero_of_not_mem s c f hx)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : ‖f x‖ ≤ c
  · simp [finiteLowPart, hx, h]
  · simp [finiteLowPart, hx, h, ENNReal.zero_rpow_of_pos hp]

/-- The exact strict-level distribution estimate in the first step of
approved `lm:interpolation`. The two terms are written in `ENNReal` as
`Aᵢ^sᵢ` times the finite `sᵢ`-moment, divided by `λ^sᵢ`; this is the
extended-norm encoding of the source's `Aᵢ^sᵢ λ^{-sᵢ}` factors. -/
theorem strongInterpolation_strictLevelDistribution
    {s₀ s₁ A₀ A₁ η lam : ℝ}
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hη : 0 < η) (hlam : 0 < lam)
    (s : Finset ℤ) (f : ℤ → ℂ)
    (T : (ℤ → ℂ) → ℤ → ℝ)
    (hTsub : ∀ g h, (∀ x ∉ s, g x = 0) → (∀ x ∉ s, h x = 0) →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (hTnonneg : ∀ g, (∀ x ∉ s, g x = 0) → ∀ x, 0 ≤ T g x)
    (hTbound₀ : ∀ g, (∀ x ∉ s, g x = 0) →
      eLpNorm (T g) (ENNReal.ofReal s₀) Measure.count ≤
        ENNReal.ofReal A₀ * eLpNorm g (ENNReal.ofReal s₀) Measure.count)
    (hTbound₁ : ∀ g, (∀ x ∉ s, g x = 0) →
      eLpNorm (T g) (ENNReal.ofReal s₁) Measure.count ≤
        ENNReal.ofReal A₁ * eLpNorm g (ENNReal.ofReal s₁) Measure.count)
    (hf : ∀ x ∉ s, f x = 0) :
    Measure.count {x : ℤ | 2 * lam < T f x} ≤
      ((ENNReal.ofReal A₀) ^ s₀ *
        (∑ x ∈ s.filter (fun x => η * lam < ‖f x‖), ‖f x‖ₑ ^ s₀)) /
          ((ENNReal.ofReal lam) ^ s₀) +
      ((ENNReal.ofReal A₁) ^ s₁ *
        (∑ x ∈ s.filter (fun x => ‖f x‖ ≤ η * lam), ‖f x‖ₑ ^ s₁)) /
          ((ENNReal.ofReal lam) ^ s₁) := by
  classical
  let c : ℝ := η * lam
  let hi : ℤ → ℂ := finiteHighPart s c f
  let lo : ℤ → ℂ := finiteLowPart s c f
  have hc : 0 < c := by dsimp [c]; exact mul_pos hη hlam
  have hhi : ∀ x ∉ s, hi x = 0 := by
    intro x hx
    exact finiteHighPart_eq_zero_of_not_mem s c f hx
  have hlo : ∀ x ∉ s, lo x = 0 := by
    intro x hx
    exact finiteLowPart_eq_zero_of_not_mem s c f hx
  have hsplit : f = hi + lo := by
    funext x
    by_cases hx : x ∈ s
    · by_cases hlow : ‖f x‖ ≤ c
      · simp [hi, lo, finiteHighPart, finiteLowPart, hx, hlow,
          not_lt_of_ge hlow]
      · have hhigh : c < ‖f x‖ := lt_of_not_ge hlow
        simp [hi, lo, finiteHighPart, finiteLowPart, hx, hlow, hhigh]
    · simp [hi, lo, finiteHighPart, finiteLowPart, hx, hf x hx]
  have hsubPoint (x : ℤ) : T f x ≤ T hi x + T lo x := by
    have h := hTsub hi lo hhi hlo x
    rw [← hsplit] at h
    exact h
  have hlevelSubset : {x : ℤ | 2 * lam < T f x} ⊆
      {x | lam ≤ T hi x} ∪ {x | lam ≤ T lo x} := by
    intro x hx
    change 2 * lam < T f x at hx
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hnot
    have hhi' : T hi x < lam := lt_of_not_ge hnot.1
    have hlo' : T lo x < lam := lt_of_not_ge hnot.2
    linarith [hsubPoint x]
  have hs₀ENN0 : ENNReal.ofReal s₀ ≠ 0 := (ENNReal.ofReal_pos.mpr hs₀).ne'
  have hs₀ENNTop : ENNReal.ofReal s₀ ≠ ∞ := ENNReal.ofReal_ne_top
  have hs₁ENN0 : ENNReal.ofReal s₁ ≠ 0 := (ENNReal.ofReal_pos.mpr hs₁).ne'
  have hs₁ENNTop : ENNReal.ofReal s₁ ≠ ∞ := ENNReal.ofReal_ne_top
  have hlamS0Pos : 0 < (ENNReal.ofReal lam) ^ s₀ :=
    ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hlam) ENNReal.ofReal_ne_top
  have hlamS0Ne : (ENNReal.ofReal lam) ^ s₀ ≠ 0 := hlamS0Pos.ne'
  have hlamS0Top : (ENNReal.ofReal lam) ^ s₀ ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg hs₀.le ENNReal.ofReal_ne_top).ne
  have hlamS1Pos : 0 < (ENNReal.ofReal lam) ^ s₁ :=
    ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hlam) ENNReal.ofReal_ne_top
  have hlamS1Ne : (ENNReal.ofReal lam) ^ s₁ ≠ 0 := hlamS1Pos.ne'
  have hlamS1Top : (ENNReal.ofReal lam) ^ s₁ ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg hs₁.le ENNReal.ofReal_ne_top).ne
  have hmarkHi :=
    MeasureTheory.mul_meas_ge_le_pow_eLpNorm'
      (μ := (Measure.count : Measure ℤ)) (p := ENNReal.ofReal s₀)
      hs₀ENN0 hs₀ENNTop (f := T hi) (ENNReal.ofReal lam)
  have hmarkLo :=
    MeasureTheory.mul_meas_ge_le_pow_eLpNorm'
      (μ := (Measure.count : Measure ℤ)) (p := ENNReal.ofReal s₁)
      hs₁ENN0 hs₁ENNTop (f := T lo) (ENNReal.ofReal lam)
  have hnormHi (x : ℤ) : ‖T hi x‖ₑ = ENNReal.ofReal (T hi x) := by
    calc
      ‖T hi x‖ₑ = ENNReal.ofReal ‖T hi x‖ := by
        simp only [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, ← coe_nnnorm]
      _ = ENNReal.ofReal (T hi x) := by
        rw [Real.norm_of_nonneg (hTnonneg hi hhi x)]
  have hnormLo (x : ℤ) : ‖T lo x‖ₑ = ENNReal.ofReal (T lo x) := by
    calc
      ‖T lo x‖ₑ = ENNReal.ofReal ‖T lo x‖ := by
        simp only [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, ← coe_nnnorm]
      _ = ENNReal.ofReal (T lo x) := by
        rw [Real.norm_of_nonneg (hTnonneg lo hlo x)]
  have hlevelHi : {x : ℤ | lam ≤ T hi x} ⊆
      {x | ENNReal.ofReal lam ≤ ‖T hi x‖ₑ} := by
    intro x hx
    change lam ≤ T hi x at hx
    change ENNReal.ofReal lam ≤ ‖T hi x‖ₑ
    rw [hnormHi x]
    exact ENNReal.ofReal_le_ofReal hx
  have hlevelLo : {x : ℤ | lam ≤ T lo x} ⊆
      {x | ENNReal.ofReal lam ≤ ‖T lo x‖ₑ} := by
    intro x hx
    change lam ≤ T lo x at hx
    change ENNReal.ofReal lam ≤ ‖T lo x‖ₑ
    rw [hnormLo x]
    exact ENNReal.ofReal_le_ofReal hx
  have hhiMoment :
      (eLpNorm hi (ENNReal.ofReal s₀) Measure.count) ^ s₀ =
        ∑ x ∈ s.filter (fun x => c < ‖f x‖), ‖f x‖ₑ ^ s₀ :=
    finiteHighPart_eLpNorm_rpow hs₀ s c f
  have hloMoment :
      (eLpNorm lo (ENNReal.ofReal s₁) Measure.count) ^ s₁ =
        ∑ x ∈ s.filter (fun x => ‖f x‖ ≤ c), ‖f x‖ₑ ^ s₁ :=
    finiteLowPart_eLpNorm_rpow hs₁ s c f
  have hhiEndpoint :
      (eLpNorm (T hi) (ENNReal.ofReal s₀) Measure.count) ^ s₀ ≤
        (ENNReal.ofReal A₀) ^ s₀ *
          (∑ x ∈ s.filter (fun x => c < ‖f x‖), ‖f x‖ₑ ^ s₀) := by
    calc
      (eLpNorm (T hi) (ENNReal.ofReal s₀) Measure.count) ^ s₀ ≤
          (ENNReal.ofReal A₀ * eLpNorm hi (ENNReal.ofReal s₀) Measure.count) ^ s₀ :=
        ENNReal.rpow_le_rpow (hTbound₀ hi hhi) hs₀.le
      _ = (ENNReal.ofReal A₀) ^ s₀ *
          (eLpNorm hi (ENNReal.ofReal s₀) Measure.count) ^ s₀ :=
        ENNReal.mul_rpow_of_nonneg _ _ hs₀.le
      _ = _ := by rw [hhiMoment]
  have hloEndpoint :
      (eLpNorm (T lo) (ENNReal.ofReal s₁) Measure.count) ^ s₁ ≤
        (ENNReal.ofReal A₁) ^ s₁ *
          (∑ x ∈ s.filter (fun x => ‖f x‖ ≤ c), ‖f x‖ₑ ^ s₁) := by
    calc
      (eLpNorm (T lo) (ENNReal.ofReal s₁) Measure.count) ^ s₁ ≤
          (ENNReal.ofReal A₁ * eLpNorm lo (ENNReal.ofReal s₁) Measure.count) ^ s₁ :=
        ENNReal.rpow_le_rpow (hTbound₁ lo hlo) hs₁.le
      _ = (ENNReal.ofReal A₁) ^ s₁ *
          (eLpNorm lo (ENNReal.ofReal s₁) Measure.count) ^ s₁ :=
        ENNReal.mul_rpow_of_nonneg _ _ hs₁.le
      _ = _ := by rw [hloMoment]
  have hhiCount : Measure.count {x : ℤ | lam ≤ T hi x} ≤
      ((ENNReal.ofReal A₀) ^ s₀ *
        (∑ x ∈ s.filter (fun x => c < ‖f x‖), ‖f x‖ₑ ^ s₀)) /
          ((ENNReal.ofReal lam) ^ s₀) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hlamS0Ne) (Or.inl hlamS0Top)).2
    calc
      Measure.count {x : ℤ | lam ≤ T hi x} * (ENNReal.ofReal lam) ^ s₀ =
          (ENNReal.ofReal lam) ^ s₀ * Measure.count {x : ℤ | lam ≤ T hi x} :=
        mul_comm _ _
      _ ≤ (ENNReal.ofReal lam) ^ s₀ *
          Measure.count {x | ENNReal.ofReal lam ≤ ‖T hi x‖ₑ} :=
        mul_le_mul_right (measure_mono hlevelHi) ((ENNReal.ofReal lam) ^ s₀)
      _ ≤ (eLpNorm (T hi) (ENNReal.ofReal s₀) Measure.count) ^ s₀ := by
        simpa only [ENNReal.toReal_ofReal hs₀.le] using hmarkHi
      _ ≤ (ENNReal.ofReal A₀) ^ s₀ *
          (∑ x ∈ s.filter (fun x => c < ‖f x‖), ‖f x‖ₑ ^ s₀) := hhiEndpoint
  have hloCount : Measure.count {x : ℤ | lam ≤ T lo x} ≤
      ((ENNReal.ofReal A₁) ^ s₁ *
        (∑ x ∈ s.filter (fun x => ‖f x‖ ≤ c), ‖f x‖ₑ ^ s₁)) /
          ((ENNReal.ofReal lam) ^ s₁) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hlamS1Ne) (Or.inl hlamS1Top)).2
    calc
      Measure.count {x : ℤ | lam ≤ T lo x} * (ENNReal.ofReal lam) ^ s₁ =
          (ENNReal.ofReal lam) ^ s₁ * Measure.count {x : ℤ | lam ≤ T lo x} :=
        mul_comm _ _
      _ ≤ (ENNReal.ofReal lam) ^ s₁ *
          Measure.count {x | ENNReal.ofReal lam ≤ ‖T lo x‖ₑ} :=
        mul_le_mul_right (measure_mono hlevelLo) ((ENNReal.ofReal lam) ^ s₁)
      _ ≤ (eLpNorm (T lo) (ENNReal.ofReal s₁) Measure.count) ^ s₁ := by
        simpa only [ENNReal.toReal_ofReal hs₁.le] using hmarkLo
      _ ≤ (ENNReal.ofReal A₁) ^ s₁ *
          (∑ x ∈ s.filter (fun x => ‖f x‖ ≤ c), ‖f x‖ₑ ^ s₁) := hloEndpoint
  have hcount : Measure.count {x : ℤ | 2 * lam < T f x} ≤
      Measure.count {x : ℤ | lam ≤ T hi x} + Measure.count {x : ℤ | lam ≤ T lo x} := by
    calc
      Measure.count {x : ℤ | 2 * lam < T f x} ≤
          Measure.count ({x | lam ≤ T hi x} ∪ {x | lam ≤ T lo x}) :=
        measure_mono hlevelSubset
      _ ≤ Measure.count {x : ℤ | lam ≤ T hi x} +
          Measure.count {x : ℤ | lam ≤ T lo x} := measure_union_le _ _
  calc
    Measure.count {x : ℤ | 2 * lam < T f x} ≤
        Measure.count {x : ℤ | lam ≤ T hi x} +
          Measure.count {x : ℤ | lam ≤ T lo x} := hcount
    _ ≤ ((ENNReal.ofReal A₀) ^ s₀ *
          (∑ x ∈ s.filter (fun x => c < ‖f x‖), ‖f x‖ₑ ^ s₀)) /
          ((ENNReal.ofReal lam) ^ s₀) +
        ((ENNReal.ofReal A₁) ^ s₁ *
          (∑ x ∈ s.filter (fun x => ‖f x‖ ≤ c), ‖f x‖ₑ ^ s₁)) /
          ((ENNReal.ofReal lam) ^ s₁) := add_le_add hhiCount hloCount
    _ = _ := by simp [c]

end

/-- For positive endpoint constants, the scale prescribed by the approved
`lm:interpolation` proof makes both endpoint terms equal to the same mixed
power. -/
theorem strongInterpolation_optimized_endpoint_products
    {s₀ p s₁ A₀ A₁ : ℝ}
    (hs₀ : 0 < s₀) (hs₀p : s₀ < p) (hps₁ : p < s₁)
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) :
    let θ : ℝ := s₀ * (s₁ - p) / (p * (s₁ - s₀))
    let η : ℝ := (A₀ ^ s₀ / A₁ ^ s₁) ^ (1 / (s₁ - s₀))
    A₀ ^ s₀ * η ^ (s₀ - p) = A₀ ^ (p * θ) * A₁ ^ (p * (1 - θ)) ∧
      A₁ ^ s₁ * η ^ (s₁ - p) = A₀ ^ (p * θ) * A₁ ^ (p * (1 - θ)) := by
  let theta : ℝ := s₀ * (s₁ - p) / (p * (s₁ - s₀))
  let eta : ℝ := (A₀ ^ s₀ / A₁ ^ s₁) ^ (1 / (s₁ - s₀))
  change A₀ ^ s₀ * eta ^ (s₀ - p) =
      A₀ ^ (p * theta) * A₁ ^ (p * (1 - theta)) ∧
    A₁ ^ s₁ * eta ^ (s₁ - p) =
      A₀ ^ (p * theta) * A₁ ^ (p * (1 - theta))
  have hd : 0 < s₁ - s₀ := by linarith
  have hp : 0 < p := lt_trans hs₀ hs₀p
  have hA₀pow : 0 < A₀ ^ s₀ := Real.rpow_pos_of_pos hA₀ _
  have hA₁pow : 0 < A₁ ^ s₁ := Real.rpow_pos_of_pos hA₁ _
  have hratio : 0 < A₀ ^ s₀ / A₁ ^ s₁ := div_pos hA₀pow hA₁pow
  have htheta₀ : p * theta = s₀ * (s₁ - p) / (s₁ - s₀) := by
    dsimp [theta]
    field_simp [ne_of_gt hp, ne_of_gt hd] <;> ring
  have htheta₁ : p * (1 - theta) = s₁ * (p - s₀) / (s₁ - s₀) := by
    dsimp [theta]
    field_simp [ne_of_gt hp, ne_of_gt hd] <;> ring
  have hetaHi : eta ^ (s₀ - p) =
      (A₀ ^ s₀ / A₁ ^ s₁) ^ ((s₀ - p) / (s₁ - s₀)) := by
    dsimp [eta]
    rw [← Real.rpow_mul hratio.le (1 / (s₁ - s₀)) (s₀ - p)]
    congr 1
    field_simp [ne_of_gt hd]
  have hetaLo : eta ^ (s₁ - p) =
      (A₀ ^ s₀ / A₁ ^ s₁) ^ ((s₁ - p) / (s₁ - s₀)) := by
    dsimp [eta]
    rw [← Real.rpow_mul hratio.le (1 / (s₁ - s₀)) (s₁ - p)]
    congr 1
    field_simp [ne_of_gt hd]
  have hhi (e : ℝ) :
      A₀ ^ s₀ * (A₀ ^ s₀ / A₁ ^ s₁) ^ e =
        A₀ ^ (s₀ + s₀ * e) * A₁ ^ (-(s₁ * e)) := by
    calc
      _ = A₀ ^ s₀ * ((A₀ ^ s₀) ^ e / (A₁ ^ s₁) ^ e) := by
        rw [Real.div_rpow hA₀pow.le hA₁pow.le e]
      _ = (A₀ ^ s₀ * (A₀ ^ s₀) ^ e) * ((A₁ ^ s₁) ^ e)⁻¹ := by
        rw [div_eq_mul_inv, mul_assoc]
      _ = _ := by
        rw [← Real.rpow_mul hA₀.le s₀ e,
          ← Real.rpow_mul hA₁.le s₁ e,
          ← Real.rpow_neg hA₁.le (s₁ * e),
          ← Real.rpow_add hA₀ s₀ (s₀ * e)]
  have hlo (e : ℝ) :
      A₁ ^ s₁ * (A₀ ^ s₀ / A₁ ^ s₁) ^ e =
        A₀ ^ (s₀ * e) * A₁ ^ (s₁ - s₁ * e) := by
    calc
      _ = A₁ ^ s₁ * ((A₀ ^ s₀) ^ e / (A₁ ^ s₁) ^ e) := by
        rw [Real.div_rpow hA₀pow.le hA₁pow.le e]
      _ = (A₀ ^ s₀) ^ e * (A₁ ^ s₁ * ((A₁ ^ s₁) ^ e)⁻¹) := by
        rw [div_eq_mul_inv]
        ring
      _ = _ := by
        rw [← Real.rpow_mul hA₀.le s₀ e,
          ← Real.rpow_mul hA₁.le s₁ e,
          ← Real.rpow_neg hA₁.le (s₁ * e),
          show s₁ - s₁ * e = s₁ + -(s₁ * e) by ring,
          ← Real.rpow_add hA₁ s₁ (-(s₁ * e))]
  have hhiExp₀ : s₀ + s₀ * ((s₀ - p) / (s₁ - s₀)) = p * theta := by
    rw [htheta₀]
    field_simp [ne_of_gt hd] <;> ring
  have hhiExp₁ : -(s₁ * ((s₀ - p) / (s₁ - s₀))) = p * (1 - theta) := by
    rw [htheta₁]
    field_simp [ne_of_gt hd] <;> ring
  have hloExp₀ : s₀ * ((s₁ - p) / (s₁ - s₀)) = p * theta := by
    rw [htheta₀]
    field_simp [ne_of_gt hd]
  have hloExp₁ : s₁ - s₁ * ((s₁ - p) / (s₁ - s₀)) = p * (1 - theta) := by
    rw [htheta₁]
    field_simp [ne_of_gt hd] <;> ring
  constructor
  · calc
      A₀ ^ s₀ * eta ^ (s₀ - p) =
          A₀ ^ s₀ * (A₀ ^ s₀ / A₁ ^ s₁) ^ ((s₀ - p) / (s₁ - s₀)) := by
        rw [hetaHi]
      _ = A₀ ^ (p * theta) * A₁ ^ (p * (1 - theta)) := by
        rw [hhi ((s₀ - p) / (s₁ - s₀)), hhiExp₀, hhiExp₁]
  · calc
      A₁ ^ s₁ * eta ^ (s₁ - p) =
          A₁ ^ s₁ * (A₀ ^ s₀ / A₁ ^ s₁) ^ ((s₁ - p) / (s₁ - s₀)) := by
        rw [hetaLo]
      _ = A₀ ^ (p * theta) * A₁ ^ (p * (1 - theta)) := by
        rw [hlo ((s₁ - p) / (s₁ - s₀)), ← hloExp₀, hloExp₁]

/-- The high-value part of the strong-interpolation layer cake has this
power-tail integral. The exponent shift is chosen so that the source range
`(0, ‖f x‖ / η)` is integrated with exponent `p - s₀ - 1`. -/
theorem strongInterpolation_highTailIntegral
    {s₀ p c : ℝ} (hs₀p : s₀ < p) (hc : 0 ≤ c) :
    (∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal t ^ (p - s₀ - 1)) =
      ENNReal.ofReal (c ^ (p - s₀) / (p - s₀)) := by
  have hshift : 1 < p - s₀ + 1 := by linarith
  simpa only [show (p - s₀ + 1) - 2 = p - s₀ - 1 by ring,
    show (p - s₀ + 1) - 1 = p - s₀ by ring] using
    (interpolation_lintegral_rpow_Ioc (p := p - s₀ + 1) hshift hc)

/-- The low-value part of the strong-interpolation layer cake has this
power-tail integral. The source range `[‖f x‖ / η, ∞)` agrees almost
everywhere with the open tail used by this integral. -/
theorem strongInterpolation_lowTailIntegral
    {p s₁ c : ℝ} (hps₁ : p < s₁) (hc : 0 < c) :
    (∫⁻ t in Ioi c, ENNReal.ofReal t ^ (p - s₁ - 1)) =
      ENNReal.ofReal (c ^ (p - s₁) / (s₁ - p)) := by
  have hshift : p - s₁ + 2 < 2 := by linarith
  simpa only [show (p - s₁ + 2) - 3 = p - s₁ - 1 by ring,
    show (p - s₁ + 2) - 2 = p - s₁ by ring,
    show 2 - (p - s₁ + 2) = s₁ - p by ring] using
    (interpolation_lintegral_rpow_Ioi (p := p - s₁ + 2) hshift hc)

/-- The coordinate contribution from the strict high part of the split,
integrated against the layer-cake weight. -/
theorem strongInterpolation_highCoordinateIntegral
    {s₀ p η a : ℝ} (hs₀ : 0 < s₀) (hs₀p : s₀ < p)
    (hη : 0 < η) (ha : 0 ≤ a) :
    (∫⁻ t in Ioi (0 : ℝ),
      (if η * t < a then ENNReal.ofReal (a ^ s₀) else 0) *
        ENNReal.ofReal t ^ (p - s₀ - 1)) =
      ENNReal.ofReal (η ^ (s₀ - p) * a ^ p / (p - s₀)) := by
  have hp : 0 < p := lt_trans hs₀ hs₀p
  by_cases ha0 : a = 0
  · subst a
    calc
      (∫⁻ t in Ioi (0 : ℝ),
        (if η * t < 0 then ENNReal.ofReal (0 ^ s₀) else 0) *
          ENNReal.ofReal t ^ (p - s₀ - 1)) =
        ∫⁻ t in Ioi (0 : ℝ), (0 : ℝ≥0∞) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht0 : 0 < t := mem_Ioi.mp ht
          have hpos : 0 < η * t := mul_pos hη ht0
          simp [not_lt_of_ge hpos.le]
      _ = ENNReal.ofReal (η ^ (s₀ - p) * 0 ^ p / (p - s₀)) := by
          simp [Real.zero_rpow hp.ne']
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let c : ℝ := a / η
    have hc : 0 < c := by dsimp [c]; exact div_pos ha' hη
    have hcond (t : ℝ) : η * t < a ↔ t < c := by
      dsimp [c]
      rw [lt_div_iff₀ hη]
      simp [mul_comm]
    have hIoo : Ioo (0 : ℝ) c =ᵐ[volume] Ioc (0 : ℝ) c :=
      Ioo_ae_eq_Ioc (μ := volume) (a := 0) (b := c)
    have hbranch :
        (fun t : ℝ =>
          (if η * t < a then ENNReal.ofReal (a ^ s₀) else 0) *
            ENNReal.ofReal t ^ (p - s₀ - 1)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun t => (Ioo (0 : ℝ) c).indicator
          (fun t => ENNReal.ofReal (a ^ s₀) * ENNReal.ofReal t ^ (p - s₀ - 1)) t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := mem_Ioi.mp ht
      by_cases ht' : t < c
      · have hηt : η * t < a := (hcond t).mpr ht'
        simp [ht', hηt, ht0]
      · have hηt : ¬ η * t < a := fun h => ht' ((hcond t).mp h)
        have hnot : t ∉ Ioo (0 : ℝ) c := by
          rw [mem_Ioo]
          rintro ⟨_, htc⟩
          exact ht' htc
        simp [hηt, hnot]
    have hscale : a ^ s₀ * ((a / η) ^ (p - s₀) / (p - s₀)) =
        η ^ (s₀ - p) * a ^ p / (p - s₀) := by
      have hnum : a ^ s₀ * (a / η) ^ (p - s₀) =
          η ^ (s₀ - p) * a ^ p := by
        rw [Real.div_rpow ha'.le hη.le]
        rw [show s₀ - p = -(p - s₀) by ring, Real.rpow_neg hη.le]
        simp only [div_eq_mul_inv, mul_assoc]
        calc
          a ^ s₀ * (a ^ (p - s₀) * (η ^ (p - s₀))⁻¹) =
              (a ^ s₀ * a ^ (p - s₀)) * (η ^ (p - s₀))⁻¹ := by rw [mul_assoc]
          _ = a ^ p * (η ^ (p - s₀))⁻¹ := by
              rw [← Real.rpow_add ha' s₀ (p - s₀)]
              rw [show s₀ + (p - s₀) = p by ring]
          _ = (η ^ (p - s₀))⁻¹ * a ^ p := by ring
      calc
        a ^ s₀ * ((a / η) ^ (p - s₀) / (p - s₀)) =
            (a ^ s₀ * (a / η) ^ (p - s₀)) / (p - s₀) := by ring
        _ = η ^ (s₀ - p) * a ^ p / (p - s₀) := by rw [hnum]
    calc
      (∫⁻ t in Ioi (0 : ℝ),
        (if η * t < a then ENNReal.ofReal (a ^ s₀) else 0) *
          ENNReal.ofReal t ^ (p - s₀ - 1)) =
        ∫⁻ t, (Ioo (0 : ℝ) c).indicator
          (fun t => ENNReal.ofReal (a ^ s₀) * ENNReal.ofReal t ^ (p - s₀ - 1)) t
            ∂volume.restrict (Ioi (0 : ℝ)) := by
              exact lintegral_congr_ae hbranch
      _ = ∫⁻ t in Ioo (0 : ℝ) c,
          ENNReal.ofReal (a ^ s₀) * ENNReal.ofReal t ^ (p - s₀ - 1)
            ∂volume.restrict (Ioi (0 : ℝ)) := by
              rw [lintegral_indicator measurableSet_Ioo]
      _ = ∫⁻ t,
          ENNReal.ofReal (a ^ s₀) * ENNReal.ofReal t ^ (p - s₀ - 1)
            ∂volume.restrict (Ioo (0 : ℝ) c ∩ Ioi (0 : ℝ)) := by
              rw [Measure.restrict_restrict measurableSet_Ioo]
      _ = ∫⁻ t in Ioc (0 : ℝ) c,
          ENNReal.ofReal (a ^ s₀) * ENNReal.ofReal t ^ (p - s₀ - 1) := by
              have hset : Ioo (0 : ℝ) c ∩ Ioi (0 : ℝ) =ᵐ[volume] Ioc (0 : ℝ) c := by
                have hExact : Ioo (0 : ℝ) c ∩ Ioi (0 : ℝ) = Ioo (0 : ℝ) c := by
                  ext t
                  simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
                  constructor
                  · rintro ⟨⟨ht0, htc⟩, _⟩
                    exact ⟨ht0, htc⟩
                  · intro ⟨ht0, htc⟩
                    exact ⟨⟨ht0, htc⟩, ht0⟩
                rw [hExact]
                exact hIoo
              rw [Measure.restrict_congr_set hset]
      _ = ENNReal.ofReal (a ^ s₀) *
          (∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal t ^ (p - s₀ - 1)) := by
              exact lintegral_const_mul (ENNReal.ofReal (a ^ s₀))
                (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal)
      _ = ENNReal.ofReal (a ^ s₀) *
          ENNReal.ofReal (c ^ (p - s₀) / (p - s₀)) := by
              rw [strongInterpolation_highTailIntegral hs₀p hc.le]
      _ = ENNReal.ofReal (η ^ (s₀ - p) * a ^ p / (p - s₀)) := by
              rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha s₀)]
              simpa [c] using congrArg ENNReal.ofReal hscale

/-- The coordinate contribution from the inclusive low part of the split,
integrated against the layer-cake weight. -/
theorem strongInterpolation_lowCoordinateIntegral
    {s₀ s₁ p η a : ℝ} (hs₀ : 0 < s₀) (hs₀p : s₀ < p) (hps₁ : p < s₁)
    (hη : 0 < η) (ha : 0 ≤ a) :
    (∫⁻ t in Ioi (0 : ℝ),
      (if a ≤ η * t then ENNReal.ofReal (a ^ s₁) else 0) *
        ENNReal.ofReal t ^ (p - s₁ - 1)) =
      ENNReal.ofReal (η ^ (s₁ - p) * a ^ p / (s₁ - p)) := by
  have hp : 0 < p := lt_trans hs₀ hs₀p
  have hs₁ : 0 < s₁ := lt_trans hp hps₁
  by_cases ha0 : a = 0
  · subst a
    calc
      (∫⁻ t in Ioi (0 : ℝ),
        (if 0 ≤ η * t then ENNReal.ofReal (0 ^ s₁) else 0) *
          ENNReal.ofReal t ^ (p - s₁ - 1)) =
        ∫⁻ t in Ioi (0 : ℝ), (0 : ℝ≥0∞) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht0 : 0 < t := mem_Ioi.mp ht
          have hpos : 0 < η * t := mul_pos hη ht0
          have hzero : (0 : ℝ) ^ s₁ = 0 := Real.zero_rpow hs₁.ne'
          simp [hpos.le, hzero]
      _ = ENNReal.ofReal (η ^ (s₁ - p) * 0 ^ p / (s₁ - p)) := by
          simp [Real.zero_rpow hp.ne']
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let c : ℝ := a / η
    have hc : 0 < c := by dsimp [c]; exact div_pos ha' hη
    have hcond (t : ℝ) : a ≤ η * t ↔ c ≤ t := by
      dsimp [c]
      rw [div_le_iff₀ hη]
      simp [mul_comm]
    have hIci : Ici c =ᵐ[volume] Ioi c :=
      (Ioi_ae_eq_Ici (μ := volume) (a := c)).symm
    have hset : Ici c ∩ Ioi (0 : ℝ) =ᵐ[volume] Ioi c := by
      filter_upwards [hIci] with t ht
      have ht' : t ∈ Ici c ↔ t ∈ Ioi c := Iff.of_eq ht
      apply propext
      change (t ∈ Ici c ∧ t ∈ Ioi (0 : ℝ)) ↔ t ∈ Ioi c
      constructor
      · rintro ⟨hct, _⟩
        exact ht'.mp hct
      · intro hct
        exact ⟨ht'.mpr hct, lt_trans hc hct⟩
    have hbranch :
        (fun t : ℝ =>
          (if a ≤ η * t then ENNReal.ofReal (a ^ s₁) else 0) *
            ENNReal.ofReal t ^ (p - s₁ - 1)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun t => (Ici c).indicator
          (fun t => ENNReal.ofReal (a ^ s₁) * ENNReal.ofReal t ^ (p - s₁ - 1)) t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      by_cases ht' : c ≤ t
      · have hηt : a ≤ η * t := (hcond t).mpr ht'
        simp [ht', hηt]
      · have hηt : ¬ a ≤ η * t := fun h => ht' ((hcond t).mp h)
        have hnot : t ∉ Ici c := by
          rw [mem_Ici]
          exact not_le_of_gt (lt_of_not_ge ht')
        simp [hηt, hnot]
    have hscale : a ^ s₁ * ((a / η) ^ (p - s₁) / (s₁ - p)) =
        η ^ (s₁ - p) * a ^ p / (s₁ - p) := by
      have hnum : a ^ s₁ * (a / η) ^ (p - s₁) =
          η ^ (s₁ - p) * a ^ p := by
        rw [Real.div_rpow ha'.le hη.le]
        rw [show s₁ - p = -(p - s₁) by ring, Real.rpow_neg hη.le]
        simp only [div_eq_mul_inv, mul_assoc]
        calc
          a ^ s₁ * (a ^ (p - s₁) * (η ^ (p - s₁))⁻¹) =
              (a ^ s₁ * a ^ (p - s₁)) * (η ^ (p - s₁))⁻¹ := by rw [mul_assoc]
          _ = a ^ p * (η ^ (p - s₁))⁻¹ := by
              rw [← Real.rpow_add ha' s₁ (p - s₁)]
              rw [show s₁ + (p - s₁) = p by ring]
          _ = (η ^ (p - s₁))⁻¹ * a ^ p := by ring
      calc
        a ^ s₁ * ((a / η) ^ (p - s₁) / (s₁ - p)) =
            (a ^ s₁ * (a / η) ^ (p - s₁)) / (s₁ - p) := by ring
        _ = η ^ (s₁ - p) * a ^ p / (s₁ - p) := by rw [hnum]
    calc
      (∫⁻ t in Ioi (0 : ℝ),
        (if a ≤ η * t then ENNReal.ofReal (a ^ s₁) else 0) *
          ENNReal.ofReal t ^ (p - s₁ - 1)) =
        ∫⁻ t, (Ici c).indicator
          (fun t => ENNReal.ofReal (a ^ s₁) * ENNReal.ofReal t ^ (p - s₁ - 1)) t
            ∂volume.restrict (Ioi (0 : ℝ)) := by
              exact lintegral_congr_ae hbranch
      _ = ∫⁻ t in Ici c,
          ENNReal.ofReal (a ^ s₁) * ENNReal.ofReal t ^ (p - s₁ - 1)
            ∂volume.restrict (Ioi (0 : ℝ)) := by
              rw [lintegral_indicator measurableSet_Ici]
      _ = ∫⁻ t,
          ENNReal.ofReal (a ^ s₁) * ENNReal.ofReal t ^ (p - s₁ - 1)
            ∂volume.restrict (Ici c ∩ Ioi (0 : ℝ)) := by
              rw [Measure.restrict_restrict measurableSet_Ici]
      _ = ∫⁻ t in Ioi c,
          ENNReal.ofReal (a ^ s₁) * ENNReal.ofReal t ^ (p - s₁ - 1) := by
              rw [Measure.restrict_congr_set hset]
      _ = ENNReal.ofReal (a ^ s₁) *
          (∫⁻ t in Ioi c, ENNReal.ofReal t ^ (p - s₁ - 1)) := by
              exact lintegral_const_mul (ENNReal.ofReal (a ^ s₁))
                (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal)
      _ = ENNReal.ofReal (a ^ s₁) *
          ENNReal.ofReal (c ^ (p - s₁) / (s₁ - p)) := by
              rw [strongInterpolation_lowTailIntegral hps₁ hc]
      _ = ENNReal.ofReal (η ^ (s₁ - p) * a ^ p / (s₁ - p)) := by
              rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha s₁)]
              simpa [c] using congrArg ENNReal.ofReal hscale

private theorem strongInterpolation_weight_rpow_div
    {p s t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) / (ENNReal.ofReal t) ^ s =
      ENNReal.ofReal t ^ (p - s - 1) := by
  have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
  rw [← ENNReal.ofReal_rpow_of_pos ht]
  rw [← ENNReal.rpow_sub (p - 1) s ht0 ENNReal.ofReal_ne_top]
  congr 1
  ring

/-- The output layer-cake identity after the source's change of variable
`u = 2t`. It keeps the strict superlevel set `{2t < F x}`. -/
private theorem strongInterpolation_scaledLayercake
    {p : ℝ} (hp : 0 < p) (F : ℤ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∫⁻ x : ℤ, ENNReal.ofReal ((F x) ^ p) ∂(Measure.count : Measure ℤ)) =
      ENNReal.ofReal (2 ^ p) *
        (ENNReal.ofReal p *
          (∫⁻ t in Ioi (0 : ℝ),
            Measure.count {x : ℤ | 2 * t < F x} * ENNReal.ofReal (t ^ (p - 1)))) := by
  let g : ℤ → ℂ := fun x => ((F x / 2 : ℝ) : ℂ)
  have hgNorm (x : ℤ) : ‖g x‖ = F x / 2 := by
    dsimp [g]
    rw [Complex.norm_real, Real.norm_of_nonneg]
    exact div_nonneg (hF x) (by norm_num)
  have hgNormPow (x : ℤ) : ‖g x‖ₑ ^ p = ENNReal.ofReal ((F x / 2) ^ p) := by
    rw [← ofReal_norm, hgNorm x]
    exact ENNReal.ofReal_rpow_of_nonneg (div_nonneg (hF x) (by norm_num)) hp.le
  have hpoint (x : ℤ) :
      ENNReal.ofReal ((F x) ^ p) = ENNReal.ofReal (2 ^ p) * ‖g x‖ₑ ^ p := by
    have hreal : (F x) ^ p = 2 ^ p * (F x / 2) ^ p := by
      calc
        (F x) ^ p = (2 * (F x / 2)) ^ p := by
          conv_lhs => rw [show F x = 2 * (F x / 2) by ring]
        _ = 2 ^ p * (F x / 2) ^ p :=
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
            (div_nonneg (hF x) (by norm_num))
    rw [hreal, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p),
      ← hgNormPow x]
  have hlevel :
      (fun t : ℝ => Measure.count {x : ℤ | t < ‖g x‖} *
          ENNReal.ofReal (t ^ (p - 1))) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun t => Measure.count {x : ℤ | 2 * t < F x} *
          ENNReal.ofReal (t ^ (p - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hset : {x : ℤ | t < ‖g x‖} = {x : ℤ | 2 * t < F x} := by
      ext x
      change t < ‖g x‖ ↔ 2 * t < F x
      rw [hgNorm x, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      simp [mul_comm]
    rw [hset]
  calc
    (∫⁻ x : ℤ, ENNReal.ofReal ((F x) ^ p) ∂(Measure.count : Measure ℤ)) =
        ∫⁻ x : ℤ, ENNReal.ofReal (2 ^ p) * ‖g x‖ₑ ^ p
          ∂(Measure.count : Measure ℤ) := by
            apply lintegral_congr_ae
            exact ae_of_all _ hpoint
    _ = ENNReal.ofReal (2 ^ p) *
        (∫⁻ x : ℤ, ‖g x‖ₑ ^ p ∂(Measure.count : Measure ℤ)) := by
          exact lintegral_const_mul _ (measurable_of_countable _)
    _ = ENNReal.ofReal (2 ^ p) *
        (ENNReal.ofReal p *
          (∫⁻ t in Ioi (0 : ℝ),
            Measure.count {x : ℤ | t < ‖g x‖} * ENNReal.ofReal (t ^ (p - 1)))) := by
          rw [integerSequence_lintegral_enorm_rpow_eq_lintegral_meas_lt hp g]
    _ = ENNReal.ofReal (2 ^ p) *
        (ENNReal.ofReal p *
          (∫⁻ t in Ioi (0 : ℝ),
            Measure.count {x : ℤ | 2 * t < F x} * ENNReal.ofReal (t ^ (p - 1)))) := by
          congr 2
          exact lintegral_congr_ae hlevel

/-!
## Next source step: layer-cake moment estimate

The next independent helper should consume the checked strict-level estimate
for every positive `lam`, without assuming that either endpoint constant is
nonzero. Its intended statement is:

```lean
private theorem strongInterpolation_layercake_moment_bound
    {s₀ s₁ A₀ A₁ η p : ℝ}
    (hs₀ : 0 < s₀) (hs₀p : s₀ < p) (hps₁ : p < s₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hη : 0 < η)
    (s : Finset ℤ) (f : ℤ → ℂ) (T : (ℤ → ℂ) → ℤ → ℝ)
    (hTnonneg : ∀ x, 0 ≤ T f x)
    (hdistribution : ∀ lam, 0 < lam →
      Measure.count {x : ℤ | 2 * lam < T f x} ≤
        ((ENNReal.ofReal A₀) ^ s₀ *
          (∑ x ∈ s.filter (fun x => η * lam < ‖f x‖), ‖f x‖ₑ ^ s₀)) /
            ((ENNReal.ofReal lam) ^ s₀) +
        ((ENNReal.ofReal A₁) ^ s₁ *
          (∑ x ∈ s.filter (fun x => ‖f x‖ ≤ η * lam), ‖f x‖ₑ ^ s₁)) /
            ((ENNReal.ofReal lam) ^ s₁)) :
    ∫⁻ x : ℤ, ENNReal.ofReal ((T f x) ^ p) ∂(Measure.count : Measure ℤ) ≤
      ENNReal.ofReal (2 ^ p *
        (p * A₀ ^ s₀ * η ^ (s₀ - p) / (p - s₀) +
         p * A₁ ^ s₁ * η ^ (s₁ - p) / (s₁ - p))) *
        (∑ x ∈ s, ‖f x‖ₑ ^ p)
```

The proof is the exact source operation: apply the project's
`integerSequence_lintegral_enorm_rpow_eq_lintegral_meas_lt` to the complex
sequence `x ↦ ((T f x / 2 : ℝ) : ℂ)`; its norm is `T f x / 2` by
nonnegativity. Multiply the level inequality by `p * 2^p * lam^(p-1)` and
integrate. Expand the two finite filtered sums as sums of `if` terms, then
use Tonelli/`lintegral_finsetSum`. For each input coordinate with
`a = ‖f x‖ > 0`, the high contribution is integrated on
`(0, a / η)` and the low contribution on `[a / η, ∞)`. Their scalar tails are
respectively
`p * a^s₀ * ∫₀^(a/η) t^(p-s₀-1) dt` and
`p * a^s₁ * ∫_(a/η)^∞ t^(p-s₁-1) dt`; these give precisely
`p * η^(s₀-p) * a^p / (p-s₀)` and
`p * η^(s₁-p) * a^p / (s₁-p)`. At `a = 0`, the strict high summand
vanishes and the low summand is zero because `s₁ > 0`. In the Lean
coordinate-integral proof, handle `a = 0` before applying the low-tail
identity: its unweighted tail at cutoff zero diverges, although its actual
integrand is identically zero after multiplication by `a^s₁`. For `a > 0`,
the cutoff `a / η` is positive and both tail lemmas apply. The closed/open
endpoint differences in the source ranges have volume zero.

The scalar tail integral lemmas `interpolation_lintegral_rpow_Ioi` / `_Ioc`
in `InterpolationWeightedLayercake.lean` apply after shifting their exponent
parameter; they are scalar helpers only, while the existing full finite-output
interpolation theorem there is convolution-specific.

After this moment helper, optimize only in the positive-endpoint branch with
`η = (A₀^s₀ / A₁^s₁)^(1/(s₁-s₀))`. For a zero endpoint, follow the approved
proof exactly: replace both constants by `Aᵢ + ε`, use that both final
endpoint powers are strictly positive, and pass to `ε ↓ 0`. This draft has
not been compiled and contributes no checked declaration.
-/

private theorem strongInterpolation_highIntegrand_measurable
    (η s₀ p : ℝ) (s : Finset ℤ) (f : ℤ → ℂ) :
    Measurable (fun t : ℝ =>
      ∑ x ∈ s, (if η * t < ‖f x‖ then ENNReal.ofReal ((‖f x‖) ^ s₀) else 0) *
        ENNReal.ofReal t ^ (p - s₀ - 1)) := by
  have hweight : Measurable (fun t : ℝ => ENNReal.ofReal t ^ (p - s₀ - 1)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  exact Finset.measurable_sum s (by
    intro x hx
    have hleft : Measurable (fun t : ℝ => η * t) := measurable_const.mul measurable_id
    have hright : Measurable (fun _t : ℝ => ‖f x‖) := measurable_const
    have hset : MeasurableSet {t : ℝ | η * t < ‖f x‖} := measurableSet_lt hleft hright
    exact (Measurable.ite hset measurable_const measurable_const).mul hweight)

private theorem strongInterpolation_lowIntegrand_measurable
    (η s₁ p : ℝ) (s : Finset ℤ) (f : ℤ → ℂ) :
    Measurable (fun t : ℝ =>
      ∑ x ∈ s, (if ‖f x‖ ≤ η * t then ENNReal.ofReal ((‖f x‖) ^ s₁) else 0) *
        ENNReal.ofReal t ^ (p - s₁ - 1)) := by
  have hweight : Measurable (fun t : ℝ => ENNReal.ofReal t ^ (p - s₁ - 1)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  exact Finset.measurable_sum s (by
    intro x hx
    have hleft : Measurable (fun _t : ℝ => ‖f x‖) := measurable_const
    have hright : Measurable (fun t : ℝ => η * t) := measurable_const.mul measurable_id
    have hset : MeasurableSet {t : ℝ | ‖f x‖ ≤ η * t} := measurableSet_le hleft hright
    exact (Measurable.ite hset measurable_const measurable_const).mul hweight)

private theorem strongInterpolation_highCoordinate_measurable
    (η s₀ p : ℝ) (f : ℤ → ℂ) (x : ℤ) :
    Measurable (fun t : ℝ =>
      (if η * t < ‖f x‖ then ENNReal.ofReal ((‖f x‖) ^ s₀) else 0) *
        ENNReal.ofReal t ^ (p - s₀ - 1)) := by
  have hleft : Measurable (fun t : ℝ => η * t) := measurable_const.mul measurable_id
  have hright : Measurable (fun _t : ℝ => ‖f x‖) := measurable_const
  have hset : MeasurableSet {t : ℝ | η * t < ‖f x‖} := measurableSet_lt hleft hright
  have hweight : Measurable (fun t : ℝ => ENNReal.ofReal t ^ (p - s₀ - 1)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  exact (Measurable.ite hset measurable_const measurable_const).mul hweight

private theorem strongInterpolation_lowCoordinate_measurable
    (η s₁ p : ℝ) (f : ℤ → ℂ) (x : ℤ) :
    Measurable (fun t : ℝ =>
      (if ‖f x‖ ≤ η * t then ENNReal.ofReal ((‖f x‖) ^ s₁) else 0) *
        ENNReal.ofReal t ^ (p - s₁ - 1)) := by
  have hleft : Measurable (fun _t : ℝ => ‖f x‖) := measurable_const
  have hright : Measurable (fun t : ℝ => η * t) := measurable_const.mul measurable_id
  have hset : MeasurableSet {t : ℝ | ‖f x‖ ≤ η * t} := measurableSet_le hleft hright
  have hweight : Measurable (fun t : ℝ => ENNReal.ofReal t ^ (p - s₁ - 1)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  exact (Measurable.ite hset measurable_const measurable_const).mul hweight

private theorem strongInterpolation_filteredSum_div_mul
    {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P]
    (z : α → ℝ≥0∞) (a d w : ℝ≥0∞) :
    ((a * (∑ x ∈ s.filter P, z x)) / d) * w =
      a * (∑ x ∈ s, if P x then z x * (w / d) else 0) := by
  classical
  calc
    ((a * (∑ x ∈ s.filter P, z x)) / d) * w =
        a * ((∑ x ∈ s.filter P, z x) * (d⁻¹ * w)) := by
          simp only [div_eq_mul_inv]
          ac_rfl
    _ = a * ∑ x ∈ s.filter P, z x * (d⁻¹ * w) := by rw [Finset.sum_mul]
    _ = a * ∑ x ∈ s, (if P x then z x else 0) * (d⁻¹ * w) := by
          rw [Finset.sum_filter]
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : P x <;> simp [h]
    _ = a * ∑ x ∈ s, if P x then z x * (d⁻¹ * w) else 0 := by
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : P x <;> simp [h]
    _ = a * ∑ x ∈ s, if P x then z x * (w * d⁻¹) else 0 := by
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : P x <;> simp [h, mul_comm]
    _ = a * (∑ x ∈ s, if P x then z x * (w / d) else 0) := by
          simp only [div_eq_mul_inv]

/-- Integrating the strict-level distribution estimate gives the exact
endpoint-weighted `p`-moment bound of approved `lm:interpolation`. The finite
input support, strict high cutoff, inclusive low cutoff, endpoint exponents,
and zero-endpoint cases are retained. -/
private theorem strongInterpolation_layercake_moment_bound
    {s₀ s₁ A₀ A₁ η p : ℝ}
    (hs₀ : 0 < s₀) (hs₀p : s₀ < p) (hps₁ : p < s₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hη : 0 < η)
    (s : Finset ℤ) (f : ℤ → ℂ) (T : (ℤ → ℂ) → ℤ → ℝ)
    (hTnonneg : ∀ x, 0 ≤ T f x)
    (hdistribution : ∀ lam, 0 < lam →
      Measure.count {x : ℤ | 2 * lam < T f x} ≤
        ((ENNReal.ofReal A₀) ^ s₀ *
          (∑ x ∈ s.filter (fun x => η * lam < ‖f x‖), ‖f x‖ₑ ^ s₀)) /
            ((ENNReal.ofReal lam) ^ s₀) +
        ((ENNReal.ofReal A₁) ^ s₁ *
          (∑ x ∈ s.filter (fun x => ‖f x‖ ≤ η * lam), ‖f x‖ₑ ^ s₁)) /
            ((ENNReal.ofReal lam) ^ s₁)) :
    ∫⁻ x : ℤ, ENNReal.ofReal ((T f x) ^ p) ∂(Measure.count : Measure ℤ) ≤
      ENNReal.ofReal (2 ^ p *
        (p * A₀ ^ s₀ * η ^ (s₀ - p) / (p - s₀) +
         p * A₁ ^ s₁ * η ^ (s₁ - p) / (s₁ - p))) *
        (∑ x ∈ s, ‖f x‖ₑ ^ p) := by
  classical
  have hp : 0 < p := lt_trans hs₀ hs₀p
  have hs₁ : 0 < s₁ := lt_trans hp hps₁
  let high : ℝ → ℝ≥0∞ := fun t =>
    ∑ x ∈ s, (if η * t < ‖f x‖ then ENNReal.ofReal ((‖f x‖) ^ s₀) else 0) *
      ENNReal.ofReal t ^ (p - s₀ - 1)
  let low : ℝ → ℝ≥0∞ := fun t =>
    ∑ x ∈ s, (if ‖f x‖ ≤ η * t then ENNReal.ofReal ((‖f x‖) ^ s₁) else 0) *
      ENNReal.ofReal t ^ (p - s₁ - 1)
  let C₀ : ℝ := A₀ ^ s₀ * η ^ (s₀ - p) / (p - s₀)
  let C₁ : ℝ := A₁ ^ s₁ * η ^ (s₁ - p) / (s₁ - p)
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    positivity
  have hweight₀ : Measurable (fun t : ℝ => ENNReal.ofReal t ^ (p - s₀ - 1)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  have hweight₁ : Measurable (fun t : ℝ => ENNReal.ofReal t ^ (p - s₁ - 1)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  have hhighMeas : Measurable high := by
    change Measurable (fun t : ℝ =>
      ∑ x ∈ s, (if η * t < ‖f x‖ then ENNReal.ofReal ((‖f x‖) ^ s₀) else 0) *
        ENNReal.ofReal t ^ (p - s₀ - 1))
    exact strongInterpolation_highIntegrand_measurable η s₀ p s f
  have hlowMeas : Measurable low := by
    change Measurable (fun t : ℝ =>
      ∑ x ∈ s, (if ‖f x‖ ≤ η * t then ENNReal.ofReal ((‖f x‖) ^ s₁) else 0) *
        ENNReal.ofReal t ^ (p - s₁ - 1))
    exact strongInterpolation_lowIntegrand_measurable η s₁ p s f
  have hpoint (t : ℝ) (ht : 0 < t) :
      Measure.count {x : ℤ | 2 * t < T f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
        (ENNReal.ofReal A₀) ^ s₀ * high t +
          (ENNReal.ofReal A₁) ^ s₁ * low t := by
    have hdist := hdistribution t ht
    have hmul₀ := mul_le_mul_right hdist (ENNReal.ofReal (t ^ (p - 1)))
    have hmul :
        Measure.count {x : ℤ | 2 * t < T f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
          ((((ENNReal.ofReal A₀) ^ s₀ *
            (∑ x ∈ s.filter (fun x => η * t < ‖f x‖), ‖f x‖ₑ ^ s₀)) /
              ((ENNReal.ofReal t) ^ s₀)) +
            (((ENNReal.ofReal A₁) ^ s₁ *
            (∑ x ∈ s.filter (fun x => ‖f x‖ ≤ η * t), ‖f x‖ₑ ^ s₁)) /
              ((ENNReal.ofReal t) ^ s₁))) * ENNReal.ofReal (t ^ (p - 1)) := by
      calc
        _ = ENNReal.ofReal (t ^ (p - 1)) *
            Measure.count {x : ℤ | 2 * t < T f x} := mul_comm _ _
        _ ≤ ENNReal.ofReal (t ^ (p - 1)) *
            ((((ENNReal.ofReal A₀) ^ s₀ *
              (∑ x ∈ s.filter (fun x => η * t < ‖f x‖), ‖f x‖ₑ ^ s₀)) /
                ((ENNReal.ofReal t) ^ s₀)) +
              (((ENNReal.ofReal A₁) ^ s₁ *
              (∑ x ∈ s.filter (fun x => ‖f x‖ ≤ η * t), ‖f x‖ₑ ^ s₁)) /
                ((ENNReal.ofReal t) ^ s₁))) := hmul₀
        _ = _ := mul_comm _ _
    have hhighRewrite :
        (((ENNReal.ofReal A₀) ^ s₀ *
          (∑ x ∈ s.filter (fun x => η * t < ‖f x‖), ‖f x‖ₑ ^ s₀)) /
            ((ENNReal.ofReal t) ^ s₀)) * ENNReal.ofReal (t ^ (p - 1)) =
          (ENNReal.ofReal A₀) ^ s₀ * high t := by
      rw [strongInterpolation_filteredSum_div_mul]
      rw [strongInterpolation_weight_rpow_div (p := p) (s := s₀) ht]
      have hnormPow (x : ℤ) : ‖f x‖ₑ ^ s₀ =
          ENNReal.ofReal ((‖f x‖) ^ s₀) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs₀.le
      simp only [high]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : η * t < ‖f x‖ <;> simp [h, hnormPow]
    have hlowRewrite :
        (((ENNReal.ofReal A₁) ^ s₁ *
          (∑ x ∈ s.filter (fun x => ‖f x‖ ≤ η * t), ‖f x‖ₑ ^ s₁)) /
            ((ENNReal.ofReal t) ^ s₁)) * ENNReal.ofReal (t ^ (p - 1)) =
          (ENNReal.ofReal A₁) ^ s₁ * low t := by
      rw [strongInterpolation_filteredSum_div_mul]
      rw [strongInterpolation_weight_rpow_div (p := p) (s := s₁) ht]
      have hnormPow (x : ℤ) : ‖f x‖ₑ ^ s₁ =
          ENNReal.ofReal ((‖f x‖) ^ s₁) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs₁.le
      simp only [low]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : ‖f x‖ ≤ η * t <;> simp [h, hnormPow]
    calc
      _ ≤
        ((((ENNReal.ofReal A₀) ^ s₀ *
          (∑ x ∈ s.filter (fun x => η * t < ‖f x‖), ‖f x‖ₑ ^ s₀)) /
            ((ENNReal.ofReal t) ^ s₀)) +
          (((ENNReal.ofReal A₁) ^ s₁ *
          (∑ x ∈ s.filter (fun x => ‖f x‖ ≤ η * t), ‖f x‖ₑ ^ s₁)) /
            ((ENNReal.ofReal t) ^ s₁))) * ENNReal.ofReal (t ^ (p - 1)) := hmul
      _ = _ := by rw [add_mul, hhighRewrite, hlowRewrite]
  have hhighIntegral :
      (∫⁻ t in Ioi (0 : ℝ), high t) =
        ∑ x ∈ s, ENNReal.ofReal
          (η ^ (s₀ - p) * (‖f x‖) ^ p / (p - s₀)) := by
    change (∫⁻ t in Ioi (0 : ℝ),
      ∑ x ∈ s,
        (if η * t < ‖f x‖ then ENNReal.ofReal ((‖f x‖) ^ s₀) else 0) *
          ENNReal.ofReal t ^ (p - s₀ - 1)) = _
    rw [lintegral_finsetSum s (by
      intro x hx
      exact strongInterpolation_highCoordinate_measurable η s₀ p f x)]
    apply Finset.sum_congr rfl
    intro x hx
    exact strongInterpolation_highCoordinateIntegral hs₀ hs₀p hη (norm_nonneg _)
  have hlowIntegral :
      (∫⁻ t in Ioi (0 : ℝ), low t) =
        ∑ x ∈ s, ENNReal.ofReal
          (η ^ (s₁ - p) * (‖f x‖) ^ p / (s₁ - p)) := by
    change (∫⁻ t in Ioi (0 : ℝ),
      ∑ x ∈ s,
        (if ‖f x‖ ≤ η * t then ENNReal.ofReal ((‖f x‖) ^ s₁) else 0) *
          ENNReal.ofReal t ^ (p - s₁ - 1)) = _
    rw [lintegral_finsetSum s (by
      intro x hx
      exact strongInterpolation_lowCoordinate_measurable η s₁ p f x)]
    apply Finset.sum_congr rfl
    intro x hx
    exact strongInterpolation_lowCoordinateIntegral hs₀ hs₀p hps₁ hη (norm_nonneg _)
  let inputMoment : ℝ≥0∞ := ∑ x ∈ s, ‖f x‖ₑ ^ p
  have hhighFactor :
      (ENNReal.ofReal A₀) ^ s₀ *
        (∑ x ∈ s, ENNReal.ofReal
          (η ^ (s₀ - p) * (‖f x‖) ^ p / (p - s₀))) =
        ENNReal.ofReal C₀ * inputMoment := by
    have hA : (ENNReal.ofReal A₀) ^ s₀ = ENNReal.ofReal (A₀ ^ s₀) :=
      ENNReal.ofReal_rpow_of_nonneg hA₀ hs₀.le
    have hD : 0 ≤ η ^ (s₀ - p) / (p - s₀) := by positivity
    have hC : C₀ = A₀ ^ s₀ * (η ^ (s₀ - p) / (p - s₀)) := by
      dsimp [C₀]
      ring
    rw [hA]
    simp only [inputMoment, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hnormPow : ‖f x‖ₑ ^ p = ENNReal.ofReal ((‖f x‖) ^ p) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le
    have hreal : η ^ (s₀ - p) * (‖f x‖) ^ p / (p - s₀) =
        (η ^ (s₀ - p) / (p - s₀)) * (‖f x‖) ^ p := by ring
    rw [hreal, ENNReal.ofReal_mul hD, ← hnormPow, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hA₀ s₀), ← hC]
  have hlowFactor :
      (ENNReal.ofReal A₁) ^ s₁ *
        (∑ x ∈ s, ENNReal.ofReal
          (η ^ (s₁ - p) * (‖f x‖) ^ p / (s₁ - p))) =
        ENNReal.ofReal C₁ * inputMoment := by
    have hA : (ENNReal.ofReal A₁) ^ s₁ = ENNReal.ofReal (A₁ ^ s₁) :=
      ENNReal.ofReal_rpow_of_nonneg hA₁ hs₁.le
    have hD : 0 ≤ η ^ (s₁ - p) / (s₁ - p) := by positivity
    have hC : C₁ = A₁ ^ s₁ * (η ^ (s₁ - p) / (s₁ - p)) := by
      dsimp [C₁]
      ring
    rw [hA]
    simp only [inputMoment, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hnormPow : ‖f x‖ₑ ^ p = ENNReal.ofReal ((‖f x‖) ^ p) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le
    have hreal : η ^ (s₁ - p) * (‖f x‖) ^ p / (s₁ - p) =
        (η ^ (s₁ - p) / (s₁ - p)) * (‖f x‖) ^ p := by ring
    rw [hreal, ENNReal.ofReal_mul hD, ← hnormPow, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hA₁ s₁), ← hC]
  have hintegrated :
      (∫⁻ t in Ioi (0 : ℝ),
        Measure.count {x : ℤ | 2 * t < T f x} * ENNReal.ofReal (t ^ (p - 1))) ≤
        ENNReal.ofReal (C₀ + C₁) * inputMoment := by
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal A₀) ^ s₀ * high t +
            (ENNReal.ofReal A₁) ^ s₁ * low t := by
          apply setLIntegral_mono_ae
            ((measurable_const.mul hhighMeas).add (measurable_const.mul hlowMeas)).aemeasurable
          filter_upwards [] with t ht
          exact hpoint t (mem_Ioi.mp ht)
      _ = (ENNReal.ofReal A₀) ^ s₀ * (∫⁻ t in Ioi (0 : ℝ), high t) +
          (ENNReal.ofReal A₁) ^ s₁ * (∫⁻ t in Ioi (0 : ℝ), low t) := by
          calc
            (∫⁻ t in Ioi (0 : ℝ),
                (ENNReal.ofReal A₀) ^ s₀ * high t +
                  (ENNReal.ofReal A₁) ^ s₁ * low t) =
              (∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal A₀) ^ s₀ * high t) +
                (∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal A₁) ^ s₁ * low t) := by
                  exact lintegral_add_right
                    (fun t : ℝ => (ENNReal.ofReal A₀) ^ s₀ * high t)
                    (g := fun t : ℝ => (ENNReal.ofReal A₁) ^ s₁ * low t)
                    (measurable_const.mul hlowMeas)
            _ = _ := by
                  rw [lintegral_const_mul _ hhighMeas, lintegral_const_mul _ hlowMeas]
      _ = ENNReal.ofReal C₀ * inputMoment + ENNReal.ofReal C₁ * inputMoment := by
          rw [hhighIntegral, hlowIntegral, ← hhighFactor, ← hlowFactor]
      _ = ENNReal.ofReal (C₀ + C₁) * inputMoment := by
          rw [← add_mul, ← ENNReal.ofReal_add hC₀ hC₁]
  have hscale := strongInterpolation_scaledLayercake hp (T f) hTnonneg
  have hmomentScaled :
      ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal p *
            (∫⁻ t in Ioi (0 : ℝ),
              Measure.count {x : ℤ | 2 * t < T f x} * ENNReal.ofReal (t ^ (p - 1)))) ≤
        ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal p * (ENNReal.ofReal (C₀ + C₁) * inputMoment)) := by
    have hpMul : ENNReal.ofReal p *
        (∫⁻ t in Ioi (0 : ℝ),
          Measure.count {x : ℤ | 2 * t < T f x} * ENNReal.ofReal (t ^ (p - 1))) ≤
          ENNReal.ofReal p * (ENNReal.ofReal (C₀ + C₁) * inputMoment) := by
      simpa only [mul_comm] using
        (mul_le_mul_right hintegrated (ENNReal.ofReal p))
    simpa only [mul_comm] using
      (mul_le_mul_right hpMul (ENNReal.ofReal (2 ^ p)))
  have hcoeff :
      ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal p * ENNReal.ofReal (C₀ + C₁)) =
        ENNReal.ofReal (2 ^ p *
          (p * A₀ ^ s₀ * η ^ (s₀ - p) / (p - s₀) +
           p * A₁ ^ s₁ * η ^ (s₁ - p) / (s₁ - p))) := by
    rw [← ENNReal.ofReal_mul hp.le]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ p)]
    congr 1
    dsimp [C₀, C₁]
    ring
  calc
    (∫⁻ x : ℤ, ENNReal.ofReal ((T f x) ^ p) ∂(Measure.count : Measure ℤ)) =
        ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal p *
            (∫⁻ t in Ioi (0 : ℝ),
              Measure.count {x : ℤ | 2 * t < T f x} * ENNReal.ofReal (t ^ (p - 1)))) := hscale
    _ ≤ ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal p * (ENNReal.ofReal (C₀ + C₁) * inputMoment)) := hmomentScaled
    _ = ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal p * ENNReal.ofReal (C₀ + C₁)) * inputMoment := by ac_rfl
    _ = _ := by rw [hcoeff]
    _ = _ := by rfl

private theorem strongInterpolation_positive_endpoints
    {s₀ p s₁ A₀ A₁ : ℝ}
    (hs₀ : 0 < s₀) (hs₀p : s₀ < p) (hps₁ : p < s₁)
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (s : Finset ℤ) (f : ℤ → ℂ) (T : (ℤ → ℂ) → ℤ → ℝ)
    (hTsub : ∀ g h, (∀ x ∉ s, g x = 0) → (∀ x ∉ s, h x = 0) →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (hTnonneg : ∀ g, (∀ x ∉ s, g x = 0) → ∀ x, 0 ≤ T g x)
    (hTbound₀ : ∀ g, (∀ x ∉ s, g x = 0) →
      eLpNorm (T g) (ENNReal.ofReal s₀) Measure.count ≤
        ENNReal.ofReal A₀ * eLpNorm g (ENNReal.ofReal s₀) Measure.count)
    (hTbound₁ : ∀ g, (∀ x ∉ s, g x = 0) →
      eLpNorm (T g) (ENNReal.ofReal s₁) Measure.count ≤
        ENNReal.ofReal A₁ * eLpNorm g (ENNReal.ofReal s₁) Measure.count)
    (hf : ∀ x ∉ s, f x = 0) :
    eLpNorm (T f) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal
        (2 * (p / (p - s₀) + p / (s₁ - p)) ^ (1 / p) *
          A₀ ^ (s₀ * (s₁ - p) / (p * (s₁ - s₀))) *
          A₁ ^ (1 - s₀ * (s₁ - p) / (p * (s₁ - s₀)))) *
        eLpNorm f (ENNReal.ofReal p) Measure.count := by
  classical
  let theta : ℝ := s₀ * (s₁ - p) / (p * (s₁ - s₀))
  let eta : ℝ := (A₀ ^ s₀ / A₁ ^ s₁) ^ (1 / (s₁ - s₀))
  let S : ℝ := p / (p - s₀) + p / (s₁ - p)
  let M : ℝ := A₀ ^ theta * A₁ ^ (1 - theta)
  let coeff : ℝ := 2 * S ^ (1 / p) * A₀ ^ theta * A₁ ^ (1 - theta)
  change eLpNorm (T f) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal coeff * eLpNorm f (ENNReal.ofReal p) Measure.count
  have hp : 0 < p := lt_trans hs₀ hs₀p
  have hs₁ : 0 < s₁ := lt_trans hp hps₁
  have heta : 0 < eta := by
    dsimp [eta]
    apply Real.rpow_pos_of_pos
    exact div_pos (Real.rpow_pos_of_pos hA₀ _) (Real.rpow_pos_of_pos hA₁ _)
  have hS : 0 < S := by
    dsimp [S]
    positivity
  have htheta : 0 < theta := by
    dsimp [theta]
    have hp : 0 < p := lt_trans hs₀ hs₀p
    have h₁p : 0 < s₁ - p := sub_pos.mpr hps₁
    have h₁₀ : 0 < s₁ - s₀ := sub_pos.mpr (lt_trans hs₀p hps₁)
    have hden : 0 < p * (s₁ - s₀) := mul_pos hp h₁₀
    exact div_pos (mul_pos hs₀ h₁p) hden
  have hthetaComplement : 0 < 1 - theta := by
    have hcompl : 1 - theta = s₁ * (p - s₀) / (p * (s₁ - s₀)) := by
      dsimp [theta]
      field_simp [ne_of_gt hp, ne_of_gt (sub_pos.mpr (lt_trans hs₀p hps₁))]
      <;> ring
    have h₁₀p : 0 < p - s₀ := sub_pos.mpr hs₀p
    have h₁₀ : 0 < s₁ - s₀ := sub_pos.mpr (lt_trans hs₀p hps₁)
    have hden : 0 < p * (s₁ - s₀) := mul_pos hp h₁₀
    rw [hcompl]
    exact div_pos (mul_pos hs₁ h₁₀p) hden
  have hopt :
      A₀ ^ s₀ * eta ^ (s₀ - p) = A₀ ^ (p * theta) * A₁ ^ (p * (1 - theta)) ∧
        A₁ ^ s₁ * eta ^ (s₁ - p) = A₀ ^ (p * theta) * A₁ ^ (p * (1 - theta)) := by
    simpa [theta, eta] using
      (strongInterpolation_optimized_endpoint_products hs₀ hs₀p hps₁ hA₀ hA₁)
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (Real.rpow_nonneg hA₀.le _) (Real.rpow_nonneg hA₁.le _)
  have hMpow : M ^ p = A₀ ^ (p * theta) * A₁ ^ (p * (1 - theta)) := by
    dsimp [M]
    rw [Real.mul_rpow (Real.rpow_nonneg hA₀.le _) (Real.rpow_nonneg hA₁.le _),
      ← Real.rpow_mul hA₀.le theta p,
      ← Real.rpow_mul hA₁.le (1 - theta) p]
    congr 1 <;> ring
  have hendpoint₀ : A₀ ^ s₀ * eta ^ (s₀ - p) = M ^ p := by
    calc
      _ = A₀ ^ (p * theta) * A₁ ^ (p * (1 - theta)) := hopt.1
      _ = M ^ p := by rw [hMpow]
  have hendpoint₁ : A₁ ^ s₁ * eta ^ (s₁ - p) = M ^ p := by
    calc
      _ = A₀ ^ (p * theta) * A₁ ^ (p * (1 - theta)) := hopt.2
      _ = M ^ p := by rw [hMpow]
  have hsum :
      p * A₀ ^ s₀ * eta ^ (s₀ - p) / (p - s₀) +
          p * A₁ ^ s₁ * eta ^ (s₁ - p) / (s₁ - p) = S * M ^ p := by
    calc
      _ = p / (p - s₀) * (A₀ ^ s₀ * eta ^ (s₀ - p)) +
          p / (s₁ - p) * (A₁ ^ s₁ * eta ^ (s₁ - p) ) := by ring
      _ = p / (p - s₀) * M ^ p + p / (s₁ - p) * M ^ p := by
        rw [hendpoint₀, hendpoint₁]
      _ = S * M ^ p := by dsimp [S]; ring
  have hSroot : (S ^ (1 / p)) ^ p = S := by
    rw [← Real.rpow_mul hS.le (1 / p) p]
    rw [show (1 / p) * p = 1 by field_simp [ne_of_gt hp]]
    exact Real.rpow_one _
  have hcoeffPow : coeff ^ p = 2 ^ p * (S * M ^ p) := by
    have hpowPair :
        (A₀ ^ theta) ^ p * (A₁ ^ (1 - theta)) ^ p = M ^ p := by
      calc
        _ = A₀ ^ (p * theta) * A₁ ^ (p * (1 - theta)) := by
          rw [← Real.rpow_mul hA₀.le theta p,
            ← Real.rpow_mul hA₁.le (1 - theta) p]
          congr 2 <;> ring
        _ = M ^ p := by rw [← hMpow]
    have hOuter : coeff ^ p = (2 * S ^ (1 / p) * A₀ ^ theta) ^ p *
        (A₁ ^ (1 - theta)) ^ p := by
      dsimp [coeff]
      exact Real.mul_rpow (z := p)
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (Real.rpow_nonneg hS.le (1 / p)))
          (Real.rpow_nonneg hA₀.le theta))
        (Real.rpow_nonneg hA₁.le (1 - theta))
    have hInner : (2 * S ^ (1 / p) * A₀ ^ theta) ^ p =
        (2 ^ p * (S ^ (1 / p)) ^ p) * (A₀ ^ theta) ^ p := by
      rw [Real.mul_rpow (z := p)
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
            (Real.rpow_nonneg hS.le (1 / p)))
          (Real.rpow_nonneg hA₀.le theta),
        Real.mul_rpow (z := p) (by norm_num : (0 : ℝ) ≤ 2)
          (Real.rpow_nonneg hS.le (1 / p))]
    calc
      coeff ^ p = (2 * S ^ (1 / p) * A₀ ^ theta) ^ p *
          (A₁ ^ (1 - theta)) ^ p := hOuter
      _ = (2 ^ p * (S ^ (1 / p)) ^ p) * (A₀ ^ theta) ^ p *
          (A₁ ^ (1 - theta)) ^ p := by
        rw [hInner]
      _ = 2 ^ p * (S * ((A₀ ^ theta) ^ p * (A₁ ^ (1 - theta)) ^ p)) := by
        rw [hSroot]
        ring
      _ = 2 ^ p * (S * M ^ p) := by
        rw [hpowPair]
  have hcoeff :
      2 ^ p * (p * A₀ ^ s₀ * eta ^ (s₀ - p) / (p - s₀) +
        p * A₁ ^ s₁ * eta ^ (s₁ - p) / (s₁ - p)) = coeff ^ p := by
    rw [hsum, hcoeffPow]
  have hdistribution : ∀ lam, 0 < lam →
      Measure.count {x : ℤ | 2 * lam < T f x} ≤
        ((ENNReal.ofReal A₀) ^ s₀ *
          (∑ x ∈ s.filter (fun x => eta * lam < ‖f x‖), ‖f x‖ₑ ^ s₀)) /
            ((ENNReal.ofReal lam) ^ s₀) +
        ((ENNReal.ofReal A₁) ^ s₁ *
          (∑ x ∈ s.filter (fun x => ‖f x‖ ≤ eta * lam), ‖f x‖ₑ ^ s₁)) /
            ((ENNReal.ofReal lam) ^ s₁) := by
    intro lam hlam
    exact strongInterpolation_strictLevelDistribution hs₀ hs₁ hA₀.le hA₁.le
      heta hlam s f T hTsub hTnonneg hTbound₀ hTbound₁ hf
  have hmoment := strongInterpolation_layercake_moment_bound
    hs₀ hs₀p hps₁ hA₀.le hA₁.le heta s f T (hTnonneg f hf) hdistribution
  rw [hcoeff] at hmoment
  have hpENN0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpENNTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hTmeas : AEStronglyMeasurable (T f) Measure.count :=
    (measurable_of_countable _).aestronglyMeasurable
  have houtputPower :
      eLpNorm (T f) (ENNReal.ofReal p) Measure.count ^ p =
        ∫⁻ x : ℤ, ENNReal.ofReal ((T f x) ^ p) ∂(Measure.count : Measure ℤ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpENN0 hpENNTop hTmeas,
      ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul,
      one_div_mul_cancel hp.ne', ENNReal.rpow_one]
    apply lintegral_congr_ae
    filter_upwards [] with x
    have hnorm : ‖T f x‖ₑ = ENNReal.ofReal (T f x) := by
      rw [← ofReal_norm, Real.norm_of_nonneg (hTnonneg f hf x)]
    rw [hnorm]
    exact ENNReal.ofReal_rpow_of_nonneg (hTnonneg f hf x) hp.le
  have hinputPower :
      eLpNorm f (ENNReal.ofReal p) Measure.count ^ p =
        ∑ x ∈ s, ‖f x‖ₑ ^ p := eLpNorm_rpow_eq_sum_of_supported hp s f hf
  have hfactor :
      ENNReal.ofReal (coeff ^ p) * (∑ x ∈ s, ‖f x‖ₑ ^ p) =
        (ENNReal.ofReal coeff * eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ coeff) hp.le,
      ← hinputPower]
    exact (ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal coeff)
      (eLpNorm f (ENNReal.ofReal p) Measure.count) hp.le).symm
  have hpowered :
      eLpNorm (T f) (ENNReal.ofReal p) Measure.count ^ p ≤
        (ENNReal.ofReal coeff * eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p := by
    calc
      _ = ∫⁻ x : ℤ, ENNReal.ofReal ((T f x) ^ p) ∂(Measure.count : Measure ℤ) := houtputPower
      _ ≤ ENNReal.ofReal (coeff ^ p) * (∑ x ∈ s, ‖f x‖ₑ ^ p) := hmoment
      _ = _ := hfactor
  have hp_exp : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  exact (ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hpENN0 hpENNTop)).mp
    (by simpa [hp_exp] using hpowered)

private theorem strongInterpolation_endpoint_limit
    {s₀ p s₁ A₀ A₁ : ℝ}
    (hs₀ : 1 ≤ s₀) (hs₀p : s₀ < p) (hps₁ : p < s₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (s : Finset ℤ) (f : ℤ → ℂ) (T : (ℤ → ℂ) → ℤ → ℝ)
    (hTsub : ∀ g h, (∀ x ∉ s, g x = 0) → (∀ x ∉ s, h x = 0) →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (hTnonneg : ∀ g, (∀ x ∉ s, g x = 0) → ∀ x, 0 ≤ T g x)
    (hTbound₀ : ∀ g, (∀ x ∉ s, g x = 0) →
      eLpNorm (T g) (ENNReal.ofReal s₀) Measure.count ≤
        ENNReal.ofReal A₀ * eLpNorm g (ENNReal.ofReal s₀) Measure.count)
    (hTbound₁ : ∀ g, (∀ x ∉ s, g x = 0) →
      eLpNorm (T g) (ENNReal.ofReal s₁) Measure.count ≤
        ENNReal.ofReal A₁ * eLpNorm g (ENNReal.ofReal s₁) Measure.count)
    (hf : ∀ x ∉ s, f x = 0) :
    eLpNorm (T f) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal
        (2 * (p / (p - s₀) + p / (s₁ - p)) ^ (1 / p) *
          A₀ ^ (s₀ * (s₁ - p) / (p * (s₁ - s₀))) *
          A₁ ^ (1 - s₀ * (s₁ - p) / (p * (s₁ - s₀)))) *
        eLpNorm f (ENNReal.ofReal p) Measure.count := by
  classical
  let theta : ℝ := s₀ * (s₁ - p) / (p * (s₁ - s₀))
  let S : ℝ := p / (p - s₀) + p / (s₁ - p)
  let K : ℝ := 2 * S ^ (1 / p)
  let coeffEps : ℝ → ℝ := fun ε =>
    K * (A₀ + ε) ^ theta * (A₁ + ε) ^ (1 - theta)
  let coeff₀ : ℝ := K * A₀ ^ theta * A₁ ^ (1 - theta)
  change eLpNorm (T f) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal coeff₀ * eLpNorm f (ENNReal.ofReal p) Measure.count
  have hs₀pos : 0 < s₀ := lt_of_lt_of_le zero_lt_one hs₀
  have hp : 0 < p := lt_trans hs₀pos hs₀p
  have hs₁ : 0 < s₁ := lt_trans hp hps₁
  have hden : 0 < p * (s₁ - s₀) :=
    mul_pos hp (sub_pos.mpr (lt_trans hs₀p hps₁))
  have hthetaPos : 0 < theta := by
    dsimp [theta]
    positivity
  have hthetaComplement : 0 < 1 - theta := by
    have hcompl : 1 - theta = s₁ * (p - s₀) / (p * (s₁ - s₀)) := by
      dsimp [theta]
      field_simp [ne_of_gt hp, ne_of_gt (sub_pos.mpr (lt_trans hs₀p hps₁))]
      <;> ring
    rw [hcompl]
    positivity
  have hpENN0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpENNTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpOne : 1 ≤ p := le_of_lt (lt_of_le_of_lt hs₀ hs₀p)
  have hpENNOne : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hpOne
  have hrep : f = fun x => if x ∈ s then f x else 0 := by
    funext x
    by_cases hx : x ∈ s
    · simp [hx]
    · simp [hx, hf x hx]
  have hmemTrunc :
      MemLp (fun x : ℤ => if x ∈ s then f x else 0)
        (ENNReal.ofReal p) Measure.count :=
    finiteSupportMemLpGeneral hpENN0 hpENNTop hpENNOne s f
  have hmem : MemLp f (ENNReal.ofReal p) Measure.count := by
    rw [hrep]
    exact hmemTrunc
  have hinputNeTop : eLpNorm f (ENNReal.ofReal p) Measure.count ≠ ∞ :=
    hmem.eLpNorm_ne_top
  have hboundEps : ∀ ε, 0 < ε →
      eLpNorm (T f) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (coeffEps ε) * eLpNorm f (ENNReal.ofReal p) Measure.count := by
    intro ε hε
    have hA₀ε : 0 < A₀ + ε := by positivity
    have hA₁ε : 0 < A₁ + ε := by positivity
    have hTbound₀ε : ∀ g, (∀ x ∉ s, g x = 0) →
        eLpNorm (T g) (ENNReal.ofReal s₀) Measure.count ≤
          ENNReal.ofReal (A₀ + ε) * eLpNorm g (ENNReal.ofReal s₀) Measure.count := by
      intro g hg
      calc
        eLpNorm (T g) (ENNReal.ofReal s₀) Measure.count ≤
            ENNReal.ofReal A₀ * eLpNorm g (ENNReal.ofReal s₀) Measure.count :=
          hTbound₀ g hg
        _ ≤ ENNReal.ofReal (A₀ + ε) * eLpNorm g (ENNReal.ofReal s₀) Measure.count :=
          by simpa only [mul_comm] using
            (mul_le_mul_right
              (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hε.le))
              (eLpNorm g (ENNReal.ofReal s₀) Measure.count))
    have hTbound₁ε : ∀ g, (∀ x ∉ s, g x = 0) →
        eLpNorm (T g) (ENNReal.ofReal s₁) Measure.count ≤
          ENNReal.ofReal (A₁ + ε) * eLpNorm g (ENNReal.ofReal s₁) Measure.count := by
      intro g hg
      calc
        eLpNorm (T g) (ENNReal.ofReal s₁) Measure.count ≤
            ENNReal.ofReal A₁ * eLpNorm g (ENNReal.ofReal s₁) Measure.count :=
          hTbound₁ g hg
        _ ≤ ENNReal.ofReal (A₁ + ε) * eLpNorm g (ENNReal.ofReal s₁) Measure.count :=
          by simpa only [mul_comm] using
            (mul_le_mul_right
              (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hε.le))
              (eLpNorm g (ENNReal.ofReal s₁) Measure.count))
    simpa [coeffEps, theta, S, K] using
      (strongInterpolation_positive_endpoints hs₀pos hs₀p hps₁ hA₀ε hA₁ε
        s f T hTsub hTnonneg hTbound₀ε hTbound₁ε hf)
  have hA₀tendsto : Tendsto (fun ε : ℝ => A₀ + ε) (𝓝 0) (𝓝 A₀) :=
    by
      have hconst : Tendsto (fun _ : ℝ => A₀) (𝓝 0) (𝓝 A₀) := tendsto_const_nhds
      have hid : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0) := tendsto_id
      simpa only [Function.id_def, add_zero] using hconst.add hid
  have hA₁tendsto : Tendsto (fun ε : ℝ => A₁ + ε) (𝓝 0) (𝓝 A₁) :=
    by
      have hconst : Tendsto (fun _ : ℝ => A₁) (𝓝 0) (𝓝 A₁) := tendsto_const_nhds
      have hid : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0) := tendsto_id
      simpa only [Function.id_def, add_zero] using hconst.add hid
  have hpow₀ : Tendsto (fun ε : ℝ => (A₀ + ε) ^ theta) (𝓝 0) (𝓝 (A₀ ^ theta)) :=
    (Real.continuousAt_rpow_const A₀ theta (Or.inr hthetaPos.le)).tendsto.comp hA₀tendsto
  have hpow₁ : Tendsto (fun ε : ℝ => (A₁ + ε) ^ (1 - theta)) (𝓝 0)
      (𝓝 (A₁ ^ (1 - theta))) :=
    (Real.continuousAt_rpow_const A₁ (1 - theta)
      (Or.inr hthetaComplement.le)).tendsto.comp hA₁tendsto
  have hcoeffTendsto : Tendsto coeffEps (𝓝 0) (𝓝 coeff₀) := by
    simpa [coeffEps, coeff₀, K, S] using
      (tendsto_const_nhds.mul hpow₀).mul hpow₁
  have hRhsTendsto :
      Tendsto (fun ε : ℝ => ENNReal.ofReal (coeffEps ε) *
          eLpNorm f (ENNReal.ofReal p) Measure.count)
        (𝓝 0)
        (𝓝 (ENNReal.ofReal coeff₀ * eLpNorm f (ENNReal.ofReal p) Measure.count)) := by
    have hcont : Continuous (fun x : ℝ => ENNReal.ofReal x *
        eLpNorm f (ENNReal.ofReal p) Measure.count) :=
      (ENNReal.continuous_mul_const hinputNeTop).comp ENNReal.continuous_ofReal
    exact (hcont.tendsto coeff₀).comp hcoeffTendsto
  let εseq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεseq : Tendsto εseq atTop (𝓝 0) := by
    simpa [εseq] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hboundSeq : ∀ n,
      eLpNorm (T f) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (coeffEps (εseq n)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count := by
    intro n
    apply hboundEps
    dsimp [εseq]
    positivity
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hRhsTendsto.comp hεseq) hboundSeq

/-- Internal fixed-support form of the interpolation estimate. Its hypotheses
are localized to a common finite support set so the distribution and moment
proofs can use exact finite sums. -/
private theorem strongInterpolation_on_finset
    {s₀ p s₁ A₀ A₁ : ℝ}
    (hs₀ : 1 ≤ s₀) (hs₀p : s₀ < p) (hps₁ : p < s₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (s : Finset ℤ) (f : ℤ → ℂ) (T : (ℤ → ℂ) → ℤ → ℝ)
    (hTsub : ∀ g h, (∀ x ∉ s, g x = 0) → (∀ x ∉ s, h x = 0) →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (hTnonneg : ∀ g, (∀ x ∉ s, g x = 0) → ∀ x, 0 ≤ T g x)
    (hTbound₀ : ∀ g, (∀ x ∉ s, g x = 0) →
      eLpNorm (T g) (ENNReal.ofReal s₀) Measure.count ≤
        ENNReal.ofReal A₀ * eLpNorm g (ENNReal.ofReal s₀) Measure.count)
    (hTbound₁ : ∀ g, (∀ x ∉ s, g x = 0) →
      eLpNorm (T g) (ENNReal.ofReal s₁) Measure.count ≤
        ENNReal.ofReal A₁ * eLpNorm g (ENNReal.ofReal s₁) Measure.count)
    (hf : ∀ x ∉ s, f x = 0) :
    eLpNorm (T f) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal
        (2 * (p / (p - s₀) + p / (s₁ - p)) ^ (1 / p) *
          A₀ ^ (s₀ * (s₁ - p) / (p * (s₁ - s₀))) *
          A₁ ^ (1 - s₀ * (s₁ - p) / (p * (s₁ - s₀)))) *
        eLpNorm f (ENNReal.ofReal p) Measure.count := by
  have hs₀pos : 0 < s₀ := lt_of_lt_of_le zero_lt_one hs₀
  by_cases hA₀pos : 0 < A₀
  · by_cases hA₁pos : 0 < A₁
    · exact strongInterpolation_positive_endpoints hs₀pos hs₀p hps₁
        hA₀pos hA₁pos s f T hTsub hTnonneg hTbound₀ hTbound₁ hf
    · exact strongInterpolation_endpoint_limit hs₀ hs₀p hps₁
        hA₀ hA₁ s f T hTsub hTnonneg hTbound₀ hTbound₁ hf
  · exact strongInterpolation_endpoint_limit hs₀ hs₀p hps₁
      hA₀ hA₁ s f T hTsub hTnonneg hTbound₀ hTbound₁ hf

/-- Blueprint `lm:interpolation`: the finite-support strong interpolation
bound, with the endpoint threshold and optimizer constants from the approved
source. The zero-endpoint cases use the source-prescribed `Aᵢ + ε` limit. -/
theorem strongInterpolation
    {s₀ p s₁ A₀ A₁ : ℝ}
    (hs₀ : 1 ≤ s₀) (hs₀p : s₀ < p) (hps₁ : p < s₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (T : (ℤ → ℂ) → ℤ → ℝ)
    (hTsub : ∀ g h, g.HasFiniteSupport → h.HasFiniteSupport →
      ∀ x, T (g + h) x ≤ T g x + T h x)
    (hTnonneg : ∀ g, g.HasFiniteSupport → ∀ x, 0 ≤ T g x)
    (hTbound₀ : ∀ g, g.HasFiniteSupport →
      eLpNorm (T g) (ENNReal.ofReal s₀) Measure.count ≤
        ENNReal.ofReal A₀ * eLpNorm g (ENNReal.ofReal s₀) Measure.count)
    (hTbound₁ : ∀ g, g.HasFiniteSupport →
      eLpNorm (T g) (ENNReal.ofReal s₁) Measure.count ≤
        ENNReal.ofReal A₁ * eLpNorm g (ENNReal.ofReal s₁) Measure.count)
    (f : ℤ → ℂ) (hf : f.HasFiniteSupport) :
    eLpNorm (T f) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal
        (2 * (p / (p - s₀) + p / (s₁ - p)) ^ (1 / p) *
          A₀ ^ (s₀ * (s₁ - p) / (p * (s₁ - s₀))) *
          A₁ ^ (1 - s₀ * (s₁ - p) / (p * (s₁ - s₀)))) *
        eLpNorm f (ENNReal.ofReal p) Measure.count := by
  classical
  let s : Finset ℤ := hf.toFinset
  have hfOn : ∀ x ∉ s, f x = 0 := by
    intro x hx
    by_contra hfx
    exact hx (hf.mem_toFinset.mpr (Function.mem_support.mpr hfx))
  have supportedFinite {g : ℤ → ℂ} (hg : ∀ x ∉ s, g x = 0) :
      g.HasFiniteSupport := by
    refine s.finite_toSet.subset ?_
    intro x hx
    by_contra hxs
    exact (Function.mem_support.mp hx) (hg x hxs)
  have hTsub' : ∀ g h, (∀ x ∉ s, g x = 0) → (∀ x ∉ s, h x = 0) →
      ∀ x, T (g + h) x ≤ T g x + T h x := by
    intro g h hg hh x
    exact hTsub g h (supportedFinite hg) (supportedFinite hh) x
  have hTnonneg' : ∀ g, (∀ x ∉ s, g x = 0) → ∀ x, 0 ≤ T g x := by
    intro g hg x
    exact hTnonneg g (supportedFinite hg) x
  have hTbound₀' : ∀ g, (∀ x ∉ s, g x = 0) →
      eLpNorm (T g) (ENNReal.ofReal s₀) Measure.count ≤
        ENNReal.ofReal A₀ * eLpNorm g (ENNReal.ofReal s₀) Measure.count := by
    intro g hg
    exact hTbound₀ g (supportedFinite hg)
  have hTbound₁' : ∀ g, (∀ x ∉ s, g x = 0) →
      eLpNorm (T g) (ENNReal.ofReal s₁) Measure.count ≤
        ENNReal.ofReal A₁ * eLpNorm g (ENNReal.ofReal s₁) Measure.count := by
    intro g hg
    exact hTbound₁ g (supportedFinite hg)
  exact strongInterpolation_on_finset hs₀ hs₀p hps₁ hA₀ hA₁ s f T
    hTsub' hTnonneg' hTbound₀' hTbound₁' hfOn

end FractionalPrimes.Literature.MSZ
