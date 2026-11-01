module

public import FractionalPrimes.Literature.JSW.Conventions
public import FractionalPrimes.Literature.Variation.LayerCakeInterpolation
public import FractionalPrimes.Literature.Variation.LayerCakeInputDensity
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Quantitative real interpolation

This module formalizes the two-endpoint weak-type interpolation estimate in
`lj:interpolation`, including its finite-vector interpretation, its
strong-`L²`/strong-`L∞` corollary, and the bounded finite-support density
interface used to extend estimates.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The lower endpoint interpolation weight in `lj:interpolation`. -/
def weakTypeInterpolationTheta0 (s₀ p s₁ : ℝ) : ℝ :=
  s₀ * (s₁ - p) / (p * (s₁ - s₀))

/-- The upper endpoint interpolation weight in `lj:interpolation`. -/
def weakTypeInterpolationTheta1 (s₀ p s₁ : ℝ) : ℝ :=
  s₁ * (p - s₀) / (p * (s₁ - s₀))

/-- The exact interpolation constant displayed in `lj:interpolation`. -/
def weakTypeInterpolationConstant (s₀ p s₁ : ℝ) : ℝ :=
  2 * (p * (1 / (p - s₀) + 1 / (s₁ - p))) ^ (1 / p)

/-- A nonnegative scalar-output operator on bounded measurable inputs with
finite-measure support, equipped with positive homogeneity, subadditivity,
and two weak-type estimates. The weak estimates are written as the endpoint
constant to the endpoint exponent times the corresponding input moment and
threshold power, exactly equivalent to
`(Aᵢ ‖f‖_{sᵢ} / t) ^ sᵢ`. -/
structure WeakTypeInterpolationOperator
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s₀ s₁ A₀ A₁ : ℝ) where
  apply : Variation.LayerCakeInput μ → X → ℝ
  measurable_apply : ∀ f, Measurable (apply f)
  nonneg_apply : ∀ f x, 0 ≤ apply f x
  subadditive : ∀ (f g : Variation.LayerCakeInput μ)
      (hfg : Variation.LayerCakeAdmissible μ (f.1 + g.1)) (x : X),
      apply ⟨f.1 + g.1, hfg⟩ x ≤ apply f x + apply g x
  positive_homogeneous : ∀ (f : Variation.LayerCakeInput μ) (c : ℝ) (_hc : 0 ≤ c)
      (hcf : Variation.LayerCakeAdmissible μ (c • f.1)) (x : X),
      apply ⟨c • f.1, hcf⟩ x = c * apply f x
  weak_s₀ : ∀ (f : Variation.LayerCakeInput μ) (t : ℝ), 0 < t →
      μ {x | t < apply f x} ≤
        (ENNReal.ofReal A₀).rpow s₀ * (ENNReal.ofReal t).rpow (-s₀) *
          Variation.complexLpMoment s₀ μ f.1
  weak_s₁ : ∀ (f : Variation.LayerCakeInput μ) (t : ℝ), 0 < t →
      μ {x | t < apply f x} ≤
        (ENNReal.ofReal A₁).rpow s₁ * (ENNReal.ofReal t).rpow (-s₁) *
          Variation.complexLpMoment s₁ μ f.1

/-- Splitting an input at `c*t` turns subadditivity into the exact union
bound used by the two-endpoint layer-cake proof. -/
theorem weakTypeInterpolation_levelSplit
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {s₀ s₁ A₀ A₁ : ℝ}
    (U : WeakTypeInterpolationOperator μ s₀ s₁ A₀ A₁)
    (f : Variation.LayerCakeInput μ) (t c : ℝ) (ht : 0 < t) :
    μ {x | 2 * t < U.apply f x} ≤
      (ENNReal.ofReal A₀).rpow s₀ * (ENNReal.ofReal t).rpow (-s₀) *
          Variation.complexLpMoment s₀ μ (Variation.layerCakeHighCutoff (c * t) f.1) +
        (ENNReal.ofReal A₁).rpow s₁ * (ENNReal.ofReal t).rpow (-s₁) *
          Variation.complexLpMoment s₁ μ (Variation.layerCakeLowCutoff (c * t) f.1) := by
  let highFn := Variation.layerCakeHighCutoff (c * t) f.1
  let lowFn := Variation.layerCakeLowCutoff (c * t) f.1
  have hsplit : highFn + lowFn = f.1 := by
    funext x
    by_cases hx : c * t < ‖f.1 x‖
    · have hx' : ¬ ‖f.1 x‖ ≤ c * t := not_le_of_gt hx
      simp [highFn, lowFn, Variation.layerCakeHighCutoff,
        Variation.layerCakeLowCutoff, hx, hx']
    · have hx' : ‖f.1 x‖ ≤ c * t := le_of_not_gt hx
      simp [highFn, lowFn, Variation.layerCakeHighCutoff,
        Variation.layerCakeLowCutoff, hx, hx']
  have hsum : Variation.LayerCakeAdmissible μ (highFn + lowFn) := by
    rw [hsplit]
    exact f.2
  let highInput : Variation.LayerCakeInput μ :=
    ⟨highFn, Variation.layerCakeAdmissible_highCutoff μ (c * t) f.2⟩
  let lowInput : Variation.LayerCakeInput μ :=
    ⟨lowFn, Variation.layerCakeAdmissible_lowCutoff μ (c * t) f.2⟩
  have hsumEq : (⟨highFn + lowFn, hsum⟩ : Variation.LayerCakeInput μ) = f :=
    Subtype.ext hsplit
  have hsub (x : X) : U.apply f x ≤ U.apply highInput x + U.apply lowInput x := by
    rw [← hsumEq]
    exact U.subadditive highInput lowInput hsum x
  have hset : {x | 2 * t < U.apply f x} ⊆
      {x | t < U.apply highInput x} ∪ {x | t < U.apply lowInput x} := by
    intro x hx
    by_cases hhigh : t < U.apply highInput x
    · exact Or.inl hhigh
    · by_cases hlow : t < U.apply lowInput x
      · exact Or.inr hlow
      · have hhigh' : U.apply highInput x ≤ t := le_of_not_gt hhigh
        have hlow' : U.apply lowInput x ≤ t := le_of_not_gt hlow
        have hbound : U.apply f x ≤ 2 * t := by
          calc
            U.apply f x ≤ U.apply highInput x + U.apply lowInput x := hsub x
            _ ≤ t + t := add_le_add hhigh' hlow'
            _ = 2 * t := by ring
        exfalso
        exact (not_lt_of_ge hbound) hx
  calc
    μ {x | 2 * t < U.apply f x} ≤
        μ ({x | t < U.apply highInput x} ∪ {x | t < U.apply lowInput x}) :=
      measure_mono hset
    _ ≤ μ {x | t < U.apply highInput x} + μ {x | t < U.apply lowInput x} :=
      measure_union_le _ _
    _ ≤ (ENNReal.ofReal A₀).rpow s₀ * (ENNReal.ofReal t).rpow (-s₀) *
          Variation.complexLpMoment s₀ μ highFn +
        (ENNReal.ofReal A₁).rpow s₁ * (ENNReal.ofReal t).rpow (-s₁) *
          Variation.complexLpMoment s₁ μ lowFn := by
      exact add_le_add (U.weak_s₀ highInput t ht) (U.weak_s₁ lowInput t ht)

private def weakTypeInterpolationHighMoment
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s₀ W : ℝ)
    (f : X → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (if t < W * ‖f x‖ then
    (ENNReal.ofReal (W * ‖f x‖)).rpow s₀ else 0) ∂μ

private def weakTypeInterpolationLowMoment
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s₁ W : ℝ)
    (f : X → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (if W * ‖f x‖ ≤ t then
    (ENNReal.ofReal (W * ‖f x‖)).rpow s₁ else 0) ∂μ

private def weakTypeInterpolationHighWeighted
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s₀ p W A₀ : ℝ) (f : X → ℂ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (A₀ / W)).rpow s₀ *
    weakTypeInterpolationHighMoment μ s₀ W f t *
      (ENNReal.ofReal t).rpow (p - s₀ - 1)

private def weakTypeInterpolationLowWeighted
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p s₁ W A₁ : ℝ) (f : X → ℂ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (A₁ / W)).rpow s₁ *
    weakTypeInterpolationLowMoment μ s₁ W f t *
      ENNReal.ofReal t ^ (p - s₁ - 1)

private def weakTypeInterpolationHighKernel
    {X : Type*} (s₀ p W A₀ : ℝ) (f : X → ℂ) (t : ℝ) (x : X) : ℝ≥0∞ :=
  if t < W * ‖f x‖ then
    (ENNReal.ofReal (A₀ / W)).rpow s₀ *
      (ENNReal.ofReal (W * ‖f x‖)).rpow s₀ *
        ENNReal.ofReal t ^ (p - s₀ - 1)
  else 0

private def weakTypeInterpolationLowKernel
    {X : Type*} (p s₁ W A₁ : ℝ) (f : X → ℂ) (t : ℝ) (x : X) : ℝ≥0∞ :=
  if W * ‖f x‖ ≤ t then
    (ENNReal.ofReal (A₁ / W)).rpow s₁ *
      (ENNReal.ofReal (W * ‖f x‖)).rpow s₁ *
        ENNReal.ofReal t ^ (p - s₁ - 1)
  else 0

private theorem measurable_weakTypeInterpolationHighMoment
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s₀ W : ℝ)
    (f : X → ℂ) :
    Measurable (weakTypeInterpolationHighMoment μ s₀ W f) := by
  apply Antitone.measurable
  intro a b hab
  unfold weakTypeInterpolationHighMoment
  apply lintegral_mono
  intro x
  by_cases hb : b < W * ‖f x‖
  · have ha : a < W * ‖f x‖ := hab.trans_lt hb
    simp [ha, hb]
  · simp [hb]

private theorem measurable_weakTypeInterpolationLowMoment
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s₁ W : ℝ)
    (f : X → ℂ) :
    Measurable (weakTypeInterpolationLowMoment μ s₁ W f) := by
  apply Monotone.measurable
  intro a b hab
  unfold weakTypeInterpolationLowMoment
  apply lintegral_mono
  intro x
  by_cases ha : W * ‖f x‖ ≤ a
  · have hb : W * ‖f x‖ ≤ b := ha.trans hab
    simp [ha, hb]
  · simp [ha]

private theorem measurable_weakTypeInterpolationHighWeighted
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s₀ p W A₀ : ℝ) (f : X → ℂ) :
    Measurable (weakTypeInterpolationHighWeighted μ s₀ p W A₀ f) := by
  have hfactor : Measurable (fun t : ℝ => (ENNReal.ofReal t).rpow (p - s₀ - 1)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  exact ((measurable_const.mul
      (measurable_weakTypeInterpolationHighMoment μ s₀ W f)).mul hfactor)

private theorem measurable_weakTypeInterpolationLowWeighted
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p s₁ W A₁ : ℝ) (f : X → ℂ) :
    Measurable (weakTypeInterpolationLowWeighted μ p s₁ W A₁ f) := by
  have hfactor : Measurable (fun t : ℝ => (ENNReal.ofReal t).rpow (p - s₁ - 1)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  exact ((measurable_const.mul
      (measurable_weakTypeInterpolationLowMoment μ s₁ W f)).mul hfactor)

private theorem weakTypeInterpolation_measurableSet_nonzero
    {X : Type*} [MeasurableSpace X] {f : X → ℂ} (hf : Measurable f) :
    MeasurableSet {x | f x ≠ 0} := by
  have hz : MeasurableSet {x | f x = (0 : ℂ)} :=
    measurableSet_eq_fun hf measurable_const
  have heq : {x | f x ≠ 0} = {x | f x = (0 : ℂ)}ᶜ := by
    ext x
    simp
  rw [heq]
  exact hz.compl

private theorem weakTypeInterpolation_lintegral_eq_restrict_of_zero_outside
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (g : X → ℝ≥0∞)
    (hzero : ∀ x, x ∉ s → g x = 0) :
    (∫⁻ x, g x ∂μ) = ∫⁻ x, g x ∂(μ.restrict s) := by
  calc
    (∫⁻ x, g x ∂μ) = ∫⁻ x, s.indicator g x ∂μ := by
      apply lintegral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ s
      · simp [hx]
      · simp [hx, hzero x hx]
    _ = ∫⁻ x in s, g x ∂μ := by rw [lintegral_indicator hs]
    _ = ∫⁻ x, g x ∂(μ.restrict s) := rfl

private theorem weakTypeInterpolation_highMoment_restrict_support
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s₀ W : ℝ}
    (hs₀ : 0 < s₀) (f : X → ℂ) (hf : Measurable f) (t : ℝ) :
    weakTypeInterpolationHighMoment μ s₀ W f t =
      weakTypeInterpolationHighMoment (μ.restrict {x | f x ≠ 0}) s₀ W f t := by
  have hs : MeasurableSet {x | f x ≠ 0} :=
    weakTypeInterpolation_measurableSet_nonzero hf
  unfold weakTypeInterpolationHighMoment
  exact weakTypeInterpolation_lintegral_eq_restrict_of_zero_outside μ _ hs _ (by
    intro x hx
    have hfx : f x = 0 := by simpa using hx
    simp [hfx, ENNReal.zero_rpow_of_pos hs₀])

private theorem weakTypeInterpolation_lowMoment_restrict_support
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s₁ W : ℝ}
    (hs₁ : 0 < s₁) (f : X → ℂ) (hf : Measurable f) (t : ℝ) :
    weakTypeInterpolationLowMoment μ s₁ W f t =
      weakTypeInterpolationLowMoment (μ.restrict {x | f x ≠ 0}) s₁ W f t := by
  have hs : MeasurableSet {x | f x ≠ 0} :=
    weakTypeInterpolation_measurableSet_nonzero hf
  unfold weakTypeInterpolationLowMoment
  exact weakTypeInterpolation_lintegral_eq_restrict_of_zero_outside μ _ hs _ (by
    intro x hx
    have hfx : f x = 0 := by simpa using hx
    simp [hfx, ENNReal.zero_rpow_of_pos hs₁])

private theorem weakTypeInterpolation_complexLpMoment_restrict_support
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ}
    (hp : 0 < p) (f : X → ℂ) (hf : Measurable f) :
    Variation.complexLpMoment p μ f =
      Variation.complexLpMoment p (μ.restrict {x | f x ≠ 0}) f := by
  have hs : MeasurableSet {x | f x ≠ 0} :=
    weakTypeInterpolation_measurableSet_nonzero hf
  unfold Variation.complexLpMoment
  exact weakTypeInterpolation_lintegral_eq_restrict_of_zero_outside μ _ hs _ (by
    intro x hx
    have hfx : f x = 0 := by simpa using hx
    simp [hfx, ENNReal.zero_rpow_of_pos hp])

private theorem weakTypeInterpolation_highCutoffMoment
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s₀ W : ℝ}
    (hs₀ : 0 < s₀) (hW : 0 < W) (f : X → ℂ) (hf : Measurable f) (t : ℝ) :
    weakTypeInterpolationHighMoment μ s₀ W f t =
      (ENNReal.ofReal W).rpow s₀ *
        Variation.complexLpMoment s₀ μ
          (Variation.layerCakeHighCutoff (t / W) f) := by
  have hcut (x : X) : t < W * ‖f x‖ ↔ t / W < ‖f x‖ := by
    rw [div_lt_iff₀ hW]
    simp [mul_comm]
  have hpow (x : X) :
      (ENNReal.ofReal (W * ‖f x‖)).rpow s₀ =
        (ENNReal.ofReal W).rpow s₀ * (ENNReal.ofReal ‖f x‖).rpow s₀ := by
    rw [ENNReal.ofReal_mul hW.le]
    exact ENNReal.mul_rpow_of_nonneg _ _ hs₀.le
  have hnormMeas : Measurable (fun x : X => (ENNReal.ofReal ‖f x‖).rpow s₀) :=
    ENNReal.continuous_rpow_const.measurable.comp (hf.norm.ennreal_ofReal)
  have hcutSet : MeasurableSet {x : X | t / W < ‖f x‖} :=
    measurableSet_lt measurable_const hf.norm
  have hmomentMeas : Measurable (fun x : X =>
      if t / W < ‖f x‖ then (ENNReal.ofReal ‖f x‖).rpow s₀ else 0) :=
    Measurable.ite hcutSet hnormMeas measurable_const
  unfold weakTypeInterpolationHighMoment Variation.complexLpMoment
  calc
    (∫⁻ x, (if t < W * ‖f x‖ then
        (ENNReal.ofReal (W * ‖f x‖)).rpow s₀ else 0) ∂μ) =
      ∫⁻ x, (ENNReal.ofReal W).rpow s₀ *
        (if t / W < ‖f x‖ then (ENNReal.ofReal ‖f x‖).rpow s₀ else 0) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards with x
          by_cases hx : t / W < ‖f x‖
          · rw [if_pos ((hcut x).mpr hx), if_pos hx, hpow x]
          · have hx' : ¬ t < W * ‖f x‖ := fun h => hx ((hcut x).mp h)
            rw [if_neg hx', if_neg hx]
            simp
    _ = (ENNReal.ofReal W).rpow s₀ *
        ∫⁻ x, (if t / W < ‖f x‖ then
          (ENNReal.ofReal ‖f x‖).rpow s₀ else 0) ∂μ :=
            lintegral_const_mul _ hmomentMeas
    _ = (ENNReal.ofReal W).rpow s₀ *
        Variation.complexLpMoment s₀ μ
          (Variation.layerCakeHighCutoff (t / W) f) := by
            congr 1
            apply lintegral_congr_ae
            filter_upwards with x
            by_cases hx : t / W < ‖f x‖
            · simp [Variation.layerCakeHighCutoff, hx]
            · simp only [Variation.layerCakeHighCutoff, if_neg hx, norm_zero,
                ENNReal.ofReal_zero]
              exact (ENNReal.zero_rpow_of_pos hs₀).symm

private theorem weakTypeInterpolation_lowCutoffMoment
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s₁ W : ℝ}
    (hs₁ : 0 < s₁) (hW : 0 < W) (f : X → ℂ) (hf : Measurable f) (t : ℝ) :
    weakTypeInterpolationLowMoment μ s₁ W f t =
      (ENNReal.ofReal W).rpow s₁ *
        Variation.complexLpMoment s₁ μ
          (Variation.layerCakeLowCutoff (t / W) f) := by
  have hcut (x : X) : W * ‖f x‖ ≤ t ↔ ‖f x‖ ≤ t / W := by
    rw [le_div_iff₀ hW]
    simp [mul_comm]
  have hpow (x : X) :
      (ENNReal.ofReal (W * ‖f x‖)).rpow s₁ =
        (ENNReal.ofReal W).rpow s₁ * (ENNReal.ofReal ‖f x‖).rpow s₁ := by
    rw [ENNReal.ofReal_mul hW.le]
    exact ENNReal.mul_rpow_of_nonneg _ _ hs₁.le
  have hnormMeas : Measurable (fun x : X => (ENNReal.ofReal ‖f x‖).rpow s₁) :=
    ENNReal.continuous_rpow_const.measurable.comp (hf.norm.ennreal_ofReal)
  have hcutSet : MeasurableSet {x : X | ‖f x‖ ≤ t / W} :=
    measurableSet_le hf.norm measurable_const
  have hmomentMeas : Measurable (fun x : X =>
      if ‖f x‖ ≤ t / W then (ENNReal.ofReal ‖f x‖).rpow s₁ else 0) :=
    Measurable.ite hcutSet hnormMeas measurable_const
  unfold weakTypeInterpolationLowMoment Variation.complexLpMoment
  calc
    (∫⁻ x, (if W * ‖f x‖ ≤ t then
        (ENNReal.ofReal (W * ‖f x‖)).rpow s₁ else 0) ∂μ) =
      ∫⁻ x, (ENNReal.ofReal W).rpow s₁ *
        (if ‖f x‖ ≤ t / W then (ENNReal.ofReal ‖f x‖).rpow s₁ else 0) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards with x
          by_cases hx : ‖f x‖ ≤ t / W
          · rw [if_pos ((hcut x).mpr hx), if_pos hx, hpow x]
          · have hx' : ¬ W * ‖f x‖ ≤ t := fun h => hx ((hcut x).mp h)
            rw [if_neg hx', if_neg hx]
            simp
    _ = (ENNReal.ofReal W).rpow s₁ *
        ∫⁻ x, (if ‖f x‖ ≤ t / W then
          (ENNReal.ofReal ‖f x‖).rpow s₁ else 0) ∂μ :=
            lintegral_const_mul _ hmomentMeas
    _ = (ENNReal.ofReal W).rpow s₁ *
        Variation.complexLpMoment s₁ μ
          (Variation.layerCakeLowCutoff (t / W) f) := by
            congr 1
            apply lintegral_congr_ae
            filter_upwards with x
            by_cases hx : ‖f x‖ ≤ t / W
            · simp [Variation.layerCakeLowCutoff, hx]
            · simp only [Variation.layerCakeLowCutoff, if_neg hx, norm_zero,
                ENNReal.ofReal_zero]
              exact (ENNReal.zero_rpow_of_pos hs₁).symm

private theorem weakTypeInterpolationHighWeighted_kernelIntegral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s₀ p W A₀ : ℝ}
    (f : X → ℂ) (hf : Measurable f) (t : ℝ) :
    weakTypeInterpolationHighWeighted μ s₀ p W A₀ f t =
      ∫⁻ x, weakTypeInterpolationHighKernel s₀ p W A₀ f t x ∂μ := by
  let C := (ENNReal.ofReal (A₀ / W)).rpow s₀
  let T := ENNReal.ofReal t ^ (p - s₀ - 1)
  have hcut : MeasurableSet {x : X | t < W * ‖f x‖} :=
    measurableSet_lt measurable_const (measurable_const.mul hf.norm)
  have hnorm : Measurable (fun x : X =>
      (ENNReal.ofReal (W * ‖f x‖)).rpow s₀) :=
    ENNReal.continuous_rpow_const.measurable.comp
      ((measurable_const.mul hf.norm).ennreal_ofReal)
  have hmoment : Measurable (fun x : X =>
      if t < W * ‖f x‖ then
        (ENNReal.ofReal (W * ‖f x‖)).rpow s₀ else 0) :=
    Measurable.ite hcut hnorm measurable_const
  unfold weakTypeInterpolationHighWeighted weakTypeInterpolationHighMoment
  change C * (∫⁻ x, (if t < W * ‖f x‖ then
      (ENNReal.ofReal (W * ‖f x‖)).rpow s₀ else 0) ∂μ) * T = _
  calc
    C * (∫⁻ x, (if t < W * ‖f x‖ then
        (ENNReal.ofReal (W * ‖f x‖)).rpow s₀ else 0) ∂μ) * T =
        C * T * (∫⁻ x, (if t < W * ‖f x‖ then
          (ENNReal.ofReal (W * ‖f x‖)).rpow s₀ else 0) ∂μ) := by ac_rfl
    _ = ∫⁻ x, C * T * (if t < W * ‖f x‖ then
          (ENNReal.ofReal (W * ‖f x‖)).rpow s₀ else 0) ∂μ := by
          symm
          exact lintegral_const_mul _ hmoment
    _ = ∫⁻ x, weakTypeInterpolationHighKernel s₀ p W A₀ f t x ∂μ := by
          apply lintegral_congr_ae
          filter_upwards with x
          by_cases hx : t < W * ‖f x‖
          · simp only [weakTypeInterpolationHighKernel, if_pos hx, C, T]
            ac_rfl
          · simp [weakTypeInterpolationHighKernel, hx, C, T]

private theorem weakTypeInterpolationLowWeighted_kernelIntegral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p s₁ W A₁ : ℝ}
    (f : X → ℂ) (hf : Measurable f) (t : ℝ) :
    weakTypeInterpolationLowWeighted μ p s₁ W A₁ f t =
      ∫⁻ x, weakTypeInterpolationLowKernel p s₁ W A₁ f t x ∂μ := by
  let C := (ENNReal.ofReal (A₁ / W)).rpow s₁
  let T := ENNReal.ofReal t ^ (p - s₁ - 1)
  have hcut : MeasurableSet {x : X | W * ‖f x‖ ≤ t} :=
    measurableSet_le (measurable_const.mul hf.norm) measurable_const
  have hnorm : Measurable (fun x : X =>
      (ENNReal.ofReal (W * ‖f x‖)).rpow s₁) :=
    ENNReal.continuous_rpow_const.measurable.comp
      ((measurable_const.mul hf.norm).ennreal_ofReal)
  have hmoment : Measurable (fun x : X =>
      if W * ‖f x‖ ≤ t then
        (ENNReal.ofReal (W * ‖f x‖)).rpow s₁ else 0) :=
    Measurable.ite hcut hnorm measurable_const
  unfold weakTypeInterpolationLowWeighted weakTypeInterpolationLowMoment
  change C * (∫⁻ x, (if W * ‖f x‖ ≤ t then
      (ENNReal.ofReal (W * ‖f x‖)).rpow s₁ else 0) ∂μ) * T = _
  calc
    C * (∫⁻ x, (if W * ‖f x‖ ≤ t then
        (ENNReal.ofReal (W * ‖f x‖)).rpow s₁ else 0) ∂μ) * T =
        C * T * (∫⁻ x, (if W * ‖f x‖ ≤ t then
          (ENNReal.ofReal (W * ‖f x‖)).rpow s₁ else 0) ∂μ) := by ac_rfl
    _ = ∫⁻ x, C * T * (if W * ‖f x‖ ≤ t then
          (ENNReal.ofReal (W * ‖f x‖)).rpow s₁ else 0) ∂μ := by
          symm
          exact lintegral_const_mul _ hmoment
    _ = ∫⁻ x, weakTypeInterpolationLowKernel p s₁ W A₁ f t x ∂μ := by
          apply lintegral_congr_ae
          filter_upwards with x
          by_cases hx : W * ‖f x‖ ≤ t
          · simp only [weakTypeInterpolationLowKernel, if_pos hx, C, T]
            ac_rfl
          · simp [weakTypeInterpolationLowKernel, hx, C, T]

private theorem weakTypeInterpolation_highWeightedMoment_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s₀ p W A₀ : ℝ}
    (hs₀ : 0 < s₀) (hp : s₀ < p) (hW : 0 < W) (hA₀ : 0 < A₀)
    (f : X → ℂ) (hf : Measurable f)
    (hSupport : μ {x | f x ≠ 0} < ∞) :
    (∫⁻ t in Ioi (0 : ℝ), weakTypeInterpolationHighWeighted μ s₀ p W A₀ f t) =
      ENNReal.ofReal ((A₀ / W) ^ s₀ * (W ^ p / (p - s₀))) *
        Variation.complexLpMoment p μ f := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let s : Set X := {x | f x ≠ 0}
  let μs : Measure X := μ.restrict s
  have hs : MeasurableSet s := weakTypeInterpolation_measurableSet_nonzero hf
  haveI : IsFiniteMeasure μs := ⟨by
    change (μ.restrict s) Set.univ < ∞
    rw [Measure.restrict_apply_univ]
    exact hSupport⟩
  have hkernel : Measurable (fun z : ℝ × X =>
      weakTypeInterpolationHighKernel s₀ p W A₀ f z.1 z.2) := by
    have hbase : Measurable (fun z : ℝ × X => W * ‖f z.2‖) :=
      measurable_const.mul (hf.norm.comp measurable_snd)
    have hcut : MeasurableSet {z : ℝ × X | z.1 < W * ‖f z.2‖} :=
      measurableSet_lt measurable_fst hbase
    have hnorm : Measurable (fun z : ℝ × X =>
        (ENNReal.ofReal (W * ‖f z.2‖)).rpow s₀) :=
      ENNReal.continuous_rpow_const.measurable.comp hbase.ennreal_ofReal
    have hweight : Measurable (fun z : ℝ × X =>
        ENNReal.ofReal z.1 ^ (p - s₀ - 1)) :=
      ENNReal.continuous_rpow_const.measurable.comp measurable_fst.ennreal_ofReal
    exact Measurable.ite hcut
      ((measurable_const.mul hnorm).mul hweight) measurable_const
  have hswap :
      (∫⁻ t, ∫⁻ x, weakTypeInterpolationHighKernel s₀ p W A₀ f t x ∂μs ∂ν) =
        ∫⁻ x, ∫⁻ t, weakTypeInterpolationHighKernel s₀ p W A₀ f t x ∂ν ∂μs := by
    exact MeasureTheory.lintegral_lintegral_swap
      (μ := ν) (ν := μs)
      (f := fun t x => weakTypeInterpolationHighKernel s₀ p W A₀ f t x)
      hkernel.aemeasurable
  have htail (x : X) :
      (∫⁻ t, weakTypeInterpolationHighKernel s₀ p W A₀ f t x ∂ν) =
        (ENNReal.ofReal (A₀ / W)).rpow s₀ *
          ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (p - s₀)) := by
    have hfun : Measurable (fun t : ℝ =>
        if t < W * ‖f x‖ then
          (ENNReal.ofReal (W * ‖f x‖)).rpow s₀ *
            ENNReal.ofReal t ^ (p - s₀ - 1) else 0) := by
      exact Measurable.ite
        (measurableSet_lt measurable_id measurable_const)
        (measurable_const.mul
          (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal))
        measurable_const
    calc
      (∫⁻ t, weakTypeInterpolationHighKernel s₀ p W A₀ f t x ∂ν) =
          ∫⁻ t, (ENNReal.ofReal (A₀ / W)).rpow s₀ *
            (if t < W * ‖f x‖ then
              (ENNReal.ofReal (W * ‖f x‖)).rpow s₀ *
                ENNReal.ofReal t ^ (p - s₀ - 1) else 0) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards with t
          by_cases ht : t < W * ‖f x‖
          · simp only [weakTypeInterpolationHighKernel, if_pos ht]
            ac_rfl
          · simp [weakTypeInterpolationHighKernel, ht]
      _ = (ENNReal.ofReal (A₀ / W)).rpow s₀ *
          ∫⁻ t, (if t < W * ‖f x‖ then
            (ENNReal.ofReal (W * ‖f x‖)).rpow s₀ *
              ENNReal.ofReal t ^ (p - s₀ - 1) else 0) ∂ν :=
            lintegral_const_mul _ hfun
      _ = (ENNReal.ofReal (A₀ / W)).rpow s₀ *
          ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (p - s₀)) := by
            exact congrArg (fun z : ℝ≥0∞ => (ENNReal.ofReal (A₀ / W)).rpow s₀ * z)
              (Variation.layerCake_highInput_tail hs₀ hp hW (norm_nonneg (f x)))
  have hrestrict (t : ℝ) :
      weakTypeInterpolationHighWeighted μ s₀ p W A₀ f t =
        weakTypeInterpolationHighWeighted μs s₀ p W A₀ f t := by
    unfold weakTypeInterpolationHighWeighted
    rw [weakTypeInterpolation_highMoment_restrict_support hs₀ f hf t]
  have hBnonneg : 0 ≤ (A₀ / W) ^ s₀ :=
    Real.rpow_nonneg (div_nonneg hA₀.le hW.le) _
  have hWfrac : 0 ≤ W ^ p / (p - s₀) := by
    apply div_nonneg (Real.rpow_nonneg hW.le _)
    linarith
  have hB : 0 ≤ (A₀ / W) ^ s₀ * (W ^ p / (p - s₀)) :=
    mul_nonneg hBnonneg hWfrac
  have hqMeas : Measurable (fun x : X => ENNReal.ofReal ‖f x‖ ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp (hf.norm.ennreal_ofReal)
  have hterm (x : X) :
      (ENNReal.ofReal (A₀ / W)).rpow s₀ *
          ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (p - s₀)) =
        ENNReal.ofReal ((A₀ / W) ^ s₀ * (W ^ p / (p - s₀))) *
          ENNReal.ofReal ‖f x‖ ^ p := by
    have hA : (ENNReal.ofReal (A₀ / W)).rpow s₀ =
        ENNReal.ofReal ((A₀ / W) ^ s₀) := by
      change (ENNReal.ofReal (A₀ / W)) ^ s₀ = _
      exact ENNReal.ofReal_rpow_of_nonneg
        (div_nonneg hA₀.le hW.le) hs₀.le
    have hreal : W ^ p * ‖f x‖ ^ p / (p - s₀) =
        (W ^ p / (p - s₀)) * ‖f x‖ ^ p := by ring
    calc
      (ENNReal.ofReal (A₀ / W)).rpow s₀ *
          ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (p - s₀)) =
        ENNReal.ofReal ((A₀ / W) ^ s₀) *
          (ENNReal.ofReal (W ^ p / (p - s₀)) *
            ENNReal.ofReal (‖f x‖ ^ p)) := by
          rw [hA, hreal, ENNReal.ofReal_mul hWfrac]
      _ = ENNReal.ofReal ((A₀ / W) ^ s₀ * (W ^ p / (p - s₀))) *
          ENNReal.ofReal (‖f x‖ ^ p) := by
          calc
            ENNReal.ofReal ((A₀ / W) ^ s₀) *
                (ENNReal.ofReal (W ^ p / (p - s₀)) * ENNReal.ofReal (‖f x‖ ^ p)) =
              (ENNReal.ofReal ((A₀ / W) ^ s₀) *
                ENNReal.ofReal (W ^ p / (p - s₀))) * ENNReal.ofReal (‖f x‖ ^ p) := by ac_rfl
            _ = ENNReal.ofReal ((A₀ / W) ^ s₀ * (W ^ p / (p - s₀))) *
                ENNReal.ofReal (‖f x‖ ^ p) := by rw [← ENNReal.ofReal_mul hBnonneg]
      _ = ENNReal.ofReal ((A₀ / W) ^ s₀ * (W ^ p / (p - s₀))) *
          ENNReal.ofReal ‖f x‖ ^ p := by
          rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) (by linarith : 0 ≤ p)]
  calc
    (∫⁻ t in Ioi (0 : ℝ), weakTypeInterpolationHighWeighted μ s₀ p W A₀ f t) =
        ∫⁻ t, ∫⁻ x, weakTypeInterpolationHighKernel s₀ p W A₀ f t x ∂μs ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          rw [hrestrict t]
          exact weakTypeInterpolationHighWeighted_kernelIntegral (μ := μs) f hf t
    _ = ∫⁻ x, ∫⁻ t, weakTypeInterpolationHighKernel s₀ p W A₀ f t x ∂ν ∂μs := hswap
    _ = ∫⁻ x, (ENNReal.ofReal (A₀ / W)).rpow s₀ *
          ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (p - s₀)) ∂μs := by
          apply lintegral_congr_ae
          filter_upwards with x
          exact htail x
    _ = ∫⁻ x, ENNReal.ofReal ((A₀ / W) ^ s₀ * (W ^ p / (p - s₀))) *
          ENNReal.ofReal ‖f x‖ ^ p ∂μs := by
          apply lintegral_congr_ae
          filter_upwards with x
          exact hterm x
    _ = ENNReal.ofReal ((A₀ / W) ^ s₀ * (W ^ p / (p - s₀))) *
          Variation.complexLpMoment p μs f := by
          rw [lintegral_const_mul _ hqMeas]
          rfl
    _ = ENNReal.ofReal ((A₀ / W) ^ s₀ * (W ^ p / (p - s₀))) *
          Variation.complexLpMoment p μ f := by
          rw [← weakTypeInterpolation_complexLpMoment_restrict_support
            (by linarith : 0 < p) f hf]

private theorem weakTypeInterpolation_lowWeightedMoment_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p s₁ W A₁ : ℝ}
    (hp : 0 < p) (hp₁ : p < s₁) (hs₁ : 0 < s₁)
    (hW : 0 < W) (hA₁ : 0 < A₁) (f : X → ℂ) (hf : Measurable f)
    (hSupport : μ {x | f x ≠ 0} < ∞) :
    (∫⁻ t in Ioi (0 : ℝ), weakTypeInterpolationLowWeighted μ p s₁ W A₁ f t) =
      ENNReal.ofReal ((A₁ / W) ^ s₁ * (W ^ p / (s₁ - p))) *
        Variation.complexLpMoment p μ f := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let s : Set X := {x | f x ≠ 0}
  let μs : Measure X := μ.restrict s
  have hs : MeasurableSet s := weakTypeInterpolation_measurableSet_nonzero hf
  haveI : IsFiniteMeasure μs := ⟨by
    change (μ.restrict s) Set.univ < ∞
    rw [Measure.restrict_apply_univ]
    exact hSupport⟩
  have hkernel : Measurable (fun z : ℝ × X =>
      weakTypeInterpolationLowKernel p s₁ W A₁ f z.1 z.2) := by
    have hbase : Measurable (fun z : ℝ × X => W * ‖f z.2‖) :=
      measurable_const.mul (hf.norm.comp measurable_snd)
    have hcut : MeasurableSet {z : ℝ × X | W * ‖f z.2‖ ≤ z.1} :=
      measurableSet_le hbase measurable_fst
    have hnorm : Measurable (fun z : ℝ × X =>
        (ENNReal.ofReal (W * ‖f z.2‖)).rpow s₁) :=
      ENNReal.continuous_rpow_const.measurable.comp hbase.ennreal_ofReal
    have hweight : Measurable (fun z : ℝ × X =>
        ENNReal.ofReal z.1 ^ (p - s₁ - 1)) :=
      ENNReal.continuous_rpow_const.measurable.comp measurable_fst.ennreal_ofReal
    exact Measurable.ite hcut
      ((measurable_const.mul hnorm).mul hweight) measurable_const
  have hswap :
      (∫⁻ t, ∫⁻ x, weakTypeInterpolationLowKernel p s₁ W A₁ f t x ∂μs ∂ν) =
        ∫⁻ x, ∫⁻ t, weakTypeInterpolationLowKernel p s₁ W A₁ f t x ∂ν ∂μs := by
    exact MeasureTheory.lintegral_lintegral_swap
      (μ := ν) (ν := μs)
      (f := fun t x => weakTypeInterpolationLowKernel p s₁ W A₁ f t x)
      hkernel.aemeasurable
  have htail (x : X) :
      (∫⁻ t, weakTypeInterpolationLowKernel p s₁ W A₁ f t x ∂ν) =
        (ENNReal.ofReal (A₁ / W)).rpow s₁ *
          ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (s₁ - p)) := by
    have hfun : Measurable (fun t : ℝ =>
        if W * ‖f x‖ ≤ t then
          (ENNReal.ofReal (W * ‖f x‖)).rpow s₁ *
            ENNReal.ofReal t ^ (p - s₁ - 1) else 0) := by
      exact Measurable.ite
        (measurableSet_le measurable_const measurable_id)
        (measurable_const.mul
          (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal))
        measurable_const
    calc
      (∫⁻ t, weakTypeInterpolationLowKernel p s₁ W A₁ f t x ∂ν) =
          ∫⁻ t, (ENNReal.ofReal (A₁ / W)).rpow s₁ *
            (if W * ‖f x‖ ≤ t then
              (ENNReal.ofReal (W * ‖f x‖)).rpow s₁ *
                ENNReal.ofReal t ^ (p - s₁ - 1) else 0) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards with t
          by_cases ht : W * ‖f x‖ ≤ t
          · simp only [weakTypeInterpolationLowKernel, if_pos ht]
            ac_rfl
          · simp [weakTypeInterpolationLowKernel, ht]
      _ = (ENNReal.ofReal (A₁ / W)).rpow s₁ *
          ∫⁻ t, (if W * ‖f x‖ ≤ t then
            (ENNReal.ofReal (W * ‖f x‖)).rpow s₁ *
              ENNReal.ofReal t ^ (p - s₁ - 1) else 0) ∂ν :=
            lintegral_const_mul _ hfun
      _ = (ENNReal.ofReal (A₁ / W)).rpow s₁ *
          ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (s₁ - p)) := by
            exact congrArg (fun z : ℝ≥0∞ => (ENNReal.ofReal (A₁ / W)).rpow s₁ * z)
              (Variation.layerCake_lowInput_tail hp hp₁ hs₁ hW
                (norm_nonneg (f x)))
  have hrestrict (t : ℝ) :
      weakTypeInterpolationLowWeighted μ p s₁ W A₁ f t =
        weakTypeInterpolationLowWeighted μs p s₁ W A₁ f t := by
    unfold weakTypeInterpolationLowWeighted
    rw [weakTypeInterpolation_lowMoment_restrict_support hs₁ f hf t]
  have hBnonneg : 0 ≤ (A₁ / W) ^ s₁ :=
    Real.rpow_nonneg (div_nonneg hA₁.le hW.le) _
  have hWfrac : 0 ≤ W ^ p / (s₁ - p) := by
    apply div_nonneg (Real.rpow_nonneg hW.le _)
    linarith
  have hB : 0 ≤ (A₁ / W) ^ s₁ * (W ^ p / (s₁ - p)) :=
    mul_nonneg hBnonneg hWfrac
  have hqMeas : Measurable (fun x : X => ENNReal.ofReal ‖f x‖ ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp (hf.norm.ennreal_ofReal)
  have hterm (x : X) :
      (ENNReal.ofReal (A₁ / W)).rpow s₁ *
          ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (s₁ - p)) =
        ENNReal.ofReal ((A₁ / W) ^ s₁ * (W ^ p / (s₁ - p))) *
          ENNReal.ofReal ‖f x‖ ^ p := by
    have hA : (ENNReal.ofReal (A₁ / W)).rpow s₁ =
        ENNReal.ofReal ((A₁ / W) ^ s₁) := by
      change (ENNReal.ofReal (A₁ / W)) ^ s₁ = _
      exact ENNReal.ofReal_rpow_of_nonneg
        (div_nonneg hA₁.le hW.le) hs₁.le
    have hreal : W ^ p * ‖f x‖ ^ p / (s₁ - p) =
        (W ^ p / (s₁ - p)) * ‖f x‖ ^ p := by ring
    calc
      (ENNReal.ofReal (A₁ / W)).rpow s₁ *
          ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (s₁ - p)) =
        ENNReal.ofReal ((A₁ / W) ^ s₁) *
          (ENNReal.ofReal (W ^ p / (s₁ - p)) *
            ENNReal.ofReal (‖f x‖ ^ p)) := by
          rw [hA, hreal, ENNReal.ofReal_mul hWfrac]
      _ = ENNReal.ofReal ((A₁ / W) ^ s₁ * (W ^ p / (s₁ - p))) *
          ENNReal.ofReal (‖f x‖ ^ p) := by
          calc
            ENNReal.ofReal ((A₁ / W) ^ s₁) *
                (ENNReal.ofReal (W ^ p / (s₁ - p)) * ENNReal.ofReal (‖f x‖ ^ p)) =
              (ENNReal.ofReal ((A₁ / W) ^ s₁) *
                ENNReal.ofReal (W ^ p / (s₁ - p))) * ENNReal.ofReal (‖f x‖ ^ p) := by ac_rfl
            _ = ENNReal.ofReal ((A₁ / W) ^ s₁ * (W ^ p / (s₁ - p))) *
                ENNReal.ofReal (‖f x‖ ^ p) := by rw [← ENNReal.ofReal_mul hBnonneg]
      _ = ENNReal.ofReal ((A₁ / W) ^ s₁ * (W ^ p / (s₁ - p))) *
          ENNReal.ofReal ‖f x‖ ^ p := by
          rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) (by linarith : 0 ≤ p)]
  calc
    (∫⁻ t in Ioi (0 : ℝ), weakTypeInterpolationLowWeighted μ p s₁ W A₁ f t) =
        ∫⁻ t, ∫⁻ x, weakTypeInterpolationLowKernel p s₁ W A₁ f t x ∂μs ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          rw [hrestrict t]
          exact weakTypeInterpolationLowWeighted_kernelIntegral (μ := μs) f hf t
    _ = ∫⁻ x, ∫⁻ t, weakTypeInterpolationLowKernel p s₁ W A₁ f t x ∂ν ∂μs := hswap
    _ = ∫⁻ x, (ENNReal.ofReal (A₁ / W)).rpow s₁ *
          ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (s₁ - p)) ∂μs := by
          apply lintegral_congr_ae
          filter_upwards with x
          exact htail x
    _ = ∫⁻ x, ENNReal.ofReal ((A₁ / W) ^ s₁ * (W ^ p / (s₁ - p))) *
          ENNReal.ofReal ‖f x‖ ^ p ∂μs := by
          apply lintegral_congr_ae
          filter_upwards with x
          exact hterm x
    _ = ENNReal.ofReal ((A₁ / W) ^ s₁ * (W ^ p / (s₁ - p))) *
          Variation.complexLpMoment p μs f := by
          rw [lintegral_const_mul _ hqMeas]
          rfl
    _ = ENNReal.ofReal ((A₁ / W) ^ s₁ * (W ^ p / (s₁ - p))) *
          Variation.complexLpMoment p μ f := by
          rw [← weakTypeInterpolation_complexLpMoment_restrict_support
            (by linarith : 0 < p) f hf]

private theorem weakTypeInterpolation_optimizedCoefficient
    {s₀ p s₁ A₀ A₁ : ℝ}
    (hs₀ : 0 < s₀) (h₀ : s₀ < p) (h₁ : p < s₁)
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) :
    let W : ℝ := (A₁ ^ s₁ / A₀ ^ s₀) ^ (1 / (s₁ - s₀))
    2 ^ p * (p * ((A₀ / W) ^ s₀ * (W ^ p / (p - s₀)) +
        (A₁ / W) ^ s₁ * (W ^ p / (s₁ - p)))) =
      (weakTypeInterpolationConstant s₀ p s₁ *
        A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁ *
        A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁) ^ p := by
  let d : ℝ := s₁ - s₀
  let q : ℝ := (p - s₀) / d
  let W : ℝ := (A₁ ^ s₁ / A₀ ^ s₀) ^ (1 / d)
  let S : ℝ := p * (1 / (p - s₀) + 1 / (s₁ - p))
  let C : ℝ := weakTypeInterpolationConstant s₀ p s₁ *
    A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁ *
    A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁
  have hd : 0 < d := by dsimp [d]; linarith
  have hp : 0 < p := hs₀.trans h₀
  have hden₀ : 0 < p - s₀ := by linarith
  have hden₁ : 0 < s₁ - p := by linarith
  have hA₀pow : 0 < A₀ ^ s₀ := Real.rpow_pos_of_pos hA₀ _
  have hA₁pow : 0 < A₁ ^ s₁ := Real.rpow_pos_of_pos hA₁ _
  have hratio : 0 < A₁ ^ s₁ / A₀ ^ s₀ := div_pos hA₁pow hA₀pow
  have hW : 0 < W := by
    dsimp [W]
    exact Real.rpow_pos_of_pos hratio _
  have hWexp : W ^ d = A₁ ^ s₁ / A₀ ^ s₀ := by
    dsimp [W]
    rw [← Real.rpow_mul hratio.le (1 / d) d]
    have hexp : (1 / d) * d = 1 := by field_simp [ne_of_gt hd]
    rw [hexp, Real.rpow_one]
  have hWrel : A₁ ^ s₁ = A₀ ^ s₀ * W ^ d := by
    calc
      A₁ ^ s₁ = A₀ ^ s₀ * (A₁ ^ s₁ / A₀ ^ s₀) := by
        field_simp [ne_of_gt hA₀pow]
      _ = A₀ ^ s₀ * W ^ d := by rw [← hWexp]
  have hB₀ : (A₀ / W) ^ s₀ * (W ^ p / (p - s₀)) =
      A₀ ^ s₀ * W ^ (p - s₀) / (p - s₀) := by
    rw [Real.div_rpow hA₀.le hW.le s₀]
    calc
      A₀ ^ s₀ / W ^ s₀ * (W ^ p / (p - s₀)) =
          A₀ ^ s₀ * (W ^ p / W ^ s₀) / (p - s₀) := by
            field_simp [ne_of_gt hden₀,
              ne_of_gt (Real.rpow_pos_of_pos hW s₀)]
      _ = A₀ ^ s₀ * W ^ (p - s₀) / (p - s₀) := by
            rw [← Real.rpow_sub hW p s₀]
  have hB₁ : (A₁ / W) ^ s₁ * (W ^ p / (s₁ - p)) =
      A₀ ^ s₀ * W ^ (p - s₀) / (s₁ - p) := by
    rw [Real.div_rpow hA₁.le hW.le s₁]
    calc
      A₁ ^ s₁ / W ^ s₁ * (W ^ p / (s₁ - p)) =
          A₁ ^ s₁ * W ^ (p - s₁) / (s₁ - p) := by
            field_simp [ne_of_gt hden₁,
              ne_of_gt (Real.rpow_pos_of_pos hW s₁)]
            rw [← Real.rpow_add hW]
            congr 1
            ring
      _ = A₀ ^ s₀ * W ^ (p - s₀) / (s₁ - p) := by
            rw [hWrel]
            have hpow : W ^ d * W ^ (p - s₁) = W ^ (p - s₀) := by
              rw [← Real.rpow_add hW]
              congr 1
              dsimp [d]
              ring
            calc
              A₀ ^ s₀ * W ^ d * W ^ (p - s₁) / (s₁ - p) =
                  A₀ ^ s₀ * (W ^ d * W ^ (p - s₁)) / (s₁ - p) := by ring
              _ = A₀ ^ s₀ * W ^ (p - s₀) / (s₁ - p) := by rw [hpow]
  have hsum :
      (A₀ / W) ^ s₀ * (W ^ p / (p - s₀)) +
          (A₁ / W) ^ s₁ * (W ^ p / (s₁ - p)) =
        A₀ ^ s₀ * W ^ (p - s₀) *
          (1 / (p - s₀) + 1 / (s₁ - p)) := by
    rw [hB₀, hB₁]
    field_simp [ne_of_gt hden₀, ne_of_gt hden₁]
  have hWpower : W ^ (p - s₀) =
      A₁ ^ (s₁ * q) / A₀ ^ (s₀ * q) := by
    dsimp [W]
    have hq : (1 / d) * (p - s₀) = q := by
      dsimp [q]
      field_simp [ne_of_gt hd]
    calc
      ((A₁ ^ s₁ / A₀ ^ s₀) ^ (1 / d)) ^ (p - s₀) =
          (A₁ ^ s₁ / A₀ ^ s₀) ^ ((1 / d) * (p - s₀)) := by
            rw [← Real.rpow_mul hratio.le (1 / d) (p - s₀)]
      _ = (A₁ ^ s₁ / A₀ ^ s₀) ^ q := by rw [hq]
      _ = (A₁ ^ s₁) ^ q / (A₀ ^ s₀) ^ q := by
            rw [Real.div_rpow (Real.rpow_nonneg hA₁.le s₁)
              (Real.rpow_nonneg hA₀.le s₀) q]
      _ = A₁ ^ (s₁ * q) / A₀ ^ (s₀ * q) := by
            rw [← Real.rpow_mul hA₁.le s₁ q,
              ← Real.rpow_mul hA₀.le s₀ q]
  have htheta₀ : weakTypeInterpolationTheta0 s₀ p s₁ * p = s₀ * (1 - q) := by
    dsimp [weakTypeInterpolationTheta0, q, d]
    have hd' : s₁ - s₀ ≠ 0 := by linarith
    field_simp [ne_of_gt hp, hd']
    ring
  have htheta₁ : weakTypeInterpolationTheta1 s₀ p s₁ * p = s₁ * q := by
    dsimp [weakTypeInterpolationTheta1, q, d]
    field_simp [ne_of_gt hp, ne_of_gt hd]
  have hAterm : A₀ ^ s₀ * W ^ (p - s₀) =
      A₀ ^ (weakTypeInterpolationTheta0 s₀ p s₁ * p) *
        A₁ ^ (weakTypeInterpolationTheta1 s₀ p s₁ * p) := by
    calc
      A₀ ^ s₀ * W ^ (p - s₀) =
          A₀ ^ s₀ * (A₁ ^ (s₁ * q) / A₀ ^ (s₀ * q)) := by rw [hWpower]
      _ = A₀ ^ s₀ / A₀ ^ (s₀ * q) * A₁ ^ (s₁ * q) := by ring
      _ = A₀ ^ (s₀ * (1 - q)) * A₁ ^ (s₁ * q) := by
            rw [← Real.rpow_sub hA₀ s₀ (s₀ * q)]
            congr 1
            ring
      _ = A₀ ^ (weakTypeInterpolationTheta0 s₀ p s₁ * p) *
          A₁ ^ (weakTypeInterpolationTheta1 s₀ p s₁ * p) := by
            rw [← htheta₀, ← htheta₁]
  have hI : weakTypeInterpolationConstant s₀ p s₁ ^ p =
      2 ^ p * S := by
    have hsource := Variation.layerCake_sourceConstant_rpow hs₀ h₀ h₁
      (by norm_num : 0 ≤ (1 : ℝ))
    simpa [weakTypeInterpolationConstant, S] using hsource
  have hCpow : C ^ p =
      2 ^ p * S *
        (A₀ ^ (weakTypeInterpolationTheta0 s₀ p s₁ * p) *
          A₁ ^ (weakTypeInterpolationTheta1 s₀ p s₁ * p)) := by
    have hA₀theta : 0 ≤ A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁ :=
      Real.rpow_nonneg hA₀.le _
    have hA₁theta : 0 ≤ A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁ :=
      Real.rpow_nonneg hA₁.le _
    have hC0 : 0 ≤ weakTypeInterpolationConstant s₀ p s₁ := by
      dsimp [weakTypeInterpolationConstant]
      apply mul_nonneg (by norm_num)
      apply Real.rpow_nonneg
      apply mul_nonneg hp.le
      exact add_nonneg (div_nonneg zero_le_one hden₀.le)
        (div_nonneg zero_le_one hden₁.le)
    calc
      C ^ p = weakTypeInterpolationConstant s₀ p s₁ ^ p *
          (A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁) ^ p *
          (A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁) ^ p := by
            dsimp [C]
            rw [Real.mul_rpow
                (mul_nonneg hC0 hA₀theta) hA₁theta,
              Real.mul_rpow hC0 hA₀theta]
      _ = 2 ^ p * S *
          (A₀ ^ (weakTypeInterpolationTheta0 s₀ p s₁ * p) *
            A₁ ^ (weakTypeInterpolationTheta1 s₀ p s₁ * p)) := by
            rw [hI, ← Real.rpow_mul hA₀.le
              (weakTypeInterpolationTheta0 s₀ p s₁) p,
              ← Real.rpow_mul hA₁.le
                (weakTypeInterpolationTheta1 s₀ p s₁) p]
            ac_rfl
  calc
    2 ^ p * (p * ((A₀ / W) ^ s₀ * (W ^ p / (p - s₀)) +
        (A₁ / W) ^ s₁ * (W ^ p / (s₁ - p)))) =
      2 ^ p * S * (A₀ ^ s₀ * W ^ (p - s₀)) := by
        rw [hsum]
        dsimp [S]
        ring
    _ = C ^ p := by
        rw [hAterm, hCpow]

/-- The p-moment layer-cake identity in the `2t` normalization used by the
source interpolation proof. -/
private theorem weakTypeInterpolation_outputLayercake
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ}
    (hp : 0 < p) (F : X → ℝ) (hFnonneg : ∀ x, 0 ≤ F x)
    (hFmeas : Measurable F) :
    (∫⁻ x, ENNReal.ofReal (F x ^ p) ∂μ) =
      ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal p *
        ∫⁻ t in Ioi (0 : ℝ), μ {x | 2 * t < F x} *
          ENNReal.ofReal (t ^ (p - 1))) := by
  let G : X → ℝ := fun x => F x / 2
  have hGnonneg : ∀ x, 0 ≤ G x := fun x => div_nonneg (hFnonneg x) (by norm_num)
  have hGmeas : Measurable G := hFmeas.div_const 2
  have hLayer := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
    (μ := μ) (f := G) (Eventually.of_forall hGnonneg) hGmeas.aemeasurable hp
  have hpoint (x : X) :
      ENNReal.ofReal (F x ^ p) =
        ENNReal.ofReal (2 ^ p) * ENNReal.ofReal (G x ^ p) := by
    have hreal : F x ^ p = 2 ^ p * G x ^ p := by
      dsimp [G]
      calc
        F x ^ p = (2 * (F x / 2)) ^ p := by congr 1; ring
        _ = 2 ^ p * (F x / 2) ^ p :=
          Real.mul_rpow (by norm_num) (div_nonneg (hFnonneg x) (by norm_num))
    rw [hreal, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) p)]
  have hlevel :
      (fun t : ℝ => μ {x | t < G x} * ENNReal.ofReal (t ^ (p - 1))) =ᵐ[
        volume.restrict (Ioi (0 : ℝ))]
        (fun t => μ {x | 2 * t < F x} * ENNReal.ofReal (t ^ (p - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hset : {x | t < G x} = {x | 2 * t < F x} := by
      ext x
      change t < F x / 2 ↔ 2 * t < F x
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      ring_nf
    rw [hset]
  calc
    (∫⁻ x, ENNReal.ofReal (F x ^ p) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (2 ^ p) * ENNReal.ofReal (G x ^ p) ∂μ := by
          apply lintegral_congr_ae
          exact ae_of_all _ hpoint
    _ = ENNReal.ofReal (2 ^ p) * (∫⁻ x, ENNReal.ofReal (G x ^ p) ∂μ) := by
          rw [lintegral_const_mul _ (hGmeas.pow measurable_const).ennreal_ofReal]
    _ = ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal p *
            ∫⁻ t in Ioi (0 : ℝ), μ {x | 2 * t < F x} *
              ENNReal.ofReal (t ^ (p - 1))) := by
          rw [hLayer]
          congr 1
          apply congr_arg
          exact lintegral_congr_ae hlevel

/-- The optimized two-constant p-moment interpolation estimate. The cutoff
is chosen from the endpoint constants, and both zero-constant endpoint cases
are included. -/
theorem weakTypeInterpolation_moment
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {s₀ p s₁ A₀ A₁ : ℝ}
    (U : WeakTypeInterpolationOperator μ s₀ s₁ A₀ A₁)
    (hs₀ : 1 ≤ s₀) (h₀ : s₀ < p) (h₁ : p < s₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (f : Variation.LayerCakeInput μ) :
    (∫⁻ x, ENNReal.ofReal ((U.apply f x) ^ p) ∂μ) ≤
      ENNReal.ofReal
        ((weakTypeInterpolationConstant s₀ p s₁ *
          A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁ *
          A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁) ^ p) *
        Variation.complexLpMoment p μ f.1 := by
  have hs₀pos : 0 < s₀ := lt_of_lt_of_le zero_lt_one hs₀
  have hp : 0 < p := hs₀pos.trans h₀
  have hs₁pos : 0 < s₁ := hp.trans h₁
  let C : ℝ := weakTypeInterpolationConstant s₀ p s₁ *
    A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁ *
    A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁
  change (∫⁻ x, ENNReal.ofReal ((U.apply f x) ^ p) ∂μ) ≤
    ENNReal.ofReal (C ^ p) * Variation.complexLpMoment p μ f.1
  have hFnonneg : ∀ x, 0 ≤ U.apply f x := U.nonneg_apply f
  have hFmeas : Measurable (U.apply f) := U.measurable_apply f
  have hlayer := weakTypeInterpolation_outputLayercake (μ := μ) hp (U.apply f)
    hFnonneg hFmeas
  by_cases hA₀zero : A₀ = 0
  · have hθ₀ : 0 < weakTypeInterpolationTheta0 s₀ p s₁ := by
      have hden : 0 < p * (s₁ - s₀) := mul_pos hp (by linarith)
      have hnum : 0 < s₀ * (s₁ - p) := mul_pos hs₀pos (by linarith)
      dsimp [weakTypeInterpolationTheta0]
      exact div_pos hnum hden
    have hCzero : C = 0 := by
      dsimp [C]
      rw [hA₀zero, Real.zero_rpow (ne_of_gt hθ₀)]
      simp
    have hzeroLevel (t : ℝ) (ht : 0 < t) :
        μ {x | 2 * t < U.apply f x} = 0 := by
      have hfactor : (ENNReal.ofReal A₀).rpow s₀ = 0 := by
        rw [hA₀zero, ENNReal.ofReal_zero]
        exact ENNReal.zero_rpow_of_pos hs₀pos
      have hweak := U.weak_s₀ f (2 * t) (by linarith)
      have hle : μ {x | 2 * t < U.apply f x} ≤ 0 := by
        calc
          μ {x | 2 * t < U.apply f x} ≤
              (ENNReal.ofReal A₀).rpow s₀ * (ENNReal.ofReal (2 * t)).rpow (-s₀) *
                Variation.complexLpMoment s₀ μ f.1 := hweak
          _ = 0 := by rw [hfactor]; simp
      exact le_antisymm hle (by positivity)
    have hlevel :
        (fun t : ℝ => μ {x | 2 * t < U.apply f x} *
          ENNReal.ofReal (t ^ (p - 1))) =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp [hzeroLevel t (mem_Ioi.mp ht)]
    have hmomentZero :
        (∫⁻ x, ENNReal.ofReal ((U.apply f x) ^ p) ∂μ) = 0 := by
      rw [hlayer, lintegral_congr_ae hlevel]
      simp
    rw [hmomentZero, hCzero]
    simp [Real.zero_rpow hp.ne']
  · by_cases hA₁zero : A₁ = 0
    · have hθ₁ : 0 < weakTypeInterpolationTheta1 s₀ p s₁ := by
        have hden : 0 < p * (s₁ - s₀) := mul_pos hp (by linarith)
        have hnum : 0 < s₁ * (p - s₀) := mul_pos hs₁pos (by linarith)
        dsimp [weakTypeInterpolationTheta1]
        exact div_pos hnum hden
      have hCzero : C = 0 := by
        dsimp [C]
        rw [hA₁zero, Real.zero_rpow (ne_of_gt hθ₁)]
        simp
      have hzeroLevel (t : ℝ) (ht : 0 < t) :
          μ {x | 2 * t < U.apply f x} = 0 := by
        have hfactor : (ENNReal.ofReal A₁).rpow s₁ = 0 := by
          rw [hA₁zero, ENNReal.ofReal_zero]
          exact ENNReal.zero_rpow_of_pos hs₁pos
        have hweak := U.weak_s₁ f (2 * t) (by linarith)
        have hle : μ {x | 2 * t < U.apply f x} ≤ 0 := by
          calc
            μ {x | 2 * t < U.apply f x} ≤
                (ENNReal.ofReal A₁).rpow s₁ * (ENNReal.ofReal (2 * t)).rpow (-s₁) *
                  Variation.complexLpMoment s₁ μ f.1 := hweak
            _ = 0 := by rw [hfactor]; simp
        exact le_antisymm hle (by positivity)
      have hlevel :
          (fun t : ℝ => μ {x | 2 * t < U.apply f x} *
            ENNReal.ofReal (t ^ (p - 1))) =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        simp [hzeroLevel t (mem_Ioi.mp ht)]
      have hmomentZero :
          (∫⁻ x, ENNReal.ofReal ((U.apply f x) ^ p) ∂μ) = 0 := by
        rw [hlayer, lintegral_congr_ae hlevel]
        simp
      rw [hmomentZero, hCzero]
      simp [Real.zero_rpow hp.ne']
    · have hA₀pos : 0 < A₀ := lt_of_le_of_ne hA₀ (Ne.symm hA₀zero)
      have hA₁pos : 0 < A₁ := lt_of_le_of_ne hA₁ (Ne.symm hA₁zero)
      let W : ℝ := (A₁ ^ s₁ / A₀ ^ s₀) ^ (1 / (s₁ - s₀))
      let B₀ : ℝ := (A₀ / W) ^ s₀ * (W ^ p / (p - s₀))
      let B₁ : ℝ := (A₁ / W) ^ s₁ * (W ^ p / (s₁ - p))
      have hWpos : 0 < W := by
        dsimp [W]
        apply Real.rpow_pos_of_pos
        exact div_pos (Real.rpow_pos_of_pos hA₁pos _) (Real.rpow_pos_of_pos hA₀pos _)
      have hdiv (t : ℝ) : (1 / W) * t = t / W := by
        field_simp [ne_of_gt hWpos]
      have hscale₀ : (ENNReal.ofReal (A₀ / W)).rpow s₀ *
          (ENNReal.ofReal W).rpow s₀ = (ENNReal.ofReal A₀).rpow s₀ := by
        have hmul : ENNReal.ofReal (A₀ / W) * ENNReal.ofReal W =
            ENNReal.ofReal A₀ := by
          rw [← ENNReal.ofReal_mul (div_nonneg hA₀pos.le hWpos.le)]
          congr 1
          field_simp [ne_of_gt hWpos]
        calc
          (ENNReal.ofReal (A₀ / W)).rpow s₀ *
              (ENNReal.ofReal W).rpow s₀ =
            (ENNReal.ofReal (A₀ / W) * ENNReal.ofReal W).rpow s₀ := by
              exact (ENNReal.mul_rpow_of_nonneg _ _ hs₀pos.le).symm
          _ = (ENNReal.ofReal A₀).rpow s₀ := by rw [hmul]
      have hscale₁ : (ENNReal.ofReal (A₁ / W)).rpow s₁ *
          (ENNReal.ofReal W).rpow s₁ = (ENNReal.ofReal A₁).rpow s₁ := by
        have hmul : ENNReal.ofReal (A₁ / W) * ENNReal.ofReal W =
            ENNReal.ofReal A₁ := by
          rw [← ENNReal.ofReal_mul (div_nonneg hA₁pos.le hWpos.le)]
          congr 1
          field_simp [ne_of_gt hWpos]
        calc
          (ENNReal.ofReal (A₁ / W)).rpow s₁ *
              (ENNReal.ofReal W).rpow s₁ =
            (ENNReal.ofReal (A₁ / W) * ENNReal.ofReal W).rpow s₁ := by
              exact (ENNReal.mul_rpow_of_nonneg _ _ hs₁pos.le).symm
          _ = (ENNReal.ofReal A₁).rpow s₁ := by rw [hmul]
      have htpow (t : ℝ) (ht : 0 < t) :
          (ENNReal.ofReal t).rpow (-s₀) * ENNReal.ofReal (t ^ (p - 1)) =
            ENNReal.ofReal t ^ (p - s₀ - 1) := by
        have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
        calc
          (ENNReal.ofReal t).rpow (-s₀) * ENNReal.ofReal (t ^ (p - 1)) =
              (ENNReal.ofReal t) ^ (-s₀) * (ENNReal.ofReal t) ^ (p - 1) := by
                exact congrArg (fun z : ℝ≥0∞ => (ENNReal.ofReal t).rpow (-s₀) * z)
                  (ENNReal.ofReal_rpow_of_nonneg ht.le (by linarith : 0 ≤ p - 1)).symm
          _ = (ENNReal.ofReal t) ^ ((-s₀) + (p - 1)) := by
                rw [← ENNReal.rpow_add (x := ENNReal.ofReal t) (-s₀) (p - 1)
                  ht0 ENNReal.ofReal_ne_top]
          _ = ENNReal.ofReal t ^ (p - s₀ - 1) := by congr 1 <;> ring
      have hhighEq (t : ℝ) (ht : 0 < t) :
          (ENNReal.ofReal A₀).rpow s₀ * (ENNReal.ofReal t).rpow (-s₀) *
            Variation.complexLpMoment s₀ μ
              (Variation.layerCakeHighCutoff (t / W) f.1) *
              ENNReal.ofReal (t ^ (p - 1)) =
          weakTypeInterpolationHighWeighted μ s₀ p W A₀ f.1 t := by
        have hcut := weakTypeInterpolation_highCutoffMoment (μ := μ) hs₀pos hWpos
          f.1 f.2.1 t
        unfold weakTypeInterpolationHighWeighted
        calc
          (ENNReal.ofReal A₀).rpow s₀ * (ENNReal.ofReal t).rpow (-s₀) *
              Variation.complexLpMoment s₀ μ
                (Variation.layerCakeHighCutoff (t / W) f.1) *
              ENNReal.ofReal (t ^ (p - 1)) =
            ((ENNReal.ofReal (A₀ / W)).rpow s₀ *
              (ENNReal.ofReal W).rpow s₀) *
              Variation.complexLpMoment s₀ μ
                (Variation.layerCakeHighCutoff (t / W) f.1) *
              ((ENNReal.ofReal t).rpow (-s₀) * ENNReal.ofReal (t ^ (p - 1))) := by
                rw [hscale₀]
                ac_rfl
          _ = (ENNReal.ofReal (A₀ / W)).rpow s₀ *
              ((ENNReal.ofReal W).rpow s₀ *
                Variation.complexLpMoment s₀ μ
                  (Variation.layerCakeHighCutoff (t / W) f.1)) *
              ENNReal.ofReal t ^ (p - s₀ - 1) := by
                rw [htpow t ht]
                ac_rfl
          _ = (ENNReal.ofReal (A₀ / W)).rpow s₀ *
              weakTypeInterpolationHighMoment μ s₀ W f.1 t *
                ENNReal.ofReal t ^ (p - s₀ - 1) := by
                rw [← hcut]
          _ = weakTypeInterpolationHighWeighted μ s₀ p W A₀ f.1 t := by rfl
      have hlowEq (t : ℝ) (ht : 0 < t) :
          (ENNReal.ofReal A₁).rpow s₁ * (ENNReal.ofReal t).rpow (-s₁) *
            Variation.complexLpMoment s₁ μ
              (Variation.layerCakeLowCutoff (t / W) f.1) *
              ENNReal.ofReal (t ^ (p - 1)) =
          weakTypeInterpolationLowWeighted μ p s₁ W A₁ f.1 t := by
        have hcut := weakTypeInterpolation_lowCutoffMoment (μ := μ) hs₁pos hWpos
          f.1 f.2.1 t
        unfold weakTypeInterpolationLowWeighted
        calc
          (ENNReal.ofReal A₁).rpow s₁ * (ENNReal.ofReal t).rpow (-s₁) *
              Variation.complexLpMoment s₁ μ
                (Variation.layerCakeLowCutoff (t / W) f.1) *
              ENNReal.ofReal (t ^ (p - 1)) =
            ((ENNReal.ofReal (A₁ / W)).rpow s₁ *
              (ENNReal.ofReal W).rpow s₁) *
              Variation.complexLpMoment s₁ μ
                (Variation.layerCakeLowCutoff (t / W) f.1) *
              ((ENNReal.ofReal t).rpow (-s₁) * ENNReal.ofReal (t ^ (p - 1))) := by
                rw [hscale₁]
                ac_rfl
          _ = (ENNReal.ofReal (A₁ / W)).rpow s₁ *
              ((ENNReal.ofReal W).rpow s₁ *
                Variation.complexLpMoment s₁ μ
                  (Variation.layerCakeLowCutoff (t / W) f.1)) *
              ENNReal.ofReal t ^ (p - s₁ - 1) := by
                have htpow₁ :
                    (ENNReal.ofReal t).rpow (-s₁) * ENNReal.ofReal (t ^ (p - 1)) =
                      ENNReal.ofReal t ^ (p - s₁ - 1) := by
                  have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
                  calc
                    (ENNReal.ofReal t).rpow (-s₁) * ENNReal.ofReal (t ^ (p - 1)) =
                        (ENNReal.ofReal t) ^ (-s₁) * (ENNReal.ofReal t) ^ (p - 1) := by
                          exact congrArg
                            (fun z : ℝ≥0∞ => (ENNReal.ofReal t).rpow (-s₁) * z)
                            (ENNReal.ofReal_rpow_of_nonneg ht.le
                              (by linarith : 0 ≤ p - 1)).symm
                    _ = (ENNReal.ofReal t) ^ ((-s₁) + (p - 1)) := by
                          rw [← ENNReal.rpow_add (x := ENNReal.ofReal t) (-s₁) (p - 1)
                            ht0 ENNReal.ofReal_ne_top]
                    _ = ENNReal.ofReal t ^ (p - s₁ - 1) := by congr 1 <;> ring
                rw [htpow₁]
                ac_rfl
          _ = (ENNReal.ofReal (A₁ / W)).rpow s₁ *
              weakTypeInterpolationLowMoment μ s₁ W f.1 t *
                ENNReal.ofReal t ^ (p - s₁ - 1) := by
                rw [← hcut]
          _ = weakTypeInterpolationLowWeighted μ p s₁ W A₁ f.1 t := by rfl
      have hpoint (t : ℝ) (ht : 0 < t) :
          μ {x | 2 * t < U.apply f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
            weakTypeInterpolationHighWeighted μ s₀ p W A₀ f.1 t +
              weakTypeInterpolationLowWeighted μ p s₁ W A₁ f.1 t := by
        have hsplit := weakTypeInterpolation_levelSplit U f t (1 / W) ht
        rw [hdiv t] at hsplit
        have hmul :
            μ {x | 2 * t < U.apply f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
              ((ENNReal.ofReal A₀).rpow s₀ * (ENNReal.ofReal t).rpow (-s₀) *
                  Variation.complexLpMoment s₀ μ
                    (Variation.layerCakeHighCutoff (t / W) f.1) +
                (ENNReal.ofReal A₁).rpow s₁ * (ENNReal.ofReal t).rpow (-s₁) *
                  Variation.complexLpMoment s₁ μ
                    (Variation.layerCakeLowCutoff (t / W) f.1)) *
                ENNReal.ofReal (t ^ (p - 1)) := by
          gcongr
        rw [add_mul] at hmul
        rw [hhighEq t ht, hlowEq t ht] at hmul
        exact hmul
      have hweighted :
          (∫⁻ t in Ioi (0 : ℝ), μ {x | 2 * t < U.apply f x} *
            ENNReal.ofReal (t ^ (p - 1))) ≤
            (∫⁻ t in Ioi (0 : ℝ),
              weakTypeInterpolationHighWeighted μ s₀ p W A₀ f.1 t) +
            (∫⁻ t in Ioi (0 : ℝ),
              weakTypeInterpolationLowWeighted μ p s₁ W A₁ f.1 t) := by
        calc
          _ ≤ ∫⁻ t in Ioi (0 : ℝ),
                weakTypeInterpolationHighWeighted μ s₀ p W A₀ f.1 t +
                  weakTypeInterpolationLowWeighted μ p s₁ W A₁ f.1 t := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              exact hpoint t (mem_Ioi.mp ht)
          _ = _ := by
              rw [lintegral_add_left
                (measurable_weakTypeInterpolationHighWeighted μ s₀ p W A₀ f.1)]
      have hhighTail := weakTypeInterpolation_highWeightedMoment_integral
        hs₀pos h₀ hWpos hA₀pos f.1 f.2.1 f.2.2.2
      have hlowTail := weakTypeInterpolation_lowWeightedMoment_integral
        hp h₁ hs₁pos hWpos hA₁pos f.1 f.2.1 f.2.2.2
      have hB₀nonneg : 0 ≤ B₀ := by
        dsimp [B₀]
        exact mul_nonneg (Real.rpow_nonneg (div_nonneg hA₀pos.le hWpos.le) _)
          (div_nonneg (Real.rpow_nonneg hWpos.le _) (by linarith))
      have hB₁nonneg : 0 ≤ B₁ := by
        dsimp [B₁]
        exact mul_nonneg (Real.rpow_nonneg (div_nonneg hA₁pos.le hWpos.le) _)
          (div_nonneg (Real.rpow_nonneg hWpos.le _) (by linarith))
      have hrealCoeff : 2 ^ p * (p * (B₀ + B₁)) = C ^ p := by
        simpa [W, B₀, B₁, C] using
          (weakTypeInterpolation_optimizedCoefficient hs₀pos h₀ h₁ hA₀pos hA₁pos)
      have hcoeff : ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal p * (ENNReal.ofReal B₀ + ENNReal.ofReal B₁)) =
            ENNReal.ofReal (C ^ p) := by
        calc
          ENNReal.ofReal (2 ^ p) *
              (ENNReal.ofReal p * (ENNReal.ofReal B₀ + ENNReal.ofReal B₁)) =
            ENNReal.ofReal (2 ^ p) *
              (ENNReal.ofReal p * ENNReal.ofReal (B₀ + B₁)) := by
                rw [← ENNReal.ofReal_add hB₀nonneg hB₁nonneg]
          _ = ENNReal.ofReal (2 ^ p) * ENNReal.ofReal (p * (B₀ + B₁)) := by
                rw [← ENNReal.ofReal_mul hp.le]
          _ = ENNReal.ofReal (2 ^ p * (p * (B₀ + B₁))) := by
                rw [← ENNReal.ofReal_mul
                  (Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) p)]
          _ = ENNReal.ofReal (C ^ p) := by rw [hrealCoeff]
      calc
        (∫⁻ x, ENNReal.ofReal ((U.apply f x) ^ p) ∂μ) =
            ENNReal.ofReal (2 ^ p) *
              (ENNReal.ofReal p *
                ∫⁻ t in Ioi (0 : ℝ), μ {x | 2 * t < U.apply f x} *
                  ENNReal.ofReal (t ^ (p - 1))) := hlayer
        _ ≤ ENNReal.ofReal (2 ^ p) *
              (ENNReal.ofReal p *
                ((∫⁻ t in Ioi (0 : ℝ),
                    weakTypeInterpolationHighWeighted μ s₀ p W A₀ f.1 t) +
                  (∫⁻ t in Ioi (0 : ℝ),
                    weakTypeInterpolationLowWeighted μ p s₁ W A₁ f.1 t))) := by
              gcongr
        _ = ENNReal.ofReal (2 ^ p) *
              (ENNReal.ofReal p *
                ((ENNReal.ofReal B₀ * Variation.complexLpMoment p μ f.1) +
                  (ENNReal.ofReal B₁ * Variation.complexLpMoment p μ f.1))) := by
              rw [hhighTail, hlowTail]
        _ = ENNReal.ofReal (2 ^ p) *
              (ENNReal.ofReal p * (ENNReal.ofReal B₀ + ENNReal.ofReal B₁)) *
                Variation.complexLpMoment p μ f.1 := by
              rw [← add_mul]
              ac_rfl
        _ = ENNReal.ofReal (C ^ p) * Variation.complexLpMoment p μ f.1 := by
              rw [hcoeff]

private theorem weakTypeInterpolation_complexMoment_eq_eLpNorm_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ}
    (hp : 0 < p) (f : X → ℂ) (hf : Measurable f) :
    Variation.complexLpMoment p μ f = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  calc
    Variation.complexLpMoment p μ f = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      unfold Variation.complexLpMoment
      apply lintegral_congr_ae
      filter_upwards with x
      simp [ENNReal.rpow_eq_pow]
    _ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hf.aestronglyMeasurable,
        htoReal]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

private theorem weakTypeInterpolation_realOutputMoment_eq_eLpNorm_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ}
    (hp : 0 < p) (F : X → ℝ) (hFnonneg : ∀ x, 0 ≤ F x)
    (hFmeas : Measurable F) :
    (∫⁻ x, ENNReal.ofReal (F x ^ p) ∂μ) = eLpNorm F (ENNReal.ofReal p) μ ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  calc
    (∫⁻ x, ENNReal.ofReal (F x ^ p) ∂μ) =
        ∫⁻ x, ‖F x‖ₑ ^ p ∂μ := by
          apply lintegral_congr_ae
          filter_upwards with x
          rw [← ENNReal.ofReal_rpow_of_nonneg (hFnonneg x) hp.le]
          have hbase : ENNReal.ofReal (F x) = ‖F x‖ₑ := by
            rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hFnonneg x)]
          rw [hbase]
    _ = eLpNorm F (ENNReal.ofReal p) μ ^ p := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hFmeas.aestronglyMeasurable,
        htoReal]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- The exact finite-exponent `eLpNorm` conclusion of `lj:interpolation`. -/
theorem weakTypeInterpolation
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {s₀ p s₁ A₀ A₁ : ℝ}
    (U : WeakTypeInterpolationOperator μ s₀ s₁ A₀ A₁)
    (hs₀ : 1 ≤ s₀) (h₀ : s₀ < p) (h₁ : p < s₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (f : Variation.LayerCakeInput μ) :
    eLpNorm (U.apply f) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal
        (weakTypeInterpolationConstant s₀ p s₁ *
          A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁ *
          A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁) *
        eLpNorm f.1 (ENNReal.ofReal p) μ := by
  have hs₀pos : 0 < s₀ := lt_of_lt_of_le zero_lt_one hs₀
  have hp : 0 < p := hs₀pos.trans h₀
  have hs₁pos : 0 < s₁ := hp.trans h₁
  let C : ℝ := weakTypeInterpolationConstant s₀ p s₁ *
    A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁ *
    A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁
  have hden₀ : 0 < p - s₀ := by linarith
  have hden₁ : 0 < s₁ - p := by linarith
  have hθ₀ : 0 < weakTypeInterpolationTheta0 s₀ p s₁ := by
    have hnum : 0 < s₀ * (s₁ - p) := mul_pos hs₀pos (by linarith)
    have hden : 0 < p * (s₁ - s₀) := mul_pos hp (by linarith)
    dsimp [weakTypeInterpolationTheta0]
    exact div_pos hnum hden
  have hθ₁ : 0 < weakTypeInterpolationTheta1 s₀ p s₁ := by
    have hnum : 0 < s₁ * (p - s₀) := mul_pos hs₁pos (by linarith)
    have hden : 0 < p * (s₁ - s₀) := mul_pos hp (by linarith)
    dsimp [weakTypeInterpolationTheta1]
    exact div_pos hnum hden
  have hbracket : 0 < p * (1 / (p - s₀) + 1 / (s₁ - p)) := by
    apply mul_pos hp
    exact add_pos (div_pos zero_lt_one hden₀) (div_pos zero_lt_one hden₁)
  have hCnonneg : 0 ≤ C := by
    have hI : 0 ≤ weakTypeInterpolationConstant s₀ p s₁ := by
      dsimp [weakTypeInterpolationConstant]
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg hbracket.le _)
    have hA₀pow : 0 ≤ A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁ :=
      Real.rpow_nonneg hA₀ _
    have hA₁pow : 0 ≤ A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁ :=
      Real.rpow_nonneg hA₁ _
    dsimp [C]
    exact mul_nonneg (mul_nonneg hI hA₀pow) hA₁pow
  have hMoment := weakTypeInterpolation_moment U hs₀ h₀ h₁ hA₀ hA₁ f
  have hOutputMoment := weakTypeInterpolation_realOutputMoment_eq_eLpNorm_rpow μ hp
    (U.apply f) (U.nonneg_apply f) (U.measurable_apply f)
  have hInputMoment := weakTypeInterpolation_complexMoment_eq_eLpNorm_rpow μ hp
    f.1 f.2.1
  rw [hOutputMoment, hInputMoment,
    ← ENNReal.ofReal_rpow_of_nonneg hCnonneg hp.le] at hMoment
  have hroot := ENNReal.rpow_le_rpow hMoment (by positivity : 0 ≤ 1 / p)
  rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal C ^ p)
    (eLpNorm f.1 (ENNReal.ofReal p) μ ^ p) (by positivity : 0 ≤ 1 / p)] at hroot
  have hrootExp : p * (1 / p) = 1 := by field_simp [hp.ne']
  have hOutputRoot :
      (eLpNorm (U.apply f) (ENNReal.ofReal p) μ ^ p) ^ (1 / p) =
        eLpNorm (U.apply f) (ENNReal.ofReal p) μ := by
    rw [← ENNReal.rpow_mul, hrootExp, ENNReal.rpow_one]
  have hInputRoot :
      (eLpNorm f.1 (ENNReal.ofReal p) μ ^ p) ^ (1 / p) =
        eLpNorm f.1 (ENNReal.ofReal p) μ := by
    rw [← ENNReal.rpow_mul, hrootExp, ENNReal.rpow_one]
  have hConstantRoot : (ENNReal.ofReal C ^ p) ^ (1 / p) = ENNReal.ofReal C := by
    rw [← ENNReal.rpow_mul, hrootExp, ENNReal.rpow_one]
  rw [hOutputRoot, hConstantRoot, hInputRoot] at hroot
  simpa [C] using hroot

/-- Scalarize a complex-linear operator with values in a normed complex vector
space. The norm inherits the subadditivity and positive homogeneity required
by the scalar interpolation theorem. -/
def weakTypeInterpolationOperatorOfLinearMap
    {X : Type*} [MeasurableSpace X] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (μ : Measure X) (s₀ s₁ A₀ A₁ : ℝ)
    (T : (X → ℂ) →ₗ[ℂ] X → E)
    (hmeas : ∀ f : Variation.LayerCakeInput μ,
      Measurable (fun x => ‖T f.1 x‖))
    (hweak₀ : ∀ (f : Variation.LayerCakeInput μ) (t : ℝ), 0 < t →
      μ {x | t < ‖T f.1 x‖} ≤
        (ENNReal.ofReal A₀).rpow s₀ * (ENNReal.ofReal t).rpow (-s₀) *
          Variation.complexLpMoment s₀ μ f.1)
    (hweak₁ : ∀ (f : Variation.LayerCakeInput μ) (t : ℝ), 0 < t →
      μ {x | t < ‖T f.1 x‖} ≤
        (ENNReal.ofReal A₁).rpow s₁ * (ENNReal.ofReal t).rpow (-s₁) *
          Variation.complexLpMoment s₁ μ f.1) :
    WeakTypeInterpolationOperator μ s₀ s₁ A₀ A₁ where
  apply f x := ‖T f.1 x‖
  measurable_apply := hmeas
  nonneg_apply := fun _ _ => norm_nonneg _
  subadditive := by
    intro f g hfg x
    change ‖T (f.1 + g.1) x‖ ≤ ‖T f.1 x‖ + ‖T g.1 x‖
    rw [T.map_add]
    exact norm_add_le _ _
  positive_homogeneous := by
    intro f c hc hcf x
    have hsmul : c • f.1 = (c : ℂ) • f.1 := by
      funext y
      exact Complex.real_smul
    calc
      ‖T (c • f.1) x‖ = ‖T ((c : ℂ) • f.1) x‖ := by rw [hsmul]
      _ = ‖(c : ℂ) • (T f.1 x)‖ := by
        rw [T.map_smul]
        rfl
      _ = c * ‖T f.1 x‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  weak_s₀ := hweak₀
  weak_s₁ := hweak₁

/-- `lj:interpolation` for a complex-linear operator into a finite-dimensional
normed complex Euclidean space, with the output norm inside the `eLpNorm`. -/
theorem weakTypeInterpolation_finiteVector
    {X : Type*} [MeasurableSpace X] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {μ : Measure X} {s₀ p s₁ A₀ A₁ : ℝ}
    (T : (X → ℂ) →ₗ[ℂ] X → E)
    (hmeas : ∀ f : Variation.LayerCakeInput μ,
      Measurable (fun x => ‖T f.1 x‖))
    (hweak₀ : ∀ (f : Variation.LayerCakeInput μ) (t : ℝ), 0 < t →
      μ {x | t < ‖T f.1 x‖} ≤
        (ENNReal.ofReal A₀).rpow s₀ * (ENNReal.ofReal t).rpow (-s₀) *
          Variation.complexLpMoment s₀ μ f.1)
    (hweak₁ : ∀ (f : Variation.LayerCakeInput μ) (t : ℝ), 0 < t →
      μ {x | t < ‖T f.1 x‖} ≤
        (ENNReal.ofReal A₁).rpow s₁ * (ENNReal.ofReal t).rpow (-s₁) *
          Variation.complexLpMoment s₁ μ f.1)
    (hs₀ : 1 ≤ s₀) (h₀ : s₀ < p) (h₁ : p < s₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (f : Variation.LayerCakeInput μ) :
    eLpNorm (fun x => ‖T f.1 x‖) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal
        (weakTypeInterpolationConstant s₀ p s₁ *
          A₀ ^ weakTypeInterpolationTheta0 s₀ p s₁ *
          A₁ ^ weakTypeInterpolationTheta1 s₀ p s₁) *
        eLpNorm f.1 (ENNReal.ofReal p) μ := by
  simpa [weakTypeInterpolationOperatorOfLinearMap] using weakTypeInterpolation
    (weakTypeInterpolationOperatorOfLinearMap μ s₀ s₁ A₀ A₁ T hmeas hweak₀ hweak₁)
    hs₀ h₀ h₁ hA₀ hA₁ f

/-- A nonnegative scalar operator with a strong `L²` estimate and a strong
`L∞` estimate on bounded inputs. This is the second operator hypothesis in
`lj:interpolation`; the input class is the bounded finite-measure-support
class used for the layer-cake argument. -/
structure WeakTypeInterpolationStrongTwoInfinityOperator
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (A : ℝ) where
  apply : Variation.LayerCakeInput μ → X → ℝ
  measurable_apply : ∀ f, Measurable (apply f)
  nonneg_apply : ∀ f x, 0 ≤ apply f x
  subadditive : ∀ (f g : Variation.LayerCakeInput μ)
      (hfg : Variation.LayerCakeAdmissible μ (f.1 + g.1)) (x : X),
      apply ⟨f.1 + g.1, hfg⟩ x ≤ apply f x + apply g x
  strongL2 : ∀ f,
      (∫⁻ x, ENNReal.ofReal ((apply f x) ^ 2) ∂μ) ≤
        (ENNReal.ofReal A).rpow 2 * Variation.complexLpMoment 2 μ f.1
  strongLInf : ∀ (f : Variation.LayerCakeInput μ) (C : ℝ), 0 ≤ C →
      (∀ x, ‖f.1 x‖ ≤ C) → ∀ x, apply f x ≤ C

/-- The exact strong-`L²`/strong-`L∞` coefficient in `lj:interpolation`. -/
def weakTypeInterpolationStrongTwoInfinityConstant (q A : ℝ) : ℝ :=
  2 * (q / (q - 2)) ^ (1 / q) * A ^ (2 / q)

private theorem weakTypeInterpolation_strongTwoInfinity_levelBound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {q A : ℝ}
    (U : WeakTypeInterpolationStrongTwoInfinityOperator μ A)
    (hq : 2 < q) (_hA : 0 ≤ A) (f : Variation.LayerCakeInput μ)
    {t : ℝ} (ht : 0 < t) :
    μ {x | 2 * t < U.apply f x} * ENNReal.ofReal (t ^ (q - 1)) ≤
      weakTypeInterpolationHighWeighted μ 2 q 1 A f.1 t := by
  let highFn := Variation.layerCakeHighCutoff t f.1
  let lowFn := Variation.layerCakeLowCutoff t f.1
  let highInput : Variation.LayerCakeInput μ :=
    ⟨highFn, Variation.layerCakeAdmissible_highCutoff μ t f.2⟩
  let lowInput : Variation.LayerCakeInput μ :=
    ⟨lowFn, Variation.layerCakeAdmissible_lowCutoff μ t f.2⟩
  have hsplit : highFn + lowFn = f.1 := by
    funext x
    by_cases hx : t < ‖f.1 x‖
    · simp [highFn, lowFn, Variation.layerCakeHighCutoff,
        Variation.layerCakeLowCutoff, hx]
    · have hx' : ‖f.1 x‖ ≤ t := le_of_not_gt hx
      simp [highFn, lowFn, Variation.layerCakeHighCutoff,
        Variation.layerCakeLowCutoff, hx, hx']
  have hsum : Variation.LayerCakeAdmissible μ (highFn + lowFn) := by
    rw [hsplit]
    exact f.2
  have htriangle (x : X) :
      U.apply f x ≤ U.apply highInput x + U.apply lowInput x := by
    calc
      U.apply f x = U.apply ⟨highFn + lowFn, hsum⟩ x := by
        congr 1
        exact Subtype.ext hsplit.symm
      _ ≤ U.apply highInput x + U.apply lowInput x :=
        U.subadditive highInput lowInput hsum x
  have hlowBound : ∀ x, U.apply lowInput x ≤ t := by
    apply U.strongLInf lowInput t ht.le
    intro x
    by_cases hx : ‖f.1 x‖ ≤ t
    · simp [lowInput, lowFn, Variation.layerCakeLowCutoff, hx]
    · have hx' : t < ‖f.1 x‖ := lt_of_not_ge hx
      have hx'' : ¬ ‖f.1 x‖ ≤ t := not_le_of_gt hx'
      simp [lowInput, lowFn, Variation.layerCakeLowCutoff, hx'']
      exact ht.le
  have hset : {x | 2 * t < U.apply f x} ⊆ {x | t < U.apply highInput x} := by
    intro x hx
    change 2 * t < U.apply f x at hx
    have h := htriangle x
    have hlow := hlowBound x
    have hxsum : 2 * t < U.apply highInput x + U.apply lowInput x := lt_of_lt_of_le hx h
    have hcancel : t + t < U.apply highInput x + t := by
      calc
        t + t = 2 * t := by ring
        _ < U.apply highInput x + U.apply lowInput x := hxsum
        _ ≤ U.apply highInput x + t := by gcongr
    exact (add_lt_add_iff_right t).mp hcancel
  let G : X → ℝ≥0∞ := fun x => ENNReal.ofReal ((U.apply highInput x) ^ 2)
  have hGmeas : Measurable G :=
    ENNReal.continuous_ofReal.measurable.comp
      ((U.measurable_apply highInput).pow_const 2)
  have hGnonneg (x : X) : 0 ≤ (U.apply highInput x) ^ 2 := sq_nonneg _
  have htarget : ENNReal.ofReal (t ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos ht)).ne'
  have htargetTop : ENNReal.ofReal (t ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hmark := MeasureTheory.meas_ge_le_lintegral_div
    (μ := μ) (f := G) hGmeas.aemeasurable htarget htargetTop
  have hstrict : μ {x | t < U.apply highInput x} ≤
      μ {x | ENNReal.ofReal (t ^ 2) ≤ G x} := by
    apply measure_mono
    intro x hx
    change t < U.apply highInput x at hx
    change ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal ((U.apply highInput x) ^ 2)
    apply (ENNReal.ofReal_le_ofReal_iff (hGnonneg x)).2
    nlinarith [U.nonneg_apply highInput x]
  have hlevel : μ {x | 2 * t < U.apply f x} ≤
      ((ENNReal.ofReal A).rpow 2 *
        Variation.complexLpMoment 2 μ highFn) / ENNReal.ofReal (t ^ 2) := by
    calc
      μ {x | 2 * t < U.apply f x} ≤ μ {x | t < U.apply highInput x} := measure_mono hset
      _ ≤ μ {x | ENNReal.ofReal (t ^ 2) ≤ G x} := hstrict
      _ ≤ (∫⁻ x, G x ∂μ) / ENNReal.ofReal (t ^ 2) := hmark
      _ ≤ ((ENNReal.ofReal A).rpow 2 *
            Variation.complexLpMoment 2 μ highFn) / ENNReal.ofReal (t ^ 2) := by
            gcongr
            exact U.strongL2 highInput
  have hdenom : ENNReal.ofReal (t ^ 2) = (ENNReal.ofReal t).rpow 2 := by
    rw [← Real.rpow_natCast t 2]
    exact (ENNReal.ofReal_rpow_of_nonneg ht.le
      (by norm_num : 0 ≤ (2 : ℝ))).symm
  have hmarkov : μ {x | 2 * t < U.apply f x} ≤
      (ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (-2) *
        Variation.complexLpMoment 2 μ highFn := by
    rw [hdenom] at hlevel
    calc
      μ {x | 2 * t < U.apply f x} ≤
          ((ENNReal.ofReal A).rpow 2 *
            Variation.complexLpMoment 2 μ highFn) / (ENNReal.ofReal t).rpow 2 := hlevel
      _ = (ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (-2) *
            Variation.complexLpMoment 2 μ highFn := by
            have hneg : (ENNReal.ofReal t).rpow (-2) =
                ((ENNReal.ofReal t).rpow 2)⁻¹ := by
              exact ENNReal.rpow_neg (ENNReal.ofReal t) 2
            rw [div_eq_mul_inv, hneg]
            ac_rfl
  have hweight : ENNReal.ofReal (t ^ (q - 1)) =
      (ENNReal.ofReal t).rpow (q - 1) := by
    exact (ENNReal.ofReal_rpow_of_nonneg ht.le (by linarith : 0 ≤ q - 1)).symm
  have hcombine : (ENNReal.ofReal t).rpow (-2) *
      ENNReal.ofReal (t ^ (q - 1)) = (ENNReal.ofReal t).rpow (q - 3) := by
    rw [hweight]
    calc
      (ENNReal.ofReal t).rpow (-2) * (ENNReal.ofReal t).rpow (q - 1) =
          (ENNReal.ofReal t).rpow ((-2) + (q - 1)) :=
        (ENNReal.rpow_add (x := ENNReal.ofReal t) (-2) (q - 1)
          (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top).symm
      _ = (ENNReal.ofReal t).rpow (q - 3) := by congr 1 <;> ring
  have hcutoff := weakTypeInterpolation_highCutoffMoment
    (μ := μ) (s₀ := (2 : ℝ)) (W := (1 : ℝ)) (by norm_num) (by norm_num)
    f.1 f.2.1 t
  have hweighted :
      ((ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (-2) *
        Variation.complexLpMoment 2 μ highFn) * ENNReal.ofReal (t ^ (q - 1)) =
       weakTypeInterpolationHighWeighted μ 2 q 1 A f.1 t := by
    unfold weakTypeInterpolationHighWeighted
    rw [hcutoff]
    have hcut : t / 1 = t := by ring
    rw [hcut]
    have hexp : q - 3 = q - 2 - 1 := by ring
    calc
      (ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (-2) *
          Variation.complexLpMoment 2 μ highFn * ENNReal.ofReal (t ^ (q - 1)) =
        (ENNReal.ofReal A).rpow 2 *
          ((ENNReal.ofReal t).rpow (-2) * ENNReal.ofReal (t ^ (q - 1))) *
            Variation.complexLpMoment 2 μ highFn := by ac_rfl
      _ = (ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (q - 3) *
            Variation.complexLpMoment 2 μ highFn := by rw [hcombine]
      _ = (ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (q - 2 - 1) *
            Variation.complexLpMoment 2 μ highFn := by rw [hexp]
      _ = (ENNReal.ofReal (A / 1)).rpow 2 *
          ((ENNReal.ofReal 1).rpow 2 *
            Variation.complexLpMoment 2 μ (Variation.layerCakeHighCutoff t f.1)) *
              (ENNReal.ofReal t) ^ (q - 2 - 1) := by
            have hAdiv : (ENNReal.ofReal (A / 1)).rpow 2 =
                (ENNReal.ofReal A).rpow 2 := by
              congr 1
              congr 1
              ring
            have hone : (ENNReal.ofReal (1 : ℝ)).rpow 2 = 1 := by norm_num
            rw [hAdiv, hone]
            simp only [one_mul]
            calc
              (ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (q - 2 - 1) *
                  Variation.complexLpMoment 2 μ highFn =
                (ENNReal.ofReal A).rpow 2 *
                  ((ENNReal.ofReal t).rpow (q - 2 - 1) *
                    Variation.complexLpMoment 2 μ highFn) := by rw [mul_assoc]
              _ = (ENNReal.ofReal A).rpow 2 *
                    (Variation.complexLpMoment 2 μ highFn *
                      (ENNReal.ofReal t).rpow (q - 2 - 1)) := by
                    exact congrArg
                      (fun z : ℝ≥0∞ => (ENNReal.ofReal A).rpow 2 * z)
                      (mul_comm ((ENNReal.ofReal t).rpow (q - 2 - 1))
                        (Variation.complexLpMoment 2 μ highFn))
              _ = (ENNReal.ofReal A).rpow 2 *
                    Variation.complexLpMoment 2 μ highFn *
                      (ENNReal.ofReal t) ^ (q - 2 - 1) := by
                    have hpow : (ENNReal.ofReal t).rpow (q - 2 - 1) =
                        ENNReal.ofReal t ^ (q - 2 - 1) := rfl
                    rw [mul_assoc, hpow]
  calc
    μ {x | 2 * t < U.apply f x} * ENNReal.ofReal (t ^ (q - 1)) ≤
        ((ENNReal.ofReal A).rpow 2 * (ENNReal.ofReal t).rpow (-2) *
          Variation.complexLpMoment 2 μ highFn) * ENNReal.ofReal (t ^ (q - 1)) := by
            gcongr
    _ = weakTypeInterpolationHighWeighted μ 2 q 1 A f.1 t := hweighted

/-- The p-moment form of the strong-`L²`/strong-`L∞` interpolation estimate.
The coefficient is the exact qth power obtained from layer cake and Tonelli. -/
theorem weakTypeInterpolationStrongTwoInfinity_moment
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {q A : ℝ}
    (U : WeakTypeInterpolationStrongTwoInfinityOperator μ A)
    (hq : 2 < q) (hA : 0 ≤ A) (f : Variation.LayerCakeInput μ) :
    (∫⁻ x, ENNReal.ofReal ((U.apply f x) ^ q) ∂μ) ≤
      ENNReal.ofReal (2 ^ q * (q / (q - 2) * A ^ 2)) *
        Variation.complexLpMoment q μ f.1 := by
  have hqpos : 0 < q := by linarith
  have hFnonneg : ∀ x, 0 ≤ U.apply f x := U.nonneg_apply f
  have hFmeas : Measurable (U.apply f) := U.measurable_apply f
  have hlayer := weakTypeInterpolation_outputLayercake (μ := μ) hqpos
    (U.apply f) hFnonneg hFmeas
  by_cases hAzero : A = 0
  · have hlevelzero (t : ℝ) (ht : 0 < t) :
        μ {x | 2 * t < U.apply f x} * ENNReal.ofReal (t ^ (q - 1)) = 0 := by
      have hlevel := weakTypeInterpolation_strongTwoInfinity_levelBound
        U hq hA f ht
      have hweightBound :
          weakTypeInterpolationHighWeighted μ 2 q 1 A f.1 t = 0 := by
        rw [weakTypeInterpolationHighWeighted, hAzero]
        simp
      rw [hweightBound] at hlevel
      exact le_antisymm hlevel (by positivity)
    have hzeroae :
        (fun t : ℝ => μ {x | 2 * t < U.apply f x} *
          ENNReal.ofReal (t ^ (q - 1))) =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hlevelzero t (mem_Ioi.mp ht)
    have hmomentzero :
        (∫⁻ x, ENNReal.ofReal ((U.apply f x) ^ q) ∂μ) = 0 := by
      rw [hlayer, lintegral_congr_ae hzeroae]
      simp
    rw [hmomentzero, hAzero]
    simp
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    have htail := weakTypeInterpolation_highWeightedMoment_integral
      (μ := μ) (s₀ := (2 : ℝ)) (p := q) (W := (1 : ℝ)) (A₀ := A)
      (by norm_num) (by linarith) (by norm_num) hApos f.1 f.2.1 f.2.2.2
    have htail' :
        (∫⁻ t in Ioi (0 : ℝ), weakTypeInterpolationHighWeighted μ 2 q 1 A f.1 t) =
          ENNReal.ofReal (A ^ 2 / (q - 2)) *
            Variation.complexLpMoment q μ f.1 := by
      simpa [div_one, Real.one_rpow, div_eq_mul_inv] using htail
    have hlevelIntegral :
        (∫⁻ t in Ioi (0 : ℝ),
          μ {x | 2 * t < U.apply f x} * ENNReal.ofReal (t ^ (q - 1))) ≤
        ∫⁻ t in Ioi (0 : ℝ), weakTypeInterpolationHighWeighted μ 2 q 1 A f.1 t := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact weakTypeInterpolation_strongTwoInfinity_levelBound U hq hA f
        (mem_Ioi.mp ht)
    have hBnonneg : 0 ≤ A ^ 2 / (q - 2) := by positivity
    have hqnonneg : 0 ≤ q := hqpos.le
    have h2nonneg : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) q
    have hrealCoeff :
        2 ^ q * (q * (A ^ 2 / (q - 2))) =
          2 ^ q * (q / (q - 2) * A ^ 2) := by
      have hden : q - 2 ≠ 0 := ne_of_gt (by linarith : 0 < q - 2)
      field_simp [hden]
    calc
      (∫⁻ x, ENNReal.ofReal ((U.apply f x) ^ q) ∂μ) =
          ENNReal.ofReal (2 ^ q) *
            (ENNReal.ofReal q *
              ∫⁻ t in Ioi (0 : ℝ),
                μ {x | 2 * t < U.apply f x} * ENNReal.ofReal (t ^ (q - 1))) := hlayer
      _ ≤ ENNReal.ofReal (2 ^ q) *
            (ENNReal.ofReal q *
              ∫⁻ t in Ioi (0 : ℝ),
                weakTypeInterpolationHighWeighted μ 2 q 1 A f.1 t) := by
              gcongr
      _ = ENNReal.ofReal (2 ^ q) *
            (ENNReal.ofReal q *
              (ENNReal.ofReal (A ^ 2 / (q - 2)) *
                Variation.complexLpMoment q μ f.1)) := by rw [htail']
      _ = ENNReal.ofReal
            (2 ^ q * (q / (q - 2) * A ^ 2)) *
              Variation.complexLpMoment q μ f.1 := by
              calc
                ENNReal.ofReal (2 ^ q) *
                    (ENNReal.ofReal q *
                      (ENNReal.ofReal (A ^ 2 / (q - 2)) *
                        Variation.complexLpMoment q μ f.1)) =
                  (ENNReal.ofReal (2 ^ q) * ENNReal.ofReal q *
                    ENNReal.ofReal (A ^ 2 / (q - 2))) *
                      Variation.complexLpMoment q μ f.1 := by ac_rfl
                _ = ENNReal.ofReal
                      (2 ^ q * (q * (A ^ 2 / (q - 2)))) *
                      Variation.complexLpMoment q μ f.1 := by
                      have hmul :
                          ENNReal.ofReal (2 ^ q) * ENNReal.ofReal q *
                              ENNReal.ofReal (A ^ 2 / (q - 2)) =
                            ENNReal.ofReal (2 ^ q *
                              (q * (A ^ 2 / (q - 2)))) := by
                        calc
                          ENNReal.ofReal (2 ^ q) * ENNReal.ofReal q *
                              ENNReal.ofReal (A ^ 2 / (q - 2)) =
                            ENNReal.ofReal (2 ^ q) *
                              (ENNReal.ofReal q *
                                ENNReal.ofReal (A ^ 2 / (q - 2))) := by ac_rfl
                          _ = ENNReal.ofReal (2 ^ q) *
                                ENNReal.ofReal (q * (A ^ 2 / (q - 2))) := by
                                  rw [← ENNReal.ofReal_mul hqnonneg]
                          _ = ENNReal.ofReal (2 ^ q *
                                (q * (A ^ 2 / (q - 2)))) := by
                                  rw [← ENNReal.ofReal_mul
                                    h2nonneg]
                      exact congrArg (fun z : ℝ≥0∞ =>
                        z * Variation.complexLpMoment q μ f.1) hmul
                _ = ENNReal.ofReal
                      (2 ^ q * (q / (q - 2) * A ^ 2)) *
                      Variation.complexLpMoment q μ f.1 := by rw [hrealCoeff]

/-- The exact `L^q` norm form of the strong-`L²`/strong-`L∞`
interpolation estimate in `lj:interpolation`. -/
theorem weakTypeInterpolationStrongTwoInfinity
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {q A : ℝ}
    (U : WeakTypeInterpolationStrongTwoInfinityOperator μ A)
    (hq : 2 < q) (hA : 0 ≤ A) (f : Variation.LayerCakeInput μ) :
    eLpNorm (U.apply f) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q A) *
        eLpNorm f.1 (ENNReal.ofReal q) μ := by
  have hqpos : 0 < q := by linarith
  let C := weakTypeInterpolationStrongTwoInfinityConstant q A
  have hCnonneg : 0 ≤ C := by
    dsimp [C, weakTypeInterpolationStrongTwoInfinityConstant]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg hA _)
  have hbase : 0 ≤ q / (q - 2) := by positivity
  have hrootBase : ((q / (q - 2)) ^ (1 / q)) ^ q = q / (q - 2) := by
    rw [← Real.rpow_mul hbase]
    have hexp : (1 / q) * q = 1 := by field_simp [hqpos.ne']
    rw [hexp, Real.rpow_one]
  have hrootA : (A ^ (2 / q)) ^ q = A ^ 2 := by
    rw [← Real.rpow_mul hA]
    have hexp : (2 / q) * q = 2 := by field_simp [hqpos.ne']
    rw [hexp]
    exact Real.rpow_natCast A 2
  have hcoeff :
      (2 : ℝ) ^ q * (q / (q - 2) * A ^ 2) = C ^ q := by
    dsimp [C, weakTypeInterpolationStrongTwoInfinityConstant]
    have hgroup :
        2 * (q / (q - 2)) ^ (1 / q) * A ^ (2 / q) =
          2 * ((q / (q - 2)) ^ (1 / q) * A ^ (2 / q)) := by ring
    rw [hgroup, Real.mul_rpow (by norm_num) (by positivity),
      Real.mul_rpow (Real.rpow_nonneg hbase _) (Real.rpow_nonneg hA _),
      hrootBase, hrootA]
  have hMoment := weakTypeInterpolationStrongTwoInfinity_moment U hq hA f
  have hOutputMoment := weakTypeInterpolation_realOutputMoment_eq_eLpNorm_rpow
    μ hqpos (U.apply f) (U.nonneg_apply f) (U.measurable_apply f)
  have hInputMoment := weakTypeInterpolation_complexMoment_eq_eLpNorm_rpow
    μ hqpos f.1 f.2.1
  rw [hOutputMoment, hInputMoment, hcoeff,
    ← ENNReal.ofReal_rpow_of_nonneg hCnonneg hqpos.le] at hMoment
  have hroot := ENNReal.rpow_le_rpow hMoment (by positivity : 0 ≤ 1 / q)
  rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal C ^ q)
    (eLpNorm f.1 (ENNReal.ofReal q) μ ^ q) (by positivity : 0 ≤ 1 / q)] at hroot
  have hrootExp : q * (1 / q) = 1 := by field_simp [hqpos.ne']
  have hOutputRoot :
      (eLpNorm (U.apply f) (ENNReal.ofReal q) μ ^ q) ^ (1 / q) =
        eLpNorm (U.apply f) (ENNReal.ofReal q) μ := by
    rw [← ENNReal.rpow_mul, hrootExp, ENNReal.rpow_one]
  have hInputRoot :
      (eLpNorm f.1 (ENNReal.ofReal q) μ ^ q) ^ (1 / q) =
        eLpNorm f.1 (ENNReal.ofReal q) μ := by
    rw [← ENNReal.rpow_mul, hrootExp, ENNReal.rpow_one]
  have hConstantRoot : (ENNReal.ofReal C ^ q) ^ (1 / q) = ENNReal.ofReal C := by
    rw [← ENNReal.rpow_mul, hrootExp, ENNReal.rpow_one]
  rw [hOutputRoot, hConstantRoot, hInputRoot] at hroot
  simpa [C, weakTypeInterpolationStrongTwoInfinityConstant] using hroot

/-- Scalarize a finite-dimensional complex-linear operator while preserving
the strong `L²` and bounded-input `L∞` hypotheses for its output norm. -/
def weakTypeInterpolationStrongTwoInfinityOperatorOfLinearMap
    {X : Type*} [MeasurableSpace X] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (μ : Measure X) (A : ℝ) (T : (X → ℂ) →ₗ[ℂ] X → E)
    (hmeas : ∀ f : Variation.LayerCakeInput μ,
      Measurable (fun x => ‖T f.1 x‖))
    (hstrongL2 : ∀ f : Variation.LayerCakeInput μ,
      (∫⁻ x, ENNReal.ofReal ((‖T f.1 x‖) ^ 2) ∂μ) ≤
        (ENNReal.ofReal A).rpow 2 * Variation.complexLpMoment 2 μ f.1)
    (hstrongLInf : ∀ (f : Variation.LayerCakeInput μ) (C : ℝ), 0 ≤ C →
      (∀ x, ‖f.1 x‖ ≤ C) → ∀ x, ‖T f.1 x‖ ≤ C) :
    WeakTypeInterpolationStrongTwoInfinityOperator μ A where
  apply f x := ‖T f.1 x‖
  measurable_apply := hmeas
  nonneg_apply := fun _ _ => norm_nonneg _
  subadditive := by
    intro f g hfg x
    change ‖T (f.1 + g.1) x‖ ≤ ‖T f.1 x‖ + ‖T g.1 x‖
    rw [T.map_add]
    exact norm_add_le _ _
  strongL2 := hstrongL2
  strongLInf := by
    intro f C hC hbound
    exact hstrongLInf f C hC hbound

/-- The strong `L²`/`L∞` conclusion of `lj:interpolation` for a linear map
into a finite-dimensional normed complex vector space. -/
theorem weakTypeInterpolationStrongTwoInfinity_finiteVector
    {X : Type*} [MeasurableSpace X] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {μ : Measure X} {q A : ℝ}
    (T : (X → ℂ) →ₗ[ℂ] X → E)
    (hmeas : ∀ f : Variation.LayerCakeInput μ,
      Measurable (fun x => ‖T f.1 x‖))
    (hstrongL2 : ∀ f : Variation.LayerCakeInput μ,
      (∫⁻ x, ENNReal.ofReal ((‖T f.1 x‖) ^ 2) ∂μ) ≤
        (ENNReal.ofReal A).rpow 2 * Variation.complexLpMoment 2 μ f.1)
    (hstrongLInf : ∀ (f : Variation.LayerCakeInput μ) (C : ℝ), 0 ≤ C →
      (∀ x, ‖f.1 x‖ ≤ C) → ∀ x, ‖T f.1 x‖ ≤ C)
    (hq : 2 < q) (hA : 0 ≤ A) (f : Variation.LayerCakeInput μ) :
    eLpNorm (fun x => ‖T f.1 x‖) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (weakTypeInterpolationStrongTwoInfinityConstant q A) *
        eLpNorm f.1 (ENNReal.ofReal q) μ := by
  exact weakTypeInterpolationStrongTwoInfinity
    (weakTypeInterpolationStrongTwoInfinityOperatorOfLinearMap
      μ A T hmeas hstrongL2 hstrongLInf) hq hA f

/-- The consistency data for extending a raw finite-input operator to
`L^p`, with its action preserved almost everywhere on bounded
finite-measure-support inputs. -/
structure WeakTypeInterpolationLpExtension
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (p : ℝ) (hp : 1 ≤ p)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (T : (X → ℂ) →ₗ[ℂ] X → E) where
  map : letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp⟩
    Lp ℂ (ENNReal.ofReal p) μ →L[ℂ] Lp E (ENNReal.ofReal p) μ
  agrees : letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp⟩
    ∀ (g : Variation.LayerCakeInput μ)
      (hg : MemLp g.1 (ENNReal.ofReal p) μ),
      ((map (hg.toLp g.1) : X → E) =ᵐ[μ] T g.1)

/-- A norm estimate proved on the common dense class of bounded
finite-measure-support inputs extends to every `L^p` input when the raw
linear operator has a continuous `L^p` extension agreeing almost everywhere
on that class. The proof uses the class's approximating sequence, one
almost-everywhere convergent subsequence of the extended outputs, and Fatou. -/
theorem weakTypeInterpolation_extend_dense
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {p : ℝ} (hp : 1 ≤ p)
    (T : (X → ℂ) →ₗ[ℂ] X → E)
    (extension : WeakTypeInterpolationLpExtension μ p hp T)
    (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ (g : Variation.LayerCakeInput μ)
      (_hg : MemLp g.1 (ENNReal.ofReal p) μ),
      eLpNorm (fun x => ‖T g.1 x‖) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal C * eLpNorm g.1 (ENNReal.ofReal p) μ)
    (f : Lp ℂ (ENNReal.ofReal p) μ) :
    eLpNorm (fun x => ‖(extension.map f : X → E) x‖)
        (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal C * eLpNorm (f : X → ℂ) (ENNReal.ofReal p) μ := by
  let P : ℝ≥0∞ := ENNReal.ofReal p
  let _ : Fact (1 ≤ P) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  have hp0 : 0 < p := by linarith
  obtain ⟨g, _inputNs, hgMem, _hinputNs, hgnorm, _hinputAE⟩ :=
    Variation.exists_layerCakeInput_approximation μ hp0 (f : X → ℂ)
      (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  let gLp : ℕ → Lp ℂ P μ := fun n => (hgMem n).toLp (g n).1
  have hgLpTendsto : Tendsto gLp atTop (𝓝 f) := by
    simpa only [P, gLp, Lp.toLp_coeFn] using
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => (g n).1) hgMem (f : X → ℂ) (Lp.memLp f)).mpr hgnorm
  let outputs : ℕ → Lp E P μ := fun n => extension.map (gLp n)
  have houtputsTendsto : Tendsto outputs atTop (𝓝 (extension.map f)) :=
    (extension.map.continuous.tendsto f).comp hgLpTendsto
  obtain ⟨ns, hns, houtputsAE⟩ :=
    (MeasureTheory.tendstoInMeasure_of_tendsto_Lp houtputsTendsto).exists_seq_tendsto_ae
  have hagree (n : ℕ) : ∀ᵐ x ∂μ,
      (outputs (ns n) : X → E) x = T (g (ns n)).1 x := by
    simpa only [outputs, gLp, Filter.EventuallyEq] using
      extension.agrees (g (ns n)) (hgMem (ns n))
  have hagreeAll : ∀ᵐ x ∂μ, ∀ n,
      (outputs (ns n) : X → E) x = T (g (ns n)).1 x := by
    rw [ae_all_iff]
    exact hagree
  have hrawAE : ∀ᵐ x ∂μ,
      Tendsto (fun n => T (g (ns n)).1 x) atTop
        (𝓝 ((extension.map f : X → E) x)) := by
    filter_upwards [houtputsAE, hagreeAll] with x hx heq
    exact hx.congr' (Filter.Eventually.of_forall heq)
  have hrawMeas (n : ℕ) : AEStronglyMeasurable (T (g (ns n)).1) μ := by
    apply (Lp.stronglyMeasurable (outputs (ns n))).aestronglyMeasurable.congr
    exact hagree n
  have htargetMeas : AEStronglyMeasurable
      ((extension.map f : X → E)) μ :=
    (Lp.stronglyMeasurable (extension.map f)).aestronglyMeasurable
  have hfatou :
      eLpNorm ((extension.map f : X → E)) P μ ≤
        atTop.liminf (fun n => eLpNorm (T (g (ns n)).1) P μ) :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm
      hrawMeas ((extension.map f : X → E)) htargetMeas hrawAE
  have hfiniteBound (n : ℕ) :
      eLpNorm (T (g (ns n)).1) P μ ≤
        ENNReal.ofReal C * eLpNorm (g (ns n)).1 P μ := by
    rw [← eLpNorm_norm (T (g (ns n)).1) (hrawMeas n)]
    exact hbound (g (ns n)) (hgMem (ns n))
  have hnormTendsto : Tendsto (fun n => eLpNorm (g (ns n)).1 P μ)
      atTop (𝓝 (eLpNorm (f : X → ℂ) P μ)) := by
    have hsubseq : Tendsto (fun n => gLp (ns n)) atTop (𝓝 f) :=
      hgLpTendsto.comp hns.tendsto_atTop
    have henorm := continuous_enorm.continuousAt.tendsto.comp hsubseq
    have henorm' : Tendsto (fun n => eLpNorm (g (ns n)).1 P μ)
        atTop (𝓝 ‖f‖ₑ) := by
      simpa only [gLp, Lp.enorm_toLp, Function.comp_def] using henorm
    simpa only [Lp.enorm_def, P] using henorm'
  have hrhsTendsto : Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (g (ns n)).1 P μ) atTop
      (𝓝 (ENNReal.ofReal C * eLpNorm (f : X → ℂ) P μ)) :=
    ENNReal.Tendsto.const_mul hnormTendsto
      (Or.inr ENNReal.ofReal_ne_top)
  have hliminf :
      atTop.liminf (fun n => eLpNorm (T (g (ns n)).1) P μ) ≤
        ENNReal.ofReal C * eLpNorm (f : X → ℂ) P μ := by
    calc
      atTop.liminf (fun n => eLpNorm (T (g (ns n)).1) P μ) ≤
          atTop.liminf
            (fun n => ENNReal.ofReal C * eLpNorm (g (ns n)).1 P μ) :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hfiniteBound)
      _ = ENNReal.ofReal C * eLpNorm (f : X → ℂ) P μ := hrhsTendsto.liminf_eq
  have hvectorBound := hfatou.trans hliminf
  simpa only [P, eLpNorm_norm (extension.map f : X → E) htargetMeas] using
    hvectorBound

end

end FractionalPrimes.Literature.JSW

end
