module

public import FractionalPrimes.Literature.JSW.Cutoffs
public import FractionalPrimes.Literature.Variation.FiniteChainVariation
public import FractionalPrimes.Literature.Variation.FiniteOrderedVariation
public import FractionalPrimes.Literature.Variation.JumpCount
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Map

/-!
# JSW real-line conventions

This module records the Fourier, convolution, dilation, scale, jump-count,
and increment-variation conventions in `lj:conventions`.  Countable variation
is the existing supremum of finite ordered chains with values in `ℝ≥0∞`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.JSW

open MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace

noncomputable section

/-- The real-line Fourier transform with phase `exp(-2π i x ξ)`. -/
def jswFourier (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  𝓕 f ξ

/-- The Fourier convention written as an ordinary complex exponential. -/
theorem jswFourier_eq_integral (f : ℝ → ℂ) (ξ : ℝ) :
    jswFourier f ξ =
      ∫ x, Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) * f x ∂volume := by
  rw [jswFourier, Real.fourier_eq']
  simp only [Real.inner_apply, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  congr 1
  congr 1
  ring_nf

/-- Convolution of a function with a measure, using the `f(x-y)` convention. -/
def jswConvolution (μ : Measure ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f (x - y) ∂μ

/-- Pushforward dilation of a measure by `y ↦ t*y`, for `t > 0`. -/
def jswMeasureDilation (μ : Measure ℝ) (_hμ : IsFiniteMeasure μ)
    (t : ℝ) (_ht : 0 < t) : Measure ℝ :=
  Measure.map (fun y : ℝ => t * y) μ

theorem jswMeasureDilation_apply (μ : Measure ℝ) (hμ : IsFiniteMeasure μ)
    (t : ℝ) (ht : 0 < t)
    (s : Set ℝ) (hs : MeasurableSet s) :
    jswMeasureDilation μ hμ t ht s = μ ((fun y : ℝ => t * y) ⁻¹' s) := by
  exact Measure.map_apply (by fun_prop) hs

/-- Dilation of a density: `h_t(x) = t⁻¹ h(x/t)`. -/
def jswDensityDilation (h : ℝ → ℂ) (t : ℝ) (_ht : 0 < t) (x : ℝ) : ℂ :=
  (t⁻¹ : ℝ) • h (x / t)

/-- The base `b = 2^a` used for geometric scales. -/
def jswB (a : ℝ) (_ha : 0 < a) : ℝ := Real.rpow 2 a

/-- The geometric scale `τ_k = b^k`. -/
def jswTau (a : ℝ) (ha : 0 < a) (k : ℤ) : ℝ := jswB a ha ^ k

/-- The dyadic comparison exponent `m_k = floor(a*k)`. -/
def jswM (a : ℝ) (_ha : 0 < a) (k : ℤ) : ℤ := Int.floor (a * (k : ℝ))

/-- The exact multiplicity bound `M_a = ceil(1/a) + 1`. -/
def jswMultiplicity (a : ℝ) (_ha : 0 < a) : ℕ := Nat.ceil (1 / a) + 1

theorem jswB_gt_one {a : ℝ} (ha : 0 < a) : 1 < jswB a ha := by
  rw [jswB, ← Real.rpow_zero (2 : ℝ)]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ha

theorem jswTau_eq_rpow (a : ℝ) (ha : 0 < a) (k : ℤ) :
    jswTau a ha k = Real.rpow 2 (a * (k : ℝ)) := by
  rw [jswTau, jswB]
  exact (Real.rpow_mul_intCast (by norm_num : 0 ≤ (2 : ℝ)) a k).symm

/-- Exact dyadic comparison for negative and positive integer scale indices. -/
theorem jswTau_floor_bounds (a : ℝ) (ha : 0 < a) (k : ℤ) :
    (2 : ℝ) ^ jswM a ha k ≤ jswTau a ha k ∧
      jswTau a ha k < (2 : ℝ) ^ (jswM a ha k + 1) := by
  rw [jswTau_eq_rpow a ha k]
  have hfloorle : ((jswM a ha k : ℤ) : ℝ) ≤ a * (k : ℝ) := Int.floor_le _
  have hltfloor : a * (k : ℝ) < ((jswM a ha k + 1 : ℤ) : ℝ) := by
    simp only [jswM, Int.cast_add, Int.cast_one]
    exact Int.lt_floor_add_one (a * (k : ℝ))
  constructor
  · rw [← Real.rpow_intCast (2 : ℝ) (jswM a ha k)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloorle
  · rw [← Real.rpow_intCast (2 : ℝ) (jswM a ha k + 1)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hltfloor

/-- The separated-pair jump count, with the witness convention from
`lv:jump-count`. -/
def jswJumpCount {I : Type*} [LinearOrder I] (u : I → ℂ) (threshold : ℝ) : ℝ≥0∞ :=
  FractionalPrimes.Literature.Variation.separatedJumpCount u threshold

/-- The homogeneous increment seminorm over finite increasing chains. -/
def jswVariation {I : Type*} [LinearOrder I] (r : ℝ) (u : I → ℂ) : ℝ≥0∞ :=
  FractionalPrimes.Literature.Variation.orderedRVariation r u

/-- Empty and singleton finite families have zero increment variation. -/
theorem jswVariation_eq_zero_of_card_le_one {I : Type*} [LinearOrder I] [Fintype I]
    (r : ℝ) (u : I → ℂ) (hr : 0 < r) (hcard : Fintype.card I ≤ 1) :
    jswVariation r u = 0 :=
  FractionalPrimes.Literature.Variation.orderedRVariation_eq_zero_of_card_le_one
    r u hr hcard

/-- The conventions node is a proved metadata marker; its definitions and
normalization facts are given above. -/
theorem Conventions : True := trivial

end

end FractionalPrimes.Literature.JSW

end
