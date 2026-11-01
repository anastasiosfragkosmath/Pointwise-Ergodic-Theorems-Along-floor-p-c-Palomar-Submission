module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section

/-!
# Core objects for fractional-prime averages

This module records the paper's basic objects with positive averaging scales.
The analytic theorems are developed in later modules.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

/-- Positive integer averaging scales. -/
abbrev Scale := { N : ℕ // 0 < N }

/-- A real number is nonintegral when it differs from every integer. -/
def NonIntegral (c : ℝ) : Prop := ∀ z : ℤ, c ≠ (z : ℝ)

/-- The fixed nonintegral exponent from the paper. -/
structure FractionalExponent where
  value : ℝ
  one_lt : 1 < value
  nonIntegral : NonIntegral value

/-- The integer part of the fractional-power time associated to `n`. -/
def floorPower (c : ℝ) (n : ℕ) : ℤ := ⌊Real.rpow (n : ℝ) c⌋

/-- The same fractional-power time viewed as a natural number. -/
def floorTime (c : ℝ) (n : ℕ) : ℕ := (floorPower c n).toNat

theorem floorPower_nonneg (c : ℝ) (n : ℕ) : 0 ≤ floorPower c n := by
  apply Int.floor_nonneg.mpr
  exact Real.rpow_nonneg (Nat.cast_nonneg n) c

theorem coe_floorTime (c : ℝ) (n : ℕ) : (floorTime c n : ℤ) = floorPower c n := by
  exact Int.toNat_of_nonneg (floorPower_nonneg c n)

/-- An invertible sigma-finite measure-preserving system. -/
structure InvertibleSystem (X : Type*) [MeasurableSpace X] where
  μ : Measure X
  sigmaFinite : SigmaFinite μ
  T : X ≃ᵐ X
  preserves : MeasurePreserving T μ μ

namespace InvertibleSystem

/-- The integer iterate of the transformation. -/
def iterate {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (n : ℤ) : X → X :=
  fun x => (S.T.toEquiv ^ n) x

/-- Translate a function along an integer iterate of the system. -/
def shift {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (n : ℤ)
    (f : X → ℂ) : X → ℂ :=
  fun x => f (S.iterate n x)

end InvertibleSystem

/-- The von Mangoldt weight, using Mathlib's arithmetic function. -/
def vonMangoldtWeight (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n

/-- The Möbius weight, using Mathlib's arithmetic function. -/
def mobiusWeight (n : ℕ) : ℤ := ArithmeticFunction.moebius n

@[simp] theorem vonMangoldtWeight_def (n : ℕ) :
    vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n := rfl

@[simp] theorem mobiusWeight_def (n : ℕ) :
    mobiusWeight n = ArithmeticFunction.moebius n := rfl

/-- A finite weighted average over the interval `[1, N]`. -/
def weightedAverage {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (w : ℕ → ℂ) (f : X → ℂ) (N : Scale) : X → ℂ :=
  fun x => (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
    w n * f (S.iterate (floorPower c n) x)

/-- The unweighted averages from the paper. -/
def unweightedAverage {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) (N : Scale) : X → ℂ :=
  weightedAverage S c (fun _ => 1) f N

/-- The von Mangoldt-weighted averages from the paper. -/
def vonMangoldtAverage {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) (N : Scale) : X → ℂ :=
  weightedAverage S c (fun n => (vonMangoldtWeight n : ℂ)) f N

/-- The Möbius-weighted averages from the paper. -/
def mobiusAverage {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) (N : Scale) : X → ℂ :=
  weightedAverage S c (fun n => (mobiusWeight n : ℂ)) f N

/-- The prime average from blueprint `def:operators`, normalized by
`π(N)` and defined for `N ≥ 2`. -/
def primeAverage {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) (c : ℝ)
    (f : X → ℂ) (N : ℕ) (_hN : 2 ≤ N) : X → ℂ :=
  (Nat.primeCounting N : ℂ)⁻¹ • fun x =>
    ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      f (S.iterate (floorPower c p) x)

theorem primeCounting_pos_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    0 < Nat.primeCounting N := by
  have hne : Nat.primeCounting N ≠ 0 := by
    intro hzero
    have hsmall : N ≤ 1 := Nat.primeCounting_eq_zero_iff.mp hzero
    omega
  exact Nat.pos_of_ne_zero hne

/-- A finite strictly increasing chain of positive averaging scales. -/
structure StrictScaleChain (length : ℕ) where
  index : Fin (length + 1) → Scale
  strictMono : StrictMono index

/--
The homogeneous `r`-variation over all finite increasing scale chains.
This total Lean definition is used for source-facing statements only under
their stated exponent hypotheses (in particular, `r > 2` for the main target).
-/
def rVariation {E : Type*} [NormedAddCommGroup E] (r : ℝ) (u : Scale → E) : ℝ≥0∞ :=
  ⨆ (length : ℕ) (chain : StrictScaleChain length),
    (∑ i : Fin length,
      (ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖).rpow r).rpow r⁻¹

theorem rVariation_eq {E : Type*} [NormedAddCommGroup E] (r : ℝ) (u : Scale → E) :
    rVariation r u = ⨆ (length : ℕ) (chain : StrictScaleChain length),
      (∑ i : Fin length,
        (ENNReal.ofReal ‖u (chain.index i.succ) - u (chain.index i.castSucc)‖).rpow r).rpow r⁻¹ := rfl

/-- Pointwise homogeneous `r`-variation for a family of functions. -/
def rVariationFun {X E : Type*} [NormedAddCommGroup E] (r : ℝ)
    (u : Scale → X → E) : X → ℝ≥0∞ :=
  fun x => rVariation r (fun N => u N x)

theorem rVariationFun_apply {X E : Type*} [NormedAddCommGroup E] (r : ℝ)
    (u : Scale → X → E) (x : X) :
    rVariationFun r u x = rVariation r (fun N => u N x) := rfl

theorem weightedAverage_zero {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (w : ℕ → ℂ) (N : Scale) :
    weightedAverage S c w (fun _ => 0) N = 0 := by
  funext x
  simp [weightedAverage]

theorem unweightedAverage_zero {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (N : Scale) :
    unweightedAverage S c (fun _ => 0) N = 0 := by
  exact weightedAverage_zero S c (fun _ => 1) N

theorem vonMangoldtAverage_zero {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (N : Scale) :
    vonMangoldtAverage S c (fun _ => 0) N = 0 := by
  exact weightedAverage_zero S c (fun n => (vonMangoldtWeight n : ℂ)) N

theorem mobiusAverage_zero {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (N : Scale) :
    mobiusAverage S c (fun _ => 0) N = 0 := by
  exact weightedAverage_zero S c (fun n => (mobiusWeight n : ℂ)) N

theorem weightedAverage_add {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (w : ℕ → ℂ) (f g : X → ℂ) (N : Scale) :
    weightedAverage S c w (f + g) N = weightedAverage S c w f N + weightedAverage S c w g N := by
  funext x
  change (N.1 : ℂ)⁻¹ * (∑ n ∈ Finset.Icc 1 N.1,
      w n * (f (S.iterate (floorPower c n) x) + g (S.iterate (floorPower c n) x))) =
    (N.1 : ℂ)⁻¹ * (∑ n ∈ Finset.Icc 1 N.1, w n * f (S.iterate (floorPower c n) x)) +
      (N.1 : ℂ)⁻¹ * (∑ n ∈ Finset.Icc 1 N.1, w n * g (S.iterate (floorPower c n) x))
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

theorem rVariation_const {E : Type*} [NormedAddCommGroup E] (r : ℝ) (hr : 0 < r) (z : E) :
    rVariation r (fun _ : Scale => z) = 0 := by
  simp [rVariation, ENNReal.zero_rpow_of_pos hr,
    ENNReal.zero_rpow_of_pos (by positivity : 0 < r⁻¹)]

/-- Parameters in the range of the paper's variation theorem. -/
structure VariationParameters where
  exponent : FractionalExponent
  p : ℝ
  one_lt_p : 1 < p
  r : ℝ
  two_lt_r : 2 < r

/-- The variation estimate with a specified constant on one system. -/
def PrimePowerVariationBound {X : Type*} [MeasurableSpace X] (C : ℝ≥0)
    (S : InvertibleSystem X) (q : VariationParameters) : Prop :=
  ∀ f : X → ℂ, MemLp f (ENNReal.ofReal q.p) S.μ →
    eLpNorm (rVariationFun q.r (vonMangoldtAverage S q.exponent.value f))
        (ENNReal.ofReal q.p) S.μ
      ≤ (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal q.p) S.μ

/-- The variation estimate on one fixed system, with an unspecified system-dependent bound. -/
def PrimePowerVariationForSystem {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (q : VariationParameters) : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧ PrimePowerVariationBound C S q

/--
The paper's main variation target: one constant works for every invertible
sigma-finite measure-preserving system and every admissible input function.
-/
def PrimePowerVariationStatement (q : VariationParameters) : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧ ∀ {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X),
    PrimePowerVariationBound C S q

/-- A uniform variation statement supplies the corresponding estimate on each system. -/
theorem primePowerVariationStatement_forSystem.{u} (q : VariationParameters)
    (h : PrimePowerVariationStatement.{u} q) {X : Type u} [MeasurableSpace X]
    (S : InvertibleSystem X) : PrimePowerVariationForSystem S q := by
  rcases h with ⟨C, hCpos, hC⟩
  exact ⟨C, hCpos, hC S⟩

end

end FractionalPrimes

end
