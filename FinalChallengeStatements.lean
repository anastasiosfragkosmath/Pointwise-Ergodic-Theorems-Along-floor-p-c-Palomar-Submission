module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Fractional powers of primes: statements of the main results

These definitions spell out the three main claims of
the baseline manuscript. The Solution supplies the proofs. The revised statements below are propositions only; this review module
introduces no theorem placeholders.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

noncomputable section

/-- Positive integer averaging scales. -/
abbrev Scale := { N : ℕ // 0 < N }

/-- Nonintegral means unequal to every integer. -/
def NonIntegral (c : ℝ) : Prop := ∀ z : ℤ, c ≠ (z : ℝ)

/-- The exponent range in the paper. -/
structure FractionalExponent where
  value : ℝ
  one_lt : 1 < value
  nonIntegral : NonIntegral value

/-- The time assigned to the integer `n`. -/
def floorPower (c : ℝ) (n : ℕ) : ℤ := ⌊Real.rpow (n : ℝ) c⌋

def floorTime (c : ℝ) (n : ℕ) : ℕ := (floorPower c n).toNat

/-- The arithmetic weights are Mathlib's von Mangoldt and Möbius functions. -/
def vonMangoldtWeight (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n
def mobiusWeight (n : ℕ) : ℤ := ArithmeticFunction.moebius n

/-- The first-`J`-prime average; Mathlib's prime enumeration starts at zero. -/
def enumeratedPrimeMean {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (g : ℕ → E) (J : ℕ) : E :=
  (J : ℝ)⁻¹ • ∑ j ∈ Finset.range J, g (Nat.nth Nat.Prime j)

/-- The exact domain of the paper's cutoff prime averages. -/
abbrev AdmissiblePrimeCutoff := {N : ℕ // 2 ≤ N}

/-- A finite strictly increasing chain of positive scales. -/
structure StrictScaleChain (length : ℕ) where
  index : Fin (length + 1) → Scale
  strictMono : StrictMono index

/-- The homogeneous `r`-variation over every finite increasing scale chain. -/
def rVariation {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (u : Scale → E) : ℝ≥0∞ :=
  ⨆ (length : ℕ) (chain : StrictScaleChain length),
    (∑ i : Fin length,
      (ENNReal.ofReal ‖u (chain.index i.succ) -
        u (chain.index i.castSucc)‖).rpow r).rpow r⁻¹

/-- Pointwise homogeneous variation. -/
def rVariationFun {X E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (u : Scale → X → E) : X → ℝ≥0∞ :=
  fun x => rVariation r (fun N => u N x)

/-- The full parameter range of the main variation theorem. -/
structure VariationParameters where
  exponent : FractionalExponent
  p : ℝ
  one_lt_p : 1 < p
  r : ℝ
  two_lt_r : 2 < r

namespace Final
universe u
structure System (X : Type*) [MeasurableSpace X] where
  μ : Measure X
  sigmaFinite : SigmaFinite μ
  T : X → X
  preserves : MeasurePreserving T μ μ

namespace System
variable {X : Type*} [MeasurableSpace X]
def shift (S : System X) (n : ℕ) (f : X → ℂ) : X → ℂ :=
  f ∘ S.T^[n]

end System
def weightedAverage {X : Type*} [MeasurableSpace X] (S : System X) (c : ℝ)
    (w : ℕ → ℂ) (f : X → ℂ) (N : Scale) : X → ℂ :=
  fun x => (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
    w n * S.shift (floorTime c n) f x

def vonMangoldtAverage {X : Type*} [MeasurableSpace X] (S : System X) (c : ℝ)
    (f : X → ℂ) (N : Scale) : X → ℂ :=
  weightedAverage S c (fun n => (vonMangoldtWeight n : ℂ)) f N

def mobiusAverage {X : Type*} [MeasurableSpace X] (S : System X) (c : ℝ)
    (f : X → ℂ) (N : Scale) : X → ℂ :=
  weightedAverage S c (fun n => (mobiusWeight n : ℂ)) f N

def logWeightedMobiusAverage {X : Type*} [MeasurableSpace X]
    (S : System X) (c A : ℝ) (f : X → ℂ) (N : Scale) : X → ℂ :=
  (Real.rpow (Real.log (N.1 : ℝ)) A) • mobiusAverage S c f N

def PrimeVariationStatement (q : VariationParameters) : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ {X : Type u} [MeasurableSpace X] (S : System X) (f : X → ℂ),
      MemLp f (ENNReal.ofReal q.p) S.μ →
      eLpNorm (rVariationFun q.r (vonMangoldtAverage S q.exponent.value f))
        (ENNReal.ofReal q.p) S.μ ≤
        (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal q.p) S.μ
def primeAverage {X : Type*} [MeasurableSpace X] (S : System X) (c : ℝ)
    (f : X → ℂ) (N : ℕ) : X → ℂ :=
  (Nat.primeCounting N : ℂ)⁻¹ • fun x =>
    ∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime,
      S.shift (floorTime c n) f x


section
attribute [local instance 2000] NormedSpace.complexToReal NormedField.toNormedSpace
def enumeratedPrimeAverage {X : Type*} [MeasurableSpace X]
    (S : System X) (c : ℝ) (f : X → ℂ) (J : Scale) : X → ℂ :=
  enumeratedPrimeMean (fun n => S.shift (floorTime c n) f) J.val

end
end Final

namespace FinalStatementReview
universe u

def primePowerVariationTarget (q : VariationParameters) : Prop := Final.PrimeVariationStatement.{u} q

def primeAverageConvergenceTarget {p : ℝ} (hp : 1 < p)
    (c : FractionalPrimes.FractionalExponent)
    {X : Type u} [MeasurableSpace X] (S : FractionalPrimes.Final.System X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) : Prop :=
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun N : FractionalPrimes.Scale =>
        FractionalPrimes.Final.vonMangoldtAverage S c.value f N x) atTop (𝓝 (g x))) ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun N : FractionalPrimes.AdmissiblePrimeCutoff =>
        FractionalPrimes.Final.primeAverage S c.value f N.1 x) atTop (𝓝 (g x))) ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun J : FractionalPrimes.Scale =>
        FractionalPrimes.Final.enumeratedPrimeAverage S c.value f J x) atTop (𝓝 (g x)))
def mobiusLogRateTarget {p A : ℝ} (hp : 1 < p) (hA : 1 < A)
    (c : FractionalPrimes.FractionalExponent)
    {X : Type u} [MeasurableSpace X] (S : FractionalPrimes.Final.System X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) : Prop :=
    ∀ᵐ x ∂S.μ, Tendsto (fun N : FractionalPrimes.Scale =>
      FractionalPrimes.Final.logWeightedMobiusAverage S c.value A f N x) atTop (𝓝 0)
end FinalStatementReview
end
end FractionalPrimes
end
