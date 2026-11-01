module
public import FractionalPrimes.Systems
@[expose] public section

namespace FractionalPrimes.Final
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The revised manuscript permits transformations without an inverse. -/
structure System (X : Type*) [MeasurableSpace X] where
  μ : Measure X
  sigmaFinite : SigmaFinite μ
  T : X → X
  preserves : MeasurePreserving T μ μ

namespace System
variable {X : Type*} [MeasurableSpace X]

def shift (S : System X) (n : ℕ) (f : X → ℂ) : X → ℂ :=
  f ∘ S.T^[n]

theorem measurePreserving_iterate (S : System X) (n : ℕ) :
    MeasurePreserving S.T^[n] S.μ S.μ := S.preserves.iterate n

theorem memLp_shift (S : System X) (n : ℕ) {p : ℝ≥0∞} {f : X → ℂ}
    (hf : MemLp f p S.μ) : MemLp (S.shift n f) p S.μ :=
  hf.comp_measurePreserving (S.measurePreserving_iterate n)

theorem eLpNorm_shift (S : System X) (n : ℕ) {p : ℝ≥0∞} {f : X → ℂ}
    (hf : AEStronglyMeasurable f S.μ) :
    eLpNorm (S.shift n f) p S.μ = eLpNorm f p S.μ :=
  eLpNorm_comp_measurePreserving hf (S.measurePreserving_iterate n)
end System

def ofInvertible {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X) : System X where
  μ := S.μ
  sigmaFinite := S.sigmaFinite
  T := S.T
  preserves := S.preserves

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

/-- These are exactly the previously verified averages on invertible systems. -/
theorem weightedAverage_ofInvertible {X : Type*} [MeasurableSpace X]
    (S : InvertibleSystem X) (c : ℝ) (w : ℕ → ℂ) (f : X → ℂ) (N : Scale) :
    weightedAverage (ofInvertible S) c w f N =
      FractionalPrimes.weightedAverage S c w f N := by
  funext x
  apply congrArg ((N.1 : ℂ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  exact (S.shift_floorPower_apply c n f x).symm

/-- Positive logarithmic weights, including the manuscript's range A > 1. -/
def logWeightedMobiusAverage {X : Type*} [MeasurableSpace X]
    (S : System X) (c A : ℝ) (f : X → ℂ) (N : Scale) : X → ℂ :=
  (Real.rpow (Real.log (N.1 : ℝ)) A) • mobiusAverage S c f N

/-- The revised Mobius target as a proposition; no proof is claimed here. -/
def MobiusLogRateStatement (c : FractionalExponent) (p A : ℝ) : Prop :=
  ∀ {X : Type*} [MeasurableSpace X] (S : System X) (f : X → ℂ),
    MemLp f (ENNReal.ofReal p) S.μ →
    ∀ᵐ x ∂S.μ, Filter.Tendsto
      (fun N : Scale => logWeightedMobiusAverage S c.value A f N x)
      Filter.atTop (nhds 0)

#print axioms System.memLp_shift
#print axioms System.eLpNorm_shift
#print axioms weightedAverage_ofInvertible
end
end FractionalPrimes.Final
