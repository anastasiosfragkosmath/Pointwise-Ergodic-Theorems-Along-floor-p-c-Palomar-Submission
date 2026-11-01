module
public import FractionalPrimes.Final.ForwardSystems
public import FractionalPrimes.PrimePowerVariationManifest
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance 2000] NormedField.toNormedCommRing
universe u

/-- Exact uniform variation target for the revised manuscript. -/
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

/-- Common almost-everywhere limit for the two cutoff averages. -/
def PrimeConvergenceStatement (c : FractionalExponent) (p : ℝ) : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (S : System X) (f : X → ℂ),
    MemLp f (ENNReal.ofReal p) S.μ →
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun N : Scale => vonMangoldtAverage S c.value f N x)
        atTop (𝓝 (g x))) ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun N : {n : ℕ // 2 ≤ n} =>
        primeAverage S c.value f N.1 x) atTop (𝓝 (g x)))

/-- The previous uniform variation theorem is available on all invertible
systems expressed through the new forward-average interface. -/
theorem primeVariation_ofInvertible (q : VariationParameters) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ {X : Type u} [MeasurableSpace X] (S : InvertibleSystem X) (f : X → ℂ),
        MemLp f (ENNReal.ofReal q.p) S.μ →
        eLpNorm (rVariationFun q.r
          (vonMangoldtAverage (ofInvertible S) q.exponent.value f))
            (ENNReal.ofReal q.p) S.μ ≤
          (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal q.p) S.μ := by
  obtain ⟨C, hC, hbound⟩ := FractionalPrimes.primePowerVariation.{u} q
  refine ⟨C, hC, ?_⟩
  intro X _ S f hf
  have havg : vonMangoldtAverage (ofInvertible S) q.exponent.value f =
      FractionalPrimes.vonMangoldtAverage S q.exponent.value f := by
    funext N
    exact weightedAverage_ofInvertible S q.exponent.value
      (fun n => (vonMangoldtWeight n : ℂ)) f N
  rw [havg]
  exact hbound S f hf

#print axioms primeVariation_ofInvertible
end
end FractionalPrimes.Final
