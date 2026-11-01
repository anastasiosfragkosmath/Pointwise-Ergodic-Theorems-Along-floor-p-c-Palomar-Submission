module
public import FractionalPrimes.Final.PrimeConvergence
public import FractionalPrimes.Final.MobiusLogRate
@[expose] public section
namespace FractionalPrimes.Final.Palomar
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
attribute [local instance 2000] NormedField.toNormedCommRing
universe u

/-- Final manuscript Theorem t:maintheorem. -/
theorem primePowerVariation (q : FractionalPrimes.VariationParameters) :
    FractionalPrimes.Final.PrimeVariationStatement.{u} q :=
  FractionalPrimes.Final.primePowerVariation q

/-- Final manuscript Corollary cor:prime-convergence, including its
first-J-primes formulation and one common almost-everywhere limit. -/
theorem primeAverageConvergence {p : ℝ} (hp : 1 < p)
    (c : FractionalPrimes.FractionalExponent)
    {X : Type u} [MeasurableSpace X] (S : FractionalPrimes.Final.System X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun N : FractionalPrimes.Scale =>
        FractionalPrimes.Final.vonMangoldtAverage S c.value f N x) atTop (𝓝 (g x))) ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun N : FractionalPrimes.AdmissiblePrimeCutoff =>
        FractionalPrimes.Final.primeAverage S c.value f N.1 x) atTop (𝓝 (g x))) ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun J : FractionalPrimes.Scale =>
        FractionalPrimes.Final.enumeratedPrimeAverage S c.value f J x) atTop (𝓝 (g x))) :=
  FractionalPrimes.Final.primeAverageConvergenceWithEnumeration hp c S f hf

/-- Final manuscript Theorem t:mobius-convergence, with logarithmic rate. -/
theorem mobiusAverageTendsToZero {p A : ℝ} (hp : 1 < p) (hA : 1 < A)
    (c : FractionalPrimes.FractionalExponent)
    {X : Type u} [MeasurableSpace X] (S : FractionalPrimes.Final.System X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∀ᵐ x ∂S.μ, Tendsto (fun N : FractionalPrimes.Scale =>
      FractionalPrimes.Final.logWeightedMobiusAverage S c.value A f N x) atTop (𝓝 0) :=
  FractionalPrimes.Final.mobiusLogRate hp hA c S f hf

#print axioms primePowerVariation
#print axioms primeAverageConvergence
#print axioms mobiusAverageTendsToZero
end
end FractionalPrimes.Final.Palomar
