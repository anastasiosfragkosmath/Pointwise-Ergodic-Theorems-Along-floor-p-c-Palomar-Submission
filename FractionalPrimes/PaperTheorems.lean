module
public import FractionalPrimes.Final.PrimeConvergence
public import FractionalPrimes.Final.MobiusLogRate
/-!
# Paper-facing main theorem statements

Review entry point for the author's final manuscript
`source-paper/fractionalpowersofprimesfinal.tex`. These explicit types retain
the full parameter ranges, common limits and quantifier order. The proofs
reuse the verified development in `FractionalPrimes.Final`.

`FractionalExponent` records c>1 and nonintegrality; `Final.System` records
sigma-finiteness and measure preservation without an inverse. `Scale` is
positive natural cutoffs. The arithmetic averages use the exact [1,N] sums
and natural iterates at floor(n^c). No auxiliary arithmetic premise is added.
-/

@[expose] public section
namespace FractionalPrimes.PaperTheorems
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
attribute [local instance 2000] NormedField.toNormedCommRing
universe u

/-- Theorem `t:maintheorem`: homogeneous variation, with one finite positive
constant for every sigma-finite measure-preserving system and observable.
The transformation need not be invertible. -/
theorem prime_power_variation (c : FractionalPrimes.FractionalExponent)
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ {X : Type u} [MeasurableSpace X] (S : FractionalPrimes.Final.System X)
        (f : X → ℂ), MemLp f (ENNReal.ofReal p) S.μ →
        eLpNorm (FractionalPrimes.rVariationFun r
          (FractionalPrimes.Final.vonMangoldtAverage S c.value f))
            (ENNReal.ofReal p) S.μ ≤
          (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) S.μ :=
  FractionalPrimes.Final.primePowerVariation ⟨c, p, hp, r, hr⟩

/-- Final manuscript Corollary cor:prime-convergence, including its
first-J-primes formulation and one common almost-everywhere limit. -/
theorem prime_average_convergence {p : ℝ} (hp : 1 < p)
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
theorem mobius_logarithmic_convergence {p A : ℝ} (hp : 1 < p) (hA : 1 < A)
    (c : FractionalPrimes.FractionalExponent)
    {X : Type u} [MeasurableSpace X] (S : FractionalPrimes.Final.System X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∀ᵐ x ∂S.μ, Tendsto (fun N : FractionalPrimes.Scale =>
      (Real.log (N.1 : ℝ)) ^ A • FractionalPrimes.Final.mobiusAverage S c.value f N x) atTop (𝓝 0) :=
  FractionalPrimes.Final.mobiusLogRate hp hA c S f hf

#print axioms prime_power_variation
#print axioms prime_average_convergence
#print axioms mobius_logarithmic_convergence
end
end FractionalPrimes.PaperTheorems
