module
public import FractionalPrimes.PrimeConvergenceConditionalArithmetic
public import FractionalPrimes.MobiusConvergenceConditionalArithmetic
@[expose] public section

/-!
# Conditional joint prime and Möbius convergence

This packages the checked conditional prime common-limit theorem together
with the checked arbitrary-Lp Möbius-zero theorem. The exact source DP and
restricted PTW contracts remain the only arithmetic task premises.
-/

namespace FractionalPrimes

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Under the exact source DP and restricted PTW tasks, all three prime
averaging formulations converge almost everywhere and in Lp to a common
limit, while the actual Möbius averages converge almost everywhere and in
Lp to zero. -/
theorem primeAndMobiusConvergenceOf_OAISource_DP_PTW
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask)
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Tendsto
        (fun N : Scale => vonMangoldtAverage S c.value f N x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun N : Scale =>
        eLpNorm (vonMangoldtAverage S c.value f N - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto
        (fun n : ℕ => primeAverage S c.value f (n + 2) (by omega) x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun n : ℕ =>
        eLpNorm (primeAverage S c.value f (n + 2) (by omega) - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto
        (fun J : Scale => enumeratedPrimeAverage S c.value f J x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun J : Scale =>
        eLpNorm (enumeratedPrimeAverage S c.value f J - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto
        (fun N : Scale => mobiusAverage S c.value f N x)
        atTop (𝓝 0)) ∧
      Tendsto (fun N : Scale =>
        eLpNorm (mobiusAverage S c.value f N) (ENNReal.ofReal p) S.μ)
        atTop (𝓝 0) := by
  obtain ⟨g, hg, hΛAE, hΛLp, hprimeAE, hprimeLp, henumeratedAE,
      henumeratedLp⟩ :=
    primeConvergenceWithEnumerationOf_OAISource_DP_PTW
      hp c hDP hPTW S f hf
  obtain ⟨hμAE, hμLp⟩ :=
    mobiusAverageTendsToZero_of_OAISource_DP_PTW
      S c hp hDP hPTW f hf
  exact ⟨g, hg, hΛAE, hΛLp, hprimeAE, hprimeLp,
    henumeratedAE, henumeratedLp, hμAE, hμLp⟩

#print axioms primeAndMobiusConvergenceOf_OAISource_DP_PTW

end
end FractionalPrimes
