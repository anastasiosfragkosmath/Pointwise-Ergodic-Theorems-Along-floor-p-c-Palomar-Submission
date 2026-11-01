module
public import FractionalPrimes.PrimeMobiusFinalUnconditional
@[expose] public section

namespace FractionalPrimes

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- Blueprint manifest `FractionalPrimes.vonMangoldtAverageConvergence`:
the von Mangoldt averages have one common almost-everywhere and `Lᵖ` limit. -/
theorem vonMangoldtAverageConvergence
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Tendsto
        (fun N : Scale => vonMangoldtAverage S c.value f N x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun N : Scale =>
        eLpNorm (vonMangoldtAverage S c.value f N - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
  obtain ⟨g, hg, hΛAE, hΛLp, _hprimeAE, _hprimeLp,
      _henumeratedAE, _henumeratedLp, _hμAE, _hμLp⟩ :=
    primeAndMobiusConvergenceAtCutoffs_of_OAISource hp c S f hf
  exact ⟨g, hg, hΛAE, hΛLp⟩

/-- Blueprint manifest `FractionalPrimes.primeAverageConvergence`:
the prime-cutoff and enumerated-prime averages converge to the same limit
as the von Mangoldt averages, almost everywhere and in `Lᵖ`. The subtype
`AdmissiblePrimeCutoff` is exactly the paper's range `N ≥ 2`. -/
theorem primeAverageConvergence
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
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
        (fun N : AdmissiblePrimeCutoff =>
          primeAverage S c.value f N.1 N.2 x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun N : AdmissiblePrimeCutoff =>
        eLpNorm (primeAverage S c.value f N.1 N.2 - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto
        (fun J : Scale => enumeratedPrimeAverage S c.value f J x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun J : Scale =>
        eLpNorm (enumeratedPrimeAverage S c.value f J - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
  obtain ⟨g, hg, hΛAE, hΛLp, hprimeAE, hprimeLp,
      henumeratedAE, henumeratedLp, _hμAE, _hμLp⟩ :=
    primeAndMobiusConvergenceAtCutoffs_of_OAISource hp c S f hf
  exact ⟨g, hg, hΛAE, hΛLp, hprimeAE, hprimeLp,
    henumeratedAE, henumeratedLp⟩

/-- Blueprint manifest `FractionalPrimes.mobiusAverageTendsToZero`:
the Möbius averages converge almost everywhere and in `Lᵖ` to zero. -/
theorem mobiusAverageTendsToZero
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    (∀ᵐ x ∂S.μ, Tendsto
      (fun N : Scale => mobiusAverage S c.value f N x)
      atTop (𝓝 0)) ∧
    Tendsto (fun N : Scale =>
      eLpNorm (mobiusAverage S c.value f N) (ENNReal.ofReal p) S.μ)
      atTop (𝓝 0) := by
  obtain ⟨_g, _hg, _hΛAE, _hΛLp, _hprimeAE, _hprimeLp,
      _henumeratedAE, _henumeratedLp, hμAE, hμLp⟩ :=
    primeAndMobiusConvergenceAtCutoffs_of_OAISource hp c S f hf
  exact ⟨hμAE, hμLp⟩

#print axioms vonMangoldtAverageConvergence
#print axioms primeAverageConvergence
#print axioms mobiusAverageTendsToZero

end
end FractionalPrimes
