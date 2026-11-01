module
public import FractionalPrimes.PrimeMobiusFinalSourceBridge
public import FractionalPrimes.Literature.DirichletAdapter.DPSourceTask
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalPTWOfOAISource
@[expose] public section

/-! Unconditional prime-power variation and almost-everywhere convergence,
obtained by discharging both arithmetic inputs of the checked source bridge. -/

namespace FractionalPrimes

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- The actual von Mangoldt prime-power averages satisfy the paper's
finite-`r` variation estimate, for every fractional exponent and `p>1`.
Both source arithmetic tasks have been discharged. -/
theorem primePowerVariation_of_OAISource
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r) (c : FractionalExponent) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
        (f : X → ℂ), MemLp f (ENNReal.ofReal p) S.μ →
        eLpNorm (rVariationFun r
          (fun N => vonMangoldtAverage S c.value f N))
            (ENNReal.ofReal p) S.μ ≤
          C * eLpNorm f (ENNReal.ofReal p) S.μ :=
  primePowerVariationOf_OAISource_DP_PTW hp hr c
    Literature.DirichletAdapter.shortIntervalDirichletTask_of_sourceComponents
    Literature.Polynomial.restrictedPolynomialTwistedTask_of_OAISource

/-- The paper's von Mangoldt, prime cutoff, enumerated-prime, and Möbius
convergence assertions, with the same limit for all three prime families
and zero limit for Möbius, now without arithmetic premises. -/
theorem primeAndMobiusConvergenceAtCutoffs_of_OAISource
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
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂S.μ, Tendsto
        (fun N : Scale => mobiusAverage S c.value f N x)
        atTop (𝓝 0)) ∧
      Tendsto (fun N : Scale =>
        eLpNorm (mobiusAverage S c.value f N) (ENNReal.ofReal p) S.μ)
        atTop (𝓝 0) :=
  primeAndMobiusConvergenceAtCutoffsOf_OAISource_DP_PTW hp c
    Literature.DirichletAdapter.shortIntervalDirichletTask_of_sourceComponents
    Literature.Polynomial.restrictedPolynomialTwistedTask_of_OAISource S f hf

/-- The original prime cutoffs `N ≥ 2` of the paper converge almost
everywhere and in `L^p` to one common `L^p` function. -/
theorem primePowerAverage_ae_and_Lp_convergence_of_OAISource
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Tendsto
        (fun N : AdmissiblePrimeCutoff =>
          primeAverage S c.value f N.1 N.2 x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun N : AdmissiblePrimeCutoff =>
        eLpNorm (primeAverage S c.value f N.1 N.2 - g)
          (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
  obtain ⟨g, hg, _hΛAE, _hΛLp, hprimeAE, hprimeLp,
      _henumeratedAE, _henumeratedLp, _hμAE, _hμLp⟩ :=
    primeAndMobiusConvergenceAtCutoffs_of_OAISource hp c S f hf
  exact ⟨g, hg, hprimeAE, hprimeLp⟩

/-- The paper's Möbius-weighted theorem, projected from the common
unconditional convergence package. -/
theorem mobiusPowerAverage_ae_and_Lp_zero_of_OAISource
    {p : ℝ} (hp : 1 < p) (c : FractionalExponent)
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    (∀ᵐ x ∂S.μ, Tendsto
      (fun N : Scale => mobiusAverage S c.value f N x)
      atTop (𝓝 0)) ∧
    Tendsto (fun N : Scale =>
      eLpNorm (mobiusAverage S c.value f N)
        (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
  obtain ⟨_g, _hg, _hΛAE, _hΛLp, _hprimeAE, _hprimeLp,
      _henumeratedAE, _henumeratedLp, hμAE, hμLp⟩ :=
    primeAndMobiusConvergenceAtCutoffs_of_OAISource hp c S f hf
  exact ⟨hμAE, hμLp⟩

#print axioms primePowerVariation_of_OAISource
#print axioms primeAndMobiusConvergenceAtCutoffs_of_OAISource
#print axioms primePowerAverage_ae_and_Lp_convergence_of_OAISource
#print axioms mobiusPowerAverage_ae_and_Lp_zero_of_OAISource

end
end FractionalPrimes
