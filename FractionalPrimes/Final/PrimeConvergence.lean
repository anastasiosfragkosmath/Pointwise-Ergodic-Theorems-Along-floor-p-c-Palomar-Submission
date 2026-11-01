module
public import FractionalPrimes.Final.HigherPrimePowersVanish
public import FractionalPrimes.Final.WeightedPrimeCommonLimit
public import FractionalPrimes.Final.PrimePointwiseNormalization
public import FractionalPrimes.Final.PrimeLpNormalization
public import FractionalPrimes.Final.PrimeAverageEnumeration
public import FractionalPrimes.Final.ArithmeticDecay
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- One common almost-everywhere limit for the von Mangoldt, prime-cutoff,
and enumerated-prime averages on sigma-finite measure-preserving systems. -/
theorem primeAverageConvergenceWithEnumeration {p : ℝ} (hp : 1 < p)
    (c : FractionalExponent) {X : Type*} [MeasurableSpace X]
    (S : System X) (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun N : Scale => vonMangoldtAverage S c.value f N x)
        atTop (𝓝 (g x))) ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun N : AdmissiblePrimeCutoff =>
        primeAverage S c.value f N.1 x) atTop (𝓝 (g x))) ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun J : Scale => enumeratedPrimeAverage S c.value f J x)
        atTop (𝓝 (g x))) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨g, hg, hPAE, hPLp⟩ :=
    paperPrimeOnlyPart_converges_of_vonMangoldtAverage_converges S c p hp f hf
      (vonMangoldtAverageConvergence hp c S f hf)
  have hA := vonMangoldt_tendsto_of_primeOnly_tendsto S c.value hp f g hf hPAE hPLp
  have hpi := primeCountingAsymptotic c
  have hprimeAE := primeAverage_ae_tendsto_of_logWeighted S c.value f g hPAE hpi
  refine ⟨g, hg, hA.1, ?_,
    (primeAverage_ae_tendsto_iff_enumerated S c.value f g).mp hprimeAE⟩
  filter_upwards [hprimeAE] with x hx
  exact tendsto_admissiblePrimeCutoff_of_nat_add_two
    (fun N => primeAverage S c.value f N.1 x) hx

theorem primeAverageConvergence {p : ℝ} (hp : 1 < p) (c : FractionalExponent) :
    PrimeConvergenceStatement c p := by
  intro X _ S f hf
  obtain ⟨g, hg, hA, hP, _⟩ :=
    primeAverageConvergenceWithEnumeration hp c S f hf
  exact ⟨g, hg, hA, hP⟩

#print axioms primeAverageConvergenceWithEnumeration
#print axioms primeAverageConvergence
end
end FractionalPrimes.Final
