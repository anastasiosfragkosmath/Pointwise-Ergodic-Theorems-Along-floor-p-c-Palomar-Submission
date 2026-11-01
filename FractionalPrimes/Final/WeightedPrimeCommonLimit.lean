module

public import FractionalPrimes.Final.HigherPrimePowersVanish

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FractionalPrimes.Final
noncomputable section

/-- A prescribed limit of the prime-only log-weighted means is also the
von Mangoldt limit, by the checked vanishing higher-prime-power remainder. -/
theorem vonMangoldt_tendsto_of_primeOnly_tendsto
    {X : Type*} [MeasurableSpace X] (S : System X)
    (c : ℝ) {p : ℝ} (hp : 1 < p) (f g : X → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) S.μ)
    (hAE : ∀ᵐ x ∂S.μ, Tendsto (fun N : Scale => paperPrimeOnlyPart S c f N x)
      atTop (𝓝 (g x)))
    (hLp : Tendsto (fun N : Scale =>
      eLpNorm (paperPrimeOnlyPart S c f N - g) (ENNReal.ofReal p) S.μ) atTop (𝓝 0)) :
    (∀ᵐ x ∂S.μ, Tendsto (fun N : Scale => vonMangoldtAverage S c f N x)
      atTop (𝓝 (g x))) ∧
      Tendsto (fun N : Scale => eLpNorm (vonMangoldtAverage S c f N - g)
        (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
  have hpENN := ENNReal.one_le_ofReal.mpr hp.le
  have hRae := paperHigherPrimePowerPart_ae_tendsto_zero S c f hpENN ENNReal.ofReal_ne_top hf
  have hRlp := paperHigherPrimePowerPart_eLpNorm_tendsto_zero S c f hpENN ENNReal.ofReal_ne_top hf
  have herror (N : Scale) : vonMangoldtAverage S c f N - g =
      (paperPrimeOnlyPart S c f N - g) + paperHigherPrimePowerPart S c f N := by
    rw [vonMangoldtAverage_eq_primeParts]
    ext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hbound (N : Scale) :
      eLpNorm (vonMangoldtAverage S c f N - g) (ENNReal.ofReal p) S.μ ≤
        eLpNorm (paperPrimeOnlyPart S c f N - g) (ENNReal.ofReal p) S.μ +
          eLpNorm (paperHigherPrimePowerPart S c f N) (ENNReal.ofReal p) S.μ := by
    rw [herror]
    exact eLpNorm_add_le hpENN
  have hsum : Tendsto (fun N : Scale =>
      eLpNorm (paperPrimeOnlyPart S c f N - g) (ENNReal.ofReal p) S.μ +
        eLpNorm (paperHigherPrimePowerPart S c f N) (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
    simpa only [add_zero] using hLp.add hRlp
  refine ⟨?_, ?_⟩
  · filter_upwards [hAE, hRae] with x hx hRx
    have h := hx.add hRx
    have hvalues : (fun N : Scale => paperPrimeOnlyPart S c f N x +
        paperHigherPrimePowerPart S c f N x) = (fun N => vonMangoldtAverage S c f N x) := by
      funext N
      exact (congrFun (vonMangoldtAverage_eq_primeParts S c f N) x).symm
    simpa only [hvalues, add_zero] using h
  · apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    filter_upwards [hsum.eventually (ENNReal.nhds_zero_basis_Iic.mem_of_mem hε)] with N hN
    exact (hbound N).trans hN

#print axioms vonMangoldt_tendsto_of_primeOnly_tendsto
end
end FractionalPrimes.Final
