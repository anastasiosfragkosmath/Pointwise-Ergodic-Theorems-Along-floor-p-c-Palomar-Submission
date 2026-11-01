module

public import FractionalPrimes.Literature.Ergodic.PrimeOrbitAbel

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace FractionalPrimes
noncomputable section

/-- Pointwise normalization to the same log-weighted limit. The n+2 indexing
is exactly the domain N≥2 of the approved prime average. -/
theorem primeAverage_ae_tendsto_of_logWeighted
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f g : X → ℂ)
    (hweighted : ∀ᵐ x ∂S.μ, Tendsto
      (fun N : Scale => paperPrimeOnlyPart S c f N x) atTop (𝓝 (g x)))
    (hpi : Tendsto (fun N : ℕ =>
      (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 1)) :
    ∀ᵐ x ∂S.μ, Tendsto (fun n : ℕ => primeAverage S c f (n + 2) (by omega) x)
      atTop (𝓝 (g x)) := by
  have hscale : Tendsto (fun n : ℕ => (⟨n + 1, by omega⟩ : Scale)) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N.val] with n hn
    change N.val ≤ n + 1
    omega
  filter_upwards [hweighted] with x hx
  let orbit : ℕ → ℂ := fun n => f (S.iterate (floorPower c n) x)
  have hlogSucc : Tendsto (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ)⁻¹ • primeLogPartialSum orbit (n + 1)) atTop (𝓝 (g x)) := by
    have h := hx.comp hscale
    apply h.congr'
    exact Filter.Eventually.of_forall (fun n =>
      (primeLogMean_orbit_eq S c f ⟨n + 1, by omega⟩ x).symm)
  have hlog : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • primeLogPartialSum orbit N)
      atTop (𝓝 (g x)) := (tendsto_add_atTop_iff_nat 1).mp hlogSucc
  have hnormalized := normalizedPrimeMean_tendsto_of_logMean orbit (g x) hlog hpi
  have hshift := (tendsto_add_atTop_iff_nat 2).mpr hnormalized
  apply hshift.congr'
  exact Filter.Eventually.of_forall (fun n => primeMean_orbit_eq S c f (n + 2) (by omega) x)

#print axioms primeAverage_ae_tendsto_of_logWeighted
end
end FractionalPrimes
