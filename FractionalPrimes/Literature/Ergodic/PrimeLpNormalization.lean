module

public import FractionalPrimes.Literature.Ergodic.PrimeLpAbel
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FractionalPrimes
noncomputable section

/-- The source finite Abel argument in Lp, retaining the original raw
representatives and the same prescribed weighted limit. -/
theorem primeAverage_eLpNorm_tendsto_of_logWeighted
    {X : Type*} [MeasurableSpace X] (S : InvertibleSystem X)
    (c : ℝ) (f g : X → ℂ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hf : MemLp f p S.μ) (hg : MemLp g p S.μ)
    (hweighted : Tendsto (fun N : Scale =>
      eLpNorm (paperPrimeOnlyPart S c f N - g) p S.μ) atTop (𝓝 0))
    (hpi : Tendsto (fun N : ℕ =>
      (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => eLpNorm
      (primeAverage S c f (n + 2) (by omega) - g) p S.μ) atTop (𝓝 0) := by
  let orbit := primeOrbitLp S c f hf
  let logMean := fun N : ℕ => (N : ℝ)⁻¹ • primeLogPartialSum orbit N
  have hscale : Tendsto (fun n : ℕ => (⟨n + 1, by omega⟩ : Scale)) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N.val] with n hn
    change N.val ≤ n + 1
    omega
  have hlogSucc : Tendsto (fun n : ℕ => logMean (n + 1)) atTop (𝓝 (hg.toLp g)) := by
    apply Lp.tendsto_Lp_of_tendsto_eLpNorm g hg
    have hraw := hweighted.comp hscale
    apply hraw.congr'
    exact Filter.Eventually.of_forall (fun n =>
      (eLpNorm_congr_ae ((primeLogMeanLp_orbit_ae S c f hf ⟨n + 1, by omega⟩).sub
        (Filter.EventuallyEq.rfl : g =ᵐ[S.μ] g))).symm)
  have hlog : Tendsto logMean atTop (𝓝 (hg.toLp g)) :=
    (tendsto_add_atTop_iff_nat 1).mp hlogSucc
  let mean := fun N : ℕ => (Nat.primeCounting N : ℝ)⁻¹ • primePartialSum orbit N
  have hmean : Tendsto mean atTop (𝓝 (hg.toLp g)) :=
    normalizedPrimeMean_tendsto_of_logMean orbit (hg.toLp g) hlog hpi
  have hshift := (tendsto_add_atTop_iff_nat 2).mpr hmean
  have herror := (Lp.tendsto_Lp_iff_tendsto_eLpNorm (fun n => mean (n + 2)) g hg).mp hshift
  apply herror.congr'
  exact Filter.Eventually.of_forall (fun n =>
    eLpNorm_congr_ae ((primeMeanLp_orbit_ae S c f hf (n + 2) (by omega)).sub
      (Filter.EventuallyEq.rfl : g =ᵐ[S.μ] g)))

#print axioms primeAverage_eLpNorm_tendsto_of_logWeighted
end
end FractionalPrimes
