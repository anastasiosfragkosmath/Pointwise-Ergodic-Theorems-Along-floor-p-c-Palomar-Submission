module
public import FractionalPrimes.Final.PrimeVariation
public import FractionalPrimes.VariationConvergence
public import FractionalPrimes.VariationMeasurability
public import FractionalPrimes.Literature.Ergodic.ScaleConvergenceBridge
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem memLp_weightedAverage {X : Type*} [MeasurableSpace X]
    (S : System X) (c : ℝ) (w : ℕ → ℂ) (f : X → ℂ) (N : Scale)
    {p : ℝ≥0∞} (hf : MemLp f p S.μ) : MemLp (weightedAverage S c w f N) p S.μ := by
  have hsum := memLp_finsetSum (Finset.Icc 1 N.1)
    (fun n _ => (S.memLp_shift (floorTime c n) hf).const_mul (w n))
  exact hsum.const_mul (N.1 : ℂ)⁻¹

/-- The revised corollary's von Mangoldt averages converge on every
sigma-finite measure-preserving system, with no invertibility assumption. -/
theorem vonMangoldtAverageConvergence {p : ℝ} (hp : 1 < p)
    (c : FractionalExponent) {X : Type*} [MeasurableSpace X]
    (S : System X) (f : X → ℂ) (hf : MemLp f (ENNReal.ofReal p) S.μ) :
    ∃ g : X → ℂ, MemLp g (ENNReal.ofReal p) S.μ ∧
      (∀ᵐ x ∂S.μ, Tendsto (fun N : Scale => vonMangoldtAverage S c.value f N x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun N : Scale => eLpNorm (vonMangoldtAverage S c.value f N - g)
        (ENNReal.ofReal p) S.μ) atTop (𝓝 0) := by
  let F := vonMangoldtAverage S c.value f
  have hF (N : Scale) : MemLp (F N) (ENNReal.ofReal p) S.μ :=
    memLp_weightedAverage S c.value (fun n => (vonMangoldtWeight n : ℂ)) f N hf
  obtain ⟨C, _, hbound⟩ := primePowerVariation ⟨c, p, hp, 3, by norm_num⟩
  have hV : MemLp (rVariationFun 3 F) (ENNReal.ofReal p) S.μ := by
    exact lt_of_le_of_lt (hbound S f hf)
      (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.eLpNorm_lt_top)
  obtain ⟨g, _, hg, hAE, hLp⟩ := exists_limit_and_tendsto_eLpNorm_of_rVariationFun_memLp
    hp.le (by norm_num : (0 : ℝ) < 3) F (fun N => (hF N).aestronglyMeasurable)
    hV (hF ⟨1, by omega⟩)
  refine ⟨g, hg, ?_, ?_⟩
  · filter_upwards [hAE] with x hx
    exact tendsto_scale_of_natSucc (fun N => F N x) hx
  · exact tendsto_scale_of_natSucc (fun N => eLpNorm (F N - g) (ENNReal.ofReal p) S.μ) hLp

#print axioms vonMangoldtAverageConvergence
end
end FractionalPrimes.Final
