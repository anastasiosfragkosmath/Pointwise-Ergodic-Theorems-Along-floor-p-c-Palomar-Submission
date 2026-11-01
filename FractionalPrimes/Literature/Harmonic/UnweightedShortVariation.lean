module

public import FractionalPrimes.Literature.Harmonic.MSZIntegerRestriction

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
open Literature.Harmonic Literature.MSZ
noncomputable section

/-- `ha:short`: the actual integer-time dyadic short 2-variation square. -/
theorem unweightedShortVariation
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      eLpNorm (unweightedShortVariationSquare c (f : ℤ → ℂ))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C *
          eLpNorm (fun x : ℤ => f x) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨A, hA, hbound⟩ := unweightedMSZEndpointBound c hc hcNon p hp
  refine ⟨max 0 (sourceShortVariationConstant A), le_max_left _ _, fun f => ?_⟩
  have hmono : eLpNorm (unweightedShortVariationSquare c (f : ℤ → ℂ))
      (ENNReal.ofReal p) Measure.count ≤
      eLpNorm (mszSourceShortVariation A (f : ℤ → ℂ))
        (ENNReal.ofReal p) Measure.count := by
    apply eLpNorm_mono_enorm_ae (measurable_of_countable _).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [enorm_eq_self] using
        unweightedShortVariationSquare_le_msz c A hA (f : ℤ → ℂ) x)
  exact hmono.trans ((hbound f).2.trans
    (mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_max_right _ _)) bot_le))

#print axioms unweightedShortVariation
end
end FractionalPrimes
