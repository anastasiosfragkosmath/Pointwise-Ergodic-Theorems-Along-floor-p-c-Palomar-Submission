module
public import FractionalPrimes.Final.MainTargets
public import FractionalPrimes.Final.ForwardWeightedVariation
@[expose] public section
namespace FractionalPrimes.Final
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
universe u

/-- Revised manuscript Theorem t:maintheorem, including transformations
without inverses. The constant is uniform over all systems and observables. -/
theorem primePowerVariation (q : VariationParameters) :
    PrimeVariationStatement.{u} q := by
  obtain ⟨C, hC, hbound⟩ := FractionalPrimes.primePowerVariation.{0} q
  refine ⟨C, hC, ?_⟩
  intro X _ S f hf
  apply transferForwardWeightedFloorVariation q.one_lt_p
    (by linarith [q.two_lt_r] : 1 ≤ q.r)
    q.exponent.value (fun _ n => (vonMangoldtWeight n : ℂ)) C ?_ S f hf
  intro g
  exact hbound integerShiftSystem (g : ℤ → ℂ)
    (memLp_count_of_memlp_seq_finite
      (ENNReal.ofReal_ne_zero_iff.mpr (by linarith [q.one_lt_p]))
      ENNReal.ofReal_ne_top g)

#print axioms primePowerVariation
end
end FractionalPrimes.Final
