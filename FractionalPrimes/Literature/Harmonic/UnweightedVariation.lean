module

public import FractionalPrimes.Literature.Harmonic.UnweightedShortVariation
public import FractionalPrimes.MixedNorm

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes
open Literature.Harmonic
noncomputable section

theorem unweightedDyadicScale_monotone : Monotone unweightedDyadicScale := by
  intro i j hij
  change 2 ^ i ≤ 2 ^ j
  exact pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hij

theorem unweightedDyadicScale_tendsto : Filter.Tendsto unweightedDyadicScale
    Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro N
  apply Filter.eventually_atTop.2
  refine ⟨N.val, fun k hk => ?_⟩
  change N.val ≤ 2 ^ k
  exact hk.trans (Nat.lt_two_pow_self.le)

/-- `ha:unweighted`: all-scale variation of the actual integer-shift averages. -/
theorem unweightedVariation
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r)
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ),
      eLpNorm (rVariationFun r (fun N =>
          unweightedAverage integerShiftSystem c (f : ℤ → ℂ) N))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨D, hD, hdyadic⟩ := unweightedDyadicVariationAndMaximal hp hr c hc hcNon
  obtain ⟨S, hS, hshort⟩ := unweightedShortVariation c hc hcNon p hp
  refine ⟨3 * D + 3 * S, by positivity, fun f => ?_⟩
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  let g := countLpToGeneralLp hp0 ENNReal.ofReal_ne_top f
  have hg : (g : ℤ → ℂ) = (f : ℤ → ℂ) :=
    funext (countLpToGeneralLp_apply hp0 ENNReal.ofReal_ne_top f)
  have hlong : eLpNorm (rVariationFun r (unweightedDyadicFamily c (f : ℤ → ℂ)))
      (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal D * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count :=
    (le_add_of_nonneg_right bot_le).trans (hdyadic f)
  have hsquare := hshort g
  rw [hg] at hsquare
  have hreduce := eLpNorm_longShort_reduction_direct (Measure.count : Measure ℤ)
    unweightedDyadicScale (by rfl) unweightedDyadicScale_monotone
    unweightedDyadicScale_tendsto
    (fun N => unweightedAverage integerShiftSystem c (f : ℤ → ℂ) N)
    hp hr.le (fun _ => (measurable_of_countable _).aemeasurable)
  have hreduce' : eLpNorm (rVariationFun r (fun N =>
      unweightedAverage integerShiftSystem c (f : ℤ → ℂ) N))
      (ENNReal.ofReal p) Measure.count ≤
      3 * eLpNorm (rVariationFun r (unweightedDyadicFamily c (f : ℤ → ℂ)))
          (ENNReal.ofReal p) Measure.count +
        3 * eLpNorm (unweightedShortVariationSquare c (f : ℤ → ℂ))
          (ENNReal.ofReal p) Measure.count := by
    unfold unweightedDyadicFamily unweightedShortVariationSquare
    simpa only [rVariationOnFun, ENNReal.rpow_eq_pow] using hreduce
  calc
    _ ≤ _ := hreduce'
    _ ≤ 3 * (ENNReal.ofReal D * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count) +
        3 * (ENNReal.ofReal S * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count) :=
      add_le_add (mul_le_mul_of_nonneg_left hlong bot_le)
        (mul_le_mul_of_nonneg_left hsquare bot_le)
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity : 0 ≤ 3 * D) (by positivity : 0 ≤ 3 * S),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
      ring

#print axioms unweightedVariation
end
end FractionalPrimes
