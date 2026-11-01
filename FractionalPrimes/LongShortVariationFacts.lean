module

public import FractionalPrimes.LongShortVariation
public import FractionalPrimes.MixedNorm

@[expose] public section

namespace FractionalPrimes

open MeasureTheory

/-- The paper-facing pointwise, mixed-norm, and `Lᵖ` statements in
blueprint `lem:long-short`. -/
structure LongShortVariationFacts : Prop where
  pointwise_reduction : ∀ {s : ℕ → Scale},
    s 0 = ⟨1, Nat.succ_pos 0⟩ → Monotone s →
    Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale) →
    ∀ u : Scale → ℂ, ∀ {r : ℝ}, 2 ≤ r →
      rVariation r u ≤
        3 * rVariation r (fun K : Scale => u (s (K.1 - 1))) +
          3 * (∑' k : ℕ,
            ((rVariationOn 2 u (Set.Icc (s k) (s (k + 1)))).rpow 2)).rpow
              (1 / 2 : ℝ)
  repeated_scale_block_zero : ∀ (s : ℕ → Scale) (k : ℕ)
    (u : Scale → ℂ), s k = s (k + 1) →
      rVariationOn 2 u (Set.Icc (s k) (s (k + 1))) = 0
  mixed_norm : ∀ {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : ℕ → X → ENNReal) {p : ℝ}, 1 < p →
      (∀ k, AEStronglyMeasurable (f k) μ) →
      eLpNorm (fun x => (∑' k, (f k x) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ)) (ENNReal.ofReal p) μ ≤
        (∑' k, (eLpNorm (f k) (ENNReal.ofReal p) μ) ^ min p 2) ^
          (1 / min p 2)
  lp_reduction : ∀ {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (s : ℕ → Scale),
    s 0 = ⟨1, Nat.succ_pos 0⟩ → Monotone s →
    Filter.Tendsto s (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter Scale) →
    ∀ F : Scale → X → ℂ, ∀ {p r : ℝ}, 1 < p → 2 ≤ r →
      (∀ N, AEMeasurable (F N) μ) →
      eLpNorm (rVariationFun r F) (ENNReal.ofReal p) μ ≤
        3 * eLpNorm
            (rVariationFun r (fun K : Scale => F (s (K.1 - 1))))
            (ENNReal.ofReal p) μ +
          3 * (∑' k,
            (eLpNorm (rVariationOnFun 2 F
              (Set.Icc (s k) (s (k + 1)))) (ENNReal.ofReal p) μ) ^
                min p 2) ^ (1 / min p 2)

/-- The checked long/short variation package, including non-strict sparse
scales so repetitions are permitted. -/
theorem longShortVariation : LongShortVariationFacts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs0 hs hUnbounded u r hr2
    exact rVariation_le_sparse_and_blockSquare hs0 hs hUnbounded u hr2
  · intro s k u hrep
    simpa [hrep] using
      (rVariationOn_singleton_eq_zero (r := 2) (by norm_num) u (s k))
  · intro X _ μ f p hp hf
    exact eLpNorm_tsumSquare_mixed μ f hp hf
  · intro X _ μ s hs0 hs hUnbounded F p r hp hr2 hF
    exact eLpNorm_longShort_reduction μ s hs0 hs hUnbounded F hp hr2 hF

end FractionalPrimes
