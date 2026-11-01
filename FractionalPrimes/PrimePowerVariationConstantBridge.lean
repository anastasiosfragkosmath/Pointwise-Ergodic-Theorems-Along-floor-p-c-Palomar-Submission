module
public import FractionalPrimes.Core
public import FractionalPrimes.PrimeMobiusFinalUnconditional
@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
universe u

/-- A finite extended-nonnegative variation constant can be replaced by a
strictly positive finite nonnegative-real constant. The added `1` handles the
case where the original bound is zero. -/
theorem primePowerVariationStatement_of_finiteENNRealBound
    (q : VariationParameters)
    (hbound :
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧
        ∀ {X : Type u} [MeasurableSpace X] (S : InvertibleSystem X)
          (f : X → ℂ), MemLp f (ENNReal.ofReal q.p) S.μ →
          eLpNorm (rVariationFun q.r
            (fun N => vonMangoldtAverage S q.exponent.value f N))
              (ENNReal.ofReal q.p) S.μ ≤
            C * eLpNorm f (ENNReal.ofReal q.p) S.μ) :
    PrimePowerVariationStatement.{u} q := by
  obtain ⟨C₀, hC₀, hvar⟩ := hbound
  let C : ℝ≥0 := C₀.toNNReal + 1
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCcast : (C : ℝ≥0∞) = C₀ + 1 := by
    dsimp [C]
    rw [ENNReal.coe_toNNReal hC₀]
  have hC₀_le : C₀ ≤ (C : ℝ≥0∞) := by
    rw [hCcast]
    exact le_add_of_nonneg_right (by positivity)
  refine ⟨C, hCpos, ?_⟩
  intro X hX S f hf
  change eLpNorm (rVariationFun q.r
      (fun N => vonMangoldtAverage S q.exponent.value f N))
        (ENNReal.ofReal q.p) S.μ ≤
      (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal q.p) S.μ
  calc
    _ ≤ C₀ * eLpNorm f (ENNReal.ofReal q.p) S.μ := hvar S f hf
    _ ≤ (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal q.p) S.μ :=
      mul_le_mul_of_nonneg_right hC₀_le (by positivity)

/-- The source's unconditional `ℝ≥0∞` variation bound therefore gives the
paper-facing `PrimePowerVariationStatement` with a positive `ℝ≥0` constant. -/
theorem primePowerVariationStatement_of_OAISource
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r) (c : FractionalExponent) :
    PrimePowerVariationStatement.{u}
      ⟨c, p, hp, r, hr⟩ := by
  apply primePowerVariationStatement_of_finiteENNRealBound
  exact primePowerVariation_of_OAISource hp hr c

#print axioms primePowerVariationStatement_of_finiteENNRealBound
#print axioms primePowerVariationStatement_of_OAISource

end
end FractionalPrimes
