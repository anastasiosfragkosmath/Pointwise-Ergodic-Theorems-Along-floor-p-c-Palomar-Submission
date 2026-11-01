module

public import FractionalPrimes.Literature.Harmonic.ContinuousModelJSWBound

/-! The sampled continuous model has full dyadic variation bounds, with no JSW premise. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
open scoped NNReal
namespace FractionalPrimes
noncomputable section
open Literature.Harmonic

/-- `ha:model-var`: the actual sampled-model dyadic variation bound for all lp inputs. -/
theorem continuousModelDyadicVariation
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r) (c : ℝ) (hc : 1 < c) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ),
      eLpNorm (rVariationFun r (continuousModelDyadicFamily c hc f))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ) ≤
      ENNReal.ofReal C*eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let Cjsw : ℝ≥0 := Real.toNNReal (continuousModelJSWConstant c hc p r)
  have hjsw (g : ℤ →₀ ℂ) : eLpNorm
      (fun x => Literature.Variation.orderedRVariation r
        (fun k : ℤ => continuousModelAllDyadicConvolutionFamily c hc g k x))
        (ENNReal.ofReal p) volume ≤ (Cjsw : ℝ≥0∞)*
          eLpNorm (continuousModelSchwartzExtension g : ℝ → ℂ) (ENNReal.ofReal p) volume :=
    continuousModelSchwartzExtension_jsw_bound hp hr c hc g
  let Cχ := schwartzExtensionL continuousModelReproducingSchwartz^(1-p⁻¹)*
    schwartzExtensionS continuousModelReproducingSchwartz^p⁻¹
  let Cψ := schwartzExtensionS continuousModelPsiSchwartz^(1-p⁻¹)*
    schwartzExtensionL continuousModelPsiSchwartz^p⁻¹
  let B : ℝ≥0∞ := ENNReal.ofReal Cχ*(Cjsw : ℝ≥0∞)*ENNReal.ofReal Cψ
  have hB : B ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)
      ENNReal.ofReal_ne_top
  refine ⟨B.toReal,ENNReal.toReal_nonneg,fun f => ?_⟩
  rw [ENNReal.ofReal_toReal hB]
  exact continuousModelDyadicVariation_eLpNorm_le_of_jsw hp hr c hc Cjsw hjsw f

#print axioms continuousModelDyadicVariation
end
end FractionalPrimes
end
