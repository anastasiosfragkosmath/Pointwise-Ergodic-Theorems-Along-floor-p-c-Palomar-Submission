module

public import FractionalPrimes.Literature.Harmonic.ContinuousModelDyadicVariation
public import FractionalPrimes.Literature.Harmonic.DyadicSpectralError

/-! Source dyadic variation and all-scale maximal bounds for the unweighted averages. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace FractionalPrimes
noncomputable section
open Literature.Harmonic

/-- `ha:dyadic`: both approved norms for the actual unweighted integer averages. -/
theorem unweightedDyadicVariationAndMaximal
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r) (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ),
      eLpNorm (rVariationFun r (unweightedDyadicFamily c (f : ℤ → ℂ)))
          (ENNReal.ofReal p) (Measure.count : Measure ℤ)+
        eLpNorm (unweightedIntegerMaximal c (f : ℤ → ℂ))
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
  obtain ⟨E,hE,hVar⟩ := unweightedDyadicVariation_eLpNorm_le_of_jsw hp hr c hc hcNon Cjsw hjsw
  let D : ℝ≥0∞ := ENNReal.ofReal
    (schwartzExtensionL continuousModelReproducingSchwartz^(1-p⁻¹)*
      schwartzExtensionS continuousModelReproducingSchwartz^p⁻¹)*(Cjsw : ℝ≥0∞)*
    ENNReal.ofReal (schwartzExtensionS continuousModelPsiSchwartz^(1-p⁻¹)*
      schwartzExtensionL continuousModelPsiSchwartz^p⁻¹)+2*ENNReal.ofReal E
  let C : ℝ≥0∞ := D+2*(1+D)
  have hD : D ≠ ∞ := by dsimp [D]; finiteness
  have hC : C ≠ ∞ := by dsimp [C]; finiteness
  refine ⟨C.toReal,ENNReal.toReal_nonneg,fun f => ?_⟩
  rw [ENNReal.ofReal_toReal hC]
  have hgm : MemLp (fun x : ℤ => (‖(f : ℤ → ℂ) x‖ : ℂ)) (ENNReal.ofReal p) Measure.count :=
    Complex.ofRealCLM.comp_memLp' (Lp.memLp f).norm
  let g := hgm.toLp (fun x : ℤ => (‖(f : ℤ → ℂ) x‖ : ℂ))
  have hgeq : (g : ℤ → ℂ) = fun x => (‖(f : ℤ → ℂ) x‖ : ℂ) := by
    funext x
    exact ae_count_int_iff_forall.mp hgm.coeFn_toLp x
  have hgnorm : eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal p) Measure.count =
      eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable g) (Lp.aestronglyMeasurable f)
    filter_upwards [] with x
    rw [hgeq]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have hVabs : eLpNorm (rVariationFun r (unweightedDyadicFamily c
      (fun x => (‖(f : ℤ → ℂ) x‖ : ℂ)))) (ENNReal.ofReal p) Measure.count ≤
      D*eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
    have hv := hVar g
    rw [hgnorm] at hv
    simpa only [hgeq] using hv
  have hM := unweightedIntegerMaximal_eLpNorm_le_of_dyadicVariation hp (by linarith : 0 < r) c f D hVabs
  have hV := hVar f
  change _ ≤ (D+2*(1+D))*eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count
  rw [add_mul]
  exact add_le_add hV hM

#print axioms unweightedDyadicVariationAndMaximal
end
end FractionalPrimes
end
