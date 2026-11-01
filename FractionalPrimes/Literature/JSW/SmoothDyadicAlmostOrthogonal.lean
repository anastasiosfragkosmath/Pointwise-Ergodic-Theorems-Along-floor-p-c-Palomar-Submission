module

public import FractionalPrimes.Literature.JSW.SmoothDyadicFullEnergy

/-! The approved smooth/dyadic almost-orthogonality theorem, with actual raw errors. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothDyadicRawError
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (a : ℝ) (ha : 0 < a)
    (k : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  jswConvolution (Measure.map (fun z : ℝ => jswTau a ha k*z)
    (initialSquarePsiProbabilityMeasure σ)) f x-dyadicAverage (jswM a ha k) f x

def smoothDyadicRawSquareEnergy
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (a : ℝ) (ha : 0 < a)
    (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℤ, ENNReal.ofReal (‖smoothDyadicRawError σ a ha k f x‖^2)

theorem smoothDyadic_raw_full_L2_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    [Fact (1 ≤ ENNReal.ofReal (2 : ℝ))]
    {a : ℝ} (ha : 0 < a)
    (F : Lp ℂ (ENNReal.ofReal (2 : ℝ)) (volume : Measure ℝ)) :
    (∀ᵐ x ∂volume, smoothDyadicRawSquareEnergy σ a ha (F : ℝ → ℂ) x < ∞) ∧
    eLpNorm (fun x => Real.sqrt (smoothDyadicRawSquareEnergy σ a ha (F : ℝ → ℂ) x).toReal)
      (ENNReal.ofReal (2 : ℝ)) volume ≤ ENNReal.ofReal (smoothDyadicSquareConstant a ha*‖F‖) := by
  let v := fun k : ℤ => smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num)
    (jswTau a ha k) (jswM a ha k) F
  have hrep (k : ℤ) : (v k : ℝ → ℂ) =ᵐ[volume] smoothDyadicRawError σ a ha k (F : ℝ → ℂ) :=
    smoothDyadicErrorLpOperator_ae_eq hSupp (p := 2) (by norm_num) _ _ F _
      (Lp.stronglyMeasurable F).measurable (Lp.memLp F) Filter.EventuallyEq.rfl
  have henergy : (fun x => ∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)) =ᵐ[volume]
      smoothDyadicRawSquareEnergy σ a ha (F : ℝ → ℂ) := by
    filter_upwards [ae_all_iff.mpr hrep] with x hx
    apply tsum_congr
    intro k
    rw [hx k]
  have hfull := smoothDyadic_full_L2_energy hSupp ha F
  constructor
  · filter_upwards [hfull.1, henergy] with x hx heq
    rw [← heq]
    exact hx
  · have hsquare := henergy.fun_comp (fun z : ℝ≥0∞ => Real.sqrt z.toReal)
    have hn := eLpNorm_congr_ae hsquare (p := ENNReal.ofReal (2 : ℝ))
    simp only [Function.comp_def] at hn
    exact hn.symm.le.trans hfull.2

/-- `lj:smooth-almost-orthogonal`: exact block decay and the full actual
smooth/dyadic L2 square bound, with the approved A_φ, M_a and W₀. -/
theorem smoothDyadicAlmostOrthogonal
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) :
    letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
    (∀ (k j : ℤ) (f : ℝ → ℂ), MemLp f 2 volume →
      MemLp (smoothDyadicRawError σ a ha k (dyadicDifference j f)) 2 volume ∧
      lpNorm (smoothDyadicRawError σ a ha k (dyadicDifference j f)) 2 volume ≤
        smoothDyadicAmplitude*smoothDyadicWeight (jswM a ha k-j)*lpNorm (dyadicDifference j f) 2 volume) ∧
    (∀ F : Lp ℂ (ENNReal.ofReal (2 : ℝ)) (volume : Measure ℝ),
      (∀ᵐ x ∂volume, smoothDyadicRawSquareEnergy σ a ha (F : ℝ → ℂ) x < ∞) ∧
      eLpNorm (fun x => Real.sqrt (smoothDyadicRawSquareEnergy σ a ha (F : ℝ → ℂ) x).toReal)
        (ENNReal.ofReal (2 : ℝ)) volume ≤ ENNReal.ofReal (smoothDyadicSquareConstant a ha*‖F‖)) := by
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  constructor
  · intro k j f hf
    exact smoothDyadic_source_block_decay hSupp ha k j hf
  · exact smoothDyadic_raw_full_L2_bound hSupp ha

#print axioms smoothDyadicAlmostOrthogonal
#print axioms smoothDyadic_raw_full_L2_bound
end
end FractionalPrimes.Literature.JSW
end
