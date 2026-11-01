module

public import FractionalPrimes.Literature.JSW.MeasureDilateJumpBound
public import FractionalPrimes.Literature.JSW.RoughSquareRawStrongEndpoints

/-! The exact uniform jump theorem for arbitrary MemLp representatives. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def jswMeasureJumpConstant (p a : ℝ) (ha : 0 < a) (S : ℝ) : ℝ :=
  6*S+6*smoothDyadicSquareLpConstant p a ha+3*jswDyadicJumpConstant p

theorem measureDilateJumpBound_raw
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D p a : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D*|ξ|^(-β))
    (hβ : 0 < β) (hp : 1 < p) (ha : 0 < a) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (K : Finset ℤ) (t : ℝ), 0 < t →
      ∀ (f : ℝ → ℂ), MemLp f (ENNReal.ofReal p) volume →
      let J := finiteJumpControl
        (fun k : {k : ℤ // k ∈ K} => jswConvolution
          (Measure.map (fun z : ℝ => jswTau a ha k.1*z) σ) f) t
      MemLp J (ENNReal.ofReal p) volume ∧
      eLpNorm J (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (jswMeasureJumpConstant p a ha S)*eLpNorm f (ENNReal.ofReal p) volume := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨S,hS,hjump⟩ := measureDilateJumpBound hSupp hdecay hβ hp ha
  refine ⟨S,hS,fun K t ht f hf => ?_⟩
  let F := hf.toLp f
  let G := fun k : {k : ℤ // k ∈ K} => jswConvolution
    (Measure.map (fun z : ℝ => jswTau a ha k.1*z) σ) (F : ℝ → ℂ)
  let H := fun k : {k : ℤ // k ∈ K} => jswConvolution
    (Measure.map (fun z : ℝ => jswTau a ha k.1*z) σ) f
  have hcoord (k : {k : ℤ // k ∈ K}) : G k =ᵐ[volume] H k :=
    integral_sub_translation_congr_ae _ _ _ hf.coeFn_toLp
  have hctrl : finiteJumpControl G t =ᵐ[volume] finiteJumpControl H t := by
    filter_upwards [ae_all_iff.mpr hcoord] with x hx
    have heq : (fun k => G k x) = fun k => H k x := funext hx
    unfold finiteJumpControl
    rw [heq]
  obtain ⟨hGF,hNorm⟩ := hjump K t ht F
  have hH : MemLp (finiteJumpControl H t) (ENNReal.ofReal p) volume := hGF.ae_eq hctrl
  have hn := congrArg ENNReal.toReal (eLpNorm_congr_ae hctrl (p := ENNReal.ofReal p))
  change lpNorm (finiteJumpControl G t) (ENNReal.ofReal p) volume =
    lpNorm (finiteJumpControl H t) (ENNReal.ofReal p) volume at hn
  have hnF : ‖F‖ = lpNorm f (ENNReal.ofReal p) volume :=
    congrArg ENNReal.toReal (eLpNorm_congr_ae hf.coeFn_toLp)
  change lpNorm (finiteJumpControl G t) (ENNReal.ofReal p) volume ≤ _ at hNorm
  rw [hn,hnF] at hNorm
  exact ⟨hH,eLpNorm_le_mul_of_lpNorm_le hH hf hNorm⟩

#print axioms measureDilateJumpBound_raw
end
end FractionalPrimes.Literature.JSW
end
