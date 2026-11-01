module

public import FractionalPrimes.Literature.JSW.MeasureDilateJumpRaw
public import FractionalPrimes.Literature.JSW.ProbabilityConvolutionLayerCake
public import FractionalPrimes.Literature.JSW.FiniteJumpEmbeddingNorm

/-! Uniform source jump moments on every finite ordered subfamily of actual measure dilates. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
open FractionalPrimes.Literature.Variation
namespace FractionalPrimes.Literature.JSW
noncomputable section

def jswMeasureRawOperator
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (a : ℝ) (ha : 0 < a) (k : ℤ) :
    (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
  probabilityConvolutionRawLinearMap (Measure.map (fun z : ℝ => jswTau a ha k*z) σ)

theorem jswDyadicJumpConstant_nonneg {p : ℝ} (hp : 1 < p) :
    0 ≤ jswDyadicJumpConstant p := by
  have hcp : 0 ≤ littlewoodPaleyCp p := by
    unfold littlewoodPaleyCp
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by norm_num) _)
  exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hcp))
    (weakTypeJumpConstant_nonneg hp)

theorem jswMeasureJumpConstant_nonneg {p a S : ℝ} (hp : 1 < p) (ha : 0 < a) (hS : 0 ≤ S) :
    0 ≤ jswMeasureJumpConstant p a ha S := by
  have hR := smoothDyadicSquareLpConstant_nonneg hp ha
  have hJ := jswDyadicJumpConstant_nonneg hp
  unfold jswMeasureJumpConstant
  positivity

theorem measureDilateJumpMoments
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D p a : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 → ‖measureSplittingFourier σ ξ‖ ≤ D*|ξ|^(-β))
    (hβ : 0 < β) (hp : 1 < p) (ha : 0 < a) :
    ∃ S : ℝ, 0 ≤ S ∧ 0 ≤ jswMeasureJumpConstant p a ha S ∧
      ∀ {J : Type} [LinearOrder J] [Fintype J] (e : J ↪o ℤ)
        (g : LayerCakeInput (volume : Measure ℝ)) (t : ℝ), 0 < t →
      (∫⁻ x, (jumpAmplitude (fun j => jswMeasureRawOperator σ a ha (e j) g.1) t x).rpow p ∂volume) ≤
        (ENNReal.ofReal (jswMeasureJumpConstant p a ha S)).rpow p*complexLpMoment p volume g.1 := by
  obtain ⟨S,hS,hjump⟩ := measureDilateJumpBound_raw hSupp hdecay hβ hp ha
  refine ⟨S,hS,jswMeasureJumpConstant_nonneg hp ha hS,?_⟩
  intro J _ _ e g t ht
  classical
  let K : Finset ℤ := Finset.univ.image e
  let eK : J ↪o {k : ℤ // k ∈ K} := {
    toFun := fun j => ⟨e j, Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩⟩
    inj' := by intro i j h; exact e.injective (congrArg Subtype.val h)
    map_rel_iff' := by intro i j; exact e.le_iff_le }
  let G := fun k : {k : ℤ // k ∈ K} => jswConvolution
    (Measure.map (fun z : ℝ => jswTau a ha k.1*z) σ) g.1
  let H := fun j => jswMeasureRawOperator σ a ha (e j) g.1
  have hG (k : {k : ℤ // k ∈ K}) : Measurable (G k) :=
    measurable_jswConvolution_of_measurable _ g.2.1
  have hH (j : J) : Measurable (H j) := probabilityConvolutionRawLinearMap_measurable _ g
  have hHG : H = fun j => G (eK j) := by
    funext j
    exact probabilityConvolutionRawLinearMap_eq _ g.1 g.2.1 g.2.2.1
  have hK := (hjump K t ht g.1 (roughSquare_layerCakeInput_memLp g (ENNReal.ofReal p))).2
  have hsmall := finiteJumpControl_eLpNorm_comp_orderEmbedding_le eK G hG ht.le (ENNReal.ofReal p)
  have hnorm : eLpNorm (finiteJumpControl H t) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (jswMeasureJumpConstant p a ha S)*eLpNorm g.1 (ENNReal.ofReal p) volume := by
    rw [hHG]
    exact hsmall.trans hK
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpow := ENNReal.rpow_le_rpow hnorm hp0.le
  rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal (jswMeasureJumpConstant p a ha S))
    (eLpNorm g.1 (ENNReal.ofReal p) volume) hp0.le] at hpow
  rw [finiteJumpControl_moment_eq_eLpNorm_rpow H hH ht.le hp0,
    complexLpMoment_eq_eLpNorm_rpow volume hp0 g.1 g.2.1]
  simpa only [ENNReal.rpow_eq_pow] using hpow

#print axioms measureDilateJumpMoments
end
end FractionalPrimes.Literature.JSW
end
