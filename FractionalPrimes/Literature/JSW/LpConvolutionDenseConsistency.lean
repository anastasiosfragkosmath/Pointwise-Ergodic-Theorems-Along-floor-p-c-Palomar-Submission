module

public import FractionalPrimes.Literature.JSW.FinitePositiveMaximalLp
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Dense-input consistency for convolution on different `L^p` spaces

A bounded dense-class input defines the same local convolution integrals in
its `L^q` and `L^2` realizations. This is the first representative bridge
needed to compare the finite `L^q` maximal map with the source averages.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

private theorem memLp_translation_integrable_prod
    {q : ℝ} (hq : 1 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (f : ℝ → ℂ) (hf : StronglyMeasurable f)
    (hfm : MemLp f (ENNReal.ofReal q) (volume : Measure ℝ))
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s < ∞) :
    Integrable (fun z : ℝ × ℝ => f (z.1-z.2))
      ((volume.restrict s).prod ν) := by
  let p : ℝ≥0∞ := ENNReal.ofReal q
  let u : ℝ × ℝ → ℝ := fun z => ‖f (z.1-z.2)‖ ^ q
  have hqnonneg : 0 ≤ q := by linarith
  have hp0 : p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hpTop : p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpow : Integrable (fun x : ℝ => ‖f x‖ ^ q) (volume : Measure ℝ) := by
    simpa [p, ENNReal.toReal_ofReal hqnonneg] using
      hfm.integrable_norm_rpow hp0 hpTop
  have hpowSm : StronglyMeasurable (fun x : ℝ => ‖f x‖ ^ q) :=
    (Real.continuous_rpow_const hqnonneg).comp_stronglyMeasurable hf.norm
  have huSm : StronglyMeasurable u := by
    dsimp [u]
    exact hpowSm.comp_measurable (by fun_prop)
  have htranslated (y : ℝ) :
      Integrable (fun x : ℝ => ‖f (x-y)‖ ^ q) (volume : Measure ℝ) := by
    have hcomp := (measurePreserving_sub_right (volume : Measure ℝ) y).integrable_comp
      hpowSm.aestronglyMeasurable
    change Integrable ((fun x : ℝ => ‖f x‖ ^ q) ∘ (fun x => x-y)) volume
    exact hcomp.mpr hpow
  letI : IsFiniteMeasure (volume.restrict s) := ⟨by simpa using hμs⟩
  letI : IsFiniteMeasure ((volume.restrict s).prod ν) := inferInstance
  have hslice (y : ℝ) :
      Integrable (fun x : ℝ => u (x,y)) (volume.restrict s) := by
    change Integrable (fun x : ℝ => ‖f (x-y)‖ ^ q) (volume.restrict s)
    exact (htranslated y).mono_measure Measure.restrict_le_self
  have houterSm : StronglyMeasurable
      (fun y : ℝ => ∫ x, u (x,y) ∂(volume.restrict s)) :=
    huSm.integral_prod_left'
  have houterBound (y : ℝ) :
      ‖∫ x, u (x,y) ∂(volume.restrict s)‖ ≤
        ∫ x, ‖f x‖ ^ q ∂(volume : Measure ℝ) := by
    change ‖∫ x, ‖f (x-y)‖ ^ q ∂(volume.restrict s)‖ ≤ _
    rw [Real.norm_of_nonneg
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)]
    calc
      ∫ x, u (x,y) ∂(volume.restrict s) ≤
          ∫ x, ‖f (x-y)‖ ^ q ∂(volume : Measure ℝ) := by
        apply integral_mono_measure Measure.restrict_le_self
        · exact Filter.Eventually.of_forall
            (fun x => Real.rpow_nonneg (norm_nonneg _) _)
        · exact htranslated y
      _ = ∫ x, ‖f x‖ ^ q ∂(volume : Measure ℝ) := by
        simpa using
          (measurePreserving_sub_right (volume : Measure ℝ) y).integral_comp
            (measurableEmbedding_subRight y) (fun x => ‖f x‖ ^ q)
  have houter : Integrable
      (fun y : ℝ => ∫ x, u (x,y) ∂(volume.restrict s)) ν := by
    apply Integrable.of_bound houterSm.aestronglyMeasurable
      (∫ x, ‖f x‖ ^ q ∂(volume : Measure ℝ))
    filter_upwards [] with y
    exact houterBound y
  have huProd : Integrable u ((volume.restrict s).prod ν) := by
    apply (integrable_prod_iff' huSm.aestronglyMeasurable).2
    refine ⟨Filter.Eventually.of_forall hslice, ?_⟩
    convert houter using 1
    funext y
    apply integral_congr_ae
    filter_upwards [] with x
    simp [u, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hfunSm : StronglyMeasurable
      (fun z : ℝ × ℝ => f (z.1-z.2)) :=
    hf.comp_measurable (by fun_prop)
  have hmem : MemLp (fun z : ℝ × ℝ => f (z.1-z.2)) p
      ((volume.restrict s).prod ν) := by
    apply (integrable_norm_rpow_iff hfunSm.aestronglyMeasurable hp0 hpTop).mp
    simpa [u, p, ENNReal.toReal_ofReal hqnonneg] using huProd
  have hmemOne : MemLp (fun z : ℝ × ℝ => f (z.1-z.2)) 1
      ((volume.restrict s).prod ν) :=
    hmem.mono_exponent (ENNReal.one_le_ofReal.mpr hq.le)
  exact memLp_one_iff_integrable.mp hmemOne

private theorem lpComplexMeasureConvolution_setIntegral_eq
    {q : ℝ} (hq : 1 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ))
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfm : MemLp f (ENNReal.ofReal q) (volume : Measure ℝ))
    (hF : (F : ℝ → ℂ) =ᵐ[volume] f)
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s < ∞) :
    ∫ x in s, (lpComplexMeasureConvolution (ENNReal.ofReal q) μ F) x
        ∂(volume : Measure ℝ) =
      ∫ x in s, complexMeasureConvolution μ f
        (hf.stronglyMeasurable.aestronglyMeasurable) x ∂(volume : Measure ℝ) := by
  let p : ℝ≥0∞ := ENNReal.ofReal q
  let qstar : ℝ := q / (q - 1)
  let pstar : ℝ≥0∞ := ENNReal.ofReal qstar
  have hqstar : 1 < qstar := by
    dsimp [qstar]
    rw [lt_div_iff₀ (by linarith : 0 < q - 1)]
    linarith
  have hconj : q.HolderConjugate qstar := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact hq
    · dsimp [qstar]
      field_simp
      ring
  letI : Fact (1 ≤ p) := ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  letI : Fact (1 ≤ pstar) := ⟨ENNReal.one_le_ofReal.mpr hqstar.le⟩
  letI : p.HolderConjugate pstar := hconj.ennrealOfReal
  letI : IsFiniteMeasure (volume.restrict s) := ⟨by simpa using hμs⟩
  letI : IsFiniteMeasure ((volume.restrict s).prod μ.variation) := inferInstance
  let u : ℝ × ℝ → ℂ := fun z => f (z.1-z.2)
  have husm : StronglyMeasurable u :=
    hf.stronglyMeasurable.comp_measurable (by fun_prop)
  have hprod : Integrable u ((volume.restrict s).prod μ.variation) := by
    simpa [u] using memLp_translation_integrable_prod hq f
      hf.stronglyMeasurable hfm μ.variation s hs hμs
  have hshift (y : ℝ) :
      (fun x : ℝ => F (x-y)) =ᵐ[volume] (fun x => f (x-y)) :=
    (measurePreserving_sub_right (volume : Measure ℝ) y).quasiMeasurePreserving.ae hF
  let φ : Lp ℂ pstar (volume : Measure ℝ) :=
    indicatorConstLp pstar hs hμs.ne (1 : ℂ)
  let J : Lp ℂ p (volume : Measure ℝ) →L[ℝ] ℂ :=
    ((ContinuousLinearMap.lpPairing (volume : Measure ℝ) p pstar
        (ContinuousLinearMap.mul ℝ ℂ)).flip) φ
  letI : IsFiniteMeasure (volume.restrict s) := ⟨by simpa using hμs⟩
  let η : VectorMeasure ℝ ℝ :=
    (1 : ℝ) • (volume.restrict s).toSignedMeasure
  have hη : η.variation = volume.restrict s := by simp [η, VectorMeasure.variation_smul]
  letI : IsFiniteMeasure η.variation := hη ▸
    (inferInstance : IsFiniteMeasure (volume.restrict s))
  have hLpInt : IntegrableOn (lpComplexMeasureConvolution p μ F) s volume :=
    integrableOn_Lp_of_measure_ne_top (lpComplexMeasureConvolution p μ F)
      (ENNReal.one_le_ofReal.mpr hq.le) hμs.ne
  have hleft :
      J (lpComplexMeasureConvolution p μ F) =
        ∫ x in s, (lpComplexMeasureConvolution p μ F) x ∂volume := by
    change (ContinuousLinearMap.lpPairing (volume : Measure ℝ) p pstar
      (ContinuousLinearMap.mul ℝ ℂ)) (lpComplexMeasureConvolution p μ F) φ = _
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    have hφ : (φ : ℝ → ℂ) =ᵐ[volume] s.indicator (fun _ => (1 : ℂ)) :=
      indicatorConstLp_coeFn
    calc
      _ = ∫ x, (lpComplexMeasureConvolution p μ F) x *
            s.indicator (fun _ => (1 : ℂ)) x ∂volume := by
          apply integral_congr_ae
          filter_upwards [hφ] with x hx
          simp [ContinuousLinearMap.mul_apply, hx]
      _ = ∫ x in s, (lpComplexMeasureConvolution p μ F) x ∂volume := by
          rw [← integral_indicator hs]
          congr 1
          funext x
          by_cases hx : x ∈ s <;> simp [hx]
  have hOrbit := integrable_lpRightTranslate (p := p) (by
    exact ENNReal.ofReal_ne_top) μ F
  have hApply :
      J (lpComplexMeasureConvolution p μ F) =
        ∫ᵛ y, lpRightTranslate p y F ∂[
          (ContinuousLinearMap.compL ℝ ℂ (Lp ℂ p (volume : Measure ℝ)) ℂ) J ∘SL
            lpComplexSmulBilinear p; μ] := by
    simpa [lpComplexMeasureConvolution] using
      (VectorMeasure.continuousLinearMap_apply_integral
        (B := lpComplexSmulBilinear p) (C := J)
        (f := fun y : ℝ => lpRightTranslate p y F) hOrbit)
  have hCLM :
      (ContinuousLinearMap.compL ℝ ℂ (Lp ℂ p (volume : Measure ℝ)) ℂ) J ∘SL
          lpComplexSmulBilinear p =
        (ContinuousLinearMap.mul ℝ ℂ) ∘SL J := by
    ext U z
    have hInt :
        ∫ x, (z • U) x * (φ : ℝ → ℂ) x ∂volume =
          z * ∫ x, U x * (φ : ℝ → ℂ) x ∂volume := by
      calc
        _ = ∫ x, z • (U x * (φ : ℝ → ℂ) x) ∂volume := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_smul z U] with x hx
          rw [hx]
          simp [smul_eq_mul, mul_assoc]
        _ = z • ∫ x, U x * (φ : ℝ → ℂ) x ∂volume := integral_smul _ _
        _ = _ := by simp [smul_eq_mul]
    simpa [lpComplexSmulBilinear, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, J, ContinuousLinearMap.lpPairing_eq_integral,
      ContinuousLinearMap.mul_apply, mul_comm] using hInt
  rw [hCLM] at hApply
  have hComp := VectorMeasure.integral_continuousLinearMap_comp
    (B := ContinuousLinearMap.mul ℝ ℂ) (C := J)
    (f := fun y : ℝ => lpRightTranslate p y F) hOrbit
  have hTrans (y : ℝ) :
      J (lpRightTranslate p y F) = ∫ x in s, f (x-y) ∂volume := by
    change (ContinuousLinearMap.lpPairing (volume : Measure ℝ) p pstar
      (ContinuousLinearMap.mul ℝ ℂ)) (lpRightTranslate p y F) φ = _
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    have hφ : (φ : ℝ → ℂ) =ᵐ[volume] s.indicator (fun _ => (1 : ℂ)) :=
      indicatorConstLp_coeFn
    have hshiftLp := coeFn_lpRightTranslate p y F
    have hFae : (fun x : ℝ => F (x-y)) =ᵐ[volume] fun x => f (x-y) := hshift y
    calc
      _ = ∫ x, f (x-y) * s.indicator (fun _ => (1 : ℂ)) x ∂volume := by
        apply integral_congr_ae
        filter_upwards [hφ, hshiftLp, hFae] with x hx₁ hx₂ hx₃
        rw [hx₂, hx₃, hx₁]
        simp [ContinuousLinearMap.mul_apply, smul_eq_mul]
      _ = ∫ x in s, f (x-y) ∂volume := by
        rw [← integral_indicator hs]
        congr 1
        funext x
        by_cases hx : x ∈ s <;> simp [hx]
  have hVec :
      ∫ᵛ y, J (lpRightTranslate p y F) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
        ∫ᵛ y, (∫ x in s, f (x-y) ∂volume)
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
    apply VectorMeasure.integral_congr_ae
    exact ae_of_all μ.variation hTrans
  have hJ :
      J (lpComplexMeasureConvolution p μ F) =
        ∫ᵛ y, (∫ x in s, f (x-y) ∂volume)
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
    calc
      J (lpComplexMeasureConvolution p μ F) =
          ∫ᵛ y, lpRightTranslate p y F ∂[
            (ContinuousLinearMap.mul ℝ ℂ) ∘SL J; μ] := hApply
      _ = ∫ᵛ y, J (lpRightTranslate p y F)
            ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hComp.symm
      _ = ∫ᵛ y, (∫ x in s, f (x-y) ∂volume)
            ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hVec
  have hprod' : Integrable (fun z : ℝ × ℝ => f (z.1-z.2))
      (η.variation.prod μ.variation) := by
    simpa [hη, u] using hprod
  have hSwap := VectorMeasure.integral_integral_swap
    (μ := η) (ν := μ) (f := fun x y : ℝ => f (x-y))
    (B := ContinuousLinearMap.mul ℝ ℂ)
    (C := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (A := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (D := ContinuousLinearMap.mul ℝ ℂ)
    hprod' (by
      intro z w r
      simp [ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.mul_apply,
        smul_eq_mul]
      ring)
  have hOuter (g : ℝ → ℂ) :
      ∫ᵛ x, g x ∂[(ContinuousLinearMap.lsmul ℝ ℝ).flip; η] =
        ∫ x in s, g x ∂volume := by
    simpa [η] using
      (VectorMeasure.integral_toSignedMeasure
        (μ := volume.restrict s) (f := g))
  let hf' : AEStronglyMeasurable f (volume : Measure ℝ) :=
    hf.stronglyMeasurable.aestronglyMeasurable
  have hmeasMk : MeasurableSet {z : ℝ × ℝ |
      f (z.1-z.2) = hf'.mk f (z.1-z.2)} := by
    exact (hf.stronglyMeasurable.comp_measurable (by fun_prop)).measurableSet_eq_fun
      (hf'.stronglyMeasurable_mk.comp_measurable (by fun_prop))
  have hshiftMk (y : ℝ) :
      (fun x : ℝ => f (x-y)) =ᵐ[volume] (fun x => hf'.mk f (x-y)) := by
    exact (measurePreserving_sub_right (volume : Measure ℝ) y).quasiMeasurePreserving.ae
      hf'.ae_eq_mk
  have hyxMk : ∀ᵐ y ∂μ.variation, ∀ᵐ x ∂volume.restrict s,
      f (x-y) = hf'.mk f (x-y) := by
    filter_upwards [] with y
    exact ae_restrict_of_ae (hshiftMk y)
  have hxyMk := (Measure.ae_ae_comm hmeasMk).2 hyxMk
  have hprodMk : (fun z : ℝ × ℝ => f (z.1-z.2)) =ᵐ[
      (volume.restrict s).prod μ.variation]
      (fun z => hf'.mk f (z.1-z.2)) :=
    (Measure.ae_prod_iff_ae_ae hmeasMk).2 hxyMk
  have hPointAE :
      (fun x : ℝ => ∫ᵛ y, f (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =ᵐ[η.variation]
        (fun x => complexMeasureConvolution μ f hf' x) := by
    rw [hη]
    have hx : ∀ᵐ x ∂volume.restrict s,
        (fun y : ℝ => f (x-y)) =ᵐ[μ.variation]
          (fun y => hf'.mk f (x-y)) := Measure.ae_ae_of_ae_prod hprodMk
    filter_upwards [hx] with x hx
    exact VectorMeasure.integral_congr_ae hx
  have hFubini :
      ∫ᵛ y, (∫ x in s, f (x-y) ∂volume)
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
        ∫ x in s, complexMeasureConvolution μ f hf' x ∂volume := by
    calc
      ∫ᵛ y, (∫ x in s, f (x-y) ∂volume)
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
        ∫ᵛ y, (∫ᵛ x, f (x-y)
            ∂[(ContinuousLinearMap.lsmul ℝ ℝ).flip; η])
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
            apply VectorMeasure.integral_congr_ae
            exact ae_of_all μ.variation fun y => (hOuter fun x => f (x-y)).symm
      _ = ∫ᵛ x, (∫ᵛ y, f (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
            ∂[(ContinuousLinearMap.lsmul ℝ ℝ).flip; η] := hSwap.symm
      _ = ∫ᵛ x, complexMeasureConvolution μ f hf' x
            ∂[(ContinuousLinearMap.lsmul ℝ ℝ).flip; η] := by
              apply VectorMeasure.integral_congr_ae
              simpa only [hη] using hPointAE
      _ = ∫ x in s, complexMeasureConvolution μ f hf' x
            ∂volume := hOuter _
  calc
    ∫ x in s, (lpComplexMeasureConvolution p μ F) x ∂volume =
        J (lpComplexMeasureConvolution p μ F) := hleft.symm
    _ = ∫ᵛ y, (∫ x in s, f (x-y) ∂volume)
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hJ
    _ = ∫ x in s, complexMeasureConvolution μ f hf' x ∂volume := hFubini

private theorem memLp_f_representative_integrableOn
    {q : ℝ} (hq : 1 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfm : MemLp f (ENNReal.ofReal q) (volume : Measure ℝ))
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s < ∞) :
    IntegrableOn
      (complexMeasureConvolution μ f (hf.stronglyMeasurable.aestronglyMeasurable)) s volume := by
  let hf' : AEStronglyMeasurable f (volume : Measure ℝ) :=
    hf.stronglyMeasurable.aestronglyMeasurable
  letI : IsFiniteMeasure (volume.restrict s) := ⟨by simpa using hμs⟩
  letI : IsFiniteMeasure ((volume.restrict s).prod μ.variation) := inferInstance
  have hprod : Integrable
      (fun z : ℝ × ℝ => f (z.1-z.2))
      ((volume.restrict s).prod μ.variation) :=
    memLp_translation_integrable_prod hq f hf.stronglyMeasurable hfm
      μ.variation s hs hμs
  have hmeasMk : MeasurableSet {z : ℝ × ℝ |
      f (z.1-z.2) = hf'.mk f (z.1-z.2)} := by
    exact (hf.stronglyMeasurable.comp_measurable (by fun_prop)).measurableSet_eq_fun
      (hf'.stronglyMeasurable_mk.comp_measurable (by fun_prop))
  have hshiftMk (y : ℝ) :
      (fun x : ℝ => f (x-y)) =ᵐ[volume] (fun x => hf'.mk f (x-y)) := by
    exact (measurePreserving_sub_right (volume : Measure ℝ) y).quasiMeasurePreserving.ae
      hf'.ae_eq_mk
  have hyxMk : ∀ᵐ y ∂μ.variation, ∀ᵐ x ∂volume.restrict s,
      f (x-y) = hf'.mk f (x-y) := by
    filter_upwards [] with y
    exact ae_restrict_of_ae (hshiftMk y)
  have hxyMk := (Measure.ae_ae_comm hmeasMk).2 hyxMk
  have hprodMk : (fun z : ℝ × ℝ => f (z.1-z.2)) =ᵐ[
      (volume.restrict s).prod μ.variation]
      (fun z => hf'.mk f (z.1-z.2)) :=
    (Measure.ae_prod_iff_ae_ae hmeasMk).2 hxyMk
  have hprod' := hprod.congr hprodMk
  have hleft := hprod'.integral_vectorMeasure_prod_left
    (B := ContinuousLinearMap.mul ℝ ℂ)
  change Integrable
    (fun x : ℝ => ∫ᵛ y, hf'.mk f (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
    (volume.restrict s) at hleft
  change Integrable
    (complexMeasureConvolution μ f hf') (volume.restrict s)
  exact hleft

/-- Finite-exponent convolution agrees with its raw representative for every
`L^q` input with `q>1`. The local comparison uses translation invariance and
finite-set Fubini; no boundedness assumption on the input is needed. -/
theorem lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution_of_memLp
    {q : ℝ} (hq : 1 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ))
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfm : MemLp f (ENNReal.ofReal q) (volume : Measure ℝ))
    (hF : (F : ℝ → ℂ) =ᵐ[volume] f) :
    (lpComplexMeasureConvolution (ENNReal.ofReal q) μ F : ℝ → ℂ) =ᵐ[volume]
      complexMeasureConvolution μ f (hf.stronglyMeasurable.aestronglyMeasurable) := by
  apply AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq
  · intro s hs hμs
    exact integrableOn_Lp_of_measure_ne_top
      (lpComplexMeasureConvolution (ENNReal.ofReal q) μ F)
      (ENNReal.one_le_ofReal.mpr hq.le) hμs.ne
  · intro s hs hμs
    exact memLp_f_representative_integrableOn hq μ f hf hfm s hs hμs
  · intro s hs hμs
    exact lpComplexMeasureConvolution_setIntegral_eq hq μ F f hf hfm hF s hs hμs
  · exact (Lp.finStronglyMeasurable (lpComplexMeasureConvolution
      (ENNReal.ofReal q) μ F) (ENNReal.ofReal_pos.mpr (by linarith)).ne'
      ENNReal.ofReal_ne_top).aefinStronglyMeasurable
  · exact aefinStronglyMeasurable_of_aemeasurable volume
      (stronglyMeasurable_complexMeasureConvolution μ f
        (hf.stronglyMeasurable.aestronglyMeasurable)).aemeasurable

/-- For bounded measurable inputs, the general finite-exponent representative
bridge specializes to the original dense-class statement. -/
theorem lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution_of_bounded
    {q : ℝ} (hq : 1 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ))
    (f : ℝ → ℂ) (hf : Measurable f)
    (hbounded : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hF : (F : ℝ → ℂ) =ᵐ[volume] f) :
    (lpComplexMeasureConvolution (ENNReal.ofReal q) μ F : ℝ → ℂ) =ᵐ[volume]
      complexMeasureConvolution μ f (hf.stronglyMeasurable.aestronglyMeasurable) := by
  have hfm : MemLp f (ENNReal.ofReal q) (volume : Measure ℝ) := by
    apply (Lp.memLp F).congr_norm hf.stronglyMeasurable.aestronglyMeasurable
    filter_upwards [hF] with x hx
    simp [hx]
  exact lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution_of_memLp
    hq μ F f hf hfm hF

#print axioms lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution_of_memLp
#print axioms lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution_of_bounded

/-- The exact real average of the modulus at geometric scale `b^k`, written
over the undilated probability measure. -/
def initialSquareSigmaRawPositiveScale
    (σ : Measure ℝ) (b : ℝ) (k : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  ∫ y, ‖f (x - b ^ k * y)‖ ∂σ

/-- For arbitrary `L^q` data with `q>1`, the quotient-space positive
convolution map at one geometric scale agrees almost everywhere with the raw
source average. -/
theorem initialSquare_lpPositiveConvolutionMap_ae_eq_rawScale_of_memLp
    {q : ℝ} (hq : 1 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b : ℝ}
    (hb : 1 < b) (k : ℤ)
    [IsFiniteMeasure (initialSquareComplexifiedSigmaScale σ b k).variation]
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfm : MemLp f (ENNReal.ofReal q) (volume : Measure ℝ))
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℝ))
    (hF : (F : ℝ → ℂ) =ᵐ[volume] f) :
    (lpPositiveConvolutionMap (ENNReal.ofReal q) ENNReal.ofReal_ne_top
        (initialSquareComplexifiedSigmaScale σ b k) F : ℝ → ℝ) =ᵐ[volume]
      initialSquareSigmaRawPositiveScale σ b k f := by
  let p : ℝ≥0∞ := ENNReal.ofReal q
  let μ : ComplexMeasure ℝ := initialSquareComplexifiedSigmaScale σ b k
  let fAbs : ℝ → ℂ := fun x => (‖f x‖ : ℂ)
  let FAbs : Lp ℂ p (volume : Measure ℝ) :=
    (Complex.ofRealCLM.compLpL p volume) (lpComplexPointwiseNorm p F)
  letI : IsFiniteMeasure μ.variation := by
    simpa [μ] using
      (inferInstance : IsFiniteMeasure
        (initialSquareComplexifiedSigmaScale σ b k).variation)
  have hfAbs : Measurable fAbs := by
    dsimp [fAbs]
    exact Complex.continuous_ofReal.measurable.comp hf.norm
  have hnormF : (lpComplexPointwiseNorm p F : ℝ → ℝ) =ᵐ[volume]
      fun x => ‖f x‖ := by
    have h := lipschitz_complex_norm.coeFn_compLp (by simp) F
    filter_upwards [h, hF] with x hx₁ hx₂
    simpa [lpComplexPointwiseNorm] using hx₁.trans (congrArg norm hx₂)
  have hFAbs : (FAbs : ℝ → ℂ) =ᵐ[volume] fAbs := by
    have h := Complex.ofRealCLM.coeFn_compLpL (lpComplexPointwiseNorm p F)
    filter_upwards [h, hnormF] with x hx₁ hx₂
    simpa [FAbs, fAbs] using hx₁.trans (congrArg Complex.ofReal hx₂)
  have hfmAbs : MemLp fAbs p (volume : Measure ℝ) := by
    apply hfm.congr_norm hfAbs.stronglyMeasurable.aestronglyMeasurable
    filter_upwards [] with x
    simp [fAbs, Complex.norm_real, abs_of_nonneg (norm_nonneg _)]
  have hconv := lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution_of_memLp
    hq μ FAbs fAbs hfAbs hfmAbs hFAbs
  let μ₀ : SignedMeasure ℝ := σ.toSignedMeasure
  let μc : ComplexMeasure ℝ := initialSquareSigmaComplexifiedMeasure σ
  let t : ℝ := b ^ k
  have ht : t ≠ 0 := by
    dsimp [t]
    positivity
  have hmap (x : ℝ) :
      ∫ᵛ y, fAbs (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
        ∫ᵛ y, fAbs (x-t*y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ₀.toComplexMeasure 0] := by
    change ∫ᵛ y, fAbs (x-y)
        ∂[ContinuousLinearMap.mul ℝ ℂ; μc.map (fun y : ℝ => t*y)] = _
    rw [(measurableEmbedding_mulLeft₀ ht).integral_map_vectorMeasure]
    simp [μc, μ₀, initialSquareSigmaComplexifiedMeasure]
  have hreal (x : ℝ) :
      ∫ᵛ y, fAbs (x-t*y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ₀.toComplexMeasure 0] =
        ((∫ y, ‖f (x-t*y)‖ ∂σ : ℝ) : ℂ) := by
    calc
      _ = ∫ᵛ y, fAbs (x-t*y) ∂<•(σ.toSignedMeasure) :=
        initialSquareNuComplexMeasure_integral_eq μ₀ _
      _ = ∫ y, fAbs (x-t*y) ∂σ := by
        rw [VectorMeasure.integral_toSignedMeasure]
      _ = ((∫ y, ‖f (x-t*y)‖ ∂σ : ℝ) : ℂ) := by
        rw [integral_complex_ofReal]
  have hraw : (complexMeasureConvolution μ fAbs
      (hfAbs.stronglyMeasurable.aestronglyMeasurable) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ᵛ y, fAbs (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
    have hcongr := rawComplexMeasureConvolution_ae_congr μ
      (fun y => (hfAbs.stronglyMeasurable.aestronglyMeasurable).mk fAbs y)
      fAbs
      (hfAbs.stronglyMeasurable.aestronglyMeasurable.stronglyMeasurable_mk)
      hfAbs.stronglyMeasurable hfAbs.aestronglyMeasurable.ae_eq_mk.symm
    change (fun x => ∫ᵛ y,
      (hfAbs.stronglyMeasurable.aestronglyMeasurable).mk fAbs (x-y)
        ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =ᵐ[volume] _
    exact hcongr
  have hrealConv : (fun x : ℝ =>
      Complex.re ((lpComplexMeasureConvolution p μ FAbs : ℝ → ℂ) x)) =ᵐ[volume]
      initialSquareSigmaRawPositiveScale σ b k f := by
    filter_upwards [hconv, hraw] with x hxconv hxraw
    have hxval := hxconv.trans hxraw
    rw [hxval, hmap x, hreal x]
    simp [initialSquareSigmaRawPositiveScale, fAbs, t]
  have hRe := Complex.reCLM.coeFn_compLpL
    (lpComplexMeasureConvolutionCLM p ENNReal.ofReal_ne_top μ FAbs)
  have hCLM :
      (lpComplexMeasureConvolutionCLM p ENNReal.ofReal_ne_top μ FAbs :
          ℝ → ℂ) =ᵐ[volume]
        (lpComplexMeasureConvolution p μ FAbs : ℝ → ℂ) := by
    rfl
  change (Complex.reCLM.compLpL p volume
      (lpComplexMeasureConvolutionCLM p ENNReal.ofReal_ne_top μ FAbs) :
        ℝ → ℝ) =ᵐ[volume] _
  filter_upwards [hRe, hCLM, hrealConv] with x h₁ h₂ h₃
  calc
    _ = Complex.re
        ((lpComplexMeasureConvolutionCLM p ENNReal.ofReal_ne_top μ FAbs) x) := h₁
    _ = Complex.re ((lpComplexMeasureConvolution p μ FAbs) x) := by
      exact congrArg Complex.re h₂
    _ = _ := h₃

/-- The real-valued full source maximal function on a bounded measurable
input. -/
def initialSquareSigmaRawPositiveMaximal
    (σ : Measure ℝ) (b : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  (⨆ k : ℤ, ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k f x)).toReal

theorem initialSquare_layerCakeInput_memLp_two
    (g : Variation.LayerCakeInput (volume : Measure ℝ)) :
    MemLp g.1 (ENNReal.ofReal 2) (volume : Measure ℝ) := by
  rcases g.2 with ⟨hg, ⟨C, hC⟩, hfinite⟩
  let C' : ℝ := max C 0
  have hbound (x : ℝ) : ‖g.1 x‖ ≤ C' := (hC x).trans (le_max_left _ _)
  have htop : MemLp g.1 ∞ (volume : Measure ℝ) :=
    memLp_top_of_bound hg.aestronglyMeasurable C'
      (Filter.Eventually.of_forall hbound)
  exact htop.mono_exponent_of_measure_support_ne_top
    (s := {x | g.1 x ≠ 0})
    (by intro x hx; by_contra hn; exact hx hn)
    hfinite.ne (by norm_num)

private theorem measurable_initialSquareSigmaRawPositiveScale
    {σ : Measure ℝ} [SFinite σ] (b : ℝ) (k : ℤ)
    (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (initialSquareSigmaRawPositiveScale σ b k f) := by
  have hjoint : StronglyMeasurable (fun z : ℝ × ℝ =>
      ‖f (z.1 - b ^ k * z.2)‖) := by
    exact (hf.stronglyMeasurable.comp_measurable (by fun_prop)).norm
  change Measurable (fun x : ℝ => ∫ y, ‖f (x - b ^ k * y)‖ ∂σ)
  exact hjoint.integral_prod_right'.measurable

theorem measurable_initialSquareSigmaRawPositiveMaximal
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (b : ℝ)
    (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (initialSquareSigmaRawPositiveMaximal σ b f) := by
  have hscale (k : ℤ) : Measurable (fun x : ℝ =>
      ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k f x)) := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (measurable_initialSquareSigmaRawPositiveScale (σ := σ) b k f hf)
  have hs : Measurable (fun x : ℝ =>
      ⨆ k : ℤ, ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k f x)) :=
    Measurable.iSup hscale
  exact ENNReal.measurable_toReal.comp hs

theorem initialSquareSigmaRawPositiveScale_ae_congr
    {σ : Measure ℝ} [SFinite σ] (t : ℝ) {f g : ℝ → ℂ}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[volume] g) :
    (fun x : ℝ => ∫ y, ‖f (x-t*y)‖ ∂σ) =ᵐ[volume]
      (fun x => ∫ y, ‖g (x-t*y)‖ ∂σ) := by
  have hmeas : MeasurableSet {z : ℝ × ℝ | f (z.1-t*z.2) = g (z.1-t*z.2)} := by
    exact (hf.stronglyMeasurable.comp_measurable (by fun_prop)).measurableSet_eq_fun
      (hg.stronglyMeasurable.comp_measurable (by fun_prop))
  have hyx : ∀ᵐ y ∂σ, ∀ᵐ x ∂volume, f (x-t*y) = g (x-t*y) := by
    filter_upwards [] with y
    exact (measurePreserving_sub_right (volume : Measure ℝ) (t*y)).quasiMeasurePreserving.ae hfg
  have hxy : ∀ᵐ x ∂volume, ∀ᵐ y ∂σ, f (x-t*y) = g (x-t*y) :=
    (Measure.ae_ae_comm hmeas).2 hyx
  filter_upwards [hxy] with x hx
  have hnorm : (fun y : ℝ => ‖f (x-t*y)‖) =ᵐ[σ]
      fun y => ‖g (x-t*y)‖ := hx.mono fun y hy => congrArg norm hy
  exact integral_congr_ae hnorm

theorem initialSquareSigmaRawPositiveMaximalReal_ae_eq_source
    {σ : Measure ℝ} [IsProbabilityMeasure σ] (b : ℝ)
    (g : Variation.LayerCakeInput (volume : Measure ℝ))
    (F : Lp ℂ 2 (volume : Measure ℝ))
    (hF : (F : ℝ → ℂ) =ᵐ[volume] g.1) :
    initialSquareSigmaRawPositiveMaximal σ b g.1 =ᵐ[volume]
      initialSquareSigmaPositiveConvolutionMaximalReal σ b F := by
  have hterms : ∀ᵐ x ∂volume, ∀ k : ℤ,
      ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k g.1 x) =
        ENNReal.ofReal
          (∫ y, ‖F (x-y)‖ ∂Measure.map (fun y : ℝ => b ^ k * y) σ) := by
    rw [ae_all_iff]
    intro k
    have hcongr := initialSquareSigmaRawPositiveScale_ae_congr
      (σ := σ) (b ^ k) g.2.1 (Lp.stronglyMeasurable F).measurable hF.symm
    have hchange (x : ℝ) :
        ∫ y, ‖F (x-y)‖ ∂Measure.map (fun y : ℝ => b ^ k * y) σ =
          initialSquareSigmaRawPositiveScale σ b k (fun y => F y) x := by
      exact integral_map_of_stronglyMeasurable (by fun_prop)
        (((Lp.stronglyMeasurable F).comp_measurable (by fun_prop)).norm)
    filter_upwards [hcongr] with x hx
    exact congrArg ENNReal.ofReal (by
      simpa [initialSquareSigmaRawPositiveScale] using hx.trans (hchange x).symm)
  have hsup :
      (fun x : ℝ => ⨆ k : ℤ,
        ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k g.1 x)) =ᵐ[volume]
      initialSquareSigmaPositiveConvolutionMaximal σ b F := by
    change (fun x : ℝ => ⨆ k : ℤ,
        ENNReal.ofReal (initialSquareSigmaRawPositiveScale σ b k g.1 x)) =ᵐ[volume]
      fun x => ⨆ k : ℤ,
        ENNReal.ofReal (∫ y, ‖F (x-y)‖
          ∂Measure.map (fun y : ℝ => b ^ k * y) σ)
    filter_upwards [hterms] with x hx
    exact iSup_congr hx
  filter_upwards [hsup] with x hx
  exact congrArg ENNReal.toReal hx

#print axioms initialSquare_layerCakeInput_memLp_two
#print axioms measurable_initialSquareSigmaRawPositiveMaximal
#print axioms initialSquareSigmaRawPositiveMaximalReal_ae_eq_source

end

end FractionalPrimes.Literature.JSW

end
