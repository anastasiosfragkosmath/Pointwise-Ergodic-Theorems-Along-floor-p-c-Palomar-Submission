module

public import FractionalPrimes.Literature.JSW.ComplexMeasureYoung
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

private theorem rep_sq_integrable_prod
    (F : Lp ℂ 2 (volume : Measure ℝ))
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s < ∞) :
    Integrable (fun z : ℝ × ℝ => ‖F (z.1 - z.2)‖ ^ 2)
      ((volume.restrict s).prod μ.variation) := by
  let u : ℝ × ℝ → ℝ := fun z => ‖F (z.2 - z.1)‖ ^ 2
  have hu : StronglyMeasurable u := by
    dsimp [u]
    exact ((Lp.stronglyMeasurable F).norm).pow 2 |>.comp_measurable (by fun_prop)
  have hF2 : Integrable (fun x : ℝ => ‖F x‖ ^ 2) (volume : Measure ℝ) :=
    (Lp.memLp F).integrable_norm_pow (by norm_num)
  have hy (y : ℝ) : Integrable (fun x : ℝ => ‖F (x - y)‖ ^ 2) (volume : Measure ℝ) := by
    have hsm : AEStronglyMeasurable (fun x : ℝ => ‖F x‖ ^ 2) (volume : Measure ℝ) :=
      (((Lp.stronglyMeasurable F).norm).pow 2).aestronglyMeasurable
    have heq := (measurePreserving_sub_right (volume : Measure ℝ) y).integrable_comp hsm
    change Integrable ((fun t : ℝ => ‖F t‖ ^ 2) ∘ fun x : ℝ => x - y) volume
    exact heq.mpr hF2
  have hy' (y : ℝ) : Integrable (fun x : ℝ => u (y, x)) (volume.restrict s) := by
    have h := (hy y).mono_measure (μ := volume.restrict s) (ν := volume) Measure.restrict_le_self
    simpa [u] using h
  have hind_sm : StronglyMeasurable
      (fun y : ℝ => ∫ x, u (y, x) ∂(volume.restrict s)) :=
    hu.integral_prod_right
  have hC : ∀ y : ℝ, ‖∫ x, u (y, x) ∂(volume.restrict s)‖ ≤
      ∫ x, ‖F x‖ ^ 2 ∂(volume : Measure ℝ) := by
    intro y
    rw [Real.norm_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
    calc
      ∫ x, u (y, x) ∂(volume.restrict s) ≤
          ∫ x, ‖F (x - y)‖ ^ 2 ∂(volume : Measure ℝ) := by
        apply integral_mono_measure Measure.restrict_le_self
        · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
        · exact hy y
      _ = ∫ x, ‖F x‖ ^ 2 ∂(volume : Measure ℝ) := by
        simpa [u] using
          (measurePreserving_sub_right (volume : Measure ℝ) y).integral_comp
            (measurableEmbedding_subRight y) (fun x => ‖F x‖ ^ 2)
  have houter : Integrable
      (fun y : ℝ => ∫ x, ‖F (x - y)‖ ^ 2 ∂(volume.restrict s)) μ.variation := by
    apply Integrable.of_bound hind_sm.aestronglyMeasurable _
    filter_upwards [] with y
    simpa [u] using hC y
  have hu_prod : Integrable u (μ.variation.prod (volume.restrict s)) := by
    apply (integrable_prod_iff hu.aestronglyMeasurable).2
    refine ⟨?_, ?_⟩
    · filter_upwards [] with y
      exact hy' y
    · simpa [u] using houter
  simpa [u, Function.comp_def] using hu_prod.swap


private theorem rep_translation_integrable_prod
    (F : Lp ℂ 2 (volume : Measure ℝ))
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s < ∞) :
    Integrable (fun z : ℝ × ℝ => F (z.1 - z.2))
      ((volume.restrict s).prod μ.variation) := by
  letI : IsFiniteMeasure (volume.restrict s) := ⟨by simpa using hμs⟩
  letI : IsFiniteMeasure ((volume.restrict s).prod μ.variation) := inferInstance
  have hsm : AEStronglyMeasurable (fun z : ℝ × ℝ => F (z.1 - z.2))
      ((volume.restrict s).prod μ.variation) := by
    exact ((Lp.stronglyMeasurable F).comp_measurable (by fun_prop)).aestronglyMeasurable
  have hsq := rep_sq_integrable_prod F μ s hs hμs
  have hmem2 : MemLp (fun z : ℝ × ℝ => F (z.1 - z.2)) 2
      ((volume.restrict s).prod μ.variation) :=
    (memLp_two_iff_integrable_sq_norm hsm).2 hsq
  exact memLp_one_iff_integrable.mp (hmem2.mono_exponent (by norm_num))

private theorem rep_translation_mk_ae_prod
    (F : Lp ℂ 2 (volume : Measure ℝ))
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (s : Set ℝ) (hs : MeasurableSet s) :
    (fun z : ℝ × ℝ => F (z.1 - z.2)) =ᵐ[(volume.restrict s).prod μ.variation]
      (fun z => (Lp.aestronglyMeasurable F).mk (fun x : ℝ => F x) (z.1 - z.2)) := by
  let hf : AEStronglyMeasurable (fun x : ℝ => F x) (volume : Measure ℝ) :=
    Lp.aestronglyMeasurable F
  have hmeas : MeasurableSet {z : ℝ × ℝ |
      F (z.1 - z.2) = hf.mk (fun x : ℝ => F x) (z.1 - z.2)} := by
    exact ((Lp.stronglyMeasurable F).comp_measurable (by fun_prop)).measurableSet_eq_fun
      (hf.stronglyMeasurable_mk.comp_measurable (by fun_prop))
  have hshift (y : ℝ) :
      (fun x : ℝ => F (x-y)) =ᵐ[volume]
        (fun x => hf.mk (fun x : ℝ => F x) (x-y)) := by
    exact (measurePreserving_sub_right (volume : Measure ℝ) y).quasiMeasurePreserving.ae
      hf.ae_eq_mk
  have hyx : ∀ᵐ y ∂μ.variation, ∀ᵐ x ∂volume.restrict s,
      F (x-y) = hf.mk (fun x : ℝ => F x) (x-y) := by
    filter_upwards [] with y
    exact ae_restrict_of_ae (hshift y)
  have hxy := (Measure.ae_ae_comm hmeas).2 hyx
  have hprod := (Measure.ae_prod_iff_ae_ae hmeas).2 hxy
  filter_upwards [hprod] with z hz
  exact hz

private theorem rep_mk_translation_integrable_prod
    (F : Lp ℂ 2 (volume : Measure ℝ))
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s < ∞) :
    Integrable
      (fun z : ℝ × ℝ => (Lp.aestronglyMeasurable F).mk (fun x : ℝ => F x) (z.1-z.2))
      ((volume.restrict s).prod μ.variation) := by
  exact (rep_translation_integrable_prod F μ s hs hμs).congr
    (rep_translation_mk_ae_prod F μ s hs)

set_option maxHeartbeats 800000 in
private theorem rep_local_set_integral_eq
    (F : Lp ℂ 2 (volume : Measure ℝ))
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s < ∞) :
    ∫ x in s, (lpComplexMeasureConvolution 2 μ F) x ∂(volume : Measure ℝ) =
      ∫ x in s,
        complexMeasureConvolution μ (fun x : ℝ => F x)
          (Lp.aestronglyMeasurable F) x ∂(volume : Measure ℝ) := by
  let f : ℝ → ℂ := fun x => F x
  let hf : AEStronglyMeasurable f (volume : Measure ℝ) := Lp.aestronglyMeasurable F
  let φ : Lp ℂ 2 (volume : Measure ℝ) := indicatorConstLp 2 hs hμs.ne (1 : ℂ)
  let J : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] ℂ :=
    (innerSL ℂ φ).restrictScalars ℝ
  letI : IsFiniteMeasure (volume.restrict s) := ⟨by simpa using hμs⟩
  let η : VectorMeasure ℝ ℝ :=
    (1 : ℝ) • (volume.restrict s).toSignedMeasure
  have hη : η.variation = volume.restrict s := by
    simp [η, VectorMeasure.variation_smul]
  letI : IsFiniteMeasure η.variation := hη ▸ (inferInstance : IsFiniteMeasure (volume.restrict s))
  have hprodF := rep_translation_integrable_prod F μ s hs hμs
  have hprodMk := rep_mk_translation_integrable_prod F μ s hs hμs
  have hLpInt : IntegrableOn (lpComplexMeasureConvolution 2 μ F) s volume :=
    integrableOn_Lp_of_measure_ne_top (lpComplexMeasureConvolution 2 μ F)
      (by norm_num) hμs.ne
  have hpointInt : IntegrableOn
      (complexMeasureConvolution μ f hf) s volume := by
    change Integrable (complexMeasureConvolution μ f hf) (volume.restrict s)
    have h := hprodMk.integral_vectorMeasure_prod_left
      (B := ContinuousLinearMap.mul ℝ ℂ)
    change Integrable
      (fun x : ℝ => ∫ᵛ y, hf.mk f (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
      (volume.restrict s) at h
    exact h
  have hleft :
      ∫ x in s, (lpComplexMeasureConvolution 2 μ F) x ∂(volume : Measure ℝ) =
        J (lpComplexMeasureConvolution 2 μ F) := by
    simpa [J] using
      (L2.inner_indicatorConstLp_one hs hμs.ne (lpComplexMeasureConvolution 2 μ F)).symm
  have hOrbit := integrable_lpRightTranslate (p := 2) (by norm_num) μ F
  have hApply :
      J (lpComplexMeasureConvolution 2 μ F) =
        ∫ᵛ y, lpRightTranslate 2 y F ∂[
          (ContinuousLinearMap.compL ℝ ℂ (Lp ℂ 2 (volume : Measure ℝ)) ℂ) J ∘SL
            lpComplexSmulBilinear 2; μ] := by
    simpa [lpComplexMeasureConvolution] using
      (VectorMeasure.continuousLinearMap_apply_integral
        (B := lpComplexSmulBilinear 2) (C := J)
        (f := fun y : ℝ => lpRightTranslate 2 y F) hOrbit)
  have hCLM :
      (ContinuousLinearMap.compL ℝ ℂ (Lp ℂ 2 (volume : Measure ℝ)) ℂ) J ∘SL
          lpComplexSmulBilinear 2 =
        (ContinuousLinearMap.mul ℝ ℂ) ∘SL J := by
    ext U z
    simp [lpComplexSmulBilinear, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, innerSL_apply_apply, J, mul_comm]
  rw [hCLM] at hApply
  have hComp := VectorMeasure.integral_continuousLinearMap_comp
    (B := ContinuousLinearMap.mul ℝ ℂ) (C := J)
    (f := fun y : ℝ => lpRightTranslate 2 y F) hOrbit
  have hTrans (y : ℝ) :
      J (lpRightTranslate 2 y F) = ∫ x in s, F (x-y) ∂(volume : Measure ℝ) := by
    calc
      J (lpRightTranslate 2 y F) =
          ∫ x in s, (lpRightTranslate 2 y F) x ∂(volume : Measure ℝ) := by
        simpa [J] using
          (L2.inner_indicatorConstLp_one hs hμs.ne (lpRightTranslate 2 y F))
      _ = ∫ x in s, F (x-y) ∂(volume : Measure ℝ) := by
        apply integral_congr_ae
        exact ae_restrict_of_ae (coeFn_lpRightTranslate 2 y F)
  have hVec :
      ∫ᵛ y, J (lpRightTranslate 2 y F) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
        ∫ᵛ y, (∫ x in s, F (x-y) ∂(volume : Measure ℝ))
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
    apply VectorMeasure.integral_congr_ae
    exact ae_of_all μ.variation hTrans
  have hJ :
      J (lpComplexMeasureConvolution 2 μ F) =
        ∫ᵛ y, (∫ x in s, F (x-y) ∂(volume : Measure ℝ))
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
    calc
      J (lpComplexMeasureConvolution 2 μ F) =
          ∫ᵛ y, lpRightTranslate 2 y F ∂[
            (ContinuousLinearMap.mul ℝ ℂ) ∘SL J; μ] := hApply
      _ = ∫ᵛ y, J (lpRightTranslate 2 y F)
            ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hComp.symm
      _ = ∫ᵛ y, (∫ x in s, F (x-y) ∂(volume : Measure ℝ))
            ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hVec
  have hFubini :
      ∫ᵛ y, (∫ x in s, F (x-y) ∂(volume : Measure ℝ))
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
        ∫ x in s, complexMeasureConvolution μ f hf x ∂(volume : Measure ℝ) := by
    have hprod' : Integrable (fun z : ℝ × ℝ => F (z.1-z.2))
        (η.variation.prod μ.variation) := by
      simpa [hη] using hprodF
    have hSwap := VectorMeasure.integral_integral_swap
      (μ := η) (ν := μ) (f := fun x y : ℝ => F (x-y))
      (B := ContinuousLinearMap.mul ℝ ℂ)
      (C := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
      (A := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
      (D := ContinuousLinearMap.mul ℝ ℂ)
      hprod' (by
        intro z w r
        simp [ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.mul_apply,
          smul_eq_mul]
        ring)
    have hSwap' :
        ∫ᵛ x, (∫ᵛ y, F (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
            ∂[(ContinuousLinearMap.lsmul ℝ ℝ).flip; η] =
          ∫ᵛ y, (∫ᵛ x, F (x-y)
            ∂[(ContinuousLinearMap.lsmul ℝ ℝ).flip; η])
            ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
      exact hSwap
    have hOuter (g : ℝ → ℂ) :
        ∫ᵛ x, g x ∂[(ContinuousLinearMap.lsmul ℝ ℝ).flip; η] =
          ∫ x in s, g x ∂(volume : Measure ℝ) := by
      simpa [η] using
        (VectorMeasure.integral_toSignedMeasure
          (μ := volume.restrict s) (f := g))
    have hRepAE := rep_translation_mk_ae_prod F μ s hs
    have hxRep : ∀ᵐ x ∂volume.restrict s,
        (fun y : ℝ => F (x-y)) =ᵐ[μ.variation]
          (fun y => hf.mk f (x-y)) :=
      Measure.ae_ae_of_ae_prod hRepAE
    have hPointAE :
        (fun x : ℝ => ∫ᵛ y, F (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =ᵐ[η.variation]
          complexMeasureConvolution μ f hf := by
      rw [hη]
      filter_upwards [hxRep] with x hx
      exact VectorMeasure.integral_congr_ae hx
    calc
      ∫ᵛ y, (∫ x in s, F (x-y) ∂(volume : Measure ℝ))
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
        ∫ᵛ y, (∫ᵛ x, F (x-y)
            ∂[(ContinuousLinearMap.lsmul ℝ ℝ).flip; η])
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
            apply VectorMeasure.integral_congr_ae
            exact ae_of_all μ.variation (fun y => (hOuter fun x => F (x-y)).symm)
      _ = ∫ᵛ x, (∫ᵛ y, F (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
            ∂[(ContinuousLinearMap.lsmul ℝ ℝ).flip; η] := hSwap'.symm
      _ = ∫ᵛ x, complexMeasureConvolution μ f hf x
            ∂[(ContinuousLinearMap.lsmul ℝ ℝ).flip; η] := by
              apply VectorMeasure.integral_congr_ae
              exact hPointAE
      _ = ∫ x in s, complexMeasureConvolution μ f hf x
            ∂(volume : Measure ℝ) := hOuter _
  calc
    ∫ x in s, (lpComplexMeasureConvolution 2 μ F) x ∂(volume : Measure ℝ) =
        J (lpComplexMeasureConvolution 2 μ F) := hleft
    _ = ∫ᵛ y, (∫ x in s, F (x-y) ∂(volume : Measure ℝ))
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hJ
    _ = ∫ x in s, complexMeasureConvolution μ f hf x ∂(volume : Measure ℝ) := hFubini

theorem lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    (lpComplexMeasureConvolution 2 μ F : ℝ → ℂ) =ᵐ[volume]
      complexMeasureConvolution μ (fun x : ℝ => F x) (Lp.aestronglyMeasurable F) := by
  apply AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq
  · intro s hs hμs
    exact integrableOn_Lp_of_measure_ne_top (lpComplexMeasureConvolution 2 μ F)
      (by norm_num) hμs.ne
  · intro s hs hμs
    change Integrable
      (complexMeasureConvolution μ (fun x : ℝ => F x)
        (Lp.aestronglyMeasurable F)) (volume.restrict s)
    have h := rep_mk_translation_integrable_prod F μ s hs hμs
    have hi := h.integral_vectorMeasure_prod_left (B := ContinuousLinearMap.mul ℝ ℂ)
    change Integrable
      (fun x : ℝ => ∫ᵛ y, (Lp.aestronglyMeasurable F).mk
        (fun x : ℝ => F x) (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
      (volume.restrict s) at hi
    exact hi
  · intro s hs hμs
    exact rep_local_set_integral_eq F μ s hs hμs
  · exact (Lp.finStronglyMeasurable (lpComplexMeasureConvolution 2 μ F)
      (by norm_num) (by norm_num)).aefinStronglyMeasurable
  · exact aefinStronglyMeasurable_of_aemeasurable volume
      (stronglyMeasurable_complexMeasureConvolution μ
        (fun x : ℝ => F x) (Lp.aestronglyMeasurable F)).aemeasurable

private theorem complexMeasureConvolution_ae_eq_raw_integral_on
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ 2 (volume : Measure ℝ)) (s : Set ℝ) (hs : MeasurableSet s) :
    (fun x : ℝ => complexMeasureConvolution μ (fun y : ℝ => F y)
        (Lp.aestronglyMeasurable F) x) =ᵐ[volume.restrict s]
      (fun x : ℝ => ∫ᵛ y, F (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) := by
  have hrep := rep_translation_mk_ae_prod F μ s hs
  have hxRep : ∀ᵐ x ∂volume.restrict s,
      (fun y : ℝ => F (x-y)) =ᵐ[μ.variation]
        (fun y => (Lp.aestronglyMeasurable F).mk
          (fun z : ℝ => F z) (x-y)) :=
    Measure.ae_ae_of_ae_prod hrep
  filter_upwards [hxRep] with x hx
  exact (VectorMeasure.integral_congr_ae hx).symm

/-- For an `L²` representative, the pointwise complex convolution agrees
almost everywhere with the vector integral using that representative before
the canonical almost-everywhere-measurable lift is applied. -/
theorem complexMeasureConvolution_ae_eq_raw_integral
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun x : ℝ => complexMeasureConvolution μ (fun y : ℝ => F y)
        (Lp.aestronglyMeasurable F) x) =ᵐ[volume]
      (fun x : ℝ => ∫ᵛ y, F (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) := by
  have hlocal (n : ℕ) : ∀ᵐ x ∂volume,
      x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) →
        complexMeasureConvolution μ (fun y : ℝ => F y)
          (Lp.aestronglyMeasurable F) x =
            ∫ᵛ y, F (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
    exact (ae_restrict_iff' (measurableSet_Icc :
      MeasurableSet (Set.Icc (-(n : ℝ)) (n : ℝ)))).1
      (complexMeasureConvolution_ae_eq_raw_integral_on μ F _ measurableSet_Icc)
  have hall := ae_all_iff.mpr hlocal
  filter_upwards [hall] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  have hxIcc : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) := by
    rw [Set.mem_Icc]
    have h := abs_lt.mp hn
    exact ⟨by linarith, by linarith⟩
  exact hx n hxIcc

/-- Raw vector-measure convolutions agree almost everywhere when their inputs
agree almost everywhere with respect to Lebesgue measure. -/
theorem rawComplexMeasureConvolution_ae_congr
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (f g : ℝ → ℂ) (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hfg : f =ᵐ[volume] g) :
    (fun x : ℝ => ∫ᵛ y, f (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =ᵐ[volume]
      (fun x : ℝ => ∫ᵛ y, g (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) := by
  have hmeas : MeasurableSet {z : ℝ × ℝ | f (z.1-z.2) = g (z.1-z.2)} := by
    exact (hf.comp_measurable (by fun_prop)).measurableSet_eq_fun
      (hg.comp_measurable (by fun_prop))
  have hyx : ∀ᵐ y ∂μ.variation, ∀ᵐ x ∂volume,
      f (x-y) = g (x-y) := by
    filter_upwards [] with y
    exact (measurePreserving_sub_right (volume : Measure ℝ) y).quasiMeasurePreserving.ae hfg
  have hxy : ∀ᵐ x ∂volume, ∀ᵐ y ∂μ.variation,
      f (x-y) = g (x-y) := (Measure.ae_ae_comm hmeas).2 hyx
  filter_upwards [hxy] with x hx
  exact VectorMeasure.integral_congr_ae hx

#print axioms complexMeasureConvolution_ae_eq_raw_integral
#print axioms rawComplexMeasureConvolution_ae_congr

end FractionalPrimes.Literature.JSW
