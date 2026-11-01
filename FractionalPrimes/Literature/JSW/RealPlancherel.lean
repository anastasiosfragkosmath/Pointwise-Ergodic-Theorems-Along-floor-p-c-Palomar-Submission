module

public import FractionalPrimes.Literature.JSW.FiniteVectorDuality
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Real-line Plancherel and bounded `L²` multipliers

This file begins the exact implementation of blueprint lemma
`lj:plancherel`, using Mathlib's completed `L²` Fourier transform rather than
rebuilding its Schwartz-density construction.
-/

@[expose] public section

open MeasureTheory FourierTransform SchwartzMap
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The real-line Fourier transform as a surjective linear isometry of
complex `L²`. -/
def realFourierTransformL2 :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) :=
  MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

theorem realFourierTransformL2_surjective :
    Function.Surjective realFourierTransformL2 :=
  realFourierTransformL2.surjective

@[simp]
theorem norm_realFourierTransformL2
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖realFourierTransformL2 F‖ = ‖F‖ :=
  realFourierTransformL2.norm_map F

/-- Pointwise multiplication by an `L∞` multiplier, acting on `L²`. -/
def realLpMultiplier (M : Lp ℂ ∞ (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 M

theorem coeFn_realLpMultiplier
    (M : Lp ℂ ∞ (volume : Measure ℝ))
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    realLpMultiplier M F =ᵐ[(volume : Measure ℝ)]
      fun ξ => M ξ * F ξ := by
  exact (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder M F

theorem norm_realLpMultiplier_le
    (M : Lp ℂ ∞ (volume : Measure ℝ)) :
    ‖realLpMultiplier M‖ ≤ ‖M‖ := by
  change ‖(ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 M‖ ≤ ‖M‖
  calc
    _ ≤ ‖(ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2‖ * ‖M‖ :=
      (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 |>.le_opNorm M
    _ ≤ ‖ContinuousLinearMap.mul ℂ ℂ‖ * ‖M‖ := by
      gcongr
      exact ContinuousLinearMap.norm_holderL_le _
    _ ≤ 1 * ‖M‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℂ ℂ
    _ = ‖M‖ := one_mul _

/-- The `L²` Fourier multiplier `F ↦ 𝓕⁻(M · 𝓕F)`. -/
def realFourierMultiplier (M : Lp ℂ ∞ (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) :=
  realFourierTransformL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((realLpMultiplier M).comp
      realFourierTransformL2.toContinuousLinearEquiv.toContinuousLinearMap)

/-- A bounded measurable multiplier has `L²` operator norm at most its
essential-supremum norm. -/
theorem norm_realFourierMultiplier_le
    (M : Lp ℂ ∞ (volume : Measure ℝ)) :
    ‖realFourierMultiplier M‖ ≤ ‖M‖ := by
  calc
    ‖realFourierMultiplier M‖ ≤
        ‖realFourierTransformL2.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (‖realLpMultiplier M‖ *
            ‖realFourierTransformL2.toContinuousLinearEquiv.toContinuousLinearMap‖) := by
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans <| by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖M‖ * 1) := by
      gcongr
      · change ‖realFourierTransformL2.symm.toLinearIsometry.toContinuousLinearMap‖ ≤ 1
        exact realFourierTransformL2.symm.toLinearIsometry.norm_toContinuousLinearMap_le
      · exact norm_realLpMultiplier_le M
      · change ‖realFourierTransformL2.toLinearIsometry.toContinuousLinearMap‖ ≤ 1
        exact realFourierTransformL2.toLinearIsometry.norm_toContinuousLinearMap_le
    _ = ‖M‖ := by ring

/-- The Fourier phase corresponding to right translation by `y`. -/
def fourierTranslationPhase (y ξ : ℝ) : ℂ :=
  (Real.fourierChar (-(y * ξ)) : ℂ)

theorem continuous_fourierTranslationPhase (y : ℝ) :
    Continuous (fourierTranslationPhase y) := by
  exact continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp
      (continuous_const.mul continuous_id).neg)

/-- The unit-modulus translation phase as an `L∞` multiplier. -/
def fourierTranslationPhaseLpTop (y : ℝ) :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_top_of_bound
    (continuous_fourierTranslationPhase y).aestronglyMeasurable 1
    (ae_of_all volume fun ξ => by simp [fourierTranslationPhase])).toLp
      (fourierTranslationPhase y)

theorem coeFn_fourierTranslationPhaseLpTop (y : ℝ) :
    fourierTranslationPhaseLpTop y =ᵐ[(volume : Measure ℝ)]
      fourierTranslationPhase y := by
  exact MemLp.coeFn_toLp _

set_option maxHeartbeats 800000 in
/-- Right translation of a Schwartz function agrees with translation of its
`L²` class. -/
theorem lpRightTranslate_schwartz (f : 𝓢(ℝ, ℂ)) (y : ℝ) :
    lpRightTranslate 2 y (f.toLp 2) =
      (f.compSubConstCLM ℂ y).toLp 2 := by
  apply Lp.ext
  have hfcoe : ∀ᵐ z ∂(volume : Measure ℝ),
      (f.toLp 2 : ℝ → ℂ) z = f z :=
    SchwartzMap.coeFn_toLp f 2 volume
  have hfshift : ∀ᵐ x ∂(volume : Measure ℝ),
      (f.toLp 2 : ℝ → ℂ) (x - y) = f (x - y) :=
    (measurePreserving_sub_right volume y).quasiMeasurePreserving.ae hfcoe
  filter_upwards [coeFn_lpRightTranslate 2 y (f.toLp 2), hfshift,
    SchwartzMap.coeFn_toLp (f.compSubConstCLM ℂ y) 2] with x hx₁ hxshift hx₂
  calc
    (lpRightTranslate 2 y (f.toLp 2) : ℝ → ℂ) x =
        (f.toLp 2 : ℝ → ℂ) (x - y) := hx₁
    _ = f (x - y) := hxshift
    _ = (f.compSubConstCLM ℂ y) x := rfl
    _ = ((f.compSubConstCLM ℂ y).toLp 2 : ℝ → ℂ) x := hx₂.symm

theorem fourier_schwartz_rightTranslate_pointwise
    (f : 𝓢(ℝ, ℂ)) (y ξ : ℝ) :
    (𝓕 (f.compSubConstCLM ℂ y)) ξ =
      fourierTranslationPhase y ξ * (𝓕 f) ξ := by
  have h := congrFun
    (Fourier.fourierIntegral_comp_add_right Real.fourierChar volume
      (fun x : ℝ => f x) (-y)) ξ
  change (𝓕 ((f.compSubConstCLM ℂ y : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) ξ =
    fourierTranslationPhase y ξ * (𝓕 (f : ℝ → ℂ)) ξ
  rw [Real.fourier_eq, Real.fourier_eq]
  simpa [Fourier.fourierIntegral_def, Real.inner_apply,
    fourierTranslationPhase, Function.comp_def, Circle.smul_def, mul_comm,
    sub_eq_add_neg] using h

theorem fourier_lpRightTranslate_schwartz
    (f : 𝓢(ℝ, ℂ)) (y : ℝ) :
    realFourierTransformL2 (lpRightTranslate 2 y (f.toLp 2)) =
      realLpMultiplier (fourierTranslationPhaseLpTop y)
        (realFourierTransformL2 (f.toLp 2)) := by
  rw [lpRightTranslate_schwartz]
  change 𝓕 ((f.compSubConstCLM ℂ y).toLp 2) =
    realLpMultiplier (fourierTranslationPhaseLpTop y) (𝓕 (f.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  let G : Lp ℂ 2 (volume : Measure ℝ) := (𝓕 f).toLp 2
  change ((𝓕 (f.compSubConstCLM ℂ y) : 𝓢(ℝ, ℂ)).toLp 2) =
    realLpMultiplier (fourierTranslationPhaseLpTop y) G
  have hG : (G : ℝ → ℂ) =ᵐ[volume]
      ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    simpa [G] using SchwartzMap.coeFn_toLp (𝓕 f) 2
  apply Lp.ext
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (f.compSubConstCLM ℂ y)) 2,
    coeFn_realLpMultiplier (fourierTranslationPhaseLpTop y) G,
    coeFn_fourierTranslationPhaseLpTop y, hG] with
      ξ hleft hmul hphase hfourier
  calc
    (((𝓕 (f.compSubConstCLM ℂ y)).toLp 2 :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ =
        (𝓕 (f.compSubConstCLM ℂ y)) ξ := hleft
    _ = fourierTranslationPhase y ξ * (𝓕 f) ξ :=
      fourier_schwartz_rightTranslate_pointwise f y ξ
    _ = (fourierTranslationPhaseLpTop y : ℝ → ℂ) ξ * (𝓕 f) ξ :=
      congrArg (fun z : ℂ => z * (𝓕 f) ξ) hphase.symm
    _ = (fourierTranslationPhaseLpTop y : ℝ → ℂ) ξ *
        (G : ℝ → ℂ) ξ := by
      exact congrArg
        (fun z : ℂ => (fourierTranslationPhaseLpTop y : ℝ → ℂ) ξ * z)
        hfourier.symm
    _ = (realLpMultiplier (fourierTranslationPhaseLpTop y) G : ℝ → ℂ) ξ :=
      hmul.symm

/-- Fourier transformation converts every `L²` right translation into
multiplication by the exact unit-modulus phase. -/
theorem fourier_lpRightTranslate
    (F : Lp ℂ 2 (volume : Measure ℝ)) (y : ℝ) :
    realFourierTransformL2 (lpRightTranslate 2 y F) =
      realLpMultiplier (fourierTranslationPhaseLpTop y)
        (realFourierTransformL2 F) := by
  let A : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) :=
    realFourierTransformL2.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x - y)
        (measurePreserving_sub_right volume y)).toContinuousLinearMap
  let B : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) :=
    (realLpMultiplier (fourierTranslationPhaseLpTop y)).comp
      realFourierTransformL2.toContinuousLinearEquiv.toContinuousLinearMap
  change A F = B F
  refine DenseRange.induction_on (p := fun Z => A Z = B Z)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
      (p := 2) ENNReal.ofNat_ne_top) F
    (isClosed_eq A.continuous B.continuous) ?_
  intro f
  change realFourierTransformL2 (lpRightTranslate 2 y (f.toLp 2)) =
    realLpMultiplier (fourierTranslationPhaseLpTop y)
      (realFourierTransformL2 (f.toLp 2))
  exact fourier_lpRightTranslate_schwartz f y

/-- The real-linear form of the complex-linear `L²` Fourier transform. -/
def realFourierTransformL2RealCLM :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp ℂ 2 (volume : Measure ℝ) :=
  realFourierTransformL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ

theorem realFourierTransformL2RealCLM_smul
    (F : Lp ℂ 2 (volume : Measure ℝ)) (z : ℂ) :
    realFourierTransformL2RealCLM (z • F) =
      z • realFourierTransformL2RealCLM F := by
  change realFourierTransformL2 (z • F) = z • realFourierTransformL2 F
  exact realFourierTransformL2.map_smul z F

/-- The completed Fourier transform commutes with the finite-complex-measure
integral defining convolution. -/
theorem fourier_lpComplexMeasureConvolution_integral
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    realFourierTransformL2 (lpComplexMeasureConvolution 2 μ F) =
      ∫ᵛ y, realFourierTransformL2 (lpRightTranslate 2 y F)
        ∂[lpComplexSmulBilinear 2; μ] := by
  change realFourierTransformL2RealCLM
      (∫ᵛ y, lpRightTranslate 2 y F ∂[lpComplexSmulBilinear 2; μ]) = _
  rw [VectorMeasure.continuousLinearMap_apply_integral
    (integrable_lpRightTranslate (p := 2) (by norm_num) μ F)]
  have hmaps :
      ((ContinuousLinearMap.compL ℝ ℂ
          (Lp ℂ 2 (volume : Measure ℝ))
          (Lp ℂ 2 (volume : Measure ℝ))) realFourierTransformL2RealCLM ∘L
        lpComplexSmulBilinear 2) =
      (lpComplexSmulBilinear 2 ∘L realFourierTransformL2RealCLM) := by
    apply ContinuousLinearMap.ext
    intro V
    apply ContinuousLinearMap.ext
    intro z
    exact realFourierTransformL2RealCLM_smul V z
  rw [hmaps]
  rw [← VectorMeasure.integral_continuousLinearMap_comp
    (integrable_lpRightTranslate (p := 2) (by norm_num) μ F)]
  rfl

/-- Fourier--Stieltjes transform of a finite complex measure, with the exact
phase used by `jswFourier`. -/
def complexMeasureFourier (μ : ComplexMeasure ℝ) (ξ : ℝ) : ℂ :=
  ∫ᵛ y, (Real.fourierChar (-(y * ξ)) : ℂ)
    ∂[ContinuousLinearMap.mul ℝ ℂ; μ]

theorem stronglyMeasurable_complexMeasureFourier
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] :
    StronglyMeasurable (complexMeasureFourier μ) := by
  have hjoint : StronglyMeasurable
      (fun z : ℝ × ℝ => (Real.fourierChar (-(z.2 * z.1)) : ℂ)) :=
    (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp
        ((continuous_snd.mul continuous_fst).neg))).stronglyMeasurable
  change StronglyMeasurable
    (fun ξ : ℝ => ∫ᵛ y, (Real.fourierChar (-(y * ξ)) : ℂ)
      ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
  exact hjoint.integral_vectorMeasure_prod_right'
    (B := ContinuousLinearMap.mul ℝ ℂ) (ν := μ)

theorem norm_complexMeasureFourier_le
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] (ξ : ℝ) :
    ‖complexMeasureFourier μ ξ‖ ≤ μ.variation.real Set.univ := by
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ) (C := 1)
    (f := fun y : ℝ => (Real.fourierChar (-(y * ξ)) : ℂ))
    (ae_of_all μ.variation fun y => by simp)
  calc
    ‖complexMeasureFourier μ ξ‖ ≤
        1 * ‖ContinuousLinearMap.mul ℝ ℂ‖ *
          μ.variation.real Set.univ := by
      simpa [complexMeasureFourier] using h
    _ ≤ 1 * 1 * μ.variation.real Set.univ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℝ ℂ
    _ = μ.variation.real Set.univ := by ring

/-- The Fourier--Stieltjes transform as an `L∞` multiplier. -/
def complexMeasureFourierLpTop
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_top_of_bound
    (stronglyMeasurable_complexMeasureFourier μ).aestronglyMeasurable
    (μ.variation.real Set.univ)
    (ae_of_all volume (norm_complexMeasureFourier_le μ))).toLp
      (complexMeasureFourier μ)

theorem coeFn_complexMeasureFourierLpTop
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] :
    complexMeasureFourierLpTop μ =ᵐ[(volume : Measure ℝ)]
      complexMeasureFourier μ := by
  exact MemLp.coeFn_toLp _

theorem norm_complexMeasureFourierLpTop_le
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] :
    ‖complexMeasureFourierLpTop μ‖ ≤ μ.variation.real Set.univ := by
  change lpNorm (complexMeasureFourierLpTop μ : ℝ → ℂ) ∞ volume ≤
    μ.variation.real Set.univ
  have hcoe : (complexMeasureFourierLpTop μ : ℝ → ℂ) =ᵐ[volume]
      complexMeasureFourier μ := coeFn_complexMeasureFourierLpTop μ
  have hmem : MemLp (complexMeasureFourierLpTop μ : ℝ → ℂ) ∞ volume :=
    Lp.memLp _
  rw [lpNorm_exponent_top_eq_essSup hmem]
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) (ae (volume : Measure ℝ))
      (fun ξ => ‖(complexMeasureFourierLpTop μ : ℝ → ℂ) ξ‖) :=
    Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
      (Filter.Frequently.of_forall fun ξ => norm_nonneg _)
  apply essSup_le_of_ae_le (μ.variation.real Set.univ) _ hcob
  filter_upwards [hcoe] with ξ hξ
  rw [hξ]
  exact norm_complexMeasureFourier_le μ ξ

/-- The `L²` Fourier multiplier associated to a finite complex measure. -/
def realComplexMeasureFourierMultiplier
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) :=
  realFourierMultiplier (complexMeasureFourierLpTop μ)

theorem norm_realComplexMeasureFourierMultiplier_le
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] :
    ‖realComplexMeasureFourierMultiplier μ‖ ≤
      μ.variation.real Set.univ :=
  (norm_realFourierMultiplier_le (complexMeasureFourierLpTop μ)).trans
    (norm_complexMeasureFourierLpTop_le μ)

end

end FractionalPrimes.Literature.JSW
