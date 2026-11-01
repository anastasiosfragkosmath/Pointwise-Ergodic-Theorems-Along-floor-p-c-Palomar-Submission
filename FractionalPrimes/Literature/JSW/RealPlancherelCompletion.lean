module

public import FractionalPrimes.Literature.JSW.RealPlancherel

/-!
# Completion of the real-line Plancherel package

This file completes blueprint lemma `lj:plancherel`: it proves the
Fourier--Stieltjes convolution identity for arbitrary finite complex
measures by finite-interval vector-measure Fubini and exhaustion, and then
derives the exact finite-family multiplier square-function formula.
-/

@[expose] public section

open MeasureTheory FourierTransform SchwartzMap
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

private theorem integral_complexMeasure_mul_const
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (f : ℝ → ℂ) (hf : Integrable f μ.variation) (c : ℂ) :
    (∫ᵛ y, f y * c ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =
      (∫ᵛ y, f y ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) * c := by
  let R : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ).flip c
  have hmaps :
      ((ContinuousLinearMap.compL ℝ ℂ ℂ ℂ) R ∘L
          ContinuousLinearMap.mul ℝ ℂ) =
        (ContinuousLinearMap.mul ℝ ℂ ∘L R) := by
    apply ContinuousLinearMap.ext
    intro z
    apply ContinuousLinearMap.ext
    intro w
    simp [R, mul_comm, mul_left_comm, mul_assoc]
  change (∫ᵛ y, R (f y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =
    R (∫ᵛ y, f y ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
  rw [VectorMeasure.continuousLinearMap_apply_integral hf]
  rw [hmaps]
  rw [← VectorMeasure.integral_continuousLinearMap_comp hf]

private theorem fourierPhase_vectorIntegral_fubini_Icc
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (k : ℝ → ℂ) (hk : Integrable k volume) (a b : ℝ) :
    (∫ᵛ y, (∫ ξ in Set.Icc a b,
        fourierTranslationPhase y ξ * k ξ ∂volume)
      ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =
      ∫ ξ in Set.Icc a b,
        complexMeasureFourier μ ξ * k ξ ∂volume := by
  let ν : SignedMeasure ℝ := (volume.restrict (Set.Icc a b)).toSignedMeasure
  letI : IsFiniteMeasure ν.variation := ⟨by simp [ν]⟩
  have hphase : Continuous (fun z : ℝ × ℝ =>
      fourierTranslationPhase z.1 z.2) := by
    exact continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp
        ((continuous_fst.mul continuous_snd).neg))
  have hkprod : Integrable (fun z : ℝ × ℝ => k z.2)
      (μ.variation.prod (volume.restrict (Set.Icc a b))) :=
    hk.restrict.comp_snd μ.variation
  have hjoint : Integrable
      (Function.uncurry fun y ξ => fourierTranslationPhase y ξ * k ξ)
      (μ.variation.prod (volume.restrict (Set.Icc a b))) :=
    hkprod.bdd_mul (c := 1) hphase.aestronglyMeasurable
      (ae_of_all _ fun z => by simp [Function.uncurry, fourierTranslationPhase])
  have hswap := VectorMeasure.integral_integral_swap
    (μ := μ) (ν := ν)
    (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip)
    (C := ContinuousLinearMap.mul ℝ ℂ)
    (A := ContinuousLinearMap.mul ℝ ℂ)
    (D := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip)
    (f := fun y ξ => fourierTranslationPhase y ξ * k ξ)
    (by simpa [ν] using hjoint)
    (by
      intro x r z
      simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm])
  have hswap' :
      (∫ᵛ y, (∫ ξ in Set.Icc a b,
          fourierTranslationPhase y ξ * k ξ ∂volume)
        ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =
        ∫ ξ in Set.Icc a b,
          (∫ᵛ y, fourierTranslationPhase y ξ * k ξ
            ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) ∂volume := by
    simpa [ν] using hswap
  rw [hswap']
  apply integral_congr_ae
  filter_upwards [] with ξ
  have hphaseInt : Integrable (fun y : ℝ => fourierTranslationPhase y ξ)
      μ.variation :=
    Integrable.of_bound
      (continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp
          ((continuous_id.mul continuous_const).neg))
        |>.aestronglyMeasurable)
      1 (ae_of_all _ fun y => by simp [fourierTranslationPhase])
  simpa [complexMeasureFourier, fourierTranslationPhase] using
    integral_complexMeasure_mul_const μ
      (fun y : ℝ => fourierTranslationPhase y ξ) hphaseInt (k ξ)

private def realLineTruncation (n : ℕ) : Set ℝ :=
  Set.Icc (-(n : ℝ)) (n : ℝ)

private theorem measurableSet_realLineTruncation (n : ℕ) :
    MeasurableSet (realLineTruncation n) :=
  measurableSet_Icc

private theorem monotone_realLineTruncation : Monotone realLineTruncation := by
  intro n m hnm x hx
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

private theorem iUnion_realLineTruncation :
    (⋃ n : ℕ, realLineTruncation n) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, realLineTruncation, Set.mem_Icc,
    Set.mem_univ, iff_true]
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  refine ⟨n, ?_, ?_⟩
  · linarith [neg_abs_le x]
  · exact (le_abs_self x).trans hn.le

theorem fourierPhase_vectorIntegral_fubini
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (k : ℝ → ℂ) (hk : Integrable k volume) :
    (∫ᵛ y, (∫ ξ, fourierTranslationPhase y ξ * k ξ ∂volume)
      ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =
      ∫ ξ, complexMeasureFourier μ ξ * k ξ ∂volume := by
  let F : ℕ → ℝ → ℂ := fun n y =>
    ∫ ξ in realLineTruncation n,
      fourierTranslationPhase y ξ * k ξ ∂volume
  let f : ℝ → ℂ := fun y =>
    ∫ ξ, fourierTranslationPhase y ξ * k ξ ∂volume
  let C : ℝ := ∫ ξ, ‖k ξ‖ ∂volume
  have hphase : Continuous (fun z : ℝ × ℝ =>
      fourierTranslationPhase z.1 z.2) := by
    exact continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp
        ((continuous_fst.mul continuous_snd).neg))
  have hFn_meas : ∀ n, AEStronglyMeasurable (F n) μ.variation := by
    intro n
    have hkprod : Integrable (fun z : ℝ × ℝ => k z.2)
        (μ.variation.prod (volume.restrict (realLineTruncation n))) :=
      hk.restrict.comp_snd μ.variation
    have hjoint : Integrable (fun z : ℝ × ℝ =>
        fourierTranslationPhase z.1 z.2 * k z.2)
        (μ.variation.prod (volume.restrict (realLineTruncation n))) :=
      hkprod.bdd_mul (c := 1) hphase.aestronglyMeasurable
        (ae_of_all _ fun z => by simp [fourierTranslationPhase])
    exact hjoint.aestronglyMeasurable.integral_prod_right'
  have hC_int : Integrable (fun _ : ℝ => C) μ.variation :=
    integrable_const C
  have hbound : ∀ n, ∀ᵐ y ∂μ.variation, ‖F n y‖ ≤ C := by
    intro n
    filter_upwards [] with y
    calc
      ‖F n y‖ ≤ ∫ ξ in realLineTruncation n,
          ‖fourierTranslationPhase y ξ * k ξ‖ ∂volume := by
        exact norm_integral_le_integral_norm _
      _ = ∫ ξ in realLineTruncation n, ‖k ξ‖ ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with ξ
        simp [fourierTranslationPhase]
      _ ≤ ∫ ξ, ‖k ξ‖ ∂volume :=
        integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ fun ξ => norm_nonneg (k ξ)) hk.norm
      _ = C := rfl
  have hpoint : ∀ y, Filter.Tendsto (fun n => F n y) Filter.atTop (nhds (f y)) := by
    intro y
    have hyInt : Integrable
        (fun ξ => fourierTranslationPhase y ξ * k ξ) volume :=
      hk.bdd_mul (c := 1)
        (continuous_fourierTranslationPhase y).aestronglyMeasurable
        (ae_of_all _ fun ξ => by simp [fourierTranslationPhase])
    simpa [F, f, iUnion_realLineTruncation] using
      (tendsto_setIntegral_of_monotone measurableSet_realLineTruncation
        monotone_realLineTruncation hyInt.integrableOn)
  have hleft : Filter.Tendsto
      (fun n => ∫ᵛ y, F n y ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
      Filter.atTop
      (nhds (∫ᵛ y, f y ∂[ContinuousLinearMap.mul ℝ ℂ; μ])) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence
      (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ)
      (fun _ : ℝ => C) hFn_meas hC_int hbound
      (ae_of_all _ hpoint)
  have hrightInt : Integrable
      (fun ξ => complexMeasureFourier μ ξ * k ξ) volume :=
    hk.bdd_mul
      (stronglyMeasurable_complexMeasureFourier μ).aestronglyMeasurable
      (ae_of_all _ fun ξ => norm_complexMeasureFourier_le μ ξ)
  have hright : Filter.Tendsto
      (fun n => ∫ ξ in realLineTruncation n,
        complexMeasureFourier μ ξ * k ξ ∂volume)
      Filter.atTop
      (nhds (∫ ξ, complexMeasureFourier μ ξ * k ξ ∂volume)) := by
    simpa [iUnion_realLineTruncation] using
      (tendsto_setIntegral_of_monotone measurableSet_realLineTruncation
        monotone_realLineTruncation hrightInt.integrableOn)
  have heq : ∀ n,
      (∫ᵛ y, F n y ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =
        ∫ ξ in realLineTruncation n,
          complexMeasureFourier μ ξ * k ξ ∂volume := by
    intro n
    simpa [F, realLineTruncation] using
      fourierPhase_vectorIntegral_fubini_Icc μ k hk (-(n : ℝ)) (n : ℝ)
  change (∫ᵛ y, f y ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) = _
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.Eventually.of_forall fun n => (heq n).symm))

private theorem inner_lpComplexMeasure_integral
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (V : ℝ → Lp ℂ 2 (volume : Measure ℝ))
    (hV : Integrable V μ.variation)
    (H : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ H (∫ᵛ y, V y ∂[lpComplexSmulBilinear 2; μ]) =
      ∫ᵛ y, inner ℂ H (V y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
  let L : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] ℂ :=
    (innerSL ℂ H).restrictScalars ℝ
  change L (∫ᵛ y, V y ∂[lpComplexSmulBilinear 2; μ]) = _
  rw [VectorMeasure.continuousLinearMap_apply_integral hV]
  have hmaps :
      ((ContinuousLinearMap.compL ℝ ℂ
          (Lp ℂ 2 (volume : Measure ℝ)) ℂ) L ∘L
        lpComplexSmulBilinear 2) =
      (ContinuousLinearMap.mul ℝ ℂ ∘L L) := by
    apply ContinuousLinearMap.ext
    intro W
    apply ContinuousLinearMap.ext
    intro z
    simp [L, lpComplexSmulBilinear, inner_smul_right, mul_comm]
  rw [hmaps]
  rw [← VectorMeasure.integral_continuousLinearMap_comp hV]
  rfl

private theorem integrable_realLpMultiplier_translationPhase
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable
      (fun y => realLpMultiplier (fourierTranslationPhaseLpTop y) G)
      μ.variation := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := realFourierTransformL2.symm G
  have htrans := integrable_lpRightTranslate (p := 2) (by norm_num) μ F
  have hfourier : Integrable
      (fun y => realFourierTransformL2RealCLM (lpRightTranslate 2 y F))
      μ.variation :=
    realFourierTransformL2RealCLM.integrable_comp htrans
  apply hfourier.congr
  filter_upwards [] with y
  simpa [realFourierTransformL2RealCLM, F] using
    fourier_lpRightTranslate F y

private theorem inner_realLpMultiplier_translationPhase
    (H G : Lp ℂ 2 (volume : Measure ℝ)) (y : ℝ) :
    inner ℂ H (realLpMultiplier (fourierTranslationPhaseLpTop y) G) =
      ∫ ξ, fourierTranslationPhase y ξ * inner ℂ (H ξ) (G ξ) ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_realLpMultiplier
      (fourierTranslationPhaseLpTop y) G,
    coeFn_fourierTranslationPhaseLpTop y] with ξ hmul hphase
  rw [hmul, hphase]
  change inner ℂ (H ξ) (fourierTranslationPhase y ξ * G ξ) = _
  rw [← smul_eq_mul, inner_smul_right]

private theorem inner_realLpMultiplier_complexMeasureFourier
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (H G : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ H (realLpMultiplier (complexMeasureFourierLpTop μ) G) =
      ∫ ξ, complexMeasureFourier μ ξ * inner ℂ (H ξ) (G ξ) ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_realLpMultiplier
      (complexMeasureFourierLpTop μ) G,
    coeFn_complexMeasureFourierLpTop μ] with ξ hmul hfourier
  rw [hmul, hfourier]
  change inner ℂ (H ξ) (complexMeasureFourier μ ξ * G ξ) = _
  rw [← smul_eq_mul, inner_smul_right]

theorem integral_realLpMultiplier_translationPhase
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ᵛ y, realLpMultiplier (fourierTranslationPhaseLpTop y) G
      ∂[lpComplexSmulBilinear 2; μ]) =
      realLpMultiplier (complexMeasureFourierLpTop μ) G := by
  apply ext_inner_left ℂ
  intro H
  let V : ℝ → Lp ℂ 2 (volume : Measure ℝ) := fun y =>
    realLpMultiplier (fourierTranslationPhaseLpTop y) G
  have hV : Integrable V μ.variation :=
    integrable_realLpMultiplier_translationPhase μ G
  let k : ℝ → ℂ := fun ξ => inner ℂ (H ξ) (G ξ)
  have hk : Integrable k volume := L2.integrable_inner H G
  calc
    inner ℂ H (∫ᵛ y, V y ∂[lpComplexSmulBilinear 2; μ]) =
        ∫ᵛ y, inner ℂ H (V y)
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] :=
      inner_lpComplexMeasure_integral μ V hV H
    _ = ∫ᵛ y, (∫ ξ, fourierTranslationPhase y ξ * k ξ ∂volume)
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
      apply VectorMeasure.integral_congr_ae
      filter_upwards [] with y
      exact inner_realLpMultiplier_translationPhase H G y
    _ = ∫ ξ, complexMeasureFourier μ ξ * k ξ ∂volume :=
      fourierPhase_vectorIntegral_fubini μ k hk
    _ = inner ℂ H
        (realLpMultiplier (complexMeasureFourierLpTop μ) G) :=
      (inner_realLpMultiplier_complexMeasureFourier μ H G).symm

/-- Fourier transformation converts convolution by an arbitrary finite
complex measure into multiplication by its Fourier--Stieltjes transform. -/
theorem fourier_lpComplexMeasureConvolution
    (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    realFourierTransformL2 (lpComplexMeasureConvolution 2 μ F) =
      realLpMultiplier (complexMeasureFourierLpTop μ)
        (realFourierTransformL2 F) := by
  rw [fourier_lpComplexMeasureConvolution_integral]
  calc
    (∫ᵛ y, realFourierTransformL2 (lpRightTranslate 2 y F)
        ∂[lpComplexSmulBilinear 2; μ]) =
        ∫ᵛ y, realLpMultiplier (fourierTranslationPhaseLpTop y)
            (realFourierTransformL2 F)
          ∂[lpComplexSmulBilinear 2; μ] := by
      apply VectorMeasure.integral_congr_ae
      filter_upwards [] with y
      exact fourier_lpRightTranslate F y
    _ = realLpMultiplier (complexMeasureFourierLpTop μ)
        (realFourierTransformL2 F) :=
      integral_realLpMultiplier_translationPhase μ
        (realFourierTransformL2 F)

private theorem lp_two_norm_sq_eq_integral_norm_sq
    (U : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖U‖ ^ 2 = ∫ x, ‖U x‖ ^ 2 ∂volume := by
  calc
    ‖U‖ ^ 2 = RCLike.re (inner ℂ U U) :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) U).symm
    _ = RCLike.re (∫ x, inner ℂ (U x) (U x) ∂volume) := by
      rw [L2.inner_def]
    _ = ∫ x, RCLike.re (inner ℂ (U x) (U x)) ∂volume :=
      (integral_re (L2.integrable_inner U U)).symm
    _ = ∫ x, ‖U x‖ ^ 2 ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (U x)

private theorem realFourierMultiplier_integral_norm_sq
    (M : Lp ℂ ∞ (volume : Measure ℝ))
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ x, ‖(realFourierMultiplier M F : ℝ → ℂ) x‖ ^ 2 ∂volume) =
      ∫ ξ, ‖(M : ℝ → ℂ) ξ‖ ^ 2 *
        ‖(realFourierTransformL2 F : ℝ → ℂ) ξ‖ ^ 2 ∂volume := by
  rw [← lp_two_norm_sq_eq_integral_norm_sq]
  have hnorm : ‖realFourierMultiplier M F‖ =
      ‖realLpMultiplier M (realFourierTransformL2 F)‖ := by
    simpa [realFourierMultiplier] using
      realFourierTransformL2.symm.norm_map
        (realLpMultiplier M (realFourierTransformL2 F))
  rw [hnorm, lp_two_norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [coeFn_realLpMultiplier M (realFourierTransformL2 F)] with ξ hξ
  rw [hξ, norm_mul]
  ring

/-- Exact finite-family square formula, written as the square of the
pointwise square-function norm on the left. -/
theorem finiteFourierMultiplierSquareFormula
    {ι : Type*} [Fintype ι]
    (M : ι → Lp ℂ ∞ (volume : Measure ℝ))
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ x, ∑ j : ι,
        ‖(realFourierMultiplier (M j) F : ℝ → ℂ) x‖ ^ 2 ∂volume) =
      ∫ ξ, ∑ j : ι, ‖(M j : ℝ → ℂ) ξ‖ ^ 2 *
        ‖(realFourierTransformL2 F : ℝ → ℂ) ξ‖ ^ 2 ∂volume := by
  have hleft : ∀ j : ι, Integrable
      (fun x => ‖(realFourierMultiplier (M j) F : ℝ → ℂ) x‖ ^ 2)
      volume := by
    intro j
    exact (Lp.memLp (realFourierMultiplier (M j) F)).integrable_norm_pow
      (by norm_num)
  have hright : ∀ j : ι, Integrable
      (fun ξ => ‖(M j : ℝ → ℂ) ξ‖ ^ 2 *
        ‖(realFourierTransformL2 F : ℝ → ℂ) ξ‖ ^ 2) volume := by
    intro j
    have hmul : Integrable
        (fun ξ => ‖(realLpMultiplier (M j)
          (realFourierTransformL2 F) : ℝ → ℂ) ξ‖ ^ 2) volume :=
      (Lp.memLp (realLpMultiplier (M j)
        (realFourierTransformL2 F))).integrable_norm_pow (by norm_num)
    apply hmul.congr
    filter_upwards [coeFn_realLpMultiplier (M j)
      (realFourierTransformL2 F)] with ξ hξ
    rw [hξ, norm_mul]
    ring
  rw [integral_finset_sum _ (fun j _ => hleft j)]
  rw [integral_finset_sum _ (fun j _ => hright j)]
  apply Finset.sum_congr rfl
  intro j hj
  exact realFourierMultiplier_integral_norm_sq (M j) F

/-- The pointwise finite multiplier square function in the exact form used
in the blueprint. -/
def finiteFourierMultiplierSquareFunction
    {ι : Type*} [Fintype ι]
    (M : ι → Lp ℂ ∞ (volume : Measure ℝ))
    (F : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) : ℂ :=
  (Real.sqrt (∑ j : ι,
    ‖(realFourierMultiplier (M j) F : ℝ → ℂ) x‖ ^ 2) : ℝ)

private theorem finiteFourierMultiplierSquareFunction_aestronglyMeasurable
    {ι : Type*} [Fintype ι]
    (M : ι → Lp ℂ ∞ (volume : Measure ℝ))
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    AEStronglyMeasurable (finiteFourierMultiplierSquareFunction M F) volume := by
  have hsum : AEStronglyMeasurable (fun x => ∑ j : ι,
      ‖(realFourierMultiplier (M j) F : ℝ → ℂ) x‖ ^ 2) volume :=
    Finset.univ.aestronglyMeasurable_fun_sum fun j hj =>
      (continuous_pow 2).comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable (realFourierMultiplier (M j) F)).norm
  exact RCLike.continuous_ofReal.comp_aestronglyMeasurable
    (Real.continuous_sqrt.comp_aestronglyMeasurable hsum)

theorem finiteFourierMultiplierSquareFunction_memLp
    {ι : Type*} [Fintype ι]
    (M : ι → Lp ℂ ∞ (volume : Measure ℝ))
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (finiteFourierMultiplierSquareFunction M F) 2 volume := by
  have hsumInt : Integrable (fun x => ∑ j : ι,
      ‖(realFourierMultiplier (M j) F : ℝ → ℂ) x‖ ^ 2) volume :=
    integrable_finsetSum Finset.univ fun j hj =>
      (Lp.memLp (realFourierMultiplier (M j) F)).integrable_norm_pow
        (by norm_num)
  apply (memLp_two_iff_integrable_sq_norm
    (finiteFourierMultiplierSquareFunction_aestronglyMeasurable M F)).2
  apply hsumInt.congr
  filter_upwards [] with x
  have hnonneg : 0 ≤ ∑ j : ι,
      ‖(realFourierMultiplier (M j) F : ℝ → ℂ) x‖ ^ 2 :=
    Finset.sum_nonneg fun j hj => sq_nonneg _
  simp [finiteFourierMultiplierSquareFunction, Real.sq_sqrt hnonneg,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- The finite multiplier square function as an `L²` element. -/
def finiteFourierMultiplierSquareFunctionLp
    {ι : Type*} [Fintype ι]
    (M : ι → Lp ℂ ∞ (volume : Measure ℝ))
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (finiteFourierMultiplierSquareFunction_memLp M F).toLp
    (finiteFourierMultiplierSquareFunction M F)

theorem coeFn_finiteFourierMultiplierSquareFunctionLp
    {ι : Type*} [Fintype ι]
    (M : ι → Lp ℂ ∞ (volume : Measure ℝ))
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    finiteFourierMultiplierSquareFunctionLp M F =ᵐ[volume]
      finiteFourierMultiplierSquareFunction M F := by
  exact MemLp.coeFn_toLp _

/-- The exact finite-family square-function norm identity from
`lj:plancherel`. -/
theorem finiteFourierMultiplierSquareNormFormula
    {ι : Type*} [Fintype ι]
    (M : ι → Lp ℂ ∞ (volume : Measure ℝ))
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖finiteFourierMultiplierSquareFunctionLp M F‖ ^ 2 =
      ∫ ξ, ∑ j : ι, ‖(M j : ℝ → ℂ) ξ‖ ^ 2 *
        ‖(realFourierTransformL2 F : ℝ → ℂ) ξ‖ ^ 2 ∂volume := by
  rw [lp_two_norm_sq_eq_integral_norm_sq]
  calc
    (∫ x, ‖(finiteFourierMultiplierSquareFunctionLp M F : ℝ → ℂ) x‖ ^ 2
        ∂volume) =
        ∫ x, ∑ j : ι,
          ‖(realFourierMultiplier (M j) F : ℝ → ℂ) x‖ ^ 2 ∂volume := by
      apply integral_congr_ae
      filter_upwards [coeFn_finiteFourierMultiplierSquareFunctionLp M F] with x hx
      rw [hx]
      have hnonneg : 0 ≤ ∑ j : ι,
          ‖(realFourierMultiplier (M j) F : ℝ → ℂ) x‖ ^ 2 :=
        Finset.sum_nonneg fun j hj => sq_nonneg _
      simp [finiteFourierMultiplierSquareFunction, Real.sq_sqrt hnonneg,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    _ = _ := finiteFourierMultiplierSquareFormula M F

/-- Exact verified contents of blueprint lemma `lj:plancherel`. -/
structure RealPlancherel where
  fourier_schwartz : ∀ f : 𝓢(ℝ, ℂ),
    realFourierTransformL2 (f.toLp 2) = (𝓕 f).toLp 2
  fourier_surjective : Function.Surjective realFourierTransformL2
  fourier_isometry : ∀ F : Lp ℂ 2 (volume : Measure ℝ),
    ‖realFourierTransformL2 F‖ = ‖F‖
  convolution : ∀ (μ : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation]
    (F : Lp ℂ 2 (volume : Measure ℝ)),
    realFourierTransformL2 (lpComplexMeasureConvolution 2 μ F) =
      realLpMultiplier (complexMeasureFourierLpTop μ)
        (realFourierTransformL2 F)
  multiplier_norm : ∀ M : Lp ℂ ∞ (volume : Measure ℝ),
    ‖realFourierMultiplier M‖ ≤ ‖M‖
  finite_square : ∀ {ι : Type*} [Fintype ι]
    (M : ι → Lp ℂ ∞ (volume : Measure ℝ))
    (F : Lp ℂ 2 (volume : Measure ℝ)),
    ‖finiteFourierMultiplierSquareFunctionLp M F‖ ^ 2 =
      ∫ ξ, ∑ j : ι, ‖(M j : ℝ → ℂ) ξ‖ ^ 2 *
        ‖(realFourierTransformL2 F : ℝ → ℂ) ξ‖ ^ 2 ∂volume

/-- Manifest-facing proof of every clause of `lj:plancherel`. -/
theorem realPlancherel : RealPlancherel where
  fourier_schwartz := by
    intro f
    exact SchwartzMap.toLp_fourier_eq f
  fourier_surjective := realFourierTransformL2_surjective
  fourier_isometry := norm_realFourierTransformL2
  convolution := by
    intro μ hμ F
    exact fourier_lpComplexMeasureConvolution μ F
  multiplier_norm := norm_realFourierMultiplier_le
  finite_square := finiteFourierMultiplierSquareNormFormula

end

end FractionalPrimes.Literature.JSW

#print axioms FractionalPrimes.Literature.JSW.fourier_lpComplexMeasureConvolution
#print axioms FractionalPrimes.Literature.JSW.finiteFourierMultiplierSquareNormFormula
#print axioms FractionalPrimes.Literature.JSW.realPlancherel
