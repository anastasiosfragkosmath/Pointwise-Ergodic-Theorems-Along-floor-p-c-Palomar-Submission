module

public import FractionalPrimes.Literature.JSW.PositiveMaximalGeometricAdapters

/-!
# Smooth-density probability adapters for JSW positivity

The smooth part of the measure splitting is represented by the probability
measure with density `measureSplittingPsi σ`. This file records that exact
probability normalization before connecting its geometric scales to the
maximal bound.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The probability measure associated with the smooth density in the
measure splitting. -/
def initialSquarePsiProbabilityMeasure (σ : Measure ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (measureSplittingPsi σ x))

theorem initialSquarePsiProbabilityMeasure_isProbability
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    IsProbabilityMeasure (initialSquarePsiProbabilityMeasure σ) := by
  apply (isProbabilityMeasure_iff).2
  rw [initialSquarePsiProbabilityMeasure, withDensity_apply _ MeasurableSet.univ]
  have hψInt := measureSplittingPsi_integrable σ hSupp
  have hψNonneg : ∀ x, 0 ≤ measureSplittingPsi σ x :=
    measureSplittingPsi_nonneg σ
  have hlin : ENNReal.ofReal
      (∫ x, measureSplittingPsi σ x ∂volume) =
        ∫⁻ x, ENNReal.ofReal (measureSplittingPsi σ x) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hψInt (ae_of_all volume hψNonneg)
  calc
    (∫⁻ x in Set.univ, ENNReal.ofReal (measureSplittingPsi σ x) ∂volume) =
        ∫⁻ x, ENNReal.ofReal (measureSplittingPsi σ x) ∂volume := by simp
    _ = ENNReal.ofReal (∫ x, measureSplittingPsi σ x ∂volume) := hlin.symm
    _ = 1 := by rw [measureSplittingPsi_integral]; norm_num

#print axioms initialSquarePsiProbabilityMeasure_isProbability

/-- Every geometric pushforward of the smooth splitting probability measure
is again a probability measure. -/
theorem initialSquarePsiDilateProbabilityMeasure_isProbability
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (t : ℝ) :
    IsProbabilityMeasure
      (Measure.map (fun y : ℝ => t * y)
        (initialSquarePsiProbabilityMeasure σ)) := by
  apply (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2
  exact initialSquarePsiProbabilityMeasure_isProbability hSupp

#print axioms initialSquarePsiDilateProbabilityMeasure_isProbability

/-- Unfold a geometrically dilated smooth-density average into its Lebesgue
density integral. -/
theorem initialSquarePsiDilate_integral_eq_density
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (t : ℝ) (ht : t ≠ 0) (g : ℝ → ℝ) (x : ℝ) :
    (∫ y, g (x + y) ∂Measure.map (fun y : ℝ => t * y)
        (initialSquarePsiProbabilityMeasure σ)) =
      ∫ z, measureSplittingPsi σ z * g (x + t * z) ∂volume := by
  rw [(measurableEmbedding_mulLeft₀ ht).integral_map]
  rw [initialSquarePsiProbabilityMeasure]
  have hψmeas : Measurable
      (fun z : ℝ => ENNReal.ofReal (measureSplittingPsi σ z)) := by
    exact ENNReal.measurable_ofReal.comp
      (measureSplittingPsi_contDiff σ).continuous.measurable
  have hψtop : ∀ᵐ z ∂volume,
      ENNReal.ofReal (measureSplittingPsi σ z) < ∞ := by
    exact ae_of_all _ fun z => ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hψmeas hψtop]
  apply integral_congr_ae
  filter_upwards [] with z
  simp [ENNReal.toReal_ofReal (measureSplittingPsi_nonneg σ z), smul_eq_mul]

#print axioms initialSquarePsiDilate_integral_eq_density

/-- The smooth-density average in the adjoint convention is dominated by the
extended centered maximal function, with the source constant `4‖φ‖∞`. -/
theorem initialSquarePsiDilate_average_le_lineMaximal
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {g : ℝ → ℝ} (hg : LocallyIntegrable (fun y => (g (-y) : ℂ)))
    (t : ℝ) (ht : 0 < t) (x : ℝ) :
    ENNReal.ofReal
        (∫ y, g (x + y) ∂Measure.map (fun y : ℝ => t * y)
          (initialSquarePsiProbabilityMeasure σ)) ≤
      ENNReal.ofReal (4 * lpNorm φ ∞ volume) *
        lineMaximal (fun y : ℝ => (g (-y) : ℂ)) (-x) := by
  let f : ℝ → ℂ := fun y => (g (-y) : ℂ)
  let q : ℝ → ℝ := fun z => measureSplittingPsi σ z * g (x + t * z)
  have hDensity := initialSquarePsiDilate_integral_eq_density
    (σ := σ) t ht.ne' g x
  have hpoint (z : ℝ) :
      (measureSplittingPsi σ z : ℂ) * f (-x - t * z) =
        Complex.ofRealLI (q z) := by
    simp only [f, q, Complex.ofRealLI_apply]
    rw [show -x - t * z = -(x + t * z) by ring]
    simp [Complex.ofReal_mul]
  have hcomplex :
      (∫ z, (measureSplittingPsi σ z : ℂ) * f (-x - t * z) ∂volume) =
        Complex.ofRealLI (∫ z, q z ∂volume) := by
    calc
      _ = ∫ z, Complex.ofRealLI (q z) ∂volume := by
        apply integral_congr_ae
        exact ae_of_all _ hpoint
      _ = _ := Complex.ofRealLI.integral_comp_comm q
  have hnorm :
      ‖∫ z, (measureSplittingPsi σ z : ℂ) * f (-x - t * z) ∂volume‖ =
        |∫ z, q z ∂volume| := by
    rw [hcomplex]
    simp [Complex.ofRealLI_apply]
  have hkernel := initialSquare_psi_kernel_integral_bound hSupp hg (-x) t ht
  have hcenterNonneg : 0 ≤ lineCenteredAverage f (-x) (2 * t) := by
    unfold lineCenteredAverage
    apply div_nonneg
    · exact intervalIntegral.integral_nonneg (by nlinarith [ht])
        (fun y _ => norm_nonneg (f y))
    · positivity
  have hcenterMax :
      ENNReal.ofReal (lineCenteredAverage f (-x) (2 * t)) ≤
        lineMaximal f (-x) := by
    unfold lineMaximal
    exact le_iSup_of_le ⟨2 * t, by linarith⟩ le_rfl
  have hcoef : 0 ≤ 4 * lpNorm φ ∞ volume :=
    mul_nonneg (by norm_num) lpNorm_nonneg
  calc
    _ = ENNReal.ofReal (∫ z, q z ∂volume) := by rw [hDensity]
    _ ≤ ENNReal.ofReal |∫ z, q z ∂volume| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = ENNReal.ofReal ‖∫ z, (measureSplittingPsi σ z : ℂ) *
          f (-x - t * z) ∂volume‖ := by rw [hnorm]
    _ ≤ ENNReal.ofReal
          (4 * lpNorm φ ∞ volume * lineCenteredAverage f (-x) (2 * t)) :=
      ENNReal.ofReal_le_ofReal hkernel
    _ = ENNReal.ofReal (4 * lpNorm φ ∞ volume) *
          ENNReal.ofReal (lineCenteredAverage f (-x) (2 * t)) := by
      rw [ENNReal.ofReal_mul hcoef]
    _ ≤ ENNReal.ofReal (4 * lpNorm φ ∞ volume) * lineMaximal f (-x) :=
      mul_le_mul_of_nonneg_left hcenterMax bot_le

#print axioms initialSquarePsiDilate_average_le_lineMaximal

/-- The finite geometric family generated by the smooth splitting density has
the exact `L^q` maximal majorant obtained from the source `4‖φ‖∞` kernel
comparison and the centered line maximal theorem. -/
theorem finiteGeometricPsiPositiveMaximalBound
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hb : 1 < b) (hq : 1 < q)
    (κ : ι → ℤ) (g : ℝ → ℝ)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    ∃ M : ℝ → ℝ,
      MemLp M (ENNReal.ofReal q) volume ∧
      (∀ x, 0 ≤ M x) ∧
      (∀ᵐ x ∂volume, ∀ i,
        (∫ y, g (x + y) ∂Measure.map
          (fun y : ℝ => b ^ κ i * y) (initialSquarePsiProbabilityMeasure σ)) ≤ M x) ∧
      lpNorm M (ENNReal.ofReal q) volume ≤
        (4 * lpNorm φ ∞ volume) *
          ((6 * q * 2 ^ (q - 1) / (q - 1)) ^ (1 / q)) *
        lpNorm g (ENNReal.ofReal q) volume := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal q
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := le_of_lt hq
  have hP1 : (1 : ℝ≥0∞) ≤ P := by
    dsimp [P]
    exact ENNReal.one_le_ofReal.mpr hq1
  let g' : ℝ → ℝ := hg.aestronglyMeasurable.mk g
  have hgRep : g =ᵐ[volume] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hg'Strong : StronglyMeasurable g' :=
    hg.aestronglyMeasurable.stronglyMeasurable_mk
  have hg'Mem : MemLp g' P volume := by
    apply hg.congr_norm hg'Strong.aestronglyMeasurable
    filter_upwards [hgRep] with x hx
    simp [hx]
  let f : ℝ → ℂ := fun y => (g' (-y) : ℂ)
  have hg'Neg : MemLp (fun y : ℝ => g' (-y)) P volume :=
    hg'Mem.comp_measurePreserving (Measure.measurePreserving_neg volume)
  have hfStrong : StronglyMeasurable f := by
    exact (Complex.continuous_ofReal.comp_stronglyMeasurable hg'Strong)
      |>.comp_measurable (by fun_prop)
  have hfMem : MemLp f P volume := by
    apply hg'Neg.congr_norm hfStrong.aestronglyMeasurable
    filter_upwards [] with x
    simp [f, Real.norm_eq_abs]
  have hNormF : eLpNorm f P volume = eLpNorm g P volume := by
    calc
      eLpNorm f P volume = eLpNorm (fun y : ℝ => g' (-y)) P volume := by
        rw [← eLpNorm_norm f hfStrong.aestronglyMeasurable,
          ← eLpNorm_norm (fun y : ℝ => g' (-y)) hg'Neg.aestronglyMeasurable]
        apply eLpNorm_congr_ae
        filter_upwards [] with y
        simp [f, Real.norm_eq_abs]
      _ = eLpNorm g' P volume :=
        eLpNorm_comp_measurePreserving hg'Strong.aestronglyMeasurable
          (Measure.measurePreserving_neg volume)
      _ = eLpNorm g P volume := by
        rw [← eLpNorm_norm g' hg'Strong.aestronglyMeasurable,
          ← eLpNorm_norm g hg.aestronglyMeasurable]
        apply eLpNorm_congr_ae
        filter_upwards [hgRep] with y hy
        simp [hy]
  have hfLoc : LocallyIntegrable f volume := hfMem.locallyIntegrable hP1
  have hLineMeas : Measurable (lineMaximalReal f) :=
    lineMaximalReal_measurable_of_locallyIntegrable hfLoc
  let C : ℝ := 4 * lpNorm φ ∞ volume
  let H : ℝ := (6 * q * 2 ^ (q - 1) / (q - 1)) ^ (1 / q)
  let B : ℝ := C * H
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) lpNorm_nonneg
  have hH : 0 ≤ H := by
    dsimp [H]
    apply Real.rpow_nonneg
    apply div_nonneg
    · positivity
    · linarith
  have hB : 0 ≤ B := mul_nonneg hC hH
  let M : ℝ → ℝ := fun x => C * lineMaximalReal f (-x)
  have hMMeas : Measurable M := by
    dsimp [M]
    exact measurable_const.mul (hLineMeas.comp measurable_neg)
  have hMNonneg (x : ℝ) : 0 ≤ M x := by
    dsimp [M]
    exact mul_nonneg hC (ENNReal.toReal_nonneg)
  have hCnorm : ‖C‖ₑ = ENNReal.ofReal C := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC]
  have hMsmul : M = C • (fun x : ℝ => lineMaximalReal f (-x)) := by
    funext x
    simp [M, smul_eq_mul]
  have hLineBound := lineMaximal_strongLp hq hfMem
  have hMEnorm : eLpNorm M P volume ≤
      ENNReal.ofReal B * eLpNorm g P volume := by
    calc
      eLpNorm M P volume ≤
          ENNReal.ofReal C *
            eLpNorm (fun x : ℝ => lineMaximalReal f (-x)) P volume := by
        calc
          eLpNorm M P volume =
              eLpNorm (C • (fun x : ℝ => lineMaximalReal f (-x))) P volume := by
            rw [hMsmul]
          _ ≤ ‖C‖ₑ * eLpNorm
              (fun x : ℝ => lineMaximalReal f (-x)) P volume :=
            (eLpNorm_const_smul_le
              (c := C) (f := fun x : ℝ => lineMaximalReal f (-x))
              (p := P) (μ := volume))
          _ = ENNReal.ofReal C * eLpNorm
              (fun x : ℝ => lineMaximalReal f (-x)) P volume := by
            rw [hCnorm]
      _ = ENNReal.ofReal C * eLpNorm (lineMaximalReal f) P volume := by
        congr 1
        exact eLpNorm_comp_measurePreserving hLineMeas.aestronglyMeasurable
          (Measure.measurePreserving_neg volume)
      _ ≤ ENNReal.ofReal C *
          (ENNReal.ofReal H * eLpNorm f P volume) :=
        mul_le_mul_of_nonneg_left hLineBound (by positivity)
      _ = ENNReal.ofReal B * eLpNorm g P volume := by
        change ENNReal.ofReal C * (ENNReal.ofReal H * eLpNorm f P volume) =
          ENNReal.ofReal (C * H) * eLpNorm g P volume
        rw [ENNReal.ofReal_mul hC, hNormF]
        ring
  have hMmem : MemLp M P volume :=
    lt_of_le_of_lt hMEnorm
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top)
  have hMlpNorm : lpNorm M P volume ≤ B * lpNorm g P volume := by
    dsimp [lpNorm]
    calc
      (eLpNorm M P volume).toReal ≤
          (ENNReal.ofReal B * eLpNorm g P volume).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top).ne hMEnorm
      _ = B * (eLpNorm g P volume).toReal := by
        rw [ENNReal.toReal_mul]
        simp [ENNReal.toReal_ofReal hB]
  have hFinLine : ∀ᵐ x ∂volume, lineMaximal f x < ∞ :=
    lineMaximal_lt_top_ae_of_memLp hq hfMem
  have hFinLineNeg : ∀ᵐ x ∂volume, lineMaximal f (-x) < ∞ := by
    have hneg : MeasurePreserving (fun x : ℝ => -x) volume volume :=
      Measure.measurePreserving_neg volume
    have hlineMeasExt : Measurable (lineMaximal f) :=
      lineMaximal_measurable_of_locallyIntegrable hfLoc
    have hmap : ∀ᵐ y ∂Measure.map (fun x : ℝ => -x) volume,
        lineMaximal f y < ∞ := by
      rw [hneg.map_eq]
      exact hFinLine
    exact (ae_map_iff (by fun_prop : AEMeasurable (fun x : ℝ => -x) volume)
      (hlineMeasExt measurableSet_Iio)).1 hmap
  have hMajor (i : ι) : ∀ᵐ x ∂volume,
      (∫ y, g (x + y) ∂Measure.map
        (fun y : ℝ => b ^ κ i * y) (initialSquarePsiProbabilityMeasure σ)) ≤ M x := by
    let t : ℝ := b ^ κ i
    have ht : 0 < t := by
      dsimp [t]
      exact zpow_pos (by linarith) _
    let μ : Measure ℝ := Measure.map (fun y : ℝ => t * y)
      (initialSquarePsiProbabilityMeasure σ)
    haveI : IsProbabilityMeasure μ := by
      dsimp [μ]
      exact initialSquarePsiDilateProbabilityMeasure_isProbability hSupp t
    have hTransfer := integral_add_translation_congr_ae μ g g' hgRep
    have hbound : ∀ x : ℝ,
        ENNReal.ofReal (∫ y, g' (x + y) ∂μ) ≤
          ENNReal.ofReal C * lineMaximal f (-x) := by
      intro x
      dsimp [μ, t]
      exact initialSquarePsiDilate_average_le_lineMaximal hSupp
        (by simpa [f] using hfLoc) (b ^ κ i) ht x
    filter_upwards [hTransfer, hFinLineNeg] with x hxTransfer hxFin
    have hreal : (∫ y, g' (x + y) ∂μ) ≤ M x := by
      apply (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg hC ENNReal.toReal_nonneg)).mp
      have hxFin' : lineMaximal f (-x) ≠ ∞ := ne_of_lt hxFin
      calc
        ENNReal.ofReal (∫ y, g' (x + y) ∂μ) ≤
            ENNReal.ofReal C * lineMaximal f (-x) := hbound x
        _ = ENNReal.ofReal (C * lineMaximalReal f (-x)) := by
          rw [← ENNReal.ofReal_toReal hxFin', ENNReal.ofReal_mul hC]
          rfl
    calc
      (∫ y, g (x + y) ∂Measure.map
          (fun y : ℝ => b ^ κ i * y) (initialSquarePsiProbabilityMeasure σ)) =
        ∫ y, g' (x + y) ∂μ := by
          exact hxTransfer
      _ ≤ M x := hreal
  refine ⟨M, hMmem, hMNonneg, ae_all_iff.mpr hMajor, ?_⟩
  simpa [B, C, H, lpNorm] using hMlpNorm

#print axioms finiteGeometricPsiPositiveMaximalBound

end

end FractionalPrimes.Literature.JSW

end
