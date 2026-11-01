module

public import FractionalPrimes.Literature.JSW.RoughSquareMaximalNorm

/-! Transfer the checked complex σ maximal norm to the adjoint positive contract. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem geometricAdjointMaximalBound_of_sigmaLpMaximal
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p b B : ℝ}
    (hp : 1 < p) (hB : 0 ≤ B)
    (hfinite : ∀ F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      ∀ᵐ x ∂volume, (⨆ k : ℤ, ENNReal.ofReal
        ‖(geometricSigmaLpConvolution σ p b hp k F : ℝ → ℂ) x‖) < ∞)
    (hbound : ∀ F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      eLpNorm (geometricSigmaLpMaximalReal σ hp b F) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal B * eLpNorm (F : ℝ → ℂ) (ENNReal.ofReal p) volume) :
    GeometricAdjointMaximalBound σ b p B := by
  intro g hg
  let P : ℝ≥0∞ := ENNReal.ofReal p
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := le_of_lt hp
  have hP1 : (1 : ℝ≥0∞) ≤ P := by
    dsimp [P]
    exact ENNReal.one_le_ofReal.mpr hp1
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
  letI : Fact (1 ≤ P) := ⟨hP1⟩
  let F : Lp ℂ P (volume : Measure ℝ) := hfMem.toLp f
  have hF : (F : ℝ → ℂ) =ᵐ[volume] f := hfMem.coeFn_toLp
  let S := geometricSigmaLpMaximalReal σ hp b F
  have hS : Measurable S := by
    apply ENNReal.measurable_toReal.comp
    apply Measurable.iSup
    intro k
    exact ENNReal.continuous_ofReal.measurable.comp
      (Lp.stronglyMeasurable (geometricSigmaLpConvolution σ p b hp k F)).measurable.norm
  let M : ℝ → ℝ := fun x => S (-x)
  have hNormM : eLpNorm M P volume ≤ ENNReal.ofReal B * eLpNorm g P volume := by
    calc
      _ = eLpNorm S P volume := eLpNorm_comp_measurePreserving
        hS.aestronglyMeasurable (Measure.measurePreserving_neg volume)
      _ ≤ ENNReal.ofReal B * eLpNorm (F : ℝ → ℂ) P volume := hbound F
      _ = _ := by rw [eLpNorm_congr_ae hF, hNormF]
  have hMemM : MemLp M P volume := lt_of_le_of_lt hNormM
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top)
  have hFinNeg : ∀ᵐ x ∂volume, (⨆ k : ℤ, ENNReal.ofReal
        ‖(geometricSigmaLpConvolution σ p b hp k F : ℝ → ℂ) (-x)‖) < ∞ :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae (hfinite F)
  have hMajor (k : ℤ) : ∀ᵐ x ∂volume,
      (∫ y, g (x+y) ∂Measure.map (fun y : ℝ => b^k*y) σ) ≤ M x := by
    let μ := Measure.map (fun y : ℝ => b^k*y) σ
    have hraw := lpComplexSigmaConvolution_ae_eq_jswConvolution hp μ F f
      hfStrong.measurable hfMem hF
    have hrawNeg := (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae hraw
    have htransfer := integral_add_translation_congr_ae μ g g' hgRep
    filter_upwards [hrawNeg, htransfer, hFinNeg] with x hx hxtransfer hxfin
    have heq : (geometricSigmaLpConvolution σ p b hp k F : ℝ → ℂ) (-x) =
        Complex.ofReal (∫ y, g' (x+y) ∂μ) := by
      change (lpComplexMeasureConvolution P (initialSquareSigmaComplexMeasure μ) F : ℝ → ℂ) (-x) = _
      rw [hx]
      change (∫ y, f (-x-y) ∂μ) = _
      simp only [f, show ∀ y : ℝ, -(-x-y) = x+y by intro y; ring]
      exact integral_complex_ofReal
    have hscale : ‖(geometricSigmaLpConvolution σ p b hp k F : ℝ → ℂ) (-x)‖ ≤ M x := by
      have hle := le_iSup (fun j : ℤ => ENNReal.ofReal
        ‖(geometricSigmaLpConvolution σ p b hp j F : ℝ → ℂ) (-x)‖) k
      have ht := ENNReal.toReal_mono hxfin.ne hle
      simpa only [ENNReal.toReal_ofReal (norm_nonneg _), M, S, geometricSigmaLpMaximalReal] using ht
    rw [hxtransfer]
    calc
      (∫ y, g' (x+y) ∂μ) ≤ |∫ y, g' (x+y) ∂μ| := le_abs_self _
      _ = ‖(geometricSigmaLpConvolution σ p b hp k F : ℝ → ℂ) (-x)‖ := by
        rw [heq, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ M x := hscale
  refine ⟨M, hMemM, fun x => ENNReal.toReal_nonneg, ae_all_iff.mpr hMajor, ?_⟩
  change (eLpNorm M P volume).toReal ≤ B * (eLpNorm g P volume).toReal
  calc
    _ ≤ (ENNReal.ofReal B * eLpNorm g P volume).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top).ne hNormM
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB]

theorem roughSquare_positive_maximal_stage
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq : 1 < q)
    (hMax : ∀ s : ℝ, q < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hp : 1 < p) (hr : |p⁻¹ - (2 : ℝ)⁻¹| < (2*q)⁻¹) :
    ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b p B := by
  obtain ⟨B, hB, hbound⟩ := roughSquare_sigma_maximal_stage_norm hSupp hσ hb hβ hq hMax hp hr
  refine ⟨B, hB, geometricAdjointMaximalBound_of_sigmaLpMaximal hp hB ?_ hbound⟩
  obtain ⟨K, hK, hfull⟩ := roughSquare_full_stage_bound_all hSupp hσ hb hβ hq hMax hp hr
  intro F
  exact roughSquare_sigma_sup_finite hSupp hp hb F (hfull F).1

#print axioms roughSquare_positive_maximal_stage
#print axioms geometricAdjointMaximalBound_of_sigmaLpMaximal
end
end FractionalPrimes.Literature.JSW
end
