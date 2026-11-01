module

public import FractionalPrimes.Literature.JSW.PositiveMaximalSourceAdapters

/-!
# Geometric source maximal majorants for JSW positivity

This module supplies the finite-family majorant for geometric dilates of the
probability measure and starts the corresponding smooth-density adapter.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The initial-square positive maximal theorem gives the reflected
geometric-scale AE majorant needed for a finite family of probability
averages. The scalar test is an arbitrary `L^q` representative; the
representative-transfer lemma handles its values on singular scale measures. -/
theorem countableGeometricSigmaPositiveMaximalBound
    {ι : Type*} [Countable ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (hq : 2 < q)
    (κ : ι → ℤ) (g : ℝ → ℝ)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    ∃ M : ℝ → ℝ,
      MemLp M (ENNReal.ofReal q) volume ∧
      (∀ x, 0 ≤ M x) ∧
      (∀ᵐ x ∂volume, ∀ i,
        (∫ y, g (x + y) ∂Measure.map (fun y : ℝ => b ^ κ i * y) σ) ≤ M x) ∧
      lpNorm M (ENNReal.ofReal q) volume ≤
        weakTypeInterpolationStrongTwoInfinityConstant q
          (initialSquareSigmaPositiveMaximalB2 β D b) *
        lpNorm g (ENNReal.ofReal q) volume := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal q
  letI : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ q)⟩
  let g' : ℝ → ℝ := hg.aestronglyMeasurable.mk g
  have hgRep : g =ᵐ[volume] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hg'Strong : StronglyMeasurable g' :=
    hg.aestronglyMeasurable.stronglyMeasurable_mk
  have hg'Mem : MemLp g' P volume := by
    apply hg.congr_norm hg'Strong.aestronglyMeasurable
    filter_upwards [hgRep] with x hx
    simp [hx]
  let fC : ℝ → ℂ := fun x => (g' x : ℂ)
  have hfCStrong : StronglyMeasurable fC := by
    exact Complex.continuous_ofReal.comp_stronglyMeasurable hg'Strong
  have hfCMem : MemLp fC P volume := by
    apply hg'Mem.congr_norm hfCStrong.aestronglyMeasurable
    filter_upwards [] with x
    simp [fC, Real.norm_eq_abs]
  have hfCMeas : Measurable fC := hfCStrong.measurable
  let F : Lp ℂ P volume := hfCMem.toLp fC
  have hF : (F : ℝ → ℂ) =ᵐ[volume] fC := MemLp.coeFn_toLp hfCMem
  let σref : Measure ℝ := Measure.map Neg.neg σ
  haveI : IsProbabilityMeasure σref := inferInstance
  have hSuppRef : σref.support ⊆ Set.Icc (-(1 : ℝ)) 1 := by
    intro x hx
    have hxopen : ∀ U, x ∈ U → IsOpen U → 0 < σref U := by
      rw [Measure.support_eq_forall_isOpen] at hx
      exact hx
    have hxpre : -x ∈ σ.support := by
      rw [Measure.support_eq_forall_isOpen]
      intro U hU hUopen
      have hpreopen : IsOpen (Neg.neg ⁻¹' U) := hUopen.preimage continuous_neg
      have hxpre : x ∈ Neg.neg ⁻¹' U := by simpa using hU
      have hpos := hxopen (Neg.neg ⁻¹' U) hxpre hpreopen
      rw [Measure.map_apply (by fun_prop) hpreopen.measurableSet] at hpos
      simpa [σref] using hpos
    rcases Set.mem_Icc.mp (hSupp hxpre) with ⟨hlo, hhi⟩
    constructor <;> linarith
  have hsplit := measureSplitting σ hSupp β hβ D hdecay
  have hσref : MeasureSplittingBounds σref β D := by
    simpa [σref] using hsplit.2
  have hdom := initialSquareSigmaRawPositiveScale_le_rawMax_ae_of_memLp
    hSuppRef hσref hb hβ hq F fC hfCMeas hfCMem hF
  let M : ℝ → ℝ := initialSquareSigmaRawPositiveMaximal σref b fC
  have hMMeas : Measurable M :=
    measurable_initialSquareSigmaRawPositiveMaximal σref b fC hfCMeas
  have hMNonneg (x : ℝ) : 0 ≤ M x := by
    exact ENNReal.toReal_nonneg
  have hSource := initialSquareSigmaRawPositiveMaximalLp_bound_both_reflections
    hSupp hdecay hb hβ hq fC hfCMeas hfCMem
  have hMBound : eLpNorm M P volume ≤
      ENNReal.ofReal
        (weakTypeInterpolationStrongTwoInfinityConstant q
          (initialSquareSigmaPositiveMaximalB2 β D b)) *
        eLpNorm fC P volume := by
    simpa [M, P] using hSource.2
  have hMmem : MemLp M P volume := by
    calc
      eLpNorm M P volume ≤
          ENNReal.ofReal
            (weakTypeInterpolationStrongTwoInfinityConstant q
              (initialSquareSigmaPositiveMaximalB2 β D b)) *
            eLpNorm fC P volume := hMBound
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfCMem.eLpNorm_lt_top
  have hconstantNonneg : 0 ≤
      weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b) := by
    have hbase : 0 ≤ q / (q - 2) := by
      apply div_nonneg
      · linarith
      · linarith
    have hA : 0 ≤ initialSquareSigmaPositiveMaximalB2 β D b :=
      initialSquareSigmaPositiveMaximalB2_nonneg hb hβ
    dsimp [weakTypeInterpolationStrongTwoInfinityConstant]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hbase _))
      (Real.rpow_nonneg hA _)
  have hNormC : eLpNorm fC P volume = eLpNorm g P volume := by
    have hnormEq : (fun x : ℝ => ‖fC x‖) =ᵐ[volume]
        fun x => ‖g x‖ := by
      filter_upwards [hgRep] with x hx
      simp [fC, hx, Real.norm_eq_abs]
    rw [← eLpNorm_norm fC hfCStrong.aestronglyMeasurable,
      ← eLpNorm_norm g hg.aestronglyMeasurable]
    exact eLpNorm_congr_ae hnormEq
  have hMNorm : lpNorm M P volume ≤
      weakTypeInterpolationStrongTwoInfinityConstant q
        (initialSquareSigmaPositiveMaximalB2 β D b) * lpNorm g P volume := by
    dsimp [lpNorm]
    calc
      (eLpNorm M P volume).toReal ≤
          (ENNReal.ofReal
            (weakTypeInterpolationStrongTwoInfinityConstant q
              (initialSquareSigmaPositiveMaximalB2 β D b)) *
            eLpNorm fC P volume).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            hfCMem.eLpNorm_lt_top).ne hMBound
      _ = weakTypeInterpolationStrongTwoInfinityConstant q
            (initialSquareSigmaPositiveMaximalB2 β D b) *
          (eLpNorm g P volume).toReal := by
            simp [hNormC, ENNReal.toReal_mul, hconstantNonneg]
  have hMajor (i : ι) : ∀ᵐ x ∂volume,
      (∫ y, g (x + y) ∂Measure.map (fun y : ℝ => b ^ κ i * y) σ) ≤ M x := by
    let μ : Measure ℝ := Measure.map (fun y : ℝ => b ^ κ i * y) σ
    haveI : IsProbabilityMeasure μ := inferInstance
    let μneg : Measure ℝ := Measure.map Neg.neg μ
    haveI : IsProbabilityMeasure μneg := inferInstance
    have hIntNeg : ∀ᵐ x ∂volume,
        Integrable (fun z : ℝ => fC (x - z)) μneg := by
      exact integrable_translation_ae_of_memLp hq μneg fC hfCMem hfCStrong
    have hIntPlus : ∀ᵐ x ∂volume,
        Integrable (fun y : ℝ => g' (x + y)) μ := by
      filter_upwards [hIntNeg] with x hx
      have hsm : AEStronglyMeasurable
          (fun z : ℝ => fC (x - z)) μneg :=
        (hfCStrong.comp_measurable (by fun_prop)).aestronglyMeasurable
      have hmap : Integrable (fun y : ℝ => fC (x + y)) μ := by
        simpa [Function.comp_def] using
          (integrable_map_measure hsm (by fun_prop : AEMeasurable Neg.neg μ)).mp hx
      have hreal : Integrable
          (fun y : ℝ => Complex.re (fC (x + y))) μ :=
        Complex.reCLM.integrable_comp hmap
      simpa [fC] using hreal
    have htransfer := integral_add_translation_congr_ae μ g g' hgRep
    have hscaleDom := hdom (κ i)
    filter_upwards [hIntPlus, htransfer, hscaleDom] with x hxInt hxTransfer hxDom
    have hAbsInt : Integrable (fun y : ℝ => |g' (x + y)|) μ := by
      have h := hxInt.norm
      simpa [Real.norm_eq_abs] using h
    have hIntegralLe :
        (∫ y, g' (x + y) ∂μ) ≤ ∫ y, |g' (x + y)| ∂μ :=
      integral_mono_ae hxInt hAbsInt
        (ae_of_all μ fun y => le_abs_self (g' (x + y)))
    have hscaleEq :
        (∫ y, |g' (x + y)| ∂μ) =
          initialSquareSigmaRawPositiveScale σref b (κ i) fC x := by
      have h := initialSquare_reflectedScale_integral_eq_rawPositiveScale
        (σ := σ) hb (κ i) (fun y : ℝ => |g' y|)
        (fun _ => abs_nonneg _) x
      simpa [μ, σref, fC, initialSquareSigmaRawPositiveScale,
        Real.norm_eq_abs, abs_abs] using h
    calc
      (∫ y, g (x + y) ∂μ) = ∫ y, g' (x + y) ∂μ := hxTransfer
      _ ≤ ∫ y, |g' (x + y)| ∂μ := hIntegralLe
      _ = initialSquareSigmaRawPositiveScale σref b (κ i) fC x := hscaleEq
      _ ≤ M x := hxDom
  refine ⟨M, hMmem, hMNonneg, ?_, hMNorm⟩
  exact ae_all_iff.mpr hMajor


theorem finiteGeometricSigmaPositiveMaximalBound
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    (hb : 1 < b) (hβ : 0 < β) (hq : 2 < q)
    (κ : ι → ℤ) (g : ℝ → ℝ)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    ∃ M : ℝ → ℝ,
      MemLp M (ENNReal.ofReal q) volume ∧
      (∀ x, 0 ≤ M x) ∧
      (∀ᵐ x ∂volume, ∀ i,
        (∫ y, g (x + y) ∂Measure.map (fun y : ℝ => b ^ κ i * y) σ) ≤ M x) ∧
      lpNorm M (ENNReal.ofReal q) volume ≤
        weakTypeInterpolationStrongTwoInfinityConstant q
          (initialSquareSigmaPositiveMaximalB2 β D b) *
        lpNorm g (ENNReal.ofReal q) volume := by
  exact countableGeometricSigmaPositiveMaximalBound hSupp hdecay hb hβ hq κ g hg

#print axioms finiteGeometricSigmaPositiveMaximalBound

end

end FractionalPrimes.Literature.JSW

end
