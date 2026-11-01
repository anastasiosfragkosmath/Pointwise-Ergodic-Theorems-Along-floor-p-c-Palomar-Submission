module

public import FractionalPrimes.Literature.JSW.SmoothPsiReflectedIdentity
public import FractionalPrimes.Literature.JSW.SmoothDyadicFiniteOperator
public import FractionalPrimes.Literature.JSW.SmoothDyadicAdjointVectorAtom

/-! Actual finite reflected error operators and their source representatives. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem lpComplexSigmaConvolution_ae_eq_jswConvolution_of_memLp
    {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (g : ℝ → ℂ) (hg : MemLp g (ENNReal.ofReal p) volume)
    (hF : (F : ℝ → ℂ) =ᵐ[volume] g) :
    (lpComplexMeasureConvolution (ENNReal.ofReal p)
      (initialSquareSigmaComplexMeasure μ) F : ℝ → ℂ) =ᵐ[volume] jswConvolution μ g := by
  let g' := hg.aestronglyMeasurable.mk g
  have hgg' : g =ᵐ[volume] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hg' : Measurable g' := hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgm' := (memLp_congr_ae hgg').mp hg
  have hrep := lpComplexSigmaConvolution_ae_eq_jswConvolution hp μ F g' hg' hgm' (hF.trans hgg')
  exact hrep.trans (integral_sub_translation_congr_ae μ g' g hgg'.symm)

def smoothPsiReflectedLpOperator
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (τ : ℝ) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  let μ := Measure.map (Neg.neg : ℝ → ℝ)
    (Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ))
  letI : IsProbabilityMeasure (Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)) :=
    initialSquarePsiDilateProbabilityMeasure_isProbability hSupp τ
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let μc := initialSquareSigmaComplexMeasure μ
  letI : IsFiniteMeasure μc.variation := by
    dsimp [μc]
    rw [initialSquareSigmaComplexMeasure_variation_eq]
    infer_instance
  exact lpComplexMeasureConvolutionCLM (ENNReal.ofReal p) ENNReal.ofReal_ne_top μc

def smoothDyadicReflectedErrorLpOperator
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (τ : ℝ) (m : ℤ) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
  smoothPsiReflectedLpOperator hSupp p τ-(dyadicAverageLpCLM hp m).restrictScalars ℝ

theorem smoothDyadicReflectedErrorLpOperator_ae_eq
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) {τ : ℝ} (hτ : 0 < τ) (m : ℤ)
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) (g : ℝ → ℂ)
    (hg : MemLp g (ENNReal.ofReal p) volume) (hF : (F : ℝ → ℂ) =ᵐ[volume] g) :
    (smoothDyadicReflectedErrorLpOperator hSupp hp τ m F : ℝ → ℂ) =ᵐ[volume]
      (fun x => smoothPsiReflectedConvolution σ τ g x-dyadicAverage m g x) := by
  let μ := Measure.map (Neg.neg : ℝ → ℝ)
    (Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ))
  letI : IsProbabilityMeasure (Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)) :=
    initialSquarePsiDilateProbabilityMeasure_isProbability hSupp τ
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hconv := lpComplexSigmaConvolution_ae_eq_jswConvolution_of_memLp hp μ F g hg hF
  have havg := dyadicAverageLpCLM_coeFn hp m F
  have hsub := Lp.coeFn_sub (smoothPsiReflectedLpOperator hSupp p τ F) (dyadicAverageLpCLM hp m F)
  filter_upwards [hconv, havg, hsub] with x hc ha hs
  change (smoothPsiReflectedLpOperator hSupp p τ F-dyadicAverageLpCLM hp m F :
    Lp ℂ (ENNReal.ofReal p) volume) x = _
  change (smoothPsiReflectedLpOperator hSupp p τ F : ℝ → ℂ) x = jswConvolution μ g x at hc
  rw [hs, Pi.sub_apply, hc, ha, dyadicAverage_eq_of_ae_eq_jump hF m x,
    smoothPsiReflectedConvolution_eq_map_neg hτ]

def smoothDyadicReflectedErrorOperatorAt
    {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P = ENNReal.ofReal (2 : ℝ))
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (τ : ℝ) (m : ℤ) :
    Lp ℂ P (volume : Measure ℝ) →L[ℝ] Lp ℂ P (volume : Measure ℝ) := by
  subst P
  exact smoothDyadicReflectedErrorLpOperator hSupp (p := 2) (by norm_num) τ m

def smoothDyadicFiniteAdjointOperatorAt
    {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P = ENNReal.ofReal (2 : ℝ))
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (a : ℝ) (ha : 0 < a) (K : Finset ℤ) :
    Lp (EuclideanSpace ℂ {k : ℤ // k ∈ K}) P (volume : Measure ℝ) →L[ℝ]
      Lp ℂ P (volume : Measure ℝ) := by
  classical
  exact ∑ k : {k : ℤ // k ∈ K},
    (smoothDyadicReflectedErrorOperatorAt hP hSupp (jswTau a ha k.1) (jswM a ha k.1)).comp
      ((PiLp.proj 2 (fun _ : {k : ℤ // k ∈ K} => ℂ) k :
        EuclideanSpace ℂ {k : ℤ // k ∈ K} →L[ℝ] ℂ).compLpL P volume)

theorem smoothDyadicFiniteAdjointOperatorAt_ae_eq
    {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P = ENNReal.ofReal (2 : ℝ))
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) {a : ℝ} (ha : 0 < a) (K : Finset ℤ)
    (F : Lp (EuclideanSpace ℂ {k : ℤ // k ∈ K}) P (volume : Measure ℝ))
    (g : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K})
    (hg : MemLp g P volume) (hF : (F : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K}) =ᵐ[volume] g) :
    (smoothDyadicFiniteAdjointOperatorAt hP hSupp a ha K F : ℝ → ℂ) =ᵐ[volume]
      smoothDyadicRawAdjointError σ a ha K (fun k y => g y k) := by
  classical
  let L := fun k : {k : ℤ // k ∈ K} =>
    (PiLp.proj 2 (fun _ : {k : ℤ // k ∈ K} => ℂ) k :
      EuclideanSpace ℂ {k : ℤ // k ∈ K} →L[ℝ] ℂ)
  let v := fun k : {k : ℤ // k ∈ K} =>
    smoothDyadicReflectedErrorOperatorAt hP hSupp (jswTau a ha k.1) (jswM a ha k.1)
      ((L k).compLpL P volume F)
  have hcoord (k : {k : ℤ // k ∈ K}) :
      (v k : ℝ → ℂ) =ᵐ[volume] (fun x =>
        smoothPsiReflectedConvolution σ (jswTau a ha k.1) (fun y => g y k) x-
          dyadicAverage (jswM a ha k.1) (fun y => g y k) x) := by
    have hproj := ((L k).coeFn_compLpL F).trans (hF.fun_comp (L k))
    have hgm : MemLp (fun y => g y k) P volume := (L k).comp_memLp' hg
    subst P
    exact smoothDyadicReflectedErrorLpOperator_ae_eq hSupp (p := 2) (by norm_num)
      (zpow_pos (by linarith [jswB_gt_one ha]) _) _ _ _ hgm hproj
  have hsum := Lp.coeFn_finsetSum Finset.univ v
  filter_upwards [hsum, ae_all_iff.mpr hcoord] with x hx hc
  have heq : smoothDyadicFiniteAdjointOperatorAt hP hSupp a ha K F = ∑ k, v k := by
    simp only [smoothDyadicFiniteAdjointOperatorAt, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply, v, L]
  rw [heq]
  rw [hx]
  simp only [Finset.sum_apply, smoothDyadicRawAdjointError]
  exact Finset.sum_congr rfl fun k _ => hc k

theorem smoothDyadicFiniteAdjointOperator_offSupport
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ) :
    weakCZOffSupportBound
      (smoothDyadicFiniteAdjointOperatorAt (P := 2) (by norm_num) hSupp a ha K)
      (smoothDyadicOffSupportConstant a ha) := by
  intro u m j hu₁ hu₂ hmean hsupp
  obtain ⟨hInt,hbound⟩ := smoothDyadicRawAdjointError_vector_atom_L1 hSupp ha K m j
    (memLp_one_iff_integrable.mp hu₁) hmean hsupp
  have hrep := smoothDyadicFiniteAdjointOperatorAt_ae_eq (P := 2) (by norm_num) hSupp ha K
    (hu₂.toLp u) u hu₂ hu₂.coeFn_toLp
  have hn : (fun x => ‖(smoothDyadicFiniteAdjointOperatorAt (P := 2) (by norm_num)
      hSupp a ha K (hu₂.toLp u) : ℝ → ℂ) x‖) =ᵐ[volume.restrict (dyadicNinefoldInterval m j)ᶜ]
      (fun x => ‖smoothDyadicRawAdjointError σ a ha K (fun k y => u y k) x‖) :=
    ae_restrict_of_ae (hrep.fun_comp norm)
  refine ⟨hInt.congr hn.symm, ?_⟩
  rw [integral_congr_ae hn]
  exact hbound

#print axioms smoothDyadicFiniteAdjointOperator_offSupport
end
end FractionalPrimes.Literature.JSW
end
