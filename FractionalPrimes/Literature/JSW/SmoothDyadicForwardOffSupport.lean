module

public import FractionalPrimes.Literature.JSW.SmoothDyadicAtomMajorantIntegral
public import FractionalPrimes.Literature.JSW.SmoothDyadicFiniteOperator

/-! The exact forward off-support criterion for the actual finite smooth error operator. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem smoothDyadic_raw_forward_offSupport
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ) (m j : ℤ) {u : ℝ → ℂ}
    (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume)
    (hmean : ∫ y, u y ∂volume = 0)
    (hsupp : ∀ y, y ∉ dyadicInterval m j → u y = 0) :
    IntegrableOn (fun x => ‖smoothDyadicRawFiniteError σ a ha K u x‖)
      (dyadicNinefoldInterval m j)ᶜ volume ∧
    (∫ x in (dyadicNinefoldInterval m j)ᶜ, ‖smoothDyadicRawFiniteError σ a ha K u x‖ ∂volume) ≤
      smoothDyadicOffSupportConstant a ha*(∫ x, ‖u x‖ ∂volume) := by
  classical
  letI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let V := smoothDyadicRawFiniteError σ a ha K u
  let S := K.filter (fun k => (2 : ℝ)^m < jswTau a ha k)
  let M := fun x => ∑ k ∈ S, ‖smoothPsiDensityConvolution σ (jswTau a ha k) u x‖
  let E := (dyadicNinefoldInterval m j)ᶜ
  have hu : Integrable u volume := memLp_one_iff_integrable.mp hu₁
  obtain ⟨hMInt,hMbound⟩ := smoothDyadic_atom_majorant_integral hSupp ha K m j hu hmean hsupp
  have hrep : (smoothDyadicFiniteOperatorAt (P := 2) (by norm_num) hSupp a ha K
      (hu₂.toLp u) : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K}) =ᵐ[volume] V :=
    smoothDyadicFiniteOperatorAt_ae_eq (by norm_num) hSupp ha K _ u hu₂ hu₂.coeFn_toLp
  have hVmeas : AEStronglyMeasurable V volume := (Lp.aestronglyMeasurable _).congr hrep
  have hEmeas : MeasurableSet E := measurableSet_Ico.compl
  have hpoint : ∀ᵐ x ∂volume.restrict E, ‖V x‖ ≤ M x := by
    filter_upwards [ae_restrict_mem hEmeas] with x hx
    exact smoothDyadicRawFiniteError_atom_norm_majorant hSupp ha K m j hmean hsupp hx
  have hVInt : IntegrableOn (fun x => ‖V x‖) E volume := by
    apply hMInt.integrableOn.mono' (hVmeas.norm.mono_measure Measure.restrict_le_self)
    filter_upwards [hpoint] with x hx
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hx
  refine ⟨hVInt, ?_⟩
  calc
    _ ≤ ∫ x in E, M x ∂volume := integral_mono_ae hVInt hMInt.integrableOn hpoint
    _ ≤ ∫ x, M x ∂volume := integral_mono_measure Measure.restrict_le_self
      (ae_of_all volume fun x => Finset.sum_nonneg fun k _ => norm_nonneg _) hMInt
    _ ≤ _ := hMbound

theorem smoothDyadicFiniteOperator_offSupport
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ) :
    weakCZOffSupportBound
      (smoothDyadicFiniteOperatorAt (P := 2) (by norm_num) hSupp a ha K)
      (smoothDyadicOffSupportConstant a ha) := by
  intro u m j hu₁ hu₂ hmean hsupp
  obtain ⟨hInt,hbound⟩ := smoothDyadic_raw_forward_offSupport hSupp ha K m j hu₁ hu₂ hmean hsupp
  have hrep := smoothDyadicFiniteOperatorAt_ae_eq (P := 2) (by norm_num) hSupp ha K
    (hu₂.toLp u) u hu₂ hu₂.coeFn_toLp
  have hnorm : (fun x => ‖(smoothDyadicFiniteOperatorAt (P := 2) (by norm_num) hSupp a ha K
      (hu₂.toLp u) : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K}) x‖) =ᵐ[volume.restrict (dyadicNinefoldInterval m j)ᶜ]
      (fun x => ‖smoothDyadicRawFiniteError σ a ha K u x‖) :=
    ae_restrict_of_ae (hrep.fun_comp norm)
  refine ⟨hInt.congr hnorm.symm, ?_⟩
  rw [integral_congr_ae hnorm]
  exact hbound

#print axioms smoothDyadicFiniteOperator_offSupport
#print axioms smoothDyadic_raw_forward_offSupport
end
end FractionalPrimes.Literature.JSW
end
