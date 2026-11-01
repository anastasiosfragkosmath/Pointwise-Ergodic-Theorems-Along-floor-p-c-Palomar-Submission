module

public import FractionalPrimes.Literature.JSW.SmoothDyadicFiniteAdjointPairing

/-! The actual finite smooth error operator on every finite exponent p>1. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothDyadicFiniteLpOperator
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    (a : ℝ) (ha : 0 < a) (K : Finset ℤ) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp (EuclideanSpace ℂ {k : ℤ // k ∈ K}) (ENNReal.ofReal p) (volume : Measure ℝ) := by
  classical
  exact (finiteVectorLpAssembly (ENNReal.ofReal p)).comp (ContinuousLinearMap.pi
    (fun k : {k : ℤ // k ∈ K} => smoothDyadicErrorLpOperator hSupp hp
      (jswTau a ha k.1) (jswM a ha k.1)))

theorem smoothDyadicFiniteLpOperator_ae_eq
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ)
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) (g : ℝ → ℂ)
    (hg : MemLp g (ENNReal.ofReal p) volume) (hF : (F : ℝ → ℂ) =ᵐ[volume] g) :
    (smoothDyadicFiniteLpOperator hSupp hp a ha K F : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K}) =ᵐ[volume]
      smoothDyadicRawFiniteError σ a ha K g := by
  classical
  have hrep (k : {k : ℤ // k ∈ K}) :
      (smoothDyadicErrorLpOperator hSupp hp (jswTau a ha k.1) (jswM a ha k.1) F : ℝ → ℂ) =ᵐ[volume]
        smoothDyadicRawError σ a ha k.1 g :=
    smoothDyadicErrorLpOperator_ae_eq_of_memLp hSupp hp _ _ F g hg hF
  have hvec := finiteVectorLpAssembly_ae_eq (ENNReal.ofReal p)
    (fun k : {k : ℤ // k ∈ K} => smoothDyadicErrorLpOperator hSupp hp
      (jswTau a ha k.1) (jswM a ha k.1) F)
  filter_upwards [hvec, ae_all_iff.mpr hrep] with x hx hi
  change (finiteVectorLpAssembly (ENNReal.ofReal p)
    (fun k : {k : ℤ // k ∈ K} => smoothDyadicErrorLpOperator hSupp hp
      (jswTau a ha k.1) (jswM a ha k.1) F) : ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K}) x = _ at hx ⊢
  rw [hx]
  ext k
  exact hi k

theorem smoothDyadicFiniteLpOperator_norm_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ)
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    ‖smoothDyadicFiniteLpOperator hSupp hp a ha K F‖ ≤
      weakTypeFromOffSupportStrongConstant p (smoothDyadicSquareConstant a ha)
        (smoothDyadicOffSupportConstant a ha)*‖F‖ := by
  classical
  let T := smoothDyadicFiniteOperatorAt (P := 2) (by norm_num) hSupp a ha K
  let S := smoothDyadicFiniteAdjointOperatorAt (P := 2) (by norm_num) hSupp a ha K
  obtain ⟨U,hbound,hagree⟩ := weakTypeFromOffSupport_extension_agrees_on_Lp_inter_L2 T
    (smoothDyadicFiniteOperatorAt_opNorm_le (P := 2) (by norm_num) hSupp ha K)
    (smoothDyadicFiniteOperator_offSupport hSupp ha K) S
    (smoothDyadic_finite_operator_pairing hSupp ha K)
    (smoothDyadicFiniteAdjointOperator_norm_le hSupp ha K)
    (smoothDyadicFiniteAdjointOperator_offSupport hSupp ha K) p hp
  have hEq : U = smoothDyadicFiniteLpOperator hSupp hp a ha K :=
    lpContinuousLinearMap_eq_of_agree_inter_L2 ENNReal.ofReal_ne_top U _ (by
      intro f hf₂
      apply Lp.ext
      have hL₂ := smoothDyadicFiniteOperatorAt_ae_eq (P := 2) (by norm_num) hSupp ha K
        (hf₂.toLp (f : ℝ → ℂ)) (f : ℝ → ℂ) hf₂ hf₂.coeFn_toLp
      have hpRep := smoothDyadicFiniteLpOperator_ae_eq hSupp hp ha K f (f : ℝ → ℂ)
        (Lp.memLp f) Filter.EventuallyEq.rfl
      exact (hagree f hf₂).trans (hL₂.trans hpRep.symm))
  rw [← hEq]
  exact hbound F

#print axioms smoothDyadicFiniteLpOperator_norm_bound
end
end FractionalPrimes.Literature.JSW
end
