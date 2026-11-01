module

public import FractionalPrimes.Literature.JSW.SmoothDyadicScalarOperatorPairing
public import FractionalPrimes.Literature.JSW.FiniteEuclideanLpPairing
public import FractionalPrimes.Literature.JSW.SmoothDyadicForwardOffSupport

/-! The actual finite smooth error operators are an adjoint pair with the exact L2 norm. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem smoothDyadic_finite_operator_pairing
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ)
    (F : Lp ℂ 2 (volume : Measure ℝ))
    (G : Lp (EuclideanSpace ℂ {k : ℤ // k ∈ K}) 2 (volume : Measure ℝ)) :
    (∫ x, inner ℝ ((smoothDyadicFiniteOperatorAt (P := 2) (by norm_num) hSupp a ha K F :
        ℝ → EuclideanSpace ℂ {k : ℤ // k ∈ K}) x) (G x) ∂volume) =
      ∫ x, inner ℝ (F x) ((smoothDyadicFiniteAdjointOperatorAt (P := 2) (by norm_num)
        hSupp a ha K G : ℝ → ℂ) x) ∂volume := by
  classical
  let T := fun k : {k : ℤ // k ∈ K} =>
    smoothDyadicErrorOperatorAt (P := 2) (by norm_num) hSupp (jswTau a ha k.1) (jswM a ha k.1)
  let S := fun k : {k : ℤ // k ∈ K} =>
    smoothDyadicReflectedErrorOperatorAt (P := 2) (by norm_num) hSupp (jswTau a ha k.1) (jswM a ha k.1)
  have hp (k : {k : ℤ // k ∈ K}) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
      (∫ x, inner ℝ ((T k f : ℝ → ℂ) x) (g x) ∂volume) =
        ∫ x, inner ℝ (f x) ((S k g : ℝ → ℂ) x) ∂volume :=
    smoothDyadic_scalar_operatorAt_pairing (P := 2) (by norm_num) hSupp
      (zpow_pos (by linarith [jswB_gt_one ha]) _) _ f g
  have h := finiteEuclideanLp_integral_pairing T S hp F G
  have hTF : smoothDyadicFiniteOperatorAt (P := 2) (by norm_num) hSupp a ha K F =
      finiteVectorLpAssembly 2 (fun k => T k F) := by
    change finiteVectorLpAssembly 2 (ContinuousLinearMap.pi T F) = _
    congr 1
  rw [hTF]
  simpa only [smoothDyadicFiniteAdjointOperatorAt,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    T, S] using h

theorem smoothDyadicFiniteAdjointOperator_norm_eq
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ) :
    ‖smoothDyadicFiniteAdjointOperatorAt (P := 2) (by norm_num) hSupp a ha K‖ =
      ‖smoothDyadicFiniteOperatorAt (P := 2) (by norm_num) hSupp a ha K‖ := by
  letI : InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure ℝ)) := MeasureTheory.L2.innerProductSpace
  letI : InnerProductSpace ℝ (Lp (EuclideanSpace ℂ {k : ℤ // k ∈ K}) 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  let T := smoothDyadicFiniteOperatorAt (P := 2) (by norm_num) hSupp a ha K
  let S := smoothDyadicFiniteAdjointOperatorAt (P := 2) (by norm_num) hSupp a ha K
  have hEq : T = S.adjoint := (ContinuousLinearMap.eq_adjoint_iff T S).mpr (by
    intro F G
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    exact smoothDyadic_finite_operator_pairing hSupp ha K F G)
  change ‖S‖ = ‖T‖
  rw [hEq]
  exact (ContinuousLinearMap.adjoint.norm_map S).symm

theorem smoothDyadicFiniteAdjointOperator_norm_le
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ) :
    ‖smoothDyadicFiniteAdjointOperatorAt (P := 2) (by norm_num) hSupp a ha K‖ ≤
      smoothDyadicSquareConstant a ha := by
  rw [smoothDyadicFiniteAdjointOperator_norm_eq hSupp ha K]
  exact smoothDyadicFiniteOperatorAt_opNorm_le (P := 2) (by norm_num) hSupp ha K

#print axioms smoothDyadic_finite_operator_pairing
#print axioms smoothDyadicFiniteAdjointOperator_norm_le
end
end FractionalPrimes.Literature.JSW
end
