module

public import FractionalPrimes.Literature.JSW.SmoothPsiReflectedAtom
public import FractionalPrimes.Literature.JSW.SmoothDyadicAtomMajorantIntegral

/-! The exact source adjoint atom sum: coordinate L1 bounds precede scale summation. -/
@[expose] public section
open MeasureTheory
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothDyadicRawAdjointError
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (a : ℝ) (ha : 0 < a)
    (K : Finset ℤ) (u : {k : ℤ // k ∈ K} → ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k, (smoothPsiReflectedConvolution σ (jswTau a ha k.1) (u k) x-
    dyadicAverage (jswM a ha k.1) (u k) x)

theorem smoothDyadicRawAdjointError_atom_eq
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ) (m j : ℤ)
    (u : {k : ℤ // k ∈ K} → ℝ → ℂ)
    (hmean : ∀ k, ∫ y, u k y ∂volume = 0)
    (hsupp : ∀ k y, y ∉ dyadicInterval m j → u k y = 0)
    {x : ℝ} (hx : x ∉ dyadicNinefoldInterval m j) :
    smoothDyadicRawAdjointError σ a ha K u x =
      ∑ k ∈ Finset.univ.filter (fun k : {k : ℤ // k ∈ K} => (2 : ℝ)^m < jswTau a ha k.1),
        smoothPsiReflectedConvolution σ (jswTau a ha k.1) (u k) x := by
  classical
  unfold smoothDyadicRawAdjointError
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dyadicAverage_meanZeroAtom_zero_off_ninefold (hmean k) m j (hsupp k)
    (jswM a ha k.1) hx, sub_zero]
  split_ifs with hlarge
  · rfl
  · exact smoothPsiReflectedConvolution_atom_smallScale_zero hSupp
      (zpow_pos (by linarith [jswB_gt_one ha]) _) m j (le_of_not_gt hlarge) (hsupp k) hx

theorem smoothDyadicRawAdjointError_atom_L1
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ) (m j : ℤ)
    (u : {k : ℤ // k ∈ K} → ℝ → ℂ)
    (hu : ∀ k, Integrable (u k) volume)
    (hmean : ∀ k, ∫ y, u k y ∂volume = 0)
    (hsupp : ∀ k y, y ∉ dyadicInterval m j → u k y = 0)
    {U : ℝ} (hU : 0 ≤ U) (hcoord : ∀ k, lpNorm (u k) 1 volume ≤ U) :
    IntegrableOn (fun x => ‖smoothDyadicRawAdjointError σ a ha K u x‖)
      (dyadicNinefoldInterval m j)ᶜ volume ∧
    (∫ x in (dyadicNinefoldInterval m j)ᶜ,
      ‖smoothDyadicRawAdjointError σ a ha K u x‖ ∂volume) ≤
      smoothDyadicOffSupportConstant a ha*U := by
  classical
  let S := Finset.univ.filter (fun k : {k : ℤ // k ∈ K} => (2 : ℝ)^m < jswTau a ha k.1)
  let V := fun x => ∑ k ∈ S, smoothPsiReflectedConvolution σ (jswTau a ha k.1) (u k) x
  let M := fun x => ∑ k ∈ S, ‖smoothPsiReflectedConvolution σ (jswTau a ha k.1) (u k) x‖
  let E := (dyadicNinefoldInterval m j)ᶜ
  have hτ (k : ℤ) : 0 < jswTau a ha k := zpow_pos (by linarith [jswB_gt_one ha]) _
  have hcomp (k : {k : ℤ // k ∈ K}) := smoothPsiReflectedConvolution_atom_L1_bound hSupp
    (hτ k.1) m j (hu k) (hmean k) (hsupp k)
  have hVInt : Integrable V volume := integrable_finset_sum S (fun k _ => (hcomp k).1)
  have hMInt : Integrable M volume := integrable_finset_sum S (fun k _ => (hcomp k).1.norm)
  have hEq : (fun x => ‖smoothDyadicRawAdjointError σ a ha K u x‖) =ᵐ[volume.restrict E]
      (fun x => ‖V x‖) := by
    filter_upwards [ae_restrict_mem (show MeasurableSet E from measurableSet_Ico.compl)] with x hx
    rw [smoothDyadicRawAdjointError_atom_eq hSupp ha K m j u hmean hsupp hx]
  refine ⟨hVInt.norm.integrableOn.congr hEq.symm, ?_⟩
  rw [integral_congr_ae hEq]
  calc
    _ ≤ ∫ x in E, M x ∂volume := integral_mono hVInt.norm.integrableOn hMInt.integrableOn
      (fun x => norm_sum_le S _)
    _ ≤ ∫ x, M x ∂volume := integral_mono_measure Measure.restrict_le_self
      (ae_of_all volume fun x => Finset.sum_nonneg fun k _ => norm_nonneg _) hMInt
    _ = ∑ k ∈ S, ∫ x, ‖smoothPsiReflectedConvolution σ (jswTau a ha k.1) (u k) x‖ ∂volume :=
      integral_finset_sum S (fun k _ => (hcomp k).1.norm)
    _ ≤ ∑ k ∈ S, ((2 : ℝ)^m/(2*jswTau a ha k.1))*lpNorm (deriv φ) 1 volume*U := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← lpNorm_one_eq_integral_norm (hcomp k).1.aestronglyMeasurable]
      exact (hcomp k).2.trans (mul_le_mul_of_nonneg_left (hcoord k)
        (mul_nonneg (div_nonneg (zpow_pos (by norm_num) _).le
          (mul_nonneg (by norm_num) (hτ k.1).le)) lpNorm_nonneg))
    _ = (lpNorm (deriv φ) 1 volume/2)*(∑ k ∈ S, (2 : ℝ)^m/jswTau a ha k.1)*U := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ smoothDyadicOffSupportConstant a ha*U := by
      apply mul_le_mul_of_nonneg_right _ hU
      apply mul_le_mul_of_nonneg_left _ (div_nonneg lpNorm_nonneg (by norm_num))
      have hsum : (∑ k ∈ S, (2 : ℝ)^m/jswTau a ha k.1) =
          ∑ k ∈ K.filter (fun k => (2 : ℝ)^m < jswTau a ha k), (2 : ℝ)^m/jswTau a ha k := by
        dsimp [S]
        rw [Finset.sum_filter, Finset.sum_filter]
        exact Finset.sum_attach K (fun k : ℤ =>
          if (2 : ℝ)^m < jswTau a ha k then (2 : ℝ)^m/jswTau a ha k else 0)
      rw [hsum]
      exact jswTau_finite_largeScale_reciprocal_sum ha (zpow_pos (by norm_num) _) K

#print axioms smoothDyadicRawAdjointError_atom_L1
end
end FractionalPrimes.Literature.JSW
end
