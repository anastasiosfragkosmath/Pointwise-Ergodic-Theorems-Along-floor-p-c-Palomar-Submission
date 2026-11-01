module

public import FractionalPrimes.Literature.JSW.SmoothDyadicFiniteLpOperator

/-! Full smooth-to-dyadic square comparison with the approved weak-CZ constant. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothDyadicSquareLpConstant (p a : ℝ) (ha : 0 < a) : ℝ :=
  weakTypeFromOffSupportStrongConstant p (smoothDyadicSquareConstant a ha)
    (smoothDyadicOffSupportConstant a ha)

theorem smoothDyadicSquareLpConstant_nonneg {p a : ℝ} (hp : 1 < p) (ha : 0 < a) :
    0 ≤ smoothDyadicSquareLpConstant p a ha := by
  have hA := smoothDyadicSquareConstant_nonneg ha
  have hB := smoothDyadicOffSupportConstant_nonneg ha
  unfold smoothDyadicSquareLpConstant weakTypeFromOffSupportStrongConstant
  split_ifs with hp₂ hpEq
  · unfold weakTypeInterpolationConstant
    positivity
  · exact hA
  · have hpgt : 2 < p := lt_of_le_of_ne (le_of_not_gt hp₂) (Ne.symm hpEq)
    have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
    have hq1 := hpq.symm.lt
    have hq2 : p.conjExponent < 2 := by
      have hqpos := hpq.symm.pos
      have hprod : p = p.conjExponent*(p-1) := by
        have hdiv := hpq.div_conj_eq_sub_one
        field_simp [ne_of_gt hqpos] at hdiv
        nlinarith
      by_contra hnot
      have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) (sub_nonneg.mpr hp.le)
      nlinarith
    unfold weakTypeInterpolationConstant
    positivity

theorem smoothDyadic_finite_output_vector_norm
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    {a : ℝ} (ha : 0 < a) (K : Finset ℤ)
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    let v := fun k : ℤ => smoothDyadicErrorLpOperator hSupp hp
      (jswTau a ha k) (jswM a ha k) F
    lpNorm (fun x => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ K} =>
      (v k.1 : ℝ → ℂ) x)) (ENNReal.ofReal p) volume ≤
        smoothDyadicSquareLpConstant p a ha*‖F‖ := by
  classical
  let v := fun k : ℤ => smoothDyadicErrorLpOperator hSupp hp
    (jswTau a ha k) (jswM a ha k) F
  have heq : smoothDyadicFiniteLpOperator hSupp hp a ha K F =
      finiteVectorLpAssembly (ENNReal.ofReal p) (fun k : {k : ℤ // k ∈ K} => v k.1) := by
    change finiteVectorLpAssembly (ENNReal.ofReal p) (ContinuousLinearMap.pi
      (fun k : {k : ℤ // k ∈ K} => smoothDyadicErrorLpOperator hSupp hp
        (jswTau a ha k.1) (jswM a ha k.1)) F) = _
    congr 1
  have hrep := finiteVectorLpAssembly_ae_eq (ENNReal.ofReal p)
    (fun k : {k : ℤ // k ∈ K} => v k.1)
  have hn := congrArg ENNReal.toReal (eLpNorm_congr_ae hrep (p := ENNReal.ofReal p))
  rw [← Lp.norm_def, ← heq] at hn
  change ‖smoothDyadicFiniteLpOperator hSupp hp a ha K F‖ = lpNorm _ _ _ at hn
  exact hn.symm.le.trans (smoothDyadicFiniteLpOperator_norm_bound hSupp hp ha K F)

/-- `lj:smooth-comparison`: the full actual square function, with the exact
source constant and almost-everywhere finite energy, for every finite p>1. -/
theorem smoothDyadicSquareBound
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {p : ℝ} (hp : 1 < p) {a : ℝ} (ha : 0 < a)
    (f : ℝ → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume) :
    let Q := fun x => Real.sqrt (smoothDyadicRawSquareEnergy σ a ha f x).toReal
    (∀ᵐ x ∂volume, smoothDyadicRawSquareEnergy σ a ha f x < ∞) ∧
    MemLp Q (ENNReal.ofReal p) volume ∧
    lpNorm Q (ENNReal.ofReal p) volume ≤
      smoothDyadicSquareLpConstant p a ha*lpNorm f (ENNReal.ofReal p) volume := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let F := hf.toLp f
  let v := fun k : ℤ => smoothDyadicErrorLpOperator hSupp hp
    (jswTau a ha k) (jswM a ha k) F
  let C := smoothDyadicSquareLpConstant p a ha
  have hC : 0 ≤ C := smoothDyadicSquareLpConstant_nonneg hp ha
  have hfull := roughSquare_full_energy_bound hp (mul_nonneg hC (norm_nonneg F)) v
    (fun K => smoothDyadic_finite_output_vector_norm hSupp hp ha K F)
  have hrep (k : ℤ) : (v k : ℝ → ℂ) =ᵐ[volume] smoothDyadicRawError σ a ha k f :=
    smoothDyadicErrorLpOperator_ae_eq_of_memLp hSupp hp _ _ F f hf hf.coeFn_toLp
  have he : (fun x => ∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)) =ᵐ[volume]
      smoothDyadicRawSquareEnergy σ a ha f := by
    filter_upwards [ae_all_iff.mpr hrep] with x hx
    apply tsum_congr
    intro k
    rw [hx k]
  have hnormF : ‖F‖ = lpNorm f (ENNReal.ofReal p) volume := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hf.coeFn_toLp)
  have hQ := he.fun_comp (fun z : ℝ≥0∞ => Real.sqrt z.toReal)
  have hbound : eLpNorm (fun x => Real.sqrt (smoothDyadicRawSquareEnergy σ a ha f x).toReal)
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (C*lpNorm f (ENNReal.ofReal p) volume) := by
    have hn := eLpNorm_congr_ae hQ (p := ENNReal.ofReal p)
    simp only [Function.comp_def] at hn
    rw [← hn]
    simpa only [hnormF] using hfull.2
  have hmem : MemLp (fun x => Real.sqrt (smoothDyadicRawSquareEnergy σ a ha f x).toReal)
      (ENNReal.ofReal p) volume := memLp_iff.mpr (hbound.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨?_, hmem, ?_⟩
  · filter_upwards [hfull.1, he] with x hx heq
    rw [← heq]
    exact hx
  · have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rw [ENNReal.toReal_ofReal (mul_nonneg hC lpNorm_nonneg)] at ht
    exact ht

#print axioms smoothDyadicSquareBound
#print axioms smoothDyadic_finite_output_vector_norm
end
end FractionalPrimes.Literature.JSW
end
