module

public import FractionalPrimes.Literature.JSW.SmoothDyadicAdjointOperator
public import FractionalPrimes.Literature.JSW.PositiveMaximalVectorBounds

/-! Fubini and dyadic self-adjointness identify each source scalar error pair. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem smoothDyadic_scalar_raw_adjoint_pairing
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (m : ℤ) {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫ x, (jswConvolution (Measure.map (fun z : ℝ => τ*z)
        (initialSquarePsiProbabilityMeasure σ)) f x-dyadicAverage m f x)*conj (g x) ∂volume) =
      ∫ x, f x*conj (smoothPsiReflectedConvolution σ τ g x-dyadicAverage m g x) ∂volume := by
  let μ := Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)
  letI : IsProbabilityMeasure μ := initialSquarePsiDilateProbabilityMeasure_isProbability hSupp τ
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) volume := by simpa using hg
  have hpq : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  obtain ⟨hLeft,hRight⟩ := integrable_translated_pair_products_of_memLp μ hpq f g hf' hg'
  have hpair := integral_jswConvolution_mul_conj_eq_adjoint μ f g hLeft hRight
  have hconvInt : Integrable (fun x => jswConvolution μ f x*conj (g x)) volume := by
    convert hLeft.integral_prod_left using 1
    funext x
    exact (integral_mul_const (conj (g x)) (fun y : ℝ => f (x-y))).symm
  have hrefInt : Integrable (fun x => f x*conj (smoothPsiReflectedConvolution σ τ g x)) volume := by
    convert hRight.integral_prod_left using 1
    funext x
    rw [smoothPsiReflectedConvolution_eq_plus hτ]
    change f x*conj (∫ t, g (x+t) ∂μ) = ∫ t, f x*conj (g (x+t)) ∂μ
    rw [← integral_conj, integral_const_mul]
  have havgf : MemLp (dyadicAverage m f) 2 volume :=
    memLp_iff.mpr ((eLpNorm_two_dyadicAverage_le hf m).trans_lt hf.eLpNorm_lt_top)
  have havgg : MemLp (dyadicAverage m g) 2 volume :=
    memLp_iff.mpr ((eLpNorm_two_dyadicAverage_le hg m).trans_lt hg.eLpNorm_lt_top)
  have havgLeft : Integrable (fun x => dyadicAverage m f x*conj (g x)) volume :=
    MemLp.integrable_mul havgf hg.star
  have havgRight : Integrable (fun x => f x*conj (dyadicAverage m g x)) volume :=
    MemLp.integrable_mul hf havgg.star
  simp_rw [sub_mul, map_sub, mul_sub]
  rw [integral_sub hconvInt havgLeft, integral_sub hrefInt havgRight]
  have hdyadic : (∫ x, dyadicAverage m f x*conj (g x) ∂volume) =
      ∫ x, f x*conj (dyadicAverage m g x) ∂volume := by
    simpa only [Complex.star_def] using dyadicAverage_selfAdjoint hf hg m
  rw [hdyadic]
  congr 1
  simp_rw [smoothPsiReflectedConvolution_eq_plus hτ]
  exact hpair

#print axioms smoothDyadic_scalar_raw_adjoint_pairing
end
end FractionalPrimes.Literature.JSW
end
