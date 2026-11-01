module

public import FractionalPrimes.Literature.JSW.SmoothDyadicL2Operator
public import FractionalPrimes.Literature.JSW.SmoothDyadicFiniteSummation

/-! The source block bound as a bound on the actual continuous L2 operator. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem smoothDyadicErrorLpOperator_L2_block
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    [Fact (1 ≤ ENNReal.ofReal (2 : ℝ))]
    {τ : ℝ} (hτ : 0 < τ) {m : ℤ} (hlower : (2 : ℝ)^m ≤ τ) (hupper : τ ≤ (2 : ℝ)^(m+1))
    (j : ℤ) {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal (2 : ℝ)) volume) :
    ‖smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num) τ m
      (dyadicDifferenceLpAt (by norm_num) hf j)‖ ≤
      smoothDyadicAmplitude * smoothDyadicWeight (m-j) *
        ‖dyadicDifferenceLpAt (by norm_num) hf j‖ := by
  let g := dyadicDifference j f
  let δ := dyadicDifferenceLpAt (by norm_num : ENNReal.ofReal (2 : ℝ) = 2) hf j
  let R := smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num) τ m
  have hf2 : MemLp f 2 volume := by simpa only [ENNReal.ofReal_ofNat] using hf
  have hg2 := memLp_dyadicDifference_two_of_memLp hf2 j
  have hgP : MemLp g (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa only [ENNReal.ofReal_ofNat] using hg2
  have hgmeas : Measurable g :=
    (measurable_dyadicAverage (j-1) f).sub (measurable_dyadicAverage j f)
  have hδ : (δ : ℝ → ℂ) =ᵐ[volume] g := dyadicDifferenceLpAt_ae_eq _ hf j
  have hrepr := smoothDyadicErrorLpOperator_ae_eq hSupp (p := 2) (by norm_num) τ m
    δ g hgmeas hgP hδ
  let e : ℝ → ℂ := fun x => jswConvolution
    (Measure.map (fun z : ℝ => τ*z) (initialSquarePsiProbabilityMeasure σ)) g x-dyadicAverage m g x
  have hnormR : ‖R δ‖ = lpNorm e 2 volume := by
    calc
      _ = (eLpNorm (R δ : ℝ → ℂ) (ENNReal.ofReal (2 : ℝ)) volume).toReal := Lp.norm_def _
      _ = (eLpNorm e (ENNReal.ofReal (2 : ℝ)) volume).toReal := congrArg ENNReal.toReal (eLpNorm_congr_ae hrepr)
      _ = _ := by norm_num only [ENNReal.ofReal_ofNat]; rfl
  have hnormδ : ‖δ‖ = lpNorm g 2 volume := by
    calc
      _ = (eLpNorm (δ : ℝ → ℂ) (ENNReal.ofReal (2 : ℝ)) volume).toReal := Lp.norm_def _
      _ = (eLpNorm g (ENNReal.ofReal (2 : ℝ)) volume).toReal := congrArg ENNReal.toReal (eLpNorm_congr_ae hδ)
      _ = _ := by norm_num only [ENNReal.ofReal_ofNat]; rfl
  change ‖R δ‖ ≤ smoothDyadicAmplitude*smoothDyadicWeight (m-j)*‖δ‖
  rw [hnormR, hnormδ]
  exact (smoothDyadic_block_decay hSupp hτ hlower hupper j hf2).2

#print axioms smoothDyadicErrorLpOperator_L2_block
end
end FractionalPrimes.Literature.JSW
end
