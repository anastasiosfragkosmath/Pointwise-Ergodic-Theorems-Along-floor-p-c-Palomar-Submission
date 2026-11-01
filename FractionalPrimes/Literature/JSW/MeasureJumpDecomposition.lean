module

public import FractionalPrimes.Literature.JSW.RoughSquareFiniteFromFull
public import FractionalPrimes.Literature.JSW.SmoothDyadicSquareClosure

/-! Exact actual σ = ν + smooth-error + dyadic-average decomposition for jump assembly. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem sigmaDilateConvolution_ae_three_decomposition
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    {a : ℝ} (ha : 0 < a) (k : ℤ)
    (F : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    jswConvolution (Measure.map (fun z : ℝ => jswTau a ha k*z) σ) (F : ℝ → ℂ) =ᵐ[volume]
      (fun x => (localizedSquareNuLpConvolution hSupp p (jswB a ha) hp k F : ℝ → ℂ) x+
        (smoothDyadicErrorLpOperator hSupp hp (jswTau a ha k) (jswM a ha k) F : ℝ → ℂ) x+
        dyadicAverage (jswM a ha k) (F : ℝ → ℂ) x) := by
  let Tσ := geometricSigmaLpConvolution σ p (jswB a ha) hp k F
  let Tψ := geometricPsiLpConvolution hSupp p (jswB a ha) hp k F
  let μσ := Measure.map (fun z : ℝ => jswTau a ha k*z) σ
  let μψ := Measure.map (fun z : ℝ => jswTau a ha k*z) (initialSquarePsiProbabilityMeasure σ)
  letI : IsProbabilityMeasure (initialSquarePsiProbabilityMeasure σ) :=
    initialSquarePsiProbabilityMeasure_isProbability hSupp
  have hσ : (Tσ : ℝ → ℂ) =ᵐ[volume] jswConvolution μσ (F : ℝ → ℂ) :=
    lpComplexSigmaConvolution_ae_eq_jswConvolution_of_memLp hp μσ F (F : ℝ → ℂ)
      (Lp.memLp F) Filter.EventuallyEq.rfl
  have hψ : (Tψ : ℝ → ℂ) =ᵐ[volume] jswConvolution μψ (F : ℝ → ℂ) :=
    lpComplexSigmaConvolution_ae_eq_jswConvolution_of_memLp hp μψ F (F : ℝ → ℂ)
      (Lp.memLp F) Filter.EventuallyEq.rfl
  have hν : localizedSquareNuLpConvolution hSupp p (jswB a ha) hp k F = Tσ-Tψ := by
    exact geometricNuLpConvolution_eq_positive_sub hSupp hp k F
  have hr := smoothDyadicErrorLpOperator_ae_eq_of_memLp hSupp hp
    (jswTau a ha k) (jswM a ha k) F (F : ℝ → ℂ) (Lp.memLp F) Filter.EventuallyEq.rfl
  filter_upwards [hσ,hψ,hr,Lp.coeFn_sub Tσ Tψ] with x hxσ hxψ hxR hxsub
  rw [hν,hxsub]
  change jswConvolution μσ (F : ℝ → ℂ) x =
    (Tσ x-Tψ x)+_+_
  rw [hxσ,hxψ,hxR]
  change jswConvolution μσ (F : ℝ → ℂ) x =
    (jswConvolution μσ (F : ℝ → ℂ) x-jswConvolution μψ (F : ℝ → ℂ) x)+
      (jswConvolution μψ (F : ℝ → ℂ) x-dyadicAverage (jswM a ha k) (F : ℝ → ℂ) x)+
      dyadicAverage (jswM a ha k) (F : ℝ → ℂ) x
  ring

#print axioms sigmaDilateConvolution_ae_three_decomposition
end
end FractionalPrimes.Literature.JSW
end
