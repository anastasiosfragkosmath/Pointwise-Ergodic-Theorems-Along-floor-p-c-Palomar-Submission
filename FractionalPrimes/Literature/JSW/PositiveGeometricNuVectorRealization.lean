module

public import FractionalPrimes.Literature.JSW.PositiveGeometricNuIdentity
public import FractionalPrimes.Literature.JSW.LocalizedSquareDecay

/-!
# Source geometric ν vector as a difference of positive outputs

This is the finite-vector representative identity needed before the
lower-exponent positive-family duality argument can be applied.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- For a finite family of strongly measurable `Lᵖ` coordinates, the
source ν output has σ and ψ probability-vector representatives whose
difference agrees almost everywhere with ν. -/
theorem finiteGeometricNuVector_difference_realization
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hp : 1 < p) (κ : ι → ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
    (hstrong : ∀ i, StronglyMeasurable (f i)) :
    ∃ Uσ Uψ : ℝ → EuclideanSpace ℂ ι,
      MemLp Uσ (ENNReal.ofReal p) volume ∧
      MemLp Uψ (ENNReal.ofReal p) volume ∧
      (∀ i, (fun x => Uσ x i) =ᵐ[volume]
        (fun x => jswConvolution
          (Measure.map (fun y : ℝ => b ^ κ i * y) σ) (f i) x)) ∧
      (∀ i, (fun x => Uψ x i) =ᵐ[volume]
        (fun x => jswConvolution
          (Measure.map (fun y : ℝ => b ^ κ i * y)
            (initialSquarePsiProbabilityMeasure σ)) (f i) x)) ∧
      (fun x : ℝ => WithLp.toLp 2 (fun i : ι =>
        (localizedSquareNuLpConvolution hSupp p b hp (κ i)
          ((hf i).toLp (f i)) : ℝ → ℂ) x)) =ᵐ[volume]
        (fun x => Uσ x - Uψ x) := by
  classical
  let P : ℝ≥0∞ := ENNReal.ofReal p
  letI : Fact (1 ≤ P) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let F : ℝ → EuclideanSpace ℂ ι := fun x =>
    WithLp.toLp 2 (fun i => f i x)
  have hF : MemLp F P volume := by
    apply MemLp.of_eval_piLp
    intro i
    exact hf i
  obtain ⟨Uσ, Uψ, hUσ, hUψ, hUσraw, hUψraw⟩ :=
    finiteGeometricPositive_vector_realization (b := b) hSupp hp κ F hF
  let ψbase : Measure ℝ := initialSquarePsiProbabilityMeasure σ
  have hψprob : IsProbabilityMeasure ψbase :=
    initialSquarePsiProbabilityMeasure_isProbability hSupp
  let μσ : ι → Measure ℝ := fun i =>
    Measure.map (fun y : ℝ => b ^ κ i * y) σ
  let μψ : ι → Measure ℝ := fun i =>
    Measure.map (fun y : ℝ => b ^ κ i * y) ψbase
  have hcoord (i : ι) :
      (localizedSquareNuLpConvolution hSupp p b hp (κ i)
          ((hf i).toLp (f i)) : ℝ → ℂ) =ᵐ[volume]
        (fun x => Uσ x i - Uψ x i) := by
    letI : IsProbabilityMeasure ψbase := hψprob
    haveI : IsFiniteMeasure (μσ i) := by dsimp [μσ]; infer_instance
    haveI : IsFiniteMeasure (μψ i) := by dsimp [μψ]; infer_instance
    have hσvar : IsFiniteMeasure
        (initialSquareSigmaComplexMeasure (μσ i)).variation := by
      rw [initialSquareSigmaComplexMeasure_variation_eq]
      infer_instance
    have hψvar : IsFiniteMeasure
        (initialSquareSigmaComplexMeasure (μψ i)).variation := by
      rw [initialSquareSigmaComplexMeasure_variation_eq]
      infer_instance
    letI : IsFiniteMeasure
        (initialSquareSigmaComplexMeasure (μσ i)).variation := hσvar
    letI : IsFiniteMeasure
        (initialSquareSigmaComplexMeasure (μψ i)).variation := hψvar
    let Tσ := lpComplexMeasureConvolution P
      (initialSquareSigmaComplexMeasure (μσ i)) ((hf i).toLp (f i))
    let Tψ := lpComplexMeasureConvolution P
      (initialSquareSigmaComplexMeasure (μψ i)) ((hf i).toLp (f i))
    have hνeq : localizedSquareNuLpConvolution hSupp p b hp (κ i)
        ((hf i).toLp (f i)) = Tσ - Tψ := by
      simpa [Tσ, Tψ, μσ, μψ, ψbase, P,
        localizedSquareNuLpConvolution] using
        geometricNuLpConvolution_eq_positive_sub hSupp hp (κ i)
          ((hf i).toLp (f i))
    have hTσ : (Tσ : ℝ → ℂ) =ᵐ[volume]
        jswConvolution (μσ i) (f i) := by
      exact lpComplexSigmaConvolution_ae_eq_jswConvolution hp (μσ i)
        ((hf i).toLp (f i)) (f i) (hstrong i).measurable (hf i)
        (MemLp.coeFn_toLp (hf i))
    have hTψ : (Tψ : ℝ → ℂ) =ᵐ[volume]
        jswConvolution (μψ i) (f i) := by
      exact lpComplexSigmaConvolution_ae_eq_jswConvolution hp (μψ i)
        ((hf i).toLp (f i)) (f i) (hstrong i).measurable (hf i)
        (MemLp.coeFn_toLp (hf i))
    filter_upwards [hTσ, hTψ, hUσraw i, hUψraw i,
      Lp.coeFn_sub Tσ Tψ] with x hxσ hxψ hUσx hUψx hxsub
    rw [hνeq, hxsub]
    change Tσ x - Tψ x = Uσ x i - Uψ x i
    rw [hxσ, hxψ]
    simp only [F] at hUσx hUψx
    rw [hUσx, hUψx]
  refine ⟨Uσ, Uψ, hUσ, hUψ, hUσraw, hUψraw, ?_⟩
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  ext i
  exact hx i

#print axioms finiteGeometricNuVector_difference_realization

end

end FractionalPrimes.Literature.JSW

end
