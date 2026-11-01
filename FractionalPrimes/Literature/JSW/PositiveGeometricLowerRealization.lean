module

public import FractionalPrimes.Literature.JSW.PositiveProbabilityVectorRealization
public import FractionalPrimes.Literature.JSW.PositiveMaximalNuVectorBound

/-!
# Source geometric positive-vector outputs at lower exponents

This packages the exact geometric sigma and smooth probability families
before identifying their signed difference with the cancellation measure.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- Both positive source families admit finite-vector `Lᵖ` outputs with
their raw geometric-scale convolution coordinates, for every `p>1`. -/
theorem finiteGeometricPositive_vector_realization
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {b p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hp : 1 < p) (κ : ι → ℤ)
    (F : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F (ENNReal.ofReal p) volume) :
    ∃ Uσ Uψ : ℝ → EuclideanSpace ℂ ι,
      MemLp Uσ (ENNReal.ofReal p) volume ∧
      MemLp Uψ (ENNReal.ofReal p) volume ∧
      (∀ i, (fun x => Uσ x i) =ᵐ[volume]
        (fun x => jswConvolution
          (Measure.map (fun y : ℝ => b ^ κ i * y) σ)
          (fun y => F y i) x)) ∧
      (∀ i, (fun x => Uψ x i) =ᵐ[volume]
        (fun x => jswConvolution
          (Measure.map (fun y : ℝ => b ^ κ i * y)
            (initialSquarePsiProbabilityMeasure σ))
          (fun y => F y i) x)) := by
  classical
  let ψbase : Measure ℝ := initialSquarePsiProbabilityMeasure σ
  have hψbaseProb : IsProbabilityMeasure ψbase :=
    initialSquarePsiProbabilityMeasure_isProbability hSupp
  let μσ : ι → Measure ℝ := fun i =>
    Measure.map (fun y : ℝ => b ^ κ i * y) σ
  let μψ : ι → Measure ℝ := fun i =>
    Measure.map (fun y : ℝ => b ^ κ i * y) ψbase
  have hμσ (i : ι) : IsProbabilityMeasure (μσ i) := by
    dsimp [μσ]
    infer_instance
  have hμψ (i : ι) : IsProbabilityMeasure (μψ i) := by
    letI : IsProbabilityMeasure ψbase := hψbaseProb
    dsimp [μψ]
    infer_instance
  obtain ⟨Uσ, hUσ, hUσraw⟩ :=
    finiteProbabilityConvolution_vector_realization hp μσ hμσ F hF
  obtain ⟨Uψ, hUψ, hUψraw⟩ :=
    finiteProbabilityConvolution_vector_realization hp μψ hμψ F hF
  exact ⟨Uσ, Uψ, hUσ, hUψ, hUσraw, hUψraw⟩

#print axioms finiteGeometricPositive_vector_realization

end

end FractionalPrimes.Literature.JSW

end
