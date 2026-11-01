module

public import FractionalPrimes.Literature.JSW.PositiveReflectedDifferenceDual
public import FractionalPrimes.Literature.JSW.PositiveLowerVectorTransfer

/-!
# Lower-exponent signed probability-vector bound

The dual test is supplied by the reflected upper-exponent estimate.
The hypotheses remain abstract so the geometric source families can
be inserted without changing their definitions.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The abstract lower-exponent half of the blueprint's positive-family
vector argument for a signed difference of two probability families. -/
theorem finiteProbabilityDifference_lowerLp_bound_of_maximal
    {ι : Type*} [Fintype ι]
    {p q s : ℝ} (hpq : p.HolderConjugate q) (hq : 2 < q)
    (hqs : (q / 2).HolderConjugate s)
    (μσ μψ : ι → Measure ℝ)
    (hμσ : ∀ i, IsProbabilityMeasure (μσ i))
    (hμψ : ∀ i, IsProbabilityMeasure (μψ i))
    (F Uσ Uψ U : ℝ → EuclideanSpace ℂ ι)
    (hF : MemLp F (ENNReal.ofReal p) volume)
    (hUσ : MemLp Uσ (ENNReal.ofReal p) volume)
    (hUψ : MemLp Uψ (ENNReal.ofReal p) volume)
    (hU : MemLp U (ENNReal.ofReal p) volume)
    (hUeq : U =ᵐ[volume] fun x => Uσ x - Uψ x)
    (hUσraw : ∀ i, (fun x => Uσ x i) =ᵐ[volume]
      (fun x => jswConvolution (μσ i) (fun y => F y i) x))
    (hUψraw : ∀ i, (fun x => Uψ x i) =ᵐ[volume]
      (fun x => jswConvolution (μψ i) (fun y => F y i) x))
    (Bσ Bψ : ℝ) (hBσ : 0 ≤ Bσ) (hBψ : 0 ≤ Bψ)
    (hMaxσ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal s) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal s) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μσ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal s) volume ≤
          Bσ * lpNorm g (ENNReal.ofReal s) volume)
    (hMaxψ : ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal s) volume →
      ∃ M : ℝ → ℝ,
        MemLp M (ENNReal.ofReal s) volume ∧
        (∀ x, 0 ≤ M x) ∧
        (∀ᵐ x ∂volume, ∀ i, (∫ y, g (x + y) ∂(μψ i)) ≤ M x) ∧
        lpNorm M (ENNReal.ofReal s) volume ≤
          Bψ * lpNorm g (ENNReal.ofReal s) volume) :
    lpNorm U (ENNReal.ofReal p) volume ≤
      (Real.sqrt Bσ + Real.sqrt Bψ) *
        lpNorm F (ENNReal.ofReal p) volume := by
  have hμσfinite (i : ι) : IsFiniteMeasure (μσ i) := by
    letI : IsProbabilityMeasure (μσ i) := hμσ i
    infer_instance
  have hμψfinite (i : ι) : IsFiniteMeasure (μψ i) := by
    letI : IsProbabilityMeasure (μψ i) := hμψ i
    infer_instance
  have hC : 0 ≤ Real.sqrt Bσ + Real.sqrt Bψ :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact finiteProbabilityDifference_lowerLp_bound hpq μσ μψ
    hμσfinite hμψfinite F Uσ Uψ U hF hUσ hUψ hU hUeq
    hUσraw hUψraw (Real.sqrt Bσ + Real.sqrt Bψ) hC
    (finiteProbabilityDifference_reflected_dual_test hq hqs
      μσ μψ hμσ hμψ Bσ Bψ hBσ hBψ hMaxσ hMaxψ)

#print axioms finiteProbabilityDifference_lowerLp_bound_of_maximal

end

end FractionalPrimes.Literature.JSW

end
