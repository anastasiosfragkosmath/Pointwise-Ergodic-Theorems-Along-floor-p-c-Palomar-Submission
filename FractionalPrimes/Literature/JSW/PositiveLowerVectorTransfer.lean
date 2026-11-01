module

public import FractionalPrimes.Literature.JSW.PositiveFiniteVectorPairing

/-!
# Lower-exponent transfer for a signed difference of positive families

This theorem isolates the exact finite-vector duality step used for the
lower-`p` half of `lj:positivity`. The upper bound on the reflected
positive difference is supplied by the already checked upper-`p` result.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The lower-exponent vector norm of a signed difference follows from
positive-family raw representatives and an upper bound for every
reflected adjoint test. -/
theorem finiteProbabilityDifference_lowerLp_bound
    {ι : Type*} [Fintype ι]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (μσ μψ : ι → Measure ℝ)
    (hμσ : ∀ i, IsFiniteMeasure (μσ i))
    (hμψ : ∀ i, IsFiniteMeasure (μψ i))
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
    (C : ℝ) (hC : 0 ≤ C)
    (hDual : ∀ G : ℝ → EuclideanSpace ℂ ι,
      MemLp G (ENNReal.ofReal q) volume →
      ∃ Vσ Vψ : ℝ → EuclideanSpace ℂ ι,
        MemLp Vσ (ENNReal.ofReal q) volume ∧
        MemLp Vψ (ENNReal.ofReal q) volume ∧
        (∀ i, (fun x => Vσ x i) =ᵐ[volume]
          (fun x => ∫ y, G (x + y) i ∂(μσ i))) ∧
        (∀ i, (fun x => Vψ x i) =ᵐ[volume]
          (fun x => ∫ y, G (x + y) i ∂(μψ i))) ∧
        lpNorm (fun x => Vσ x - Vψ x) (ENNReal.ofReal q) volume ≤
          C * lpNorm G (ENNReal.ofReal q) volume) :
    lpNorm U (ENNReal.ofReal p) volume ≤
      C * lpNorm F (ENNReal.ofReal p) volume := by
  apply lpNorm_le_of_adjoint_pairing_bound hpq F U hF hU C hC
  intro G hG
  obtain ⟨Vσ, Vψ, hVσ, hVψ, hVσraw, hVψraw, hVBound⟩ := hDual G hG
  refine ⟨fun x => Vσ x - Vψ x, hVσ.sub hVψ, ?_, hVBound⟩
  calc
    (∫ x, inner ℂ (U x) (G x) ∂volume) =
        ∫ x, inner ℂ (Uσ x - Uψ x) (G x) ∂volume := by
          apply integral_congr_ae
          filter_upwards [hUeq] with x hx
          rw [hx]
    _ = ∫ x, inner ℂ (F x) (Vσ x - Vψ x) ∂volume :=
      finiteProbabilityDifference_vector_adjoint_pairing
        hpq μσ μψ hμσ hμψ F Uσ Uψ G Vσ Vψ
        hF hUσ hUψ hG hVσ hVψ
        hUσraw hUψraw hVσraw hVψraw

#print axioms finiteProbabilityDifference_lowerLp_bound

end

end FractionalPrimes.Literature.JSW

end
