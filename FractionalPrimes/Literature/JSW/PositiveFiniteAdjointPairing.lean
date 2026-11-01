module

public import FractionalPrimes.Literature.JSW.PositiveMaximalVectorBounds

/-!
# Finite-family adjoint pairing for positive convolutions

This is the coordinatewise Fubini identity needed to transfer the
upper-exponent vector estimate to its lower-exponent adjoint.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The exact finite-family pairing between probability convolution and
its reflected adjoint, for conjugate `Lᵖ` inputs. -/
theorem finiteProbabilityConvolution_adjoint_pairing
    {ι : Type*} [Fintype ι]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsFiniteMeasure (μ i))
    (f g : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
    (hg : ∀ i, MemLp (g i) (ENNReal.ofReal q) volume) :
    (∑ i, ∫ x, jswConvolution (μ i) (f i) x * conj (g i x) ∂volume) =
      ∑ i, ∫ x, f i x *
        conj (∫ y, g i (x + y) ∂(μ i)) ∂volume := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  letI : IsFiniteMeasure (μ i) := hμ i
  obtain ⟨hLeft, hRight⟩ :=
    integrable_translated_pair_products_of_memLp (μ i) hpq
      (f i) (g i) (hf i) (hg i)
  exact integral_jswConvolution_mul_conj_eq_adjoint
    (μ i) (f i) (g i) hLeft hRight

/-- The same finite Fubini identity in the complex inner-product
orientation used by vector-valued `Lᵖ` duality. -/
theorem finiteProbabilityConvolution_adjoint_inner_pairing
    {ι : Type*} [Fintype ι]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsFiniteMeasure (μ i))
    (f g : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
    (hg : ∀ i, MemLp (g i) (ENNReal.ofReal q) volume) :
    (∑ i, ∫ x, inner ℂ (jswConvolution (μ i) (f i) x) (g i x) ∂volume) =
      ∑ i, ∫ x, inner ℂ (f i x)
        (∫ y, g i (x + y) ∂(μ i)) ∂volume := by
  classical
  have h := finiteProbabilityConvolution_adjoint_pairing hpq μ hμ f g hf hg
  have hc := congrArg conj h
  simpa [map_sum, ← integral_conj, RCLike.inner_apply', mul_comm] using hc

#print axioms finiteProbabilityConvolution_adjoint_pairing
#print axioms finiteProbabilityConvolution_adjoint_inner_pairing

end

end FractionalPrimes.Literature.JSW

end
