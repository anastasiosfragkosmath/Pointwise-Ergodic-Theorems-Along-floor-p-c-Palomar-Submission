module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletMeasurability
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

open MeasureTheory Set Complex

namespace FractionalPrimes.Literature.Reciprocal

/-- Conditional integrability of the nonprincipal continued-L Mellin
integrand. The partial-sum bound is an explicit premise here; this lemma does
not prove that arithmetic estimate. -/
theorem integrableOn_nonprincipalContinuedDirichletIntegrand_of_bound
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) (s : ℂ)
    (hs : 0 < s.re)
    (hbound : ∀ t ∈ Ioi (1 : ℝ),
      ‖continuedDirichletPartialSumFormula χ t‖ ≤ (q : ℝ)) :
    IntegrableOn
      (fun t : ℝ => continuedDirichletPartialSumFormula χ t *
        (t : ℂ) ^ (-(s + 1))) (Ioi (1 : ℝ)) := by
  have hpow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1)))
      (Ioi (1 : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt
    · simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
      linarith
    · exact zero_lt_one
  have hmeas : AEStronglyMeasurable
      (continuedDirichletPartialSumFormula χ)
      (volume.restrict (Ioi (1 : ℝ))) :=
    (measurable_continuedDirichletPartialSumFormula χ).aestronglyMeasurable
  have hbound_ae : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖continuedDirichletPartialSumFormula χ t‖ ≤ (q : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hbound t ht
  exact hpow.bdd_mul hmeas hbound_ae

#print axioms integrableOn_nonprincipalContinuedDirichletIntegrand_of_bound

end FractionalPrimes.Literature.Reciprocal
