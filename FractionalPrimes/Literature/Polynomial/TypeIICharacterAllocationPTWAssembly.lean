module

public import FractionalPrimes.Literature.Polynomial.TypeIISelectedAllocationTrilinearK
public import FractionalPrimes.Literature.Uniformity.DivisorTupleCount

/-! Finite source PTW assembly from the checked per-allocation/per-character
trilinear K bound. The allocation-dependent source scale is uniformized before
the exact finite character average is integrated. -/

@[expose] public section

noncomputable section

open MeasureTheory
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- Combine the selected-group per-allocation K estimates with the exact
finite character/allocation integral identity. Here `A r` is the source
scale product `B₁(r) B₂(r) B₃(r)`, and `Kbase` is the unchanged normalized
`ldm:uncapped` expression. A source divisor bound `A r ≤ Amax` is used once;
the exact allocation count `card R` and the external `d^(-1/2)` remain. -/
theorem finiteAllocatedCharacterAverageIntegral_bound_of_allocationK
    {R : Type*} [Fintype R]
    {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d)
    (a' : ℤ) (ha' : IsCoprime a' (Q : ℤ))
    (U T Amax Kbase : ℝ)
    (F : R → BlueprintCharacter Q → ℝ → ℂ)
    (hFcont : ∀ r χ, Continuous (F r χ))
    (A : R → ℝ) (hAmax : ∀ r, A r ≤ Amax)
    (hKbase : 0 ≤ Kbase)
    (hterm : ∀ r χ,
      (∫ t in Set.Icc (-U) U, ‖F r χ t‖ ∂volume) ≤ A r * Kbase) :
    (∫ t in Set.Icc (-U) U,
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        ∑ r : R, ∑ χ : BlueprintCharacter Q,
          star (evalInt χ a') * F r χ t‖ ∂volume) ≤
      (d : ℝ) ^ (-(1 / 2 : ℝ)) * (Fintype.card R : ℝ) *
        (Amax * Kbase) := by
  have hFbound : ∀ r χ,
      (∫ t in Set.Icc (-U) U, ‖F r χ t‖ ∂volume) ≤ Amax * Kbase := by
    intro r χ
    exact (hterm r χ).trans
      (mul_le_mul_of_nonneg_right (hAmax r) hKbase)
  exact finiteAllocatedCharacterAverageIntegral_bound
    hQ hd a' ha' U T (Amax * Kbase) F hFcont hFbound

/-- The same assembly for the exact three-factor gcd-allocation type in the
nonunit source identity. Its allocation count is rewritten to `d₃(d)` using
the checked ordered-factorization count. -/
theorem nonunitTripleCharacterAverageIntegral_bound_of_allocationK
    {d Q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (a' : ℤ) (ha' : IsCoprime a' (Q : ℤ))
    (U T Amax Kbase : ℝ)
    (F : divisorFactorTuples 3 d → BlueprintCharacter Q → ℝ → ℂ)
    (hFcont : ∀ r χ, Continuous (F r χ))
    (A : divisorFactorTuples 3 d → ℝ)
    (hAmax : ∀ r, A r ≤ Amax) (hKbase : 0 ≤ Kbase)
    (hterm : ∀ r χ,
      (∫ t in Set.Icc (-U) U, ‖F r χ t‖ ∂volume) ≤ A r * Kbase) :
    (∫ t in Set.Icc (-U) U,
      ‖((d : ℂ) ^
          (-(1 / 2 : ℂ) - Complex.I * ((t - T : ℝ) : ℂ)) /
          (Q.totient : ℂ)) *
        ∑ r : divisorFactorTuples 3 d,
          ∑ χ : BlueprintCharacter Q,
            star (evalInt χ a') * F r χ t‖ ∂volume) ≤
      (d : ℝ) ^ (-(1 / 2 : ℝ)) *
        (divisorFunction 3 ⟨d, hd⟩ : ℝ) * (Amax * Kbase) := by
  have hbase := finiteAllocatedCharacterAverageIntegral_bound_of_allocationK
    hQ hd a' ha' U T Amax Kbase F hFcont A hAmax hKbase hterm
  have hcard :
      (Fintype.card (divisorFactorTuples 3 d) : ℝ) =
        (divisorFunction 3 ⟨d, hd⟩ : ℝ) := by
    exact_mod_cast (divisorFunction_eq_card_factorTuples 3 ⟨d, hd⟩).symm
  simpa [hcard, mul_assoc] using hbase

#print axioms finiteAllocatedCharacterAverageIntegral_bound_of_allocationK
#print axioms nonunitTripleCharacterAverageIntegral_bound_of_allocationK

end FractionalPrimes.Literature.DirichletMean

end
