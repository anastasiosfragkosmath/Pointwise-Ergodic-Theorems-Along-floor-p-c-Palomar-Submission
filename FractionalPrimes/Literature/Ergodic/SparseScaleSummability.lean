module

public import FractionalPrimes.SparseScales

/-!
# Summability of the sparse scale partition

This module exposes the exact `er:scales` package used by the ergodic
perturbation argument.  The elementary estimates are proved in
`FractionalPrimes.SparseScales`; this file collects them under the approved
manifest-facing declaration and records explicitly why repeated scales give
empty blocks.
-/

public section

namespace FractionalPrimes

/-! The parameters are the blueprint's `q = min(p,2)`,
`q' = q/(q-1)`, and `tau = 1/(100 q') = (q-1)/(100q)`. -/

theorem sparseScaleParameters {p : ℝ} (hp : 1 < p) :
    sparseScaleQ p = min p 2 ∧
      sparseScaleTau p = (sparseScaleQ p - 1) / (100 * sparseScaleQ p) := by
  exact ⟨sparseScaleQ_eq_min p, sparseScaleTau_eq_on_domain hp⟩

/-- Equal consecutive sparse scales make the half-open logarithmic block
empty, so repeated scales contribute exactly zero. -/
theorem sparseScaleBlockError_eq_zero_of_repeated
    {p : ℝ} {k : ℕ}
    (hk : sparseScale p (k + 1) = sparseScale p k) :
    (∑ m ∈ Finset.Ico (sparseScale p k) (sparseScale p (k + 1)),
      Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1)) = 0 := by
  rw [hk]
  simp

/-- The exact summable scale partition from blueprint `er:scales`.

Here `sparseScaleBlockError` is the half-open sum
`sum_{m=s_k}^{s_{k+1}-1} log(2m)/(m+1)`.  The final series is zeroed outside
`s_k ≥ 3`, and its exponent is exactly `D = 2/tau`. -/
theorem sparseScaleSummability {p : ℝ} (hp : 1 < p) :
    sparseScale p 0 = 1 ∧
      Monotone (sparseScale p) ∧
      Filter.Tendsto (sparseScale p) (Filter.atTop : Filter ℕ)
        (Filter.atTop : Filter ℕ) ∧
      (∀ k : ℕ, 1 ≤ k →
        (Real.log 2 / 2) * Real.rpow (k : ℝ) (sparseScaleTau p) ≤
            Real.log (sparseScale p k) ∧
          Real.log (sparseScale p k) ≤
            Real.log 2 * Real.rpow (k : ℝ) (sparseScaleTau p)) ∧
      (∃ Cτ : ℝ, 0 < Cτ ∧
        ∀ k : ℕ, 1 ≤ k →
          sparseScaleBlockError p k ≤
            Cτ * Real.rpow (k : ℝ) (2 * sparseScaleTau p - 1)) ∧
      Summable (fun k : ℕ =>
        (sparseScaleBlockError p k) ^ (sparseScaleQ p)) ∧
      (∀ k : ℕ,
        sparseScale p (k + 1) = sparseScale p k →
          (∑ m ∈ Finset.Ico (sparseScale p k) (sparseScale p (k + 1)),
            Real.log (2 * (m : ℝ)) / ((m : ℝ) + 1)) = 0) ∧
      Summable (sparseScaleLogInversePower p) := by
  refine ⟨sparseScale_zero hp, ?_⟩
  refine ⟨sparseScale_monotone hp, ?_⟩
  refine ⟨sparseScale_tendsto_atTop hp, ?_⟩
  refine ⟨?_, ?_⟩
  · intro k hk
    exact sparseScale_log_bounds hp hk
  · refine ⟨?_, ?_⟩
    · exact exists_sparseScaleBlockError_polynomial_bound hp
    · refine ⟨summable_sparseScaleBlockError_q hp, ?_⟩
      refine ⟨?_, ?_⟩
      · intro k hk
        exact sparseScaleBlockError_eq_zero_of_repeated hk
      · exact summable_sparseScaleLogInversePower hp

end FractionalPrimes

#print axioms FractionalPrimes.sparseScaleParameters
#print axioms FractionalPrimes.sparseScaleBlockError_eq_zero_of_repeated
#print axioms FractionalPrimes.sparseScaleSummability

end
