module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalDirichletMeanValue

/-! The finite dual Cauchy--Schwarz step at the start of the source proof of
`lgv:local-large-values`. It is independent of the separated-time estimate
`lgv:sample-square` and does not assert the large-values conclusion.

Blueprint: `expanded-blueprint.tex:5527-5557`.
Astra: `blueprint-sources 2/literature-expansion/sections/dirichlet-large-values.tex:122-157`.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.LargeValues

open scoped BigOperators

private lemma finiteComplexCauchyOnFinset {α : Type*} [DecidableEq α]
    (S : Finset α) (f g : α → ℂ) :
    ‖∑ n ∈ S, f n * g n‖ ^ 2 ≤
      (∑ n ∈ S, ‖f n‖ ^ 2) * ∑ n ∈ S, ‖g n‖ ^ 2 := by
  classical
  have htriangle :
      ‖∑ n ∈ S, f n * g n‖ ≤ ∑ n ∈ S, ‖f n‖ * ‖g n‖ := by
    calc
      ‖∑ n ∈ S, f n * g n‖ ≤ ∑ n ∈ S, ‖f n * g n‖ := norm_sum_le _ _
      _ = ∑ n ∈ S, ‖f n‖ * ‖g n‖ := by simp
  have hsumNonneg : 0 ≤ ∑ n ∈ S, ‖f n‖ * ‖g n‖ :=
    Finset.sum_nonneg fun n hn => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have htriangleSq := (sq_le_sq₀ (norm_nonneg _) hsumNonneg).2 htriangle
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun n => ‖f n‖) (fun n => ‖g n‖)
  exact htriangleSq.trans hcs

/-- Finite dual Cauchy--Schwarz for the source Dirichlet polynomial. The
coefficient energy is multiplied by the squared norm of the dual exponential
sum, exactly as in the first inequality of `lgv:local-large-values`. -/
theorem dirichletPolynomialDualCauchy
    (N : ℝ) (a : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ) (c : Fin R → ℂ) :
    ‖∑ j : Fin R, c j * dirichletPolynomial N a (t j)‖ ^ 2 ≤
      dirichletEnergy N a *
        ∑ n ∈ dirichletIndices N,
          ‖∑ j : Fin R,
            c j *
              Complex.exp (-Complex.I * (t j : ℂ) *
                (Real.log (n : ℝ) : ℂ))‖ ^ 2 := by
  classical
  have hswap :
      (∑ j : Fin R, c j * dirichletPolynomial N a (t j)) =
        ∑ n ∈ dirichletIndices N,
          a n * (∑ j : Fin R,
            c j *
              Complex.exp (-Complex.I * (t j : ℂ) *
                (Real.log (n : ℝ) : ℂ))) := by
    unfold dirichletPolynomial
    simp_rw [Finset.mul_sum, dirichletTerm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hswap]
  have hbound := finiteComplexCauchyOnFinset (dirichletIndices N) a
    (fun n => ∑ j : Fin R,
      c j *
        Complex.exp (-Complex.I * (t j : ℂ) *
          (Real.log (n : ℝ) : ℂ)))
  simpa [dirichletEnergy] using hbound

#print axioms dirichletPolynomialDualCauchy

end FractionalPrimes.Literature.LargeValues
