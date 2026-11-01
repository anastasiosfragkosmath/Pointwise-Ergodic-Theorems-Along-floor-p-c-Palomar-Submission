module

public import FractionalPrimes.Literature.Polynomial.PolynomialOuterCutoffPreservesAverages
public import FractionalPrimes.Literature.Polynomial.PolynomialDirichletMeanEnvelope
public import FractionalPrimes.PolynomialKernelProperties

@[expose] public section

/-!
# The exact scalar short-interval Dirichlet task

This is the source contract `lup:scalar-analytic-tasks` / `lup:dp-envelope`
for the fixed outer cutoff and the checked Mellin mean envelope.  The bound
is uniform in the arithmetic residue and in the two coefficient choices;
the source threshold also supplies the three kernel-window side conditions.
-/

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Polynomial

/-- Exact source-facing short-interval Dirichlet-polynomial task `DP`.
The coefficient families are `μ(n) ζ(n/X) 1_(n≡a mod q)` and
`Λ(n) ζ(n/X) 1_(n≡a mod q)`, encoded by the corresponding
`outerCutoffWindowData`.  The constants are chosen before `X,H,q,a,f`, and
the threshold guarantees `2 ≤ W ≤ X^(1/100)` and `T₀ ≥ W`. -/
def shortIntervalDirichletTask : Prop :=
  ∀ A B η : ℝ, (hA : 0 < A) → (hB : 0 < B) →
    (hη : 0 < η) → (hη₃ : η < 3 / 16) →
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧
      ∀ D : ℝ, D₀ ≤ D →
        ∃ C_D X_D : ℝ, 0 < C_D ∧ 3 ≤ X_D ∧
          ∀ (hXD : 3 ≤ X_D) (X H : ℕ)
            (hDX : X_D ≤ (X : ℝ))
            (hHlower : (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ))
            (hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - η)),
            let W : ℝ := (Real.log (X : ℝ)) ^ D
            let T₀ : ℝ := (X : ℝ) / (H : ℝ)
            (2 ≤ W ∧ W ≤ (X : ℝ) ^ (1 / 100 : ℝ) ∧ W ≤ T₀) ∧
              ∀ (q : ℕ) (hq : 1 ≤ q)
                (hqQ : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ B)
                (a : ℤ) (f : ℤ → ℝ)
                (hf : f = paperLambda ∨ f = fun n => (paperMu n : ℝ)),
                    let hX : 3 ≤ (X : ℝ) := le_trans hXD hDX
                    let hH : 0 < (H : ℝ) := by
                      have hXpos : 0 < (X : ℝ) := by linarith
                      have hp : 0 < (X : ℝ) ^ ((5 / 8 : ℝ) + η) :=
                        Real.rpow_pos_of_pos hXpos _
                      exact lt_of_lt_of_le hp hHlower
                    let hHX : (H : ℝ) ≤ (X : ℝ) := by
                      have hXone : 1 ≤ (X : ℝ) := by linarith
                      have hexp : 1 - η ≤ (1 : ℝ) := by linarith [hη]
                      have hpow : (X : ℝ) ^ (1 - η) ≤ (X : ℝ) := by
                        simpa only [Real.rpow_one] using
                          Real.rpow_le_rpow_of_exponent_le hXone hexp
                      exact le_trans hHupper hpow
                    dirichletMeanEnvelope
                      (outerCutoffWindowData polynomialKernelRho
                        (X : ℝ) (H : ℝ) q a f hX hH hHX
                        (by exact_mod_cast (show 0 < q by omega)) hf)
                      T₀ W ≤
                        C_D * Real.sqrt (X : ℝ) *
                          (Real.log (X : ℝ)) ^ (-A : ℝ)

#print axioms shortIntervalDirichletTask

end FractionalPrimes.Literature.Polynomial
