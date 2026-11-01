module

public import FractionalPrimes.Literature.DirichletAdapter.HighOrderResidueQuadrature
public import Mathlib.Analysis.Complex.RealDeriv

/-! Complexification of the real Mellin profile's derivatives. -/

@[expose] public section

open scoped ContDiff

namespace FractionalPrimes.Literature.DirichletAdapter

/-- Taking real derivatives commutes with the complex inclusion for a smooth
real profile. This is the integration-by-parts bridge for the Mellin term. -/
theorem iteratedDeriv_complex_ofReal
    (M : ℝ → ℝ) (hM : ContDiff ℝ ∞ M) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => (M y : ℂ)) x =
      ((iteratedDeriv n M x : ℝ) : ℂ) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have heq : iteratedDeriv n (fun y : ℝ => (M y : ℂ)) =
          fun y : ℝ => ((iteratedDeriv n M y : ℝ) : ℂ) := by
        funext y
        exact ih y
      rw [heq]
      have hdiff : DifferentiableAt ℝ (iteratedDeriv n M) x :=
        (hM.differentiable_iteratedDeriv n (by
          exact_mod_cast (WithTop.coe_lt_top n : (n : ℕ∞) < ⊤))) x
      exact hdiff.hasDerivAt.ofReal_comp.deriv

#print axioms iteratedDeriv_complex_ofReal

end FractionalPrimes.Literature.DirichletAdapter

end
