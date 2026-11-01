module

public import FractionalPrimes.Literature.JSW.RealVectorAdjointNormDuality

/-!
# Direct finite-vector duality transfer

This form applies to raw convolution representatives: an adjoint pairing
and an upper bound for each dual input imply the lower-exponent bound,
without first constructing a continuous linear operator on vector `Lp`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- A conjugate-exponent bound transfers from adjoint test functions to
the primal vector function, using the full `Lᵖ` duality formula. -/
theorem lpNorm_le_of_adjoint_pairing_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (F U : ℝ → H)
    (hF : MemLp F (ENNReal.ofReal p) volume)
    (hU : MemLp U (ENNReal.ofReal p) volume)
    (C : ℝ) (hC : 0 ≤ C)
    (hAdj : ∀ G : ℝ → H, MemLp G (ENNReal.ofReal q) volume →
      ∃ V : ℝ → H,
        MemLp V (ENNReal.ofReal q) volume ∧
        (∫ x, inner ℂ (U x) (G x) ∂volume) =
          ∫ x, inner ℂ (F x) (V x) ∂volume ∧
        lpNorm V (ENNReal.ofReal q) volume ≤
          C * lpNorm G (ENNReal.ofReal q) volume) :
    lpNorm U (ENNReal.ofReal p) volume ≤
      C * lpNorm F (ENNReal.ofReal p) volume := by
  rw [lpNorm_eq_sSup_dualPairingValues hpq hU]
  have hnonempty : (lpDualPairingValues volume q U).Nonempty := by
    refine ⟨0, fun _ => 0, MemLp.zero', by simp, ?_⟩
    simp
  apply csSup_le hnonempty
  rintro a ⟨G, hG, hGOne, rfl⟩
  obtain ⟨V, hV, hPair, hVBound⟩ := hAdj G hG
  have hHolder := norm_integral_inner_le_lpNorm_mul_lpNorm hpq hF hV
  calc
    ‖∫ x, inner ℂ (U x) (G x) ∂volume‖ =
        ‖∫ x, inner ℂ (F x) (V x) ∂volume‖ := by rw [hPair]
    _ ≤ lpNorm F (ENNReal.ofReal p) volume *
        lpNorm V (ENNReal.ofReal q) volume := hHolder
    _ ≤ lpNorm F (ENNReal.ofReal p) volume *
        (C * lpNorm G (ENNReal.ofReal q) volume) :=
      mul_le_mul_of_nonneg_left hVBound lpNorm_nonneg
    _ ≤ lpNorm F (ENNReal.ofReal p) volume * (C * 1) := by
      apply mul_le_mul_of_nonneg_left _ lpNorm_nonneg
      exact mul_le_mul_of_nonneg_left hGOne hC
    _ = C * lpNorm F (ENNReal.ofReal p) volume := by ring

#print axioms lpNorm_le_of_adjoint_pairing_bound

end

end FractionalPrimes.Literature.JSW

end
