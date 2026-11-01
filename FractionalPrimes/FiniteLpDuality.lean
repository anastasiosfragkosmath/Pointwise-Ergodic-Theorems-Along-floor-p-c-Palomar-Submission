module

public import FractionalPrimes.FiniteAdjointPairing
public import Mathlib.Analysis.Normed.Lp.lpHolder

@[expose] public section

/-!
# Finite pairings at conjugate `ℓᵖ` exponents

This records the Hölder direction of the finite-support duality step used in
the upper-exponent part of blueprint `lem:interpolation`.  It is deliberately
only a pairing bound; norm representation by dual vectors remains a separate
step.
-/

namespace FractionalPrimes

open scoped BigOperators ComplexConjugate ENNReal

noncomputable section

/-- A finite complex pairing is bounded by the product of the conjugate
`ℓᵖ` norms.  The summation may be restricted to any finite set, so this is
the exact Hölder direction needed for finite-support dual pairings. -/
theorem finiteLp_pairing_le_norm
    {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal)
    (s : Finset ℤ) (f : lp (fun _ : ℤ => ℂ) p)
    (g : lp (fun _ : ℤ => ℂ) q) :
    ‖∑ k ∈ s, f k * starRingEnd ℂ (g k)‖ ≤ ‖f‖ * ‖g‖ := by
  calc
    ‖∑ k ∈ s, f k * starRingEnd ℂ (g k)‖ ≤
        ∑ k ∈ s, ‖f k * starRingEnd ℂ (g k)‖ := norm_sum_le _ _
    _ = ∑ k ∈ s, ‖f k‖ * ‖g k‖ := by
      apply Finset.sum_congr rfl
      intro k _
      simp
    _ ≤ ∑' k : ℤ, ‖f k‖ * ‖g k‖ := by
      exact (lp.summable_mul hpq f g).sum_le_tsum _ (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖f‖ * ‖g‖ := lp.tsum_mul_le_mul_norm' hpq f g

end

end FractionalPrimes
