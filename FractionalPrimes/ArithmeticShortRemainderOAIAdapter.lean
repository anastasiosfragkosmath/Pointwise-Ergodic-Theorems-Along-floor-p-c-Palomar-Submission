module
public import FractionalPrimes.ArithmeticShortRemainderAssembly
public import FractionalPrimes.Literature.Reciprocal.MobiusUniformityOfE1
@[expose] public section

/-!
# Short-remainder assembly with the checked E1-to-MUF adapter

This wrapper supplies exactly the `MobiusUniformity` premise to the
conditional `ar:short-remainder` assembly from the accepted OAI E1 route.
The scalar Dirichlet task and restricted polynomial-twisted task remain
explicit premises; this is therefore still a conditional arithmetic result.
-/

namespace FractionalPrimes

/-- The checked OAI E1 route supplies `MUF`, so the short-remainder assembly
needs only the still-open scalar Dirichlet and restricted PTW inputs.  The
conclusion is definitionally the exact output of
`arithmeticShortRemainderOf_MUF_DP_PTW`, retaining its full-block indexing,
frequency range, both arithmetic weights, and source logarithmic bound. -/
theorem arithmeticShortRemainderOf_OAISource_DP_PTW {c : ℝ}
    (hc : 1 < c) (hcNon : NonIntegral c)
    (hDP : Literature.Polynomial.shortIntervalDirichletTask)
    (hPTW : Literature.Polynomial.restrictedPolynomialTwistedTask)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ K₀ : ℕ, 3 ≤ K₀ ∧
      ∀ K K' : ℕ, K₀ ≤ K → K ≤ K' → K' ≤ 2 * K →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        let H : ℕ := Nat.floor ((K : ℝ) ^ (arithmeticParameters c).θ)
        let q : ℕ := ⌊((K' - K : ℕ) : ℝ) / (H : ℝ)⌋₊
        (∑ v ∈ Finset.range q,
          ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H),
            (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase
              (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) ≤
          C * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) ∧
        (∑ v ∈ Finset.range q,
          ‖∑ n ∈ Finset.Ico (K + 1 + v * H)
              (K + 1 + (v + 1) * H),
            ((paperLambda (n : ℤ) -
              paperShortBlockCramerWeight ((K + v * H : ℕ) : ℝ)
                (n : ℤ) : ℝ) : ℂ) * unitFrequencyPhase
              (ξ * (Int.floor ((n : ℝ) ^ c) : ℝ))‖) ≤
          C * (K : ℝ) * (Real.log (K : ℝ)) ^ (-A : ℝ) := by
  exact arithmeticShortRemainderOf_MUF_DP_PTW hc hcNon
    Literature.Reciprocal.mobiusUniformity_of_OAISource hDP hPTW A hA

end FractionalPrimes

#print axioms FractionalPrimes.arithmeticShortRemainderOf_OAISource_DP_PTW
