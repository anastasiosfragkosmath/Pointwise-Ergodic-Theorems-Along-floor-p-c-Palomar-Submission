module

public import FractionalPrimes.Literature.Polynomial.ResiduePrefixEnvelope

/-!
# One-weight consequences of the residue-prefix major-arc task

The contract `polynomialMajorArcTask` bounds the sum of the two approved
residue-prefix envelopes.  This adapter extracts each bound separately
with the same constant, as required when the low-frequency Type-II branch
is applied to either weight in `lupo:conditional-integer`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

/-- Extract both one-weight estimates from the exact two-weight PMA
contract, preserving its common constant and all interval hypotheses. -/
theorem polynomialMajorArcTask_oneWeightBounds
    (hPMA : polynomialMajorArcTask)
    (A B η : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hη : 0 < η) (hηmax : η < 3 / 16)
    (X H : ℕ) (hX : 3 ≤ X)
    (hHlower : (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ))
    (hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - η)) :
    ∃ C : ℝ, 0 < C ∧
      residuePrefixEnvelope X H (fun n => (paperMu n : ℂ))
          ((Real.log (X : ℝ)) ^ B) ≤
        C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) ∧
      residuePrefixEnvelope X H
          (fun n => (paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
          ((Real.log (X : ℝ)) ^ B) ≤
        C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  rcases hPMA A B η hA hB hη hηmax with ⟨C, hC, hbound⟩
  have hsum := hbound X H hX hHlower hHupper
  have hmuNonneg :
      0 ≤ residuePrefixEnvelope X H (fun n => (paperMu n : ℂ))
        ((Real.log (X : ℝ)) ^ B) := by
    unfold residuePrefixEnvelope
    exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
  have hcramerNonneg :
      0 ≤ residuePrefixEnvelope X H
        (fun n => (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
        ((Real.log (X : ℝ)) ^ B) := by
    unfold residuePrefixEnvelope
    exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
  refine ⟨C, hC, ?_, ?_⟩
  · exact (le_add_of_nonneg_right hcramerNonneg).trans hsum
  · exact (le_add_of_nonneg_left hmuNonneg).trans hsum

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.polynomialMajorArcTask_oneWeightBounds
