module

public import FractionalPrimes.Literature.Polynomial.TrilinearWithoutPointwiseCaps
public import FractionalPrimes.Literature.Polynomial.ShortIntervalTrilinearTheorem

/-! Exact assembly of the divisor-moment cap removal with the checked
`ldm:trilinear` estimate, proving the stated `ldm:uncapped` corollary. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletMean

open MeasureTheory

set_option maxHeartbeats 2000000 in
/-- The exact `ldm:uncapped` estimate, with the specified divisor-moment
loss `Z_C^3` and the same hypotheses as the capped scalar trilinear theorem,
except for the two auxiliary unit pointwise caps. -/
theorem trilinearUncapped
    (C : ℕ) (X ε T alpha beta gamma δ : ℝ) (E : Set ℝ)
    (coeff₁ coeff₂ coeff₃ : ℕ → ℂ)
    (hX : (2 : ℝ) ^ 16 ≤ X)
    (hε0 : 0 < ε) (hε : ε ≤ 3 / 16)
    (hT0 : 2 ≤ T) (hT : T ≤ X ^ (3 / 8 - ε))
    (ha0 : 0 ≤ alpha) (hb0 : 0 ≤ beta) (hc0 : 0 ≤ gamma)
    (hsum : alpha + beta + gamma = 1)
    (haLow : 1 / 4 - ε / 100 ≤ alpha)
    (haHigh : alpha ≤ 1 / 2 + ε / 100)
    (hbc : |beta - gamma| ≤ 1 / 4 + ε / 100)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1)
    (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.Icc (-T) T)
    (hcoeff₁ : factorCoefficientBound C (X ^ alpha) coeff₁)
    (hcoeff₂ : factorCoefficientBound C (X ^ beta) coeff₂)
    (hcoeff₃ : factorCoefficientBound C (X ^ gamma) coeff₃)
    (hsmall : ∀ t ∈ E,
      ‖factorPolynomial (X ^ alpha) coeff₁ t‖ ≤ δ * Real.sqrt (X ^ alpha)) :
    (∫ t in E,
      ‖factorPolynomial (X ^ alpha) coeff₁ t *
        factorPolynomial (X ^ beta) coeff₂ t *
        factorPolynomial (X ^ gamma) coeff₃ t‖) ≤
      J C * Z C X ^ 3 * (Real.log (4 * X)) ^ (b C + 3) * Real.sqrt X *
        (δ ^ (1 / 16 : ℝ) + X ^ (-ε / 16 : ℝ)) := by
  apply trilinearWithoutPointwiseCaps C X ε T alpha beta gamma δ E
    coeff₁ coeff₂ coeff₃ hX hε0 hε hT0 hT ha0 hb0 hc0 hsum haLow haHigh hbc
    hδ0 hδ hE hEsub hcoeff₁ hcoeff₂ hcoeff₃ hsmall
  intro hX' hε0' hε' hT0' hT' ha0' hb0' hc0' hsum' haLow' haHigh' hbc'
    hδ0' hδ' hE' hEsub' coeff₁' coeff₂' coeff₃'
    hcoeff₁' hcoeff₂' hcoeff₃' hcap₁' hcap₂' hcap₃' hsmall'
  exact trilinearFiveEighths C X T ε alpha beta gamma δ
    coeff₁' coeff₂' coeff₃' E
    hX' hT0' hε0' hε' hT' ha0' hb0' hc0' hsum' haLow' haHigh' hbc'
    hδ0' hδ' hE' hEsub' hcoeff₁' hcoeff₂' hcoeff₃'
    hcap₁' hcap₂' hcap₃' hsmall'

#print axioms FractionalPrimes.Literature.DirichletMean.trilinearUncapped

end FractionalPrimes.Literature.DirichletMean

end
