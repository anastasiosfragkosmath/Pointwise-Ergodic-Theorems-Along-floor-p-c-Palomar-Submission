module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalNormalizedLargeValuesAssembly
public import FractionalPrimes.Literature.Polynomial.ShortIntervalHuxleyFiniteBound

/-! The exact normalized divisor-bounded large-value corollary, with its
finite Huxley input discharged. Blueprint: `lgv:normalized`. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.LargeValues

open MeasureTheory

/-- The count and level-set measure conclusions of `lgv:normalized`. -/
theorem normalizedDivisorBound
    (C : ℕ) (N T V : ℝ) (b : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ)
    (hN : 2 ≤ N) (hT : 2 ≤ T) (hV : 0 < V)
    (ht : ∀ j, |t j| ≤ T)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|)
    (hcoeff : ∀ n ∈ dirichletIndices N,
      ‖b n‖ ≤ (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C)
    (hlarge : ∀ j,
      V ≤ ‖dirichletPolynomial N (normalizedDirichletCoeff b) (t j)‖) :
    (R : ℝ) ≤
        2 ^ (3 * normalizedDivisorExponent C + 28) *
          Real.log (4 * N * T) ^ (3 * normalizedDivisorExponent C + 1) *
            (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)) ∧
      MeasurableSet (dirichletLevelSet N T V (normalizedDirichletCoeff b)) ∧
      volume.real (dirichletLevelSet N T V (normalizedDirichletCoeff b)) ≤
        2 * (2 ^ (3 * normalizedDivisorExponent C + 28) *
          Real.log (4 * N * T) ^ (3 * normalizedDivisorExponent C + 1) *
            (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6))) := by
  apply normalizedDivisorBound_ofSeparated C N T V b R t
    hN hT hV ht hsep hcoeff hlarge
  intro R' s hs hsep' hlarge'
  apply huxleyFiniteBound N T V (normalizedDirichletCoeff b) R' s
    hN hT hV hsep' (by
      intro j
      have hj := hs j
      constructor <;> linarith [abs_le.mp hj]) hlarge'

#print axioms normalizedDivisorBound

/-- The `V = N^(σ-1/2)` specialization in `lgv:normalized`. -/
theorem normalizedDivisorBound_rpow
    (C : ℕ) (N T σ : ℝ) (b : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ)
    (hN : 2 ≤ N) (hT : 2 ≤ T)
    (ht : ∀ j, |t j| ≤ T)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|)
    (hcoeff : ∀ n ∈ dirichletIndices N,
      ‖b n‖ ≤ (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C)
    (hlarge : ∀ j,
      N ^ (σ - 1 / 2) ≤
        ‖dirichletPolynomial N (normalizedDirichletCoeff b) (t j)‖) :
    (R : ℝ) ≤
        2 ^ (3 * normalizedDivisorExponent C + 28) *
          Real.log (4 * N * T) ^ (3 * normalizedDivisorExponent C + 1) *
            (N ^ (2 - 2 * σ) +
              T * min (N ^ (1 - 2 * σ)) (N ^ (4 - 6 * σ))) ∧
      MeasurableSet (dirichletLevelSet N T (N ^ (σ - 1 / 2))
        (normalizedDirichletCoeff b)) ∧
      volume.real (dirichletLevelSet N T (N ^ (σ - 1 / 2))
        (normalizedDirichletCoeff b)) ≤
        2 * (2 ^ (3 * normalizedDivisorExponent C + 28) *
          Real.log (4 * N * T) ^ (3 * normalizedDivisorExponent C + 1) *
            (N ^ (2 - 2 * σ) +
              T * min (N ^ (1 - 2 * σ)) (N ^ (4 - 6 * σ)))) := by
  apply normalizedDivisorBound_rpow_ofSeparated C N T σ b R t
    hN hT ht hsep hcoeff hlarge
  intro R' s hs hsep' hlarge'
  have hNpos : 0 < N := by linarith
  apply huxleyFiniteBound N T (N ^ (σ - 1 / 2))
    (normalizedDirichletCoeff b) R' s hN hT
    (Real.rpow_pos_of_pos hNpos _) hsep' (by
      intro j
      have hj := hs j
      constructor <;> linarith [abs_le.mp hj]) hlarge'

#print axioms normalizedDivisorBound_rpow

end FractionalPrimes.Literature.LargeValues

end
