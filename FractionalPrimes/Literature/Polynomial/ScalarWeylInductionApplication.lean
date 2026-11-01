module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylInductionDensity
public import FractionalPrimes.Literature.Polynomial.ScalarWeyl

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- Apply the degree-`d-1` induction hypothesis to the selected residue-class
polynomial. The density bridge supplies the exact source parameter
`δ/(4V)`, whose recursive bound is `F_{d-1}(4V/δ)`. -/
theorem scalarWeyl_selectedResidue_inductionApplication
    {d N N' r : ℕ} (hd : 2 ≤ d) (hN' : 1 ≤ N')
    {δ V : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (hV : 1 ≤ V)
    (hr : 0 < (r : ℝ))
    (hN'upper : (N' : ℝ) ≤ 2 * (N : ℝ) / (r : ℝ))
    (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ d - 1)
    (K : Finset ℤ)
    (hKinterval : ∃ a b : ℤ, K = Finset.Ico a b)
    (hKsubset : K ⊆ Finset.Icc (1 : ℤ) (N' : ℤ))
    (hselected : δ * (N : ℝ) / ((r : ℝ) * V) ≤
      ‖∑ n ∈ K, unitFrequencyPhase (Q.eval (n : ℝ))‖)
    (hIH : ∀ {M : ℕ}, 1 ≤ M →
      ∀ {ε : ℝ}, 0 < ε → ε < 1 / 2 →
      ∀ (Q : Polynomial ℝ), Q.natDegree ≤ d - 1 →
        ∀ K : Finset ℤ,
          (∃ a b : ℤ, K = Finset.Ico a b) →
          K ⊆ Finset.Icc (1 : ℤ) (M : ℤ) →
          ε * (M : ℝ) ≤
            ‖∑ n ∈ K, unitFrequencyPhase (Q.eval (n : ℝ))‖ →
          ∃ s : ℕ,
            1 ≤ s ∧
            (s : ℝ) ≤
              (weylBoundPolynomial (d - 1)).eval₂
                (Nat.castRingHom ℝ) ε⁻¹ ∧
            (∀ i, 1 ≤ i → i ≤ d - 1 →
              (M : ℝ) ^ i * realDistanceToIntegers
                ((s : ℝ) * Q.coeff i) ≤
                  (weylBoundPolynomial (d - 1)).eval₂
                    (Nat.castRingHom ℝ) ε⁻¹)) :
    ∃ s : ℕ,
      1 ≤ s ∧
      (s : ℝ) ≤
        (weylBoundPolynomial (d - 1)).eval₂
          (Nat.castRingHom ℝ) (4 * V / δ) ∧
      (∀ i, 1 ≤ i → i < d →
        (N' : ℝ) ^ i * realDistanceToIntegers
          ((s : ℝ) * Q.coeff i) ≤
            (weylBoundPolynomial (d - 1)).eval₂
              (Nat.castRingHom ℝ) (4 * V / δ)) := by
  have hhandoff := scalarWeyl_inductionDensityHandoff
    hr hN'upper hδ hδhalf hV hselected
  have hresult := hIH (M := N') hN'
    (ε := δ / (4 * V)) hhandoff.1 hhandoff.2.1 Q hQ K
    hKinterval hKsubset hhandoff.2.2
  have hVpos : 0 < V := by linarith
  have hinv : (δ / (4 * V))⁻¹ = 4 * V / δ := by
    field_simp [ne_of_gt hδ, ne_of_gt hVpos]
    <;> ring
  rcases hresult with ⟨s, hs, hsBound, hcoeff⟩
  refine ⟨s, hs, ?_, ?_⟩
  · simpa [hinv] using hsBound
  · intro i hi hid
    simpa [hinv] using hcoeff i hi (by omega)

end FractionalPrimes.Literature.Polynomial
