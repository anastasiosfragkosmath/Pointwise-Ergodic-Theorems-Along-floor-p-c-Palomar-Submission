module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylDegreeStep
public import FractionalPrimes.Literature.Polynomial.ScalarWeylLinearBase

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

private def scalarWeylInverseStatement (d : ℕ) : Prop :=
  ∀ {N : ℕ}, 1 ≤ N →
    ∀ {δ : ℝ}, 0 < δ → δ < 1 / 2 →
    ∀ (P : Polynomial ℝ), P.natDegree ≤ d →
    ∀ (lo hi : ℤ),
      Finset.Ico lo hi ⊆ Finset.Icc (1 : ℤ) (N : ℤ) →
      δ * (N : ℝ) ≤
        ‖∑ n ∈ Finset.Ico lo hi, unitFrequencyPhase (P.eval (n : ℝ))‖ →
      ∃ q : ℕ,
        1 ≤ q ∧
        (q : ℝ) ≤ (weylBoundPolynomial d).eval₂
          (Nat.castRingHom ℝ) δ⁻¹ ∧
        (∀ j, 1 ≤ j → j ≤ d →
          (N : ℝ) ^ j * realDistanceToIntegers
            ((q : ℝ) * P.coeff j) ≤
              (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹)

private theorem scalarWeyl_eval_eq_linear_of_degree_le_one
    (P : Polynomial ℝ) (hP : P.natDegree ≤ 1) (n : ℤ) :
    P.eval (n : ℝ) = P.coeff 1 * (n : ℝ) + P.coeff 0 := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hP]
  simp

set_option maxHeartbeats 600000 in
/-- The quantitative scalar Weyl inverse theorem with the exact recursive
constants of the approved blueprint. Its interval input is the Lean
half-open integer interval `Ico lo hi` inside `{1, …, N}`. -/
theorem scalarWeylInverse
    (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d)
    (lo hi : ℤ)
    (hJsubset : Finset.Ico lo hi ⊆ Finset.Icc (1 : ℤ) (N : ℤ))
    (hlarge : δ * (N : ℝ) ≤
      ‖∑ n ∈ Finset.Ico lo hi, unitFrequencyPhase (P.eval (n : ℝ))‖) :
    ∃ q : ℕ,
      1 ≤ q ∧
      (q : ℝ) ≤ (weylBoundPolynomial d).eval₂
        (Nat.castRingHom ℝ) δ⁻¹ ∧
      (∀ j, 1 ≤ j → j ≤ d →
        (N : ℝ) ^ j * realDistanceToIntegers
          ((q : ℝ) * P.coeff j) ≤
            (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹) := by
  have hmain : ∀ k, 1 ≤ k → scalarWeylInverseStatement k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      dsimp [scalarWeylInverseStatement]
      intro M hM ε hε hεhalf Q hQ a b hKsubset hlargeK
      by_cases hkone : k = 1
      · subst k
        have hlargeLinear : ε * (M : ℝ) ≤
            ‖∑ n ∈ Finset.Ico a b,
              unitFrequencyPhase
                (Q.coeff 1 * (n : ℝ) + Q.coeff 0)‖ := by
          calc
            ε * (M : ℝ) ≤
                ‖∑ n ∈ Finset.Ico a b,
                  unitFrequencyPhase (Q.eval (n : ℝ))‖ := hlargeK
            _ = ‖∑ n ∈ Finset.Ico a b,
                  unitFrequencyPhase
                    (Q.coeff 1 * (n : ℝ) + Q.coeff 0)‖ := by
              congr 1
              apply Finset.sum_congr rfl
              intro n hn
              rw [scalarWeyl_eval_eq_linear_of_degree_le_one Q hQ n]
        obtain ⟨q, hq, hqF, hqα₁⟩ :=
          scalarWeyl_degreeOne_case hM ⟨a, b, rfl⟩ hKsubset
            hε hεhalf hlargeLinear
        refine ⟨q, hq, ?_, ?_⟩
        · simpa [weylBoundPolynomial_one] using hqF
        · intro j hj hjk
          have hjone : j = 1 := by omega
          subst j
          simpa [weylBoundPolynomial_one] using hqα₁
      · have hklarge : 2 ≤ k := by omega
        have hIH : ∀ {M : ℕ}, 1 ≤ M →
            ∀ {ε : ℝ}, 0 < ε → ε < 1 / 2 →
            ∀ (Q : Polynomial ℝ), Q.natDegree ≤ k - 1 →
              ∀ K : Finset ℤ,
                (∃ a b : ℤ, K = Finset.Ico a b) →
                K ⊆ Finset.Icc (1 : ℤ) (M : ℤ) →
                ε * (M : ℝ) ≤
                  ‖∑ n ∈ K, unitFrequencyPhase (Q.eval (n : ℝ))‖ →
                ∃ q : ℕ,
                  1 ≤ q ∧
                  (q : ℝ) ≤
                    (weylBoundPolynomial (k - 1)).eval₂
                      (Nat.castRingHom ℝ) ε⁻¹ ∧
                  (∀ j, 1 ≤ j → j ≤ k - 1 →
                    (M : ℝ) ^ j * realDistanceToIntegers
                      ((q : ℝ) * Q.coeff j) ≤
                        (weylBoundPolynomial (k - 1)).eval₂
                          (Nat.castRingHom ℝ) ε⁻¹) := by
          intro M hM ε hε hεhalf Q hQ K hK hKsubset hlarge'
          rcases hK with ⟨a, b, rfl⟩
          have hprev := ih (k - 1) (by omega) (by omega) (N := M)
          exact hprev hM hε hεhalf Q hQ a b hKsubset hlarge'
        exact scalarWeyl_degreeStep hklarge hM hε hεhalf Q hQ a b
          hKsubset hlargeK hIH
  exact hmain d hd hN hδ hδhalf P hP lo hi hJsubset hlarge

end FractionalPrimes.Literature.Polynomial
