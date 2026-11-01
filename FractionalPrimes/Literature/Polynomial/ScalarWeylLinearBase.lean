module

public import FractionalPrimes.Literature.Polynomial.ScalarWeyl

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- The degree-one base case of the approved scalar-Weyl inverse theorem.
It takes `q = 1` and applies the checked linear-phase inverse estimate. -/
theorem scalarWeyl_degreeOne_case
    {N : ℕ} (hN : 1 ≤ N) {J : Finset ℤ}
    (hJ : ∃ a b : ℤ, J = Finset.Ico a b)
    (hJsubset : J ⊆ Finset.Icc (1 : ℤ) (N : ℤ))
    {δ α₀ α₁ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hlarge : δ * (N : ℝ) ≤
      ‖∑ n ∈ J, unitFrequencyPhase (α₁ * (n : ℝ) + α₀)‖) :
    ∃ q : ℕ,
      1 ≤ q ∧
      (q : ℝ) ≤ (weylBoundPolynomial 1).eval₂
        (Nat.castRingHom ℝ) δ⁻¹ ∧
      (N : ℝ) * realDistanceToIntegers ((q : ℝ) * α₁) ≤
        (weylBoundPolynomial 1).eval₂ (Nat.castRingHom ℝ) δ⁻¹ := by
  let F₁ : ℝ :=
    (weylBoundPolynomial 1).eval₂ (Nat.castRingHom ℝ) δ⁻¹
  have hF₁ : F₁ = 2 * δ⁻¹ := by
    simp [F₁, weylBoundPolynomial_one]
  have hδle : δ ≤ 1 := by linarith
  have hinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδle
  have hlinear := linearPhaseInverse hN hJ hJsubset hδ hlarge
  have hratio : 1 / (2 * δ) ≤ 2 * δ⁻¹ := by
    have hden : 0 < (2 : ℝ) * δ := mul_pos (by norm_num) hδ
    rw [div_le_iff₀ hden]
    calc
      (1 : ℝ) ≤ 4 := by norm_num
      _ = (2 * δ⁻¹) * (2 * δ) := by
        field_simp [ne_of_gt hδ]
        norm_num
  have hdist :
      (N : ℝ) * realDistanceToIntegers α₁ ≤ F₁ := by
    calc
      (N : ℝ) * realDistanceToIntegers α₁ ≤ 1 / (2 * δ) := hlinear
      _ ≤ 2 * δ⁻¹ := hratio
      _ = F₁ := hF₁.symm
  refine ⟨1, by norm_num, ?_, ?_⟩
  · have hOne : (1 : ℝ) ≤ 2 * δ⁻¹ := by nlinarith [hinv]
    simpa [weylBoundPolynomial_one] using hOne
  · simpa [F₁, weylBoundPolynomial_one] using hdist

end FractionalPrimes.Literature.Polynomial
