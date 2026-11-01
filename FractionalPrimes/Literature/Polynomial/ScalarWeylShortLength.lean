module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylRecursivePositivity

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

/-- The q=1 branch of the approved scalar-Weyl inverse theorem when
`N < 4 R_d(δ⁻¹)`. The centered representative gives distance at most `1/2`,
and the first recursive term `(4 R_d)^d` is bounded by `F_d`. -/
theorem scalarWeyl_shortLength_case
    (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N)
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (P : Polynomial ℝ)
    (hNshort : (N : ℝ) <
      4 * (weylBoundPolynomialR d).eval₂ (Nat.castRingHom ℝ) δ⁻¹) :
    ∃ q : ℕ,
      1 ≤ q ∧
      (q : ℝ) ≤ (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ ∧
      (∀ j, 1 ≤ j → j ≤ d →
        (N : ℝ) ^ j * realDistanceToIntegers ((q : ℝ) * P.coeff j) ≤
          (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹) := by
  let R : ℝ :=
    (weylBoundPolynomialR d).eval₂ (Nat.castRingHom ℝ) δ⁻¹
  let F : ℝ :=
    (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹
  have hRone : 1 ≤ R := by
    simpa [R] using
      (weylBoundPolynomialRD_eval_inv_ge_one d hd hδ hδhalf).1
  have hδle : δ ≤ 1 := by linarith
  have hinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδle
  have hFone : 1 ≤ F := by
    simpa [F] using
      (weylBoundPowerControl d (by omega) δ⁻¹ hinv).1
  have hmain : (4 * R) ^ d ≤ F := by
    simpa [R, F] using weylBoundPolynomial_mainTerm_le d hd δ⁻¹ hinv
  have hNle : (N : ℝ) ≤ 4 * R := by
    dsimp [R] at hNshort ⊢
    exact hNshort.le
  have hNpow : (N : ℝ) ^ d ≤ (4 * R) ^ d :=
    pow_le_pow_left₀ (Nat.cast_nonneg N) hNle d
  have hdist (j : ℕ) :
      realDistanceToIntegers (P.coeff j) ≤ (1 / 2 : ℝ) := by
    rw [realDistanceToIntegers_eq_abs_centered]
    exact abs_le.mpr ⟨(centeredFrequency_mem (P.coeff j)).1,
      le_of_lt (centeredFrequency_mem (P.coeff j)).2⟩
  refine ⟨1, by norm_num, ?_, ?_⟩
  · simpa using hFone
  · intro j hj hjd
    have hNj : (N : ℝ) ^ j ≤ (N : ℝ) ^ d :=
      pow_le_pow_right₀ (by exact_mod_cast hN) hjd
    calc
      (N : ℝ) ^ j * realDistanceToIntegers (((1 : ℕ) : ℝ) * P.coeff j) ≤
          (N : ℝ) ^ j * (1 / 2 : ℝ) := by
        simpa only [Nat.cast_one, one_mul] using
          mul_le_mul_of_nonneg_left (hdist j)
            (pow_nonneg (Nat.cast_nonneg N) j)
      _ = (N : ℝ) ^ j / 2 := by ring
      _ ≤ (N : ℝ) ^ d / 2 :=
        div_le_div_of_nonneg_right hNj (by norm_num)
      _ ≤ (4 * R) ^ d := by
        calc
          (N : ℝ) ^ d / 2 ≤ (4 * R) ^ d / 2 :=
            div_le_div_of_nonneg_right hNpow (by norm_num)
          _ ≤ (4 * R) ^ d := by
            nlinarith [pow_nonneg (show 0 ≤ 4 * R by positivity) d]
      _ ≤ F := hmain

end FractionalPrimes.Literature.Polynomial
