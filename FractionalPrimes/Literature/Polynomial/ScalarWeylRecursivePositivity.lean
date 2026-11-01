module

public import FractionalPrimes.Literature.Polynomial.ScalarWeyl
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

/-- At the source evaluation point `x = δ⁻¹`, both recursive budgets are at
least one. This is the positivity prerequisite used by the top-coefficient
and denominator estimates; the constants remain the approved `R_d` and
`D_d` from `weylBoundPolynomialR` and `weylBoundPolynomialD`. -/
theorem weylBoundPolynomialRD_eval_inv_ge_one
    (d : ℕ) (hd : 2 ≤ d) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    1 ≤ (weylBoundPolynomialR d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ ∧
      1 ≤ (weylBoundPolynomialD d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ := by
  let x : ℝ := δ⁻¹
  let f : ℕ →+* ℝ := Nat.castRingHom ℝ
  have hδle : δ ≤ 1 := by linarith
  have hx : 1 ≤ x := by
    dsimp [x]
    exact (one_le_inv₀ hδ).2 hδle
  have hx2 : 1 ≤ x ^ 2 := by
    simpa using (pow_le_pow_right₀ hx (Nat.zero_le 2))
  have hBinput : 1 ≤ 8 * x ^ 2 := by nlinarith
  have hBcontrol := weylBoundPowerControl (d - 1) (by omega)
    (8 * x ^ 2) hBinput
  have hBeval :
      (weylBoundPolynomialB d).eval₂ f x =
        (weylBoundPolynomial (d - 1)).eval₂ f (8 * x ^ 2) := by
    rw [weylBoundPolynomialB, Polynomial.eval₂_comp]
    simp [f, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, Polynomial.eval₂_pow]
  have hB : 1 ≤ (weylBoundPolynomialB d).eval₂ f x := by
    rw [hBeval]
    exact hBcontrol.1
  have hx4 : 1 ≤ x ^ 4 := by
    simpa using (pow_le_pow_right₀ hx (Nat.zero_le 4))
  have hRcoeff : 1 ≤ (8192 * (d : ℝ)) := by
    exact_mod_cast (show 1 ≤ 8192 * d by omega)
  have hRpow : 1 ≤ ((weylBoundPolynomialB d).eval₂ f x) ^ 3 := by
    calc
      1 = (1 : ℝ) ^ 3 := by norm_num
      _ ≤ ((weylBoundPolynomialB d).eval₂ f x) ^ 3 :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hB 3
  have hReval :
      (weylBoundPolynomialR d).eval₂ f x =
        (8192 * (d : ℝ)) * x ^ 4 *
          ((weylBoundPolynomialB d).eval₂ f x) ^ 3 := by
    simp [weylBoundPolynomialR, f, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow]
  have hR : 1 ≤ (weylBoundPolynomialR d).eval₂ f x := by
    rw [hReval]
    calc
      1 = 1 * 1 := by ring
      _ ≤ (8192 * (d : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_right hRcoeff (by norm_num)
      _ ≤ (8192 * (d : ℝ)) * x ^ 4 :=
        mul_le_mul_of_nonneg_left hx4 (by positivity)
      _ = ((8192 * (d : ℝ)) * x ^ 4) * 1 := by ring
      _ ≤ ((8192 * (d : ℝ)) * x ^ 4) *
          ((weylBoundPolynomialB d).eval₂ f x) ^ 3 :=
        mul_le_mul_of_nonneg_left hRpow (by positivity)
  have hDbracket :
      1 ≤ 1 + 8 * (weylBoundPolynomialR d).eval₂ f x := by
    nlinarith [hR]
  have hDarg :
      1 ≤ 4 * x * (1 + 8 * (weylBoundPolynomialR d).eval₂ f x) := by
    have h4x : 1 ≤ 4 * x := by nlinarith [hx]
    calc
      1 = 1 * 1 := by ring
      _ ≤ (4 * x) * 1 :=
        mul_le_mul_of_nonneg_right h4x (by norm_num)
      _ ≤ (4 * x) *
          (1 + 8 * (weylBoundPolynomialR d).eval₂ f x) :=
        mul_le_mul_of_nonneg_left hDbracket (by positivity)
  have hDcontrol := weylBoundPowerControl (d - 1) (by omega)
    (4 * x * (1 + 8 * (weylBoundPolynomialR d).eval₂ f x)) hDarg
  have hDeval :
      (weylBoundPolynomialD d).eval₂ f x =
        (weylBoundPolynomial (d - 1)).eval₂ f
          (4 * x * (1 + 8 * (weylBoundPolynomialR d).eval₂ f x)) := by
    rw [weylBoundPolynomialD, Polynomial.eval₂_comp]
    simp [f, Polynomial.eval₂_mul, Polynomial.eval₂_add,
      Polynomial.eval₂_C, Polynomial.eval₂_X, hReval]
  constructor
  · simpa [x, f] using hR
  · rw [hDeval]
    exact hDcontrol.1

end FractionalPrimes.Literature.Polynomial
