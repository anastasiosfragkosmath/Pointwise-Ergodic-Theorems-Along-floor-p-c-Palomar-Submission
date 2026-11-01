module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylRecursivePositivity
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

/-- The two coefficient budgets occurring after affine inversion are
bounded by the approved recursive polynomial `F_d`. The first conjunct is
the low-coefficient budget `2^d D_d R_d^(d-1)`; the second covers both the
top-coefficient and denominator budgets `D_d R_d^(d-1)`. -/
theorem weylBoundPolynomial_inductionBudgets_le
    (d : ℕ) (hd : 2 ≤ d) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    (2 : ℝ) ^ d *
        (weylBoundPolynomialD d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ *
          ((weylBoundPolynomialR d).eval₂ (Nat.castRingHom ℝ) δ⁻¹) ^ (d - 1) ≤
      (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ ∧
    (weylBoundPolynomialD d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ *
        ((weylBoundPolynomialR d).eval₂ (Nat.castRingHom ℝ) δ⁻¹) ^ (d - 1) ≤
      (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) δ⁻¹ := by
  let x : ℝ := δ⁻¹
  let f : ℕ →+* ℝ := Nat.castRingHom ℝ
  let Rval : ℝ := (weylBoundPolynomialR d).eval₂ f x
  let Dval : ℝ := (weylBoundPolynomialD d).eval₂ f x
  let Fval : ℝ := (weylBoundPolynomial d).eval₂ f x
  have hRD := weylBoundPolynomialRD_eval_inv_ge_one d hd hδ hδhalf
  have hR : 1 ≤ Rval := by simpa [Rval, x, f] using hRD.1
  have hD : 1 ≤ Dval := by simpa [Dval, x, f] using hRD.2
  have hrecEval : Fval =
      (4 * Rval) ^ d + (2 : ℝ) ^ d * Dval * Rval ^ (d - 1) + 1 := by
    have hraw := congrArg
      (fun p : Polynomial ℕ => p.eval₂ f x)
      (weylBoundPolynomial_recursion (d - 2))
    have hidx : d - 2 + 2 = d := by omega
    have hsub : d - 2 + 1 = d - 1 := by omega
    simpa [Fval, Rval, Dval, f, Polynomial.eval₂_add,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
      Polynomial.eval₂_one, hidx, hsub] using hraw
  have hRNonneg : 0 ≤ Rval := by linarith
  have hDNonneg : 0 ≤ Dval := by linarith
  have hmainNonneg : 0 ≤ (4 * Rval) ^ d :=
    pow_nonneg (mul_nonneg (by norm_num) hRNonneg) _
  have hbudgetNonneg : 0 ≤ Dval * Rval ^ (d - 1) :=
    mul_nonneg hDNonneg (pow_nonneg hRNonneg _)
  have hlowBudget :
      (2 : ℝ) ^ d * Dval * Rval ^ (d - 1) ≤ Fval := by
    rw [hrecEval]
    nlinarith [hmainNonneg]
  have htwoPow : 1 ≤ (2 : ℝ) ^ d := by
    calc
      1 = (1 : ℝ) ^ d := by simp
      _ ≤ (2 : ℝ) ^ d :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
          (by norm_num : (1 : ℝ) ≤ 2) d
  have htopAndDenom : Dval * Rval ^ (d - 1) ≤
      (2 : ℝ) ^ d * Dval * Rval ^ (d - 1) := by
    calc
      Dval * Rval ^ (d - 1) = 1 * (Dval * Rval ^ (d - 1)) := by ring
      _ ≤ (2 : ℝ) ^ d * (Dval * Rval ^ (d - 1)) :=
        mul_le_mul_of_nonneg_right htwoPow hbudgetNonneg
      _ = (2 : ℝ) ^ d * Dval * Rval ^ (d - 1) := by ring
  constructor
  · simpa [Fval, Dval, Rval, x, f] using hlowBudget
  · simpa [Fval, Dval, Rval, x, f] using htopAndDenom.trans hlowBudget

end FractionalPrimes.Literature.Polynomial
