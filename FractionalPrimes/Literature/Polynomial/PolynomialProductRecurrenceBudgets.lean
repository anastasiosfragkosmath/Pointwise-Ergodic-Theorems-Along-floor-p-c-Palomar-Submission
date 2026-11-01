module

public import FractionalPrimes.Literature.Polynomial.PolynomialRecurrenceBudgets

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

/-- The two natural-coefficient polynomials used by the two-coordinate
recurrence argument. -/
structure ProductRecurrenceBudgetPolynomials where
  A : Polynomial ℕ
  B : Polynomial ℕ

/-- `A_j(z)=R_j(2z)+T_j(2z)^j`. -/
noncomputable def productRecurrenceAPolynomial (j : ℕ) : Polynomial ℕ :=
  (recurrenceBudgets j).R.comp (C 2 * X) +
    ((recurrenceBudgets j).T.comp (C 2 * X)) ^ j

/-- The polynomial substitution `4 A_j(z) z`. -/
noncomputable def productRecurrenceSecondArgumentPolynomial (j : ℕ) :
    Polynomial ℕ :=
  C 4 * productRecurrenceAPolynomial j * X

/--
`B_j(z)=A_j(z)[R_j(4A_j(z)z)+T_j(4A_j(z)z)^j]`.
-/
noncomputable def productRecurrenceBPolynomial (j : ℕ) : Polynomial ℕ :=
  productRecurrenceAPolynomial j *
    ((recurrenceBudgets j).R.comp
        (productRecurrenceSecondArgumentPolynomial j) +
      ((recurrenceBudgets j).T.comp
        (productRecurrenceSecondArgumentPolynomial j)) ^ j)

/-- Exact natural-coefficient package for blueprint `lpi:product-budgets`. -/
noncomputable def productRecurrenceBudgets (j : ℕ) :
    ProductRecurrenceBudgetPolynomials where
  A := productRecurrenceAPolynomial j
  B := productRecurrenceBPolynomial j

/-- Real evaluation of `A_j`. -/
noncomputable def productRecurrenceA (j : ℕ) (z : ℝ) : ℝ :=
  (productRecurrenceAPolynomial j).eval₂ (Nat.castRingHom ℝ) z

/-- Real evaluation of `B_j`. -/
noncomputable def productRecurrenceB (j : ℕ) (z : ℝ) : ℝ :=
  (productRecurrenceBPolynomial j).eval₂ (Nat.castRingHom ℝ) z

/-- The exact real-evaluation formula for `A_j`. -/
theorem productRecurrenceA_eval (j : ℕ) (z : ℝ) :
    productRecurrenceA j z =
      recurrenceBudgetR j (2 * z) + recurrenceBudgetT j (2 * z) ^ j := by
  simp [productRecurrenceA, productRecurrenceAPolynomial,
    recurrenceBudgetR, recurrenceBudgetT, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_comp, Polynomial.eval₂_mul]

/-- The exact real evaluation of the second recurrence argument. -/
theorem productRecurrenceSecondArgument_eval (j : ℕ) (z : ℝ) :
    (productRecurrenceSecondArgumentPolynomial j).eval₂
        (Nat.castRingHom ℝ) z = 4 * productRecurrenceA j z * z := by
  simp [productRecurrenceSecondArgumentPolynomial, productRecurrenceA,
    Polynomial.eval₂_mul]

/-- The exact real-evaluation formula for `B_j`. -/
theorem productRecurrenceB_eval (j : ℕ) (z : ℝ) :
    productRecurrenceB j z =
      productRecurrenceA j z *
        (recurrenceBudgetR j (4 * productRecurrenceA j z * z) +
          recurrenceBudgetT j (4 * productRecurrenceA j z * z) ^ j) := by
  rw [productRecurrenceB, productRecurrenceBPolynomial,
    Polynomial.eval₂_mul]
  rw [Polynomial.eval₂_add, Polynomial.eval₂_pow]
  change productRecurrenceA j z *
      (((recurrenceBudgets j).R.comp
          (productRecurrenceSecondArgumentPolynomial j)).eval₂
          (Nat.castRingHom ℝ) z +
        (((recurrenceBudgets j).T.comp
          (productRecurrenceSecondArgumentPolynomial j)).eval₂
          (Nat.castRingHom ℝ) z) ^ j) = _
  rw [Polynomial.eval₂_comp, Polynomial.eval₂_comp,
    productRecurrenceSecondArgument_eval]
  rfl

/-- Both budget polynomials have nonnegative coefficients after casting to
the reals; the natural coefficient representation makes this structural. -/
theorem productRecurrenceBudgets_coeff_nonneg (j n : ℕ) :
    0 ≤ ((((productRecurrenceBudgets j).A.coeff n : ℕ) : ℝ)) ∧
      0 ≤ ((((productRecurrenceBudgets j).B.coeff n : ℕ) : ℝ)) := by
  exact ⟨Nat.cast_nonneg _, Nat.cast_nonneg _⟩

/-- `A_j(z)` is at least one on the approved domain `j≥1,z≥2`. -/
theorem productRecurrenceA_ge_one (j : ℕ) (hj : 1 ≤ j)
    (z : ℝ) (hz : 2 ≤ z) : 1 ≤ productRecurrenceA j z := by
  rw [productRecurrenceA_eval]
  have harg : 2 ≤ 2 * z := by nlinarith
  have hR := recurrenceBudgetR_ge_one j hj (2 * z) harg
  have hT := recurrenceBudgetT_ge_one j hj (2 * z) harg
  have hTnonneg : 0 ≤ recurrenceBudgetT j (2 * z) ^ j := by positivity
  linarith

/-- `B_j(z)` is at least one on the approved domain `j≥1,z≥2`. -/
theorem productRecurrenceB_ge_one (j : ℕ) (hj : 1 ≤ j)
    (z : ℝ) (hz : 2 ≤ z) : 1 ≤ productRecurrenceB j z := by
  rw [productRecurrenceB_eval]
  have hA := productRecurrenceA_ge_one j hj z hz
  have harg : 2 ≤ 4 * productRecurrenceA j z * z := by
    have hA0 : 0 ≤ productRecurrenceA j z := by linarith
    have hAz : 2 ≤ productRecurrenceA j z * z := by
      calc
        2 = 1 * 2 := by norm_num
        _ ≤ productRecurrenceA j z * z :=
          mul_le_mul hA hz (by norm_num) hA0
    nlinarith [mul_le_mul_of_nonneg_left hAz (by norm_num : (0 : ℝ) ≤ 4)]
  have hR := recurrenceBudgetR_ge_one j hj
    (4 * productRecurrenceA j z * z) harg
  have hT := recurrenceBudgetT_ge_one j hj
    (4 * productRecurrenceA j z * z) harg
  have hbracket : 1 ≤
      recurrenceBudgetR j (4 * productRecurrenceA j z * z) +
        recurrenceBudgetT j (4 * productRecurrenceA j z * z) ^ j := by
    have hpow : 0 ≤
        recurrenceBudgetT j (4 * productRecurrenceA j z * z) ^ j := by
      positivity
    linarith
  exact one_le_mul_of_one_le_of_one_le hA hbracket

/-- The two displayed product-recurrence budgets are simultaneously at least
one on the source domain. -/
theorem productRecurrenceBudgets_values_ge_one
    (j : ℕ) (hj : 1 ≤ j) (z : ℝ) (hz : 2 ≤ z) :
    1 ≤ productRecurrenceA j z ∧ 1 ≤ productRecurrenceB j z := by
  exact ⟨productRecurrenceA_ge_one j hj z hz,
    productRecurrenceB_ge_one j hj z hz⟩

end FractionalPrimes.Literature.Polynomial
