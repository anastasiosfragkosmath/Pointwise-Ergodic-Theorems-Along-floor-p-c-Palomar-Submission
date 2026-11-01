module

public import FractionalPrimes.Literature.Polynomial.ScalarWeyl

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

/-- The five explicit polynomial data used in the higher-degree recurrence
closure.  The coefficient ring is `ℕ`, so coefficient nonnegativity is built
into the representation. -/
structure RecurrenceBudgetPolynomials where
  W : Polynomial ℕ
  J : Polynomial ℕ
  T : Polynomial ℕ
  L : Polynomial ℕ
  R : Polynomial ℕ

/-- The dense-set interpolation coefficient budget
`L_d = (d+1)[4(d+1)]^d`. -/
def recurrenceBudgetLValue (d : ℕ) : ℕ :=
  (d + 1) * (4 * (d + 1)) ^ d

/-- `W_d(x) = F_d(10x)`, using the checked scalar-Weyl polynomial `F_d`. -/
noncomputable def recurrenceBudgetWPolynomial (d : ℕ) : Polynomial ℕ :=
  (weylBoundPolynomial d).comp (C 10 * X)

/-- `J_d(x) = (2d+3)W_d(x)`. -/
noncomputable def recurrenceBudgetJPolynomial (d : ℕ) : Polynomial ℕ :=
  C (2 * d + 3) * recurrenceBudgetWPolynomial d

/-- `T_d(x) = 4(d+1)^2 J_d(x)x`, with the source convention `T_0=1`. -/
noncomputable def recurrenceBudgetTPolynomial (d : ℕ) : Polynomial ℕ :=
  if d = 0 then 1 else
    C (4 * (d + 1) ^ 2) * recurrenceBudgetJPolynomial d * X

/-- The constant polynomial representing `L_d`. -/
noncomputable def recurrenceBudgetLPolynomial (d : ℕ) : Polynomial ℕ :=
  C (recurrenceBudgetLValue d)

/-- The nonconstant-degree formula for `R_d`; the public budget below uses
the source convention `R_0=1`. -/
noncomputable def recurrenceBudgetRFormula (d : ℕ) : Polynomial ℕ :=
  C 68 * X * (recurrenceBudgetWPolynomial d) ^ 2 +
    C 17 * recurrenceBudgetLPolynomial d * X * recurrenceBudgetWPolynomial d *
      (recurrenceBudgetJPolynomial d * X) ^ d +
    C 17 * X * recurrenceBudgetWPolynomial d

@[simp] theorem recurrenceBudgetTPolynomial_zero :
    recurrenceBudgetTPolynomial 0 = 1 := by
  simp [recurrenceBudgetTPolynomial]

/-- The explicit recurrence budgets from blueprint `lpi:recurrence-budgets`.
For `d≥1`, the fields are exactly the displayed polynomials in the blueprint;
at degree zero, `T` and `R` are the constant polynomial one. -/
noncomputable def recurrenceBudgets (d : ℕ) : RecurrenceBudgetPolynomials where
  W := recurrenceBudgetWPolynomial d
  J := recurrenceBudgetJPolynomial d
  T := recurrenceBudgetTPolynomial d
  L := recurrenceBudgetLPolynomial d
  R := if d = 0 then 1 else recurrenceBudgetRFormula d

@[simp] theorem recurrenceBudgets_T_zero : (recurrenceBudgets 0).T = 1 := by
  simp [recurrenceBudgets]

@[simp] theorem recurrenceBudgets_R_zero : (recurrenceBudgets 0).R = 1 := by
  simp [recurrenceBudgets]

/-- Real evaluation of the explicit `W_d` polynomial. -/
noncomputable def recurrenceBudgetW (d : ℕ) (x : ℝ) : ℝ :=
  (recurrenceBudgetWPolynomial d).eval₂ (Nat.castRingHom ℝ) x

/-- Real evaluation of the explicit `J_d` polynomial. -/
noncomputable def recurrenceBudgetJ (d : ℕ) (x : ℝ) : ℝ :=
  (recurrenceBudgetJPolynomial d).eval₂ (Nat.castRingHom ℝ) x

/-- Real evaluation of the explicit `T_d` polynomial. -/
noncomputable def recurrenceBudgetT (d : ℕ) (x : ℝ) : ℝ :=
  ((recurrenceBudgets d).T).eval₂ (Nat.castRingHom ℝ) x

/-- Real evaluation of the constant `L_d` polynomial. -/
noncomputable def recurrenceBudgetL (d : ℕ) (x : ℝ) : ℝ :=
  ((recurrenceBudgets d).L).eval₂ (Nat.castRingHom ℝ) x

/-- Real evaluation of the explicit `R_d` polynomial. -/
noncomputable def recurrenceBudgetR (d : ℕ) (x : ℝ) : ℝ :=
  ((recurrenceBudgets d).R).eval₂ (Nat.castRingHom ℝ) x

/-- Every coefficient in every stored budget polynomial is nonnegative after
viewing it as a real coefficient. -/
theorem recurrenceBudgets_coeff_nonneg (d n : ℕ) :
    0 ≤ (((recurrenceBudgets d).W.coeff n : ℕ) : ℝ) ∧
    0 ≤ (((recurrenceBudgets d).J.coeff n : ℕ) : ℝ) ∧
    0 ≤ (((recurrenceBudgets d).T.coeff n : ℕ) : ℝ) ∧
    0 ≤ (((recurrenceBudgets d).L.coeff n : ℕ) : ℝ) ∧
    0 ≤ (((recurrenceBudgets d).R.coeff n : ℕ) : ℝ) := by
  exact ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, Nat.cast_nonneg _,
    Nat.cast_nonneg _, Nat.cast_nonneg _⟩

/-- The explicit `W_d` budget is at least one for every stated degree and
argument.  This is the checked scalar-Weyl power-control estimate at `10x`. -/
theorem recurrenceBudgetW_ge_one (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : 2 ≤ x) : 1 ≤ recurrenceBudgetW d x := by
  rw [recurrenceBudgetW, recurrenceBudgetWPolynomial, Polynomial.eval₂_comp]
  have h10x : 1 ≤ 10 * x := by nlinarith
  simpa using (weylBoundPowerControl d hd (10 * x) h10x).1

/-- The exact real-evaluation formula `W_d(x)=F_d(10x)`. -/
theorem recurrenceBudgetW_eval (d : ℕ) (x : ℝ) :
    recurrenceBudgetW d x =
      (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) (10 * x) := by
  rw [recurrenceBudgetW, recurrenceBudgetWPolynomial, Polynomial.eval₂_comp]
  simp

/-- The exact real-evaluation formula for `J_d`. -/
theorem recurrenceBudgetJ_eval (d : ℕ) (x : ℝ) :
    recurrenceBudgetJ d x = (2 * d + 3 : ℕ) * recurrenceBudgetW d x := by
  simp [recurrenceBudgetJ, recurrenceBudgetJPolynomial, recurrenceBudgetW,
    Polynomial.eval₂_mul]

/-- The exact real-evaluation formula for `T_d` in positive degree. -/
theorem recurrenceBudgetT_eval (d : ℕ) (hd : 1 ≤ d) (x : ℝ) :
    recurrenceBudgetT d x =
      (4 * (d + 1) ^ 2 : ℕ) * recurrenceBudgetJ d x * x := by
  have hd0 : d ≠ 0 := by omega
  have hJ : (recurrenceBudgetJPolynomial d).eval₂
      (Nat.castRingHom ℝ) x = recurrenceBudgetJ d x := rfl
  change (if d = 0 then 1 else
    C (4 * (d + 1) ^ 2) * recurrenceBudgetJPolynomial d * X).eval₂
      (Nat.castRingHom ℝ) x = _
  rw [ite_eq_right hd0]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  rw [hJ, recurrenceBudgetJ_eval]
  norm_cast

/-- The source convention for the degree-zero length budget. -/
@[simp] theorem recurrenceBudgetT_zero (x : ℝ) :
    recurrenceBudgetT 0 x = 1 := by
  simp [recurrenceBudgetT, recurrenceBudgets, recurrenceBudgetTPolynomial]

/-- `L_d` is the exact constant specified by the dense interpolation bound. -/
@[simp] theorem recurrenceBudgetL_eval (d : ℕ) (x : ℝ) :
    recurrenceBudgetL d x = (recurrenceBudgetLValue d : ℝ) := by
  simp [recurrenceBudgetL, recurrenceBudgets, recurrenceBudgetLPolynomial]

/-- The exact real-evaluation formula for `R_d` in positive degree. -/
theorem recurrenceBudgetR_eval (d : ℕ) (hd : 1 ≤ d) (x : ℝ) :
    recurrenceBudgetR d x =
      68 * x * recurrenceBudgetW d x ^ 2 +
        17 * recurrenceBudgetL d x * x * recurrenceBudgetW d x *
          (recurrenceBudgetJ d x * x) ^ d +
        17 * x * recurrenceBudgetW d x := by
  have hd0 : d ≠ 0 := by omega
  change (if d = 0 then 1 else recurrenceBudgetRFormula d).eval₂
      (Nat.castRingHom ℝ) x = _
  rw [ite_eq_right hd0]
  simp [recurrenceBudgetRFormula, recurrenceBudgetL, recurrenceBudgets,
    recurrenceBudgetLPolynomial, recurrenceBudgetLValue, recurrenceBudgetJ,
    recurrenceBudgetJPolynomial, recurrenceBudgetW, recurrenceBudgetWPolynomial,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_comp]

/-- The source convention for the degree-zero recurrence budget. -/
@[simp] theorem recurrenceBudgetR_zero (x : ℝ) :
    recurrenceBudgetR 0 x = 1 := by
  simp [recurrenceBudgetR, recurrenceBudgets]

/-- The exact interpolation coefficient budget is at least one. -/
theorem recurrenceBudgetL_ge_one (d : ℕ) (x : ℝ) :
    1 ≤ recurrenceBudgetL d x := by
  have hleft : 1 ≤ d + 1 := by omega
  have hbase : 1 ≤ 4 * (d + 1) := by omega
  have hpow : 1 ≤ (4 * (d + 1)) ^ d := Nat.one_le_pow _ _ hbase
  have hval : 1 ≤ recurrenceBudgetLValue d := by
    dsimp [recurrenceBudgetLValue]
    exact one_le_mul_of_one_le_of_one_le hleft hpow
  rw [recurrenceBudgetL_eval]
  exact_mod_cast hval

/-- The `J_d` budget is at least one for every stated degree and argument. -/
theorem recurrenceBudgetJ_ge_one (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : 2 ≤ x) : 1 ≤ recurrenceBudgetJ d x := by
  rw [recurrenceBudgetJ_eval]
  have hcoeffNat : 1 ≤ 2 * d + 3 := by omega
  have hcoeff : (1 : ℝ) ≤ (2 * d + 3 : ℕ) := by exact_mod_cast hcoeffNat
  exact one_le_mul_of_one_le_of_one_le hcoeff
    (recurrenceBudgetW_ge_one d hd x hx)

/-- The `T_d` budget is at least one for every stated degree and argument. -/
theorem recurrenceBudgetT_ge_one (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : 2 ≤ x) : 1 ≤ recurrenceBudgetT d x := by
  rw [recurrenceBudgetT_eval d hd x]
  have hdsq : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hcoeffNat : 1 ≤ 4 * (d + 1) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (by norm_num) hdsq
  have hcoeff : (1 : ℝ) ≤ (4 * (d + 1) ^ 2 : ℕ) := by
    exact_mod_cast hcoeffNat
  have hA : 1 ≤ (4 * (d + 1) ^ 2 : ℕ) * recurrenceBudgetJ d x :=
    one_le_mul_of_one_le_of_one_le hcoeff
      (recurrenceBudgetJ_ge_one d hd x hx)
  exact one_le_mul_of_one_le_of_one_le hA (by linarith)

/-- The `R_d` budget is at least one for every stated degree and argument. -/
theorem recurrenceBudgetR_ge_one (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : 2 ≤ x) : 1 ≤ recurrenceBudgetR d x := by
  rw [recurrenceBudgetR_eval d hd x]
  have hW := recurrenceBudgetW_ge_one d hd x hx
  have hJ := recurrenceBudgetJ_ge_one d hd x hx
  have hL := recurrenceBudgetL_ge_one d x
  have hx1 : 1 ≤ x := by linarith
  have h17 : (1 : ℝ) ≤ 17 := by norm_num
  have h17x : 1 ≤ 17 * x := one_le_mul_of_one_le_of_one_le h17 hx1
  have hterm3 : 1 ≤ 17 * x * recurrenceBudgetW d x :=
    one_le_mul_of_one_le_of_one_le h17x hW
  have hterm1 : 0 ≤ 68 * x * recurrenceBudgetW d x ^ 2 := by
    positivity
  have hterm2 : 0 ≤
      17 * recurrenceBudgetL d x * x * recurrenceBudgetW d x *
        (recurrenceBudgetJ d x * x) ^ d := by
    positivity
  calc
    1 ≤ 17 * x * recurrenceBudgetW d x := hterm3
    _ ≤ 68 * x * recurrenceBudgetW d x ^ 2 +
          17 * recurrenceBudgetL d x * x * recurrenceBudgetW d x *
            (recurrenceBudgetJ d x * x) ^ d +
          17 * x * recurrenceBudgetW d x := by linarith

/-- The five displayed positive-degree budgets are simultaneously at least
one on the source domain `x≥2`. -/
theorem recurrenceBudgets_values_ge_one (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : 2 ≤ x) :
    1 ≤ recurrenceBudgetW d x ∧
    1 ≤ recurrenceBudgetJ d x ∧
    1 ≤ recurrenceBudgetT d x ∧
    1 ≤ recurrenceBudgetL d x ∧
    1 ≤ recurrenceBudgetR d x := by
  exact ⟨recurrenceBudgetW_ge_one d hd x hx,
    recurrenceBudgetJ_ge_one d hd x hx,
    recurrenceBudgetT_ge_one d hd x hx,
    recurrenceBudgetL_ge_one d x,
    recurrenceBudgetR_ge_one d hd x hx⟩

end FractionalPrimes.Literature.Polynomial
