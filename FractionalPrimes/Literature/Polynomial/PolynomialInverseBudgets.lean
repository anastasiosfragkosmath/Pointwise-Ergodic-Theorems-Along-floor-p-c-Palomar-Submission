module

public import FractionalPrimes.Literature.Polynomial.PolynomialRecurrenceBudgets
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

abbrev InverseBudgetBivariate := MvPolynomial (Fin 2) ℕ

noncomputable def inverseBudgetB : InverseBudgetBivariate :=
  MvPolynomial.X (0 : Fin 2)

noncomputable def inverseBudgetY : InverseBudgetBivariate :=
  MvPolynomial.X (1 : Fin 2)

/-- `D_d = 1+d 2^d` in the approved inverse-budget definition. -/
def inverseBoundDValue (d : ℕ) : ℕ := 1 + d * 2 ^ d

/-- `E_d = 1+d 2^d d^d` in the approved inverse-budget definition. -/
def inverseBoundEValue (d : ℕ) : ℕ := 1 + d * 2 ^ d * d ^ d

/-- The progression inverse polynomial
`G_d(x)=(4x)^d+(d+1)8^d F_d(4x)x^(2d)+1`. -/
noncomputable def inverseBoundGPolynomial (d : ℕ) : Polynomial ℕ :=
  (C 4 * X) ^ d +
    C ((d + 1) * 8 ^ d) * (weylBoundPolynomial d).comp (C 4 * X) * X ^ (2 * d) +
    1

/-- Real evaluation of the checked scalar-Weyl polynomial `F_d`. -/
noncomputable def inverseBoundF (d : ℕ) (x : ℝ) : ℝ :=
  (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) x

/-- The recurrence T term `T_j(8By)` as a bivariate polynomial. -/
noncomputable def inverseBoundTTermPolynomial (j : ℕ) : InverseBudgetBivariate :=
  (recurrenceBudgetTPolynomial j).eval₂
    (Nat.castRingHom InverseBudgetBivariate)
    (MvPolynomial.C 8 * inverseBudgetB * inverseBudgetY)

/-- The recurrence R term `R_j(8By)` as a bivariate polynomial. -/
noncomputable def inverseBoundRTermPolynomial (j : ℕ) : InverseBudgetBivariate :=
  ((recurrenceBudgets j).R).eval₂
    (Nat.castRingHom InverseBudgetBivariate)
    (MvPolynomial.C 8 * inverseBudgetB * inverseBudgetY)

/-- `T=1+∑_{j=1}^d T_j(8By)` from the inverse-budget definition. -/
noncomputable def inverseBoundAggregateTPolynomial (d : ℕ) : InverseBudgetBivariate :=
  1 + ∑ j ∈ Finset.Icc 1 d, inverseBoundTTermPolynomial j

/-- `R=1+∑_{j=1}^d R_j(8By)` from the inverse-budget definition. -/
noncomputable def inverseBoundAggregateRPolynomial (d : ℕ) : InverseBudgetBivariate :=
  1 + ∑ j ∈ Finset.Icc 1 d, inverseBoundRTermPolynomial j

/-- `A₀=2T+2` from the inverse-budget definition. -/
noncomputable def inverseBoundAZeroPolynomial (d : ℕ) : InverseBudgetBivariate :=
  MvPolynomial.C 2 * inverseBoundAggregateTPolynomial d + MvPolynomial.C 2

/-- The exact recurrence `U₀=B`, `U_{k+1}=(4^d+1)D_d R U_k^2`. -/
noncomputable def inverseBoundUPolynomial (d : ℕ) : ℕ → InverseBudgetBivariate
  | 0 => inverseBudgetB
  | k + 1 =>
      MvPolynomial.C ((4 ^ d + 1) * inverseBoundDValue d) *
        inverseBoundAggregateRPolynomial d * inverseBoundUPolynomial d k ^ 2

/-- `V_d(B,y)` from the approved inverse-budget recursion. -/
noncomputable def inverseBoundVPolynomial (d : ℕ) : InverseBudgetBivariate :=
  MvPolynomial.C 4 +
    MvPolynomial.C (1024 * inverseBoundDValue d) * inverseBudgetB * inverseBudgetY *
      inverseBoundUPolynomial d d ^ 2 +
    MvPolynomial.C (2 ^ (d + 1)) * inverseBudgetB *
      (MvPolynomial.C 2 * inverseBoundAZeroPolynomial d) ^ d +
    inverseBoundUPolynomial d d

/-- `I_d(x)=E_d V_d(G_d(16x^4),256x^7)` as an explicit natural-coefficient
univariate polynomial. -/
noncomputable def inverseBoundIPolynomial (d : ℕ) : Polynomial ℕ :=
  C (inverseBoundEValue d) *
    MvPolynomial.eval₂Hom (Nat.castRingHom (Polynomial ℕ))
      (fun i : Fin 2 =>
        if i = 0 then (inverseBoundGPolynomial d).comp (C 16 * X ^ 4)
        else C 256 * X ^ 7)
      (inverseBoundVPolynomial d)

/-- The full data package for blueprint `lpi:inverse-budgets`.  Univariate
budgets have natural coefficients; budgets in `(B,y)` are bivariate natural
coefficient polynomials. -/
structure InverseBoundPolynomialData (d : ℕ) where
  D : ℕ
  E : ℕ
  G : Polynomial ℕ
  T : InverseBudgetBivariate
  R : InverseBudgetBivariate
  AZero : InverseBudgetBivariate
  U : ℕ → InverseBudgetBivariate
  V : InverseBudgetBivariate
  I : Polynomial ℕ

/-- The exact polynomial data `D_d,E_d,G_d,T,R,A₀,U_k,V_d,I_d` specified
by the approved scalar inverse-budget definition. -/
noncomputable def inverseBoundPolynomials (d : ℕ) :
    InverseBoundPolynomialData d where
  D := inverseBoundDValue d
  E := inverseBoundEValue d
  G := inverseBoundGPolynomial d
  T := inverseBoundAggregateTPolynomial d
  R := inverseBoundAggregateRPolynomial d
  AZero := inverseBoundAZeroPolynomial d
  U := inverseBoundUPolynomial d
  V := inverseBoundVPolynomial d
  I := inverseBoundIPolynomial d

/-- Real evaluation of a bivariate natural-coefficient polynomial at `(B,y)`. -/
noncomputable def inverseBoundBivariateEval (p : InverseBudgetBivariate)
    (B y : ℝ) : ℝ :=
  MvPolynomial.eval₂ (Nat.castRingHom ℝ)
    (fun i : Fin 2 => if i = 0 then B else y) p

/-- Real evaluation of `G_d`. -/
noncomputable def inverseBoundG (d : ℕ) (x : ℝ) : ℝ :=
  (inverseBoundGPolynomial d).eval₂ (Nat.castRingHom ℝ) x

/-- Real evaluation of the aggregate recurrence budget `T`. -/
noncomputable def inverseBoundAggregateT (d : ℕ) (B y : ℝ) : ℝ :=
  inverseBoundBivariateEval (inverseBoundAggregateTPolynomial d) B y

/-- Real evaluation of the aggregate recurrence budget `R`. -/
noncomputable def inverseBoundAggregateR (d : ℕ) (B y : ℝ) : ℝ :=
  inverseBoundBivariateEval (inverseBoundAggregateRPolynomial d) B y

/-- Real evaluation of `A₀=2T+2`. -/
noncomputable def inverseBoundAZero (d : ℕ) (B y : ℝ) : ℝ :=
  inverseBoundBivariateEval (inverseBoundAZeroPolynomial d) B y

/-- Real evaluation of `U_k`. -/
noncomputable def inverseBoundU (d k : ℕ) (B y : ℝ) : ℝ :=
  inverseBoundBivariateEval (inverseBoundUPolynomial d k) B y

/-- Real evaluation of `V_d(B,y)`. -/
noncomputable def inverseBoundV (d : ℕ) (B y : ℝ) : ℝ :=
  inverseBoundBivariateEval (inverseBoundVPolynomial d) B y

/-- Real evaluation of `I_d`. -/
noncomputable def inverseBoundI (d : ℕ) (x : ℝ) : ℝ :=
  (inverseBoundIPolynomial d).eval₂ (Nat.castRingHom ℝ) x

/-- The exact real-evaluation identity for `G_d`. -/
theorem inverseBoundG_eval (d : ℕ) (x : ℝ) :
    inverseBoundG d x =
      (4 * x) ^ d + (d + 1 : ℝ) * 8 ^ d * inverseBoundF d (4 * x) *
        x ^ (2 * d) + 1 := by
  simp [inverseBoundG, inverseBoundGPolynomial, inverseBoundF,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_comp]

private theorem inverseBound_polynomialEval_mvp
    (p : Polynomial ℕ) (B y : ℝ) :
    inverseBoundBivariateEval
        (p.eval₂ (Nat.castRingHom InverseBudgetBivariate)
          (MvPolynomial.C 8 * inverseBudgetB * inverseBudgetY)) B y =
      p.eval₂ (Nat.castRingHom ℝ) (8 * B * y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      change MvPolynomial.eval₂ (Nat.castRingHom ℝ)
          (fun i : Fin 2 => if i = 0 then B else y)
          (p.eval₂ (Nat.castRingHom InverseBudgetBivariate)
            (MvPolynomial.C 8 * inverseBudgetB * inverseBudgetY)) = _ at hp
      change MvPolynomial.eval₂ (Nat.castRingHom ℝ)
          (fun i : Fin 2 => if i = 0 then B else y)
          (q.eval₂ (Nat.castRingHom InverseBudgetBivariate)
            (MvPolynomial.C 8 * inverseBudgetB * inverseBudgetY)) = _ at hq
      change MvPolynomial.eval₂ (Nat.castRingHom ℝ)
          (fun i : Fin 2 => if i = 0 then B else y)
          ((p + q).eval₂ (Nat.castRingHom InverseBudgetBivariate)
            (MvPolynomial.C 8 * inverseBudgetB * inverseBudgetY)) =
        (p + q).eval₂ (Nat.castRingHom ℝ) (8 * B * y)
      rw [Polynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq,
        Polynomial.eval₂_add]
  | monomial n a =>
      simp [Polynomial.eval₂_monomial, inverseBoundBivariateEval,
        MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
        inverseBudgetB, inverseBudgetY]

/-- Evaluating the bivariate `T_j(8By)` term gives the recurrence budget at
the exact source argument `8By`. -/
theorem inverseBoundTTerm_eval (j : ℕ) (B y : ℝ) :
    inverseBoundBivariateEval (inverseBoundTTermPolynomial j) B y =
      recurrenceBudgetT j (8 * B * y) := by
  simpa [inverseBoundTTermPolynomial, recurrenceBudgetT, recurrenceBudgets] using
    inverseBound_polynomialEval_mvp (recurrenceBudgetTPolynomial j) B y

/-- Evaluating the bivariate `R_j(8By)` term gives the recurrence budget at
the exact source argument `8By`. -/
theorem inverseBoundRTerm_eval (j : ℕ) (B y : ℝ) :
    inverseBoundBivariateEval (inverseBoundRTermPolynomial j) B y =
      recurrenceBudgetR j (8 * B * y) := by
  simpa [inverseBoundRTermPolynomial, recurrenceBudgetR, recurrenceBudgets] using
    inverseBound_polynomialEval_mvp ((recurrenceBudgets j).R) B y

/-- The exact evaluation identity for the aggregate T budget. -/
theorem inverseBoundAggregateT_eval (d : ℕ) (B y : ℝ) :
    inverseBoundAggregateT d B y =
      1 + ∑ j ∈ Finset.Icc 1 d, recurrenceBudgetT j (8 * B * y) := by
  simp only [inverseBoundAggregateT, inverseBoundAggregateTPolynomial,
    inverseBoundBivariateEval, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact inverseBoundTTerm_eval j B y

/-- The exact evaluation identity for the aggregate R budget. -/
theorem inverseBoundAggregateR_eval (d : ℕ) (B y : ℝ) :
    inverseBoundAggregateR d B y =
      1 + ∑ j ∈ Finset.Icc 1 d, recurrenceBudgetR j (8 * B * y) := by
  simp only [inverseBoundAggregateR, inverseBoundAggregateRPolynomial,
    inverseBoundBivariateEval, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact inverseBoundRTerm_eval j B y

/-- The exact evaluation identity `A₀=2T+2`. -/
theorem inverseBoundAZero_eval (d : ℕ) (B y : ℝ) :
    inverseBoundAZero d B y = 2 * inverseBoundAggregateT d B y + 2 := by
  simp [inverseBoundAZero, inverseBoundAZeroPolynomial,
    inverseBoundAggregateT, inverseBoundAggregateTPolynomial,
    inverseBoundBivariateEval]

/-- The exact initial value in the `U_k` recurrence. -/
@[simp] theorem inverseBoundU_zero_eval (d : ℕ) (B y : ℝ) :
    inverseBoundU d 0 B y = B := by
  simp [inverseBoundU, inverseBoundUPolynomial, inverseBoundBivariateEval,
    inverseBudgetB]

/-- The exact successor step in the `U_k` recurrence. -/
theorem inverseBoundU_succ_eval (d k : ℕ) (B y : ℝ) :
    inverseBoundU d (k + 1) B y =
      (4 ^ d + 1 : ℝ) * (inverseBoundDValue d : ℝ) *
        inverseBoundAggregateR d B y * (inverseBoundU d k B y) ^ 2 := by
  simp [inverseBoundU, inverseBoundUPolynomial, inverseBoundBivariateEval,
    inverseBoundAggregateR, inverseBoundAggregateRPolynomial,
    inverseBoundRTermPolynomial, inverseBudgetB, inverseBudgetY,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow]

/-- The exact evaluation identity for `V_d(B,y)`. -/
theorem inverseBoundV_eval (d : ℕ) (B y : ℝ) :
    inverseBoundV d B y =
      4 + 1024 * (inverseBoundDValue d : ℝ) * B * y *
          (inverseBoundU d d B y) ^ 2 +
        2 ^ (d + 1) * B * (2 * inverseBoundAZero d B y) ^ d +
        inverseBoundU d d B y := by
  simp [inverseBoundV, inverseBoundVPolynomial, inverseBoundBivariateEval,
    inverseBudgetB, inverseBudgetY, inverseBoundDValue,
    inverseBoundU, inverseBoundAZero,
    inverseBoundAZeroPolynomial,
    inverseBoundAggregateTPolynomial, inverseBoundTTermPolynomial,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_pow]

/-- The exact evaluation identity for `I_d`. -/
theorem inverseBoundI_eval (d : ℕ) (x : ℝ) :
    inverseBoundI d x =
      (inverseBoundEValue d : ℝ) *
        inverseBoundV d (inverseBoundG d (16 * x ^ 4)) (256 * x ^ 7) := by
  let φ : Polynomial ℕ →+* ℝ :=
    Polynomial.eval₂RingHom (Nat.castRingHom ℝ) x
  have hcomp : φ.comp (Nat.castRingHom (Polynomial ℕ)) = Nat.castRingHom ℝ := by
    ext n
    simp [φ, Polynomial.eval₂RingHom]
  have hg : φ ((inverseBoundGPolynomial d).comp (C 16 * X ^ 4)) =
      inverseBoundG d (16 * x ^ 4) := by
    change ((inverseBoundGPolynomial d).comp (C 16 * X ^ 4)).eval₂
      (Nat.castRingHom ℝ) x = _
    rw [Polynomial.eval₂_comp]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, Polynomial.eval₂_pow]
    rfl
  have hy : φ (C 256 * X ^ 7) = 256 * x ^ 7 := by
    simp [φ, Polynomial.eval₂RingHom, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, Polynomial.eval₂_pow]
  have hmain :
      φ (MvPolynomial.eval₂Hom (Nat.castRingHom (Polynomial ℕ))
        (fun i : Fin 2 =>
          if i = 0 then (inverseBoundGPolynomial d).comp (C 16 * X ^ 4)
          else C 256 * X ^ 7) (inverseBoundVPolynomial d)) =
        inverseBoundV d (inverseBoundG d (16 * x ^ 4)) (256 * x ^ 7) := by
    change φ (MvPolynomial.eval₂ (Nat.castRingHom (Polynomial ℕ))
      (fun i : Fin 2 =>
        if i = 0 then (inverseBoundGPolynomial d).comp (C 16 * X ^ 4)
        else C 256 * X ^ 7) (inverseBoundVPolynomial d)) = _
    rw [MvPolynomial.hom_eval₂]
    rw [hcomp]
    have hvars :
        (fun i : Fin 2 =>
          φ (if i = 0 then (inverseBoundGPolynomial d).comp (C 16 * X ^ 4)
            else C 256 * X ^ 7)) =
        (fun i : Fin 2 =>
          if i = 0 then inverseBoundG d (16 * x ^ 4) else 256 * x ^ 7) := by
      funext i
      fin_cases i
      · simpa using hg
      · simpa using hy
    rw [hvars]
    rfl
  change (inverseBoundIPolynomial d).eval₂ (Nat.castRingHom ℝ) x = _
  rw [inverseBoundIPolynomial, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  change (inverseBoundEValue d : ℝ) *
      φ (MvPolynomial.eval₂Hom (Nat.castRingHom (Polynomial ℕ))
        (fun i : Fin 2 =>
          if i = 0 then (inverseBoundGPolynomial d).comp (C 16 * X ^ 4)
          else C 256 * X ^ 7) (inverseBoundVPolynomial d)) = _
  rw [hmain]

private theorem inverseBound_natPolynomial_eval_nonneg
    (p : Polynomial ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ p.eval₂ (Nat.castRingHom ℝ) x := by
  rw [Polynomial.eval₂_eq_sum_range]
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)

private theorem inverseBound_bivariate_eval_nonneg
    (p : InverseBudgetBivariate) (B y : ℝ)
    (hB : 0 ≤ B) (hy : 0 ≤ y) :
    0 ≤ inverseBoundBivariateEval p B y := by
  change 0 ≤ MvPolynomial.eval₂ (Nat.castRingHom ℝ)
    (fun i : Fin 2 => if i = 0 then B else y) p
  rw [MvPolynomial.eval₂_eq]
  have hvars : ∀ i : Fin 2, 0 ≤ (if i = 0 then B else y) := by
    intro i
    fin_cases i <;> simp [hB, hy]
  apply Finset.sum_nonneg
  intro m hm
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.prod_nonneg
  intro i hi
  exact pow_nonneg (hvars i) _

/-- Every coefficient of every natural-coefficient polynomial is
nonnegative after casting to `ℝ`. -/
theorem inverseBoundPolynomial_coeff_nonneg (p : Polynomial ℕ) (n : ℕ) :
    0 ≤ ((p.coeff n : ℕ) : ℝ) := Nat.cast_nonneg _

/-- Every coefficient of every bivariate natural-coefficient polynomial is
nonnegative after casting to `ℝ`. -/
theorem inverseBoundBivariate_coeff_nonneg
    (p : InverseBudgetBivariate) (m : Fin 2 →₀ ℕ) :
    0 ≤ ((p.coeff m : ℕ) : ℝ) := Nat.cast_nonneg _

/-- The complete inverse-budget package has nonnegative coefficients in every
univariate and bivariate field. -/
theorem inverseBoundPolynomials_coeff_nonneg (d n k : ℕ)
    (m : Fin 2 →₀ ℕ) :
    0 ≤ (inverseBoundPolynomials d).D ∧
    0 ≤ (inverseBoundPolynomials d).E ∧
    0 ≤ (((inverseBoundPolynomials d).G.coeff n : ℕ) : ℝ) ∧
    0 ≤ (((inverseBoundPolynomials d).I.coeff n : ℕ) : ℝ) ∧
    0 ≤ (((inverseBoundPolynomials d).T.coeff m : ℕ) : ℝ) ∧
    0 ≤ (((inverseBoundPolynomials d).R.coeff m : ℕ) : ℝ) ∧
    0 ≤ (((inverseBoundPolynomials d).AZero.coeff m : ℕ) : ℝ) ∧
    0 ≤ (((((inverseBoundPolynomials d).U k).coeff m : ℕ) : ℝ)) ∧
    0 ≤ (((inverseBoundPolynomials d).V.coeff m : ℕ) : ℝ) := by
  exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.cast_nonneg _, Nat.cast_nonneg _,
    Nat.cast_nonneg _, Nat.cast_nonneg _, Nat.cast_nonneg _, Nat.cast_nonneg _,
    Nat.cast_nonneg _⟩

/-- The constants `D_d` and `E_d` are positive integers. -/
theorem inverseBoundD_ge_one (d : ℕ) : 1 ≤ inverseBoundDValue d := by
  simp [inverseBoundDValue]

theorem inverseBoundE_ge_one (d : ℕ) : 1 ≤ inverseBoundEValue d := by
  simp [inverseBoundEValue]

/-- The progression budget has the stated lower bound on `x≥2`. -/
theorem inverseBoundG_ge_one (d : ℕ) (x : ℝ) (hx : 2 ≤ x) :
    1 ≤ inverseBoundG d x := by
  rw [inverseBoundG_eval]
  have hx0 : 0 ≤ x := by linarith
  have h4x : 0 ≤ 4 * x := by positivity
  have hF : 0 ≤ inverseBoundF d (4 * x) := by
    exact inverseBound_natPolynomial_eval_nonneg _ _ h4x
  have hfirst : 0 ≤ (4 * x) ^ d := pow_nonneg (by positivity) _
  have hsecond : 0 ≤
      (d + 1 : ℝ) * 8 ^ d * inverseBoundF d (4 * x) * x ^ (2 * d) := by
    positivity
  linarith

private theorem inverseBound_8By_ge_two (B y : ℝ)
    (hB : 1 ≤ B) (hy : 2 ≤ y) : 2 ≤ 8 * B * y := by
  have hBy : 2 ≤ B * y := by
    calc
      2 = 1 * 2 := by norm_num
      _ ≤ B * y := mul_le_mul hB hy (by norm_num) (by linarith)
  calc
    2 ≤ 8 * 2 := by norm_num
    _ ≤ 8 * (B * y) := mul_le_mul_of_nonneg_left hBy (by norm_num)
    _ = 8 * B * y := by ring

/-- The aggregate recurrence T budget is at least one when `B≥1,y≥2`. -/
theorem inverseBoundAggregateT_ge_one (d : ℕ) (B y : ℝ)
    (hB : 1 ≤ B) (hy : 2 ≤ y) :
    1 ≤ inverseBoundAggregateT d B y := by
  rw [inverseBoundAggregateT_eval]
  have harg := inverseBound_8By_ge_two B y hB hy
  have hsum : 0 ≤
      ∑ j ∈ Finset.Icc 1 d, recurrenceBudgetT j (8 * B * y) := by
    apply Finset.sum_nonneg
    intro j hj
    have hjlow : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hterm := recurrenceBudgetT_ge_one j hjlow (8 * B * y) harg
    exact le_trans (by norm_num) hterm
  exact le_add_of_nonneg_right hsum

/-- The aggregate recurrence R budget is at least one when `B≥1,y≥2`. -/
theorem inverseBoundAggregateR_ge_one (d : ℕ) (B y : ℝ)
    (hB : 1 ≤ B) (hy : 2 ≤ y) :
    1 ≤ inverseBoundAggregateR d B y := by
  rw [inverseBoundAggregateR_eval]
  have harg := inverseBound_8By_ge_two B y hB hy
  have hsum : 0 ≤
      ∑ j ∈ Finset.Icc 1 d, recurrenceBudgetR j (8 * B * y) := by
    apply Finset.sum_nonneg
    intro j hj
    have hjlow : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hterm := recurrenceBudgetR_ge_one j hjlow (8 * B * y) harg
    exact le_trans (by norm_num) hterm
  exact le_add_of_nonneg_right hsum

/-- The initial count budget satisfies `A₀≥4` for `B≥1,y≥2`. -/
theorem inverseBoundAZero_ge_four (d : ℕ) (B y : ℝ)
    (hB : 1 ≤ B) (hy : 2 ≤ y) :
    4 ≤ inverseBoundAZero d B y := by
  rw [inverseBoundAZero_eval]
  have hT := inverseBoundAggregateT_ge_one d B y hB hy
  nlinarith

/-- Every value in the finite `U_k` recurrence is at least one for
`B≥1,y≥2`. -/
theorem inverseBoundU_ge_one (d : ℕ) (_hd : 1 ≤ d) (B y : ℝ)
    (hB : 1 ≤ B) (hy : 2 ≤ y) (k : ℕ) :
    1 ≤ inverseBoundU d k B y := by
  induction k with
  | zero => simpa using hB
  | succ k ih =>
      rw [inverseBoundU_succ_eval]
      have hCoeff : 1 ≤ (4 ^ d + 1 : ℝ) := by
        have hpow : 0 ≤ (4 : ℝ) ^ d := by positivity
        nlinarith
      have hD : 1 ≤ (inverseBoundDValue d : ℝ) := by
        exact_mod_cast inverseBoundD_ge_one d
      have hR := inverseBoundAggregateR_ge_one d B y hB hy
      have hU2 : 1 ≤ (inverseBoundU d k B y) ^ 2 := by
        simpa only [pow_two] using
          one_le_mul_of_one_le_of_one_le ih ih
      have hCoeffD := one_le_mul_of_one_le_of_one_le hCoeff hD
      have hCoeffDR := one_le_mul_of_one_le_of_one_le hCoeffD hR
      exact one_le_mul_of_one_le_of_one_le hCoeffDR hU2

/-- The main bivariate budget has lower bound four for `B≥1,y≥2`. -/
theorem inverseBoundV_ge_four (d : ℕ) (hd : 1 ≤ d) (B y : ℝ)
    (hB : 1 ≤ B) (hy : 2 ≤ y) :
    4 ≤ inverseBoundV d B y := by
  rw [inverseBoundV_eval]
  have hU := inverseBoundU_ge_one d hd B y hB hy d
  have hA := inverseBoundAZero_ge_four d B y hB hy
  have hfirst : 0 ≤
      1024 * (inverseBoundDValue d : ℝ) * B * y *
        (inverseBoundU d d B y) ^ 2 := by positivity
  have hsecond : 0 ≤
      2 ^ (d + 1) * B * (2 * inverseBoundAZero d B y) ^ d := by positivity
  linarith

/-- The final univariate inverse budget is at least four on `x≥2`. -/
theorem inverseBoundI_ge_four (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : 2 ≤ x) : 4 ≤ inverseBoundI d x := by
  rw [inverseBoundI_eval]
  have hx1 : 1 ≤ x := by linarith
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx1
  have hGarg : 2 ≤ 16 * x ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hx4 (by norm_num : (0 : ℝ) ≤ 16)
    nlinarith
  have hB : 1 ≤ inverseBoundG d (16 * x ^ 4) :=
    inverseBoundG_ge_one d (16 * x ^ 4) hGarg
  have hx7 : 1 ≤ x ^ 7 := one_le_pow₀ hx1
  have hy : 2 ≤ 256 * x ^ 7 := by
    have hmul := mul_le_mul_of_nonneg_left hx7 (by norm_num : (0 : ℝ) ≤ 256)
    nlinarith
  have hV := inverseBoundV_ge_four d hd
    (inverseBoundG d (16 * x ^ 4)) (256 * x ^ 7) hB hy
  have hE : 1 ≤ (inverseBoundEValue d : ℝ) := by
    exact_mod_cast inverseBoundE_ge_one d
  have hVone : 1 ≤ inverseBoundV d
      (inverseBoundG d (16 * x ^ 4)) (256 * x ^ 7) := by linarith
  have hVnonneg : 0 ≤ inverseBoundV d
      (inverseBoundG d (16 * x ^ 4)) (256 * x ^ 7) := by linarith
  calc
    4 = 1 * 4 := by norm_num
    _ ≤ (inverseBoundEValue d : ℝ) *
          inverseBoundV d (inverseBoundG d (16 * x ^ 4)) (256 * x ^ 7) :=
      mul_le_mul hE hV (by norm_num) (by linarith)

end FractionalPrimes.Literature.Polynomial
