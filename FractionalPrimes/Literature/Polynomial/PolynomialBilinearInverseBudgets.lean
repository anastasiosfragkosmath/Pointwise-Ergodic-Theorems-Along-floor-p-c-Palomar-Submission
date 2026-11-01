module

public import FractionalPrimes.Literature.Polynomial.PolynomialRecurrenceBudgets

/-!
# Explicit constants for the bilinear polynomial inverse theorem

This file formalizes blueprint item `lbi:budgets`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

noncomputable section

/-- `G_d(x)=T_d(x)+R_d(x)`, using the recurrence budgets. -/
def bilinearRecurrenceGPolynomial (d : ℕ) : Polynomial ℕ :=
  (recurrenceBudgets d).T + (recurrenceBudgets d).R

/-- `B(x)=F_d(2500x²)`. -/
def bilinearInverseBPolynomial (d : ℕ) : Polynomial ℕ :=
  (weylBoundPolynomial d).comp (C 2500 * X ^ 2)

/-- `Z₁(x)=40000x⁴B(x)`. -/
def bilinearInverseZOnePolynomial (d : ℕ) : Polynomial ℕ :=
  C 40000 * X ^ 4 * bilinearInverseBPolynomial d

/-- `V₁(x)=G_d(Z₁(x))`. -/
def bilinearInverseVOnePolynomial (d : ℕ) : Polynomial ℕ :=
  (bilinearRecurrenceGPolynomial d).comp (bilinearInverseZOnePolynomial d)

/-- `A(x)=B(x)V₁(x)^d`. -/
def bilinearInverseAPolynomial (d : ℕ) : Polynomial ℕ :=
  bilinearInverseBPolynomial d * bilinearInverseVOnePolynomial d ^ d

/-- `Z₂(x)=24000x⁴A(x)`. -/
def bilinearInverseZTwoPolynomial (d : ℕ) : Polynomial ℕ :=
  C 24000 * X ^ 4 * bilinearInverseAPolynomial d

/-- `V₂(x)=G_d(Z₂(x))`. -/
def bilinearInverseVTwoPolynomial (d : ℕ) : Polynomial ℕ :=
  (bilinearRecurrenceGPolynomial d).comp (bilinearInverseZTwoPolynomial d)

/-- `C_d=2^(2d+2)(d+1)44^d`. -/
def bilinearInverseCValue (d : ℕ) : ℕ :=
  2 ^ (2 * d + 2) * (d + 1) * 44 ^ d

/-- `E(x)=(C_d A(x)V₂(x))^(d-1)`. -/
def bilinearInverseEPolynomial (d : ℕ) : Polynomial ℕ :=
  (C (bilinearInverseCValue d) * bilinearInverseAPolynomial d *
      bilinearInverseVTwoPolynomial d) ^ (d - 1)

/-- The final polynomial `Z` in blueprint item `lbi:budgets`. -/
def bilinearInverseZPolynomial (d : ℕ) : Polynomial ℕ :=
  C 8 + bilinearInverseVOnePolynomial d + bilinearInverseVTwoPolynomial d +
    C 64 * bilinearInverseBPolynomial d * bilinearInverseZOnePolynomial d +
    C 64 * C (bilinearInverseCValue d) * bilinearInverseAPolynomial d *
      bilinearInverseEPolynomial d * bilinearInverseZTwoPolynomial d +
    C (bilinearInverseCValue d) * bilinearInverseAPolynomial d *
      bilinearInverseEPolynomial d

/-- All natural-coefficient polynomials displayed in `lbi:budgets`. -/
structure BilinearInverseBudgetPolynomials where
  G : Polynomial ℕ
  B : Polynomial ℕ
  ZOne : Polynomial ℕ
  VOne : Polynomial ℕ
  A : Polynomial ℕ
  ZTwo : Polynomial ℕ
  VTwo : Polynomial ℕ
  CValue : ℕ
  E : Polynomial ℕ
  Z : Polynomial ℕ

/-- Exact natural-coefficient package for blueprint item `lbi:budgets`. -/
def bilinearInverseBudgets (d : ℕ) : BilinearInverseBudgetPolynomials where
  G := bilinearRecurrenceGPolynomial d
  B := bilinearInverseBPolynomial d
  ZOne := bilinearInverseZOnePolynomial d
  VOne := bilinearInverseVOnePolynomial d
  A := bilinearInverseAPolynomial d
  ZTwo := bilinearInverseZTwoPolynomial d
  VTwo := bilinearInverseVTwoPolynomial d
  CValue := bilinearInverseCValue d
  E := bilinearInverseEPolynomial d
  Z := bilinearInverseZPolynomial d

/-- `K_d^bil=Z(1)`. -/
def bilinearInverseConstant (d : ℕ) : ℕ :=
  (bilinearInverseZPolynomial d).eval 1

/-- `c_d^bil=deg Z`, represented by its natural degree. -/
def bilinearInverseExponent (d : ℕ) : ℕ :=
  (bilinearInverseZPolynomial d).natDegree

/-- Real evaluation of a natural-coefficient budget polynomial. -/
def bilinearInversePolynomialEval (p : Polynomial ℕ) (x : ℝ) : ℝ :=
  p.eval₂ (Nat.castRingHom ℝ) x

def bilinearRecurrenceG (d : ℕ) (x : ℝ) : ℝ :=
  bilinearInversePolynomialEval (bilinearRecurrenceGPolynomial d) x

def bilinearInverseB (d : ℕ) (x : ℝ) : ℝ :=
  bilinearInversePolynomialEval (bilinearInverseBPolynomial d) x

def bilinearInverseZOne (d : ℕ) (x : ℝ) : ℝ :=
  bilinearInversePolynomialEval (bilinearInverseZOnePolynomial d) x

def bilinearInverseVOne (d : ℕ) (x : ℝ) : ℝ :=
  bilinearInversePolynomialEval (bilinearInverseVOnePolynomial d) x

def bilinearInverseA (d : ℕ) (x : ℝ) : ℝ :=
  bilinearInversePolynomialEval (bilinearInverseAPolynomial d) x

def bilinearInverseZTwo (d : ℕ) (x : ℝ) : ℝ :=
  bilinearInversePolynomialEval (bilinearInverseZTwoPolynomial d) x

def bilinearInverseVTwo (d : ℕ) (x : ℝ) : ℝ :=
  bilinearInversePolynomialEval (bilinearInverseVTwoPolynomial d) x

def bilinearInverseE (d : ℕ) (x : ℝ) : ℝ :=
  bilinearInversePolynomialEval (bilinearInverseEPolynomial d) x

def bilinearInverseZ (d : ℕ) (x : ℝ) : ℝ :=
  bilinearInversePolynomialEval (bilinearInverseZPolynomial d) x

theorem bilinearRecurrenceG_eval (d : ℕ) (x : ℝ) :
    bilinearRecurrenceG d x = recurrenceBudgetT d x + recurrenceBudgetR d x := by
  simp [bilinearRecurrenceG, bilinearInversePolynomialEval,
    bilinearRecurrenceGPolynomial, recurrenceBudgetT, recurrenceBudgetR]

theorem bilinearInverseB_eval (d : ℕ) (x : ℝ) :
    bilinearInverseB d x =
      (weylBoundPolynomial d).eval₂ (Nat.castRingHom ℝ) (2500 * x ^ 2) := by
  simp [bilinearInverseB, bilinearInversePolynomialEval,
    bilinearInverseBPolynomial, Polynomial.eval₂_comp, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow]

theorem bilinearInverseZOne_eval (d : ℕ) (x : ℝ) :
    bilinearInverseZOne d x = 40000 * x ^ 4 * bilinearInverseB d x := by
  simp [bilinearInverseZOne, bilinearInversePolynomialEval,
    bilinearInverseZOnePolynomial, bilinearInverseB,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow]

theorem bilinearInverseVOne_eval (d : ℕ) (x : ℝ) :
    bilinearInverseVOne d x =
      bilinearRecurrenceG d (bilinearInverseZOne d x) := by
  simp [bilinearInverseVOne, bilinearInversePolynomialEval,
    bilinearInverseVOnePolynomial, bilinearRecurrenceG, bilinearInverseZOne,
    Polynomial.eval₂_comp]

theorem bilinearInverseA_eval (d : ℕ) (x : ℝ) :
    bilinearInverseA d x =
      bilinearInverseB d x * bilinearInverseVOne d x ^ d := by
  simp [bilinearInverseA, bilinearInversePolynomialEval,
    bilinearInverseAPolynomial, bilinearInverseB, bilinearInverseVOne,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow]

theorem bilinearInverseZTwo_eval (d : ℕ) (x : ℝ) :
    bilinearInverseZTwo d x = 24000 * x ^ 4 * bilinearInverseA d x := by
  simp [bilinearInverseZTwo, bilinearInversePolynomialEval,
    bilinearInverseZTwoPolynomial, bilinearInverseA,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow]

theorem bilinearInverseVTwo_eval (d : ℕ) (x : ℝ) :
    bilinearInverseVTwo d x =
      bilinearRecurrenceG d (bilinearInverseZTwo d x) := by
  simp [bilinearInverseVTwo, bilinearInversePolynomialEval,
    bilinearInverseVTwoPolynomial, bilinearRecurrenceG, bilinearInverseZTwo,
    Polynomial.eval₂_comp]

theorem bilinearInverseE_eval (d : ℕ) (x : ℝ) :
    bilinearInverseE d x =
      ((bilinearInverseCValue d : ℝ) * bilinearInverseA d x *
        bilinearInverseVTwo d x) ^ (d - 1) := by
  simp [bilinearInverseE, bilinearInversePolynomialEval,
    bilinearInverseEPolynomial, bilinearInverseA, bilinearInverseVTwo,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow]

theorem bilinearInverseZ_eval (d : ℕ) (x : ℝ) :
    bilinearInverseZ d x =
      8 + bilinearInverseVOne d x + bilinearInverseVTwo d x +
        64 * bilinearInverseB d x * bilinearInverseZOne d x +
        64 * (bilinearInverseCValue d : ℝ) * bilinearInverseA d x *
          bilinearInverseE d x * bilinearInverseZTwo d x +
        (bilinearInverseCValue d : ℝ) * bilinearInverseA d x *
          bilinearInverseE d x := by
  simp [bilinearInverseZ, bilinearInversePolynomialEval,
    bilinearInverseZPolynomial, bilinearInverseVOne, bilinearInverseVTwo,
    bilinearInverseB, bilinearInverseZOne, bilinearInverseA,
    bilinearInverseE, bilinearInverseZTwo, Polynomial.eval₂_add,
    Polynomial.eval₂_mul]

/-- All intermediate budget values have the positivity required by the two
recurrence applications. -/
theorem bilinearInverseBudget_values
    (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (hx : 2 ≤ x) :
    1 ≤ bilinearInverseB d x ∧
    2 < bilinearInverseZOne d x ∧
    2 ≤ bilinearInverseVOne d x ∧
    1 ≤ bilinearInverseA d x ∧
    2 < bilinearInverseZTwo d x ∧
    2 ≤ bilinearInverseVTwo d x ∧
    1 ≤ (bilinearInverseCValue d : ℝ) ∧
    1 ≤ bilinearInverseE d x ∧
    8 ≤ bilinearInverseZ d x := by
  have hx1 : 1 ≤ x := by linarith
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx1
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx1
  have harg : 1 ≤ 2500 * x ^ 2 := by nlinarith
  have hB : 1 ≤ bilinearInverseB d x := by
    rw [bilinearInverseB_eval]
    exact (weylBoundPowerControl d hd (2500 * x ^ 2) harg).1
  have hZOne : 2 < bilinearInverseZOne d x := by
    rw [bilinearInverseZOne_eval]
    calc
      (2 : ℝ) < 40000 * 1 * 1 := by norm_num
      _ ≤ 40000 * x ^ 4 * bilinearInverseB d x := by gcongr <;> norm_num
  have hVOne : 2 ≤ bilinearInverseVOne d x := by
    rw [bilinearInverseVOne_eval, bilinearRecurrenceG_eval]
    have hT := recurrenceBudgetT_ge_one d hd
      (bilinearInverseZOne d x) hZOne.le
    have hR := recurrenceBudgetR_ge_one d hd
      (bilinearInverseZOne d x) hZOne.le
    linarith
  have hA : 1 ≤ bilinearInverseA d x := by
    rw [bilinearInverseA_eval]
    exact one_le_mul_of_one_le_of_one_le hB
      (one_le_pow₀ (by linarith : 1 ≤ bilinearInverseVOne d x))
  have hZTwo : 2 < bilinearInverseZTwo d x := by
    rw [bilinearInverseZTwo_eval]
    calc
      (2 : ℝ) < 24000 * 1 * 1 := by norm_num
      _ ≤ 24000 * x ^ 4 * bilinearInverseA d x := by gcongr <;> norm_num
  have hVTwo : 2 ≤ bilinearInverseVTwo d x := by
    rw [bilinearInverseVTwo_eval, bilinearRecurrenceG_eval]
    have hT := recurrenceBudgetT_ge_one d hd
      (bilinearInverseZTwo d x) hZTwo.le
    have hR := recurrenceBudgetR_ge_one d hd
      (bilinearInverseZTwo d x) hZTwo.le
    linarith
  have hC : 1 ≤ (bilinearInverseCValue d : ℝ) := by
    have hnat : 1 ≤ bilinearInverseCValue d := by
      apply Nat.one_le_iff_ne_zero.mpr
      simp only [bilinearInverseCValue]
      positivity
    exact_mod_cast hnat
  have hE : 1 ≤ bilinearInverseE d x := by
    rw [bilinearInverseE_eval]
    have hbase : 1 ≤
        (bilinearInverseCValue d : ℝ) * bilinearInverseA d x *
          bilinearInverseVTwo d x :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hC hA) (by linarith)
    exact one_le_pow₀ hbase
  have hZ : 8 ≤ bilinearInverseZ d x := by
    rw [bilinearInverseZ_eval]
    have hnonneg1 : 0 ≤ bilinearInverseVOne d x := by linarith
    have hnonneg2 : 0 ≤ bilinearInverseVTwo d x := by linarith
    have hnonneg3 : 0 ≤
        64 * bilinearInverseB d x * bilinearInverseZOne d x := by positivity
    have hnonneg4 : 0 ≤
        64 * (bilinearInverseCValue d : ℝ) * bilinearInverseA d x *
          bilinearInverseE d x * bilinearInverseZTwo d x := by positivity
    have hnonneg5 : 0 ≤
        (bilinearInverseCValue d : ℝ) * bilinearInverseA d x *
          bilinearInverseE d x := by positivity
    linarith
  exact ⟨hB, hZOne, hVOne, hA, hZTwo, hVTwo, hC, hE, hZ⟩

/-- The final budget contains each summand used in the two recurrence stages. -/
theorem bilinearInverseZ_dominates
    (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (hx : 2 ≤ x) :
    bilinearInverseVOne d x ≤ bilinearInverseZ d x ∧
    bilinearInverseVTwo d x ≤ bilinearInverseZ d x ∧
    64 * bilinearInverseB d x * bilinearInverseZOne d x ≤
      bilinearInverseZ d x ∧
    64 * (bilinearInverseCValue d : ℝ) * bilinearInverseA d x *
        bilinearInverseE d x * bilinearInverseZTwo d x ≤
      bilinearInverseZ d x ∧
    (bilinearInverseCValue d : ℝ) * bilinearInverseA d x *
        bilinearInverseE d x ≤ bilinearInverseZ d x := by
  rcases bilinearInverseBudget_values d hd x hx with
    ⟨hB, hZOne, hVOne, hA, hZTwo, hVTwo, hC, hE, hZ⟩
  rw [bilinearInverseZ_eval]
  have h1 : 0 ≤ bilinearInverseVOne d x := by linarith
  have h2 : 0 ≤ bilinearInverseVTwo d x := by linarith
  have h3 : 0 ≤ 64 * bilinearInverseB d x * bilinearInverseZOne d x := by
    positivity
  have h4 : 0 ≤
      64 * (bilinearInverseCValue d : ℝ) * bilinearInverseA d x *
        bilinearInverseE d x * bilinearInverseZTwo d x := by positivity
  have h5 : 0 ≤
      (bilinearInverseCValue d : ℝ) * bilinearInverseA d x *
        bilinearInverseE d x := by positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Natural coefficients make nonnegativity of every displayed polynomial
structural. -/
theorem bilinearInverseBudgets_coeff_nonneg (d n : ℕ) :
    0 ≤ ((((bilinearInverseBudgets d).G.coeff n : ℕ) : ℝ)) ∧
    0 ≤ ((((bilinearInverseBudgets d).B.coeff n : ℕ) : ℝ)) ∧
    0 ≤ ((((bilinearInverseBudgets d).ZOne.coeff n : ℕ) : ℝ)) ∧
    0 ≤ ((((bilinearInverseBudgets d).VOne.coeff n : ℕ) : ℝ)) ∧
    0 ≤ ((((bilinearInverseBudgets d).A.coeff n : ℕ) : ℝ)) ∧
    0 ≤ ((((bilinearInverseBudgets d).ZTwo.coeff n : ℕ) : ℝ)) ∧
    0 ≤ ((((bilinearInverseBudgets d).VTwo.coeff n : ℕ) : ℝ)) ∧
    0 ≤ ((((bilinearInverseBudgets d).E.coeff n : ℕ) : ℝ)) ∧
    0 ≤ ((((bilinearInverseBudgets d).Z.coeff n : ℕ) : ℝ)) := by
  repeat' apply And.intro (Nat.cast_nonneg _)
  exact Nat.cast_nonneg _

theorem bilinearInverseConstant_ge_two (d : ℕ) :
    2 ≤ bilinearInverseConstant d := by
  change 2 ≤ (bilinearInverseZPolynomial d).eval 1
  simp only [bilinearInverseZPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C]
  omega

private theorem natPolynomial_eval_le_eval_one_mul_pow
    (p : Polynomial ℕ) (x : ℝ) (hx : 1 ≤ x) :
    p.eval₂ (Nat.castRingHom ℝ) x ≤
      ((p.eval 1 : ℕ) : ℝ) * x ^ p.natDegree := by
  let s := Finset.range (p.natDegree + 1)
  have hsum : (∑ i ∈ s, (p.coeff i : ℝ)) = ((p.eval 1 : ℕ) : ℝ) := by
    calc
      (∑ i ∈ s, (p.coeff i : ℝ)) =
          p.eval₂ (Nat.castRingHom ℝ) 1 := by
        symm
        dsimp [s]
        rw [Polynomial.eval₂_eq_sum_range]
        simp
      _ = ((p.eval 1 : ℕ) : ℝ) := by
        rw [Polynomial.eval₂_at_one]
        simp
  have hEval : p.eval₂ (Nat.castRingHom ℝ) x =
      ∑ i ∈ s, (p.coeff i : ℝ) * x ^ i := by
    dsimp [s]
    rw [Polynomial.eval₂_eq_sum_range]
    simp
  have hterms :
      (∑ i ∈ s, (p.coeff i : ℝ) * x ^ i) ≤
        ∑ i ∈ s, (p.coeff i : ℝ) * x ^ p.natDegree := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact pow_le_pow_right₀ hx
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  calc
    p.eval₂ (Nat.castRingHom ℝ) x =
        ∑ i ∈ s, (p.coeff i : ℝ) * x ^ i := hEval
    _ ≤ ∑ i ∈ s, (p.coeff i : ℝ) * x ^ p.natDegree := hterms
    _ = (∑ i ∈ s, (p.coeff i : ℝ)) * x ^ p.natDegree := by
      rw [Finset.sum_mul]
    _ = ((p.eval 1 : ℕ) : ℝ) * x ^ p.natDegree := by rw [hsum]

private theorem bilinearInverseB_natDegree_pos (d : ℕ) (hd : 1 ≤ d) :
    0 < (bilinearInverseBPolynomial d).natDegree := by
  rw [bilinearInverseBPolynomial, Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul (by norm_num : (2500 : ℕ) ≠ 0),
    Polynomial.natDegree_X_pow]
  exact Nat.mul_pos (weylBoundExponent_pos d hd) (by norm_num)

theorem bilinearInverseExponent_ge_one (d : ℕ) (hd : 1 ≤ d) :
    1 ≤ bilinearInverseExponent d := by
  let B := bilinearInverseBPolynomial d
  let ZOne := bilinearInverseZOnePolynomial d
  let T : Polynomial ℕ := C 64 * B * ZOne
  have hBdeg : 0 < B.natDegree := by
    simpa [B] using bilinearInverseB_natDegree_pos d hd
  have hB : B ≠ 0 := ne_zero_of_natDegree_gt hBdeg
  have hC40000 : (C 40000 : Polynomial ℕ) ≠ 0 := C_ne_zero.mpr (by norm_num)
  have hX4 : (X : Polynomial ℕ) ^ 4 ≠ 0 := pow_ne_zero _ X_ne_zero
  have hZOne : ZOne ≠ 0 := by
    dsimp [ZOne]
    exact mul_ne_zero (mul_ne_zero hC40000 hX4) hB
  have hC64 : (C 64 : Polynomial ℕ) ≠ 0 := C_ne_zero.mpr (by norm_num)
  have hT : T ≠ 0 := by
    dsimp [T]
    exact mul_ne_zero (mul_ne_zero hC64 hB) hZOne
  have hTdeg : 0 < T.natDegree := by
    dsimp [T]
    rw [Polynomial.natDegree_mul (mul_ne_zero hC64 hB) hZOne,
      Polynomial.natDegree_mul hC64 hB, Polynomial.natDegree_C]
    omega
  have hTcoeff : T.coeff T.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hT
  have hle : T.coeff T.natDegree ≤
      (bilinearInverseZPolynomial d).coeff T.natDegree := by
    change T.coeff T.natDegree ≤
      (((((C 8 + bilinearInverseVOnePolynomial d) +
          bilinearInverseVTwoPolynomial d) + T) +
          C 64 * C (bilinearInverseCValue d) *
            bilinearInverseAPolynomial d * bilinearInverseEPolynomial d *
            bilinearInverseZTwoPolynomial d) +
          C (bilinearInverseCValue d) * bilinearInverseAPolynomial d *
            bilinearInverseEPolynomial d).coeff T.natDegree
    simp only [Polynomial.coeff_add]
    omega
  have hZcoeff : (bilinearInverseZPolynomial d).coeff T.natDegree ≠ 0 := by
    have hpos : 0 < T.coeff T.natDegree := Nat.pos_of_ne_zero hTcoeff
    exact Nat.ne_of_gt (lt_of_lt_of_le hpos hle)
  change 1 ≤ (bilinearInverseZPolynomial d).natDegree
  exact le_trans (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hTdeg))
    (Polynomial.le_natDegree_of_ne_zero hZcoeff)

/-- On the approved positive-degree range, the natural exponent is exactly
the ordinary polynomial degree appearing in the blueprint. -/
theorem bilinearInverseExponent_eq_degree (d : ℕ) (hd : 1 ≤ d) :
    (bilinearInverseZPolynomial d).degree =
      (bilinearInverseExponent d : WithBot ℕ) := by
  apply Polynomial.degree_eq_natDegree
  exact ne_zero_of_natDegree_gt
    (Nat.lt_of_lt_of_le Nat.zero_lt_one
      (bilinearInverseExponent_ge_one d hd))

/-- For `x≥1`, the exact final polynomial is controlled by its value at one
times the corresponding degree power. -/
theorem bilinearInverseZ_le_budget (d : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    bilinearInverseZ d x ≤
      (bilinearInverseConstant d : ℝ) * x ^ bilinearInverseExponent d := by
  simpa [bilinearInverseZ, bilinearInversePolynomialEval,
    bilinearInverseConstant, bilinearInverseExponent] using
      natPolynomial_eval_le_eval_one_mul_pow
        (bilinearInverseZPolynomial d) x hx

#print axioms bilinearInverseBudgets
#print axioms bilinearInverseBudget_values
#print axioms bilinearInverseZ_dominates
#print axioms bilinearInverseConstant_ge_two
#print axioms bilinearInverseExponent_ge_one
#print axioms bilinearInverseExponent_eq_degree
#print axioms bilinearInverseZ_le_budget

end

end FractionalPrimes.Literature.Polynomial
