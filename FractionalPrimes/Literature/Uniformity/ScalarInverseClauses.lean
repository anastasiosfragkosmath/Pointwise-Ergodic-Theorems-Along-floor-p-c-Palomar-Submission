module

public import FractionalPrimes.Literature.Uniformity.TypeIIInverseOfBilinear

/-!
# Discharge of the scalar arithmetic inverse clauses

This file formalizes blueprint item `lu:inverse-discharge`.  It first exposes
the natural constants obtained by evaluating the two approved
positive-coefficient budget polynomials at one, then combines the checked
Type-I, Type-I₂, and Type-II clauses under the exact displayed maxima.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The natural Type-I constant `I_d(1)`. -/
def typeIArithmeticConstantNat (d : ℕ) : ℕ :=
  (inverseBoundIPolynomial d).eval 1

/-- The natural Type-I₂ constant `I_d^(2)(1)`. -/
def typeI2ArithmeticConstantNat (d : ℕ) : ℕ :=
  (typeI2BoundPolynomial d).eval 1

/-- The Type-I₂ exponent `deg I_d^(2)`. -/
def typeI2ArithmeticExponent (d : ℕ) : ℕ :=
  (typeI2BoundPolynomial d).natDegree

@[simp]
theorem typeIArithmeticConstantNat_cast (d : ℕ) :
    (typeIArithmeticConstantNat d : ℝ) = typeIArithmeticConstant d := rfl

@[simp]
theorem typeI2Bound_one (d : ℕ) :
    typeI2Bound d 1 = (typeI2ArithmeticConstantNat d : ℝ) := by
  simp [typeI2Bound, typeI2PolynomialEval, typeI2ArithmeticConstantNat,
    Polynomial.eval₂_at_one]

/-- A natural-coefficient polynomial at `x≥1` is bounded by its value at one
times `x` to its degree. -/
theorem natPolynomial_eval_le_eval_one_mul_pow
    (p : Polynomial ℕ) (x : ℝ) (hx : 1 ≤ x) :
    p.eval₂ (Nat.castRingHom ℝ) x ≤
      ((p.eval 1 : ℕ) : ℝ) * x ^ p.natDegree := by
  let s := Finset.range (p.natDegree + 1)
  have hsum : (∑ i ∈ s, (p.coeff i : ℝ)) = ((p.eval 1 : ℕ) : ℝ) := by
    calc
      (∑ i ∈ s, (p.coeff i : ℝ)) = p.eval₂ (Nat.castRingHom ℝ) 1 := by
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
  calc
    p.eval₂ (Nat.castRingHom ℝ) x =
        ∑ i ∈ s, (p.coeff i : ℝ) * x ^ i := hEval
    _ ≤ ∑ i ∈ s, (p.coeff i : ℝ) * x ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact pow_le_pow_right₀ hx
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _ = (∑ i ∈ s, (p.coeff i : ℝ)) * x ^ p.natDegree := by
      rw [Finset.sum_mul]
    _ = ((p.eval 1 : ℕ) : ℝ) * x ^ p.natDegree := by rw [hsum]

theorem typeI2Bound_le_arithmeticBudget (d : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    typeI2Bound d x ≤
      (typeI2ArithmeticConstantNat d : ℝ) * x ^ typeI2ArithmeticExponent d := by
  exact natPolynomial_eval_le_eval_one_mul_pow (typeI2BoundPolynomial d) x hx

/-- The checked scalar Type-I theorem in the exact specified-constant clause
interface. -/
theorem typeIInverseTask_exact (d : ℕ) (hd : 1 ≤ d) :
    typeIInverseTaskClause d (typeIArithmeticConstantNat d)
      (typeIArithmeticExponent d) := by
  intro X H P δ A_I f hX hH hHX hP hδ hδsmall hf hlarge
  have hXr : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hHint : (1 : ℤ) ≤ H := by omega
  have hHr : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHint
  have hHXr : (H : ℝ) ≤ (X : ℝ) := by exact_mod_cast hHX
  rcases typeIInverse_arithmetic d hd (X : ℝ) (H : ℝ) δ A_I hXr hHr hHXr
      hδ hδsmall f hf P hP hlarge with
    hshort | ⟨r, hrone, hrbound, hbin, _hmono⟩
  · left
    simpa [arithmeticInverseBudget, typeIArithmeticConstantNat_cast] using hshort
  · right
    refine ⟨r, hrone, ?_, ?_⟩
    · simpa [arithmeticInverseBudget, typeIArithmeticConstantNat_cast] using hrbound
    · simpa [binomialCoefficientNorm, arithmeticInverseBudget,
        typeIArithmeticConstantNat_cast] using hbin

/-- The checked scalar Type-I₂ theorem in the exact specified-constant clause
interface. -/
theorem typeI2InverseTask_exact (d : ℕ) (hd : 1 ≤ d) :
    typeI2InverseTaskClause d (typeI2ArithmeticConstantNat d)
      (typeI2ArithmeticExponent d) := by
  intro X H P δ A_I2 f hX hH hHX hP hδ hδsmall hf hlarge
  have hXr : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hHint : (1 : ℤ) ≤ H := by omega
  have hHr : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHint
  have hHXr : (H : ℝ) ≤ (X : ℝ) := by exact_mod_cast hHX
  have hδhalf : δ < 1 / 2 := hδsmall.trans_le (min_le_left _ _)
  have hδinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 (by linarith)
  have hbudget := typeI2Bound_le_arithmeticBudget d hδinv
  rcases typeI2Inverse d hd (X : ℝ) (H : ℝ) δ A_I2 hXr hHr hHXr
      hδ hδsmall f hf P hP hlarge with
    hshort | ⟨r, hrone, hrbound, hbin⟩
  · left
    have hscaleNonneg : 0 ≤
        Real.rpow (X : ℝ) (1 / 3 : ℝ) * Real.rpow A_I2 (2 / 3 : ℝ) := by
      exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (by linarith [hf.2.2.1]) _)
    calc
      (H : ℝ) ≤ typeI2Bound d δ⁻¹ * Real.rpow (X : ℝ) (1 / 3 : ℝ) *
          Real.rpow A_I2 (2 / 3 : ℝ) := hshort
      _ ≤ ((typeI2ArithmeticConstantNat d : ℝ) *
          δ⁻¹ ^ typeI2ArithmeticExponent d) *
          Real.rpow (X : ℝ) (1 / 3 : ℝ) *
          Real.rpow A_I2 (2 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbudget
            (Real.rpow_nonneg (by linarith) _))
          (Real.rpow_nonneg (by linarith [hf.2.2.1]) _)
      _ = arithmeticInverseBudget (typeI2ArithmeticConstantNat d)
          (typeI2ArithmeticExponent d) δ *
          Real.rpow (X : ℝ) (1 / 3 : ℝ) *
          Real.rpow A_I2 (2 / 3 : ℝ) := by
        rfl
  · right
    refine ⟨r, hrone, hrbound.trans hbudget, ?_⟩
    simpa [binomialCoefficientNorm, arithmeticInverseBudget] using
      hbin.trans hbudget

/-- Increasing the natural constant and exponent enlarges the arithmetic
budget throughout the source range `0<δ≤1`. -/
theorem arithmeticInverseBudget_mono
    {K K' c c' : ℕ} {δ : ℝ} (hK : K ≤ K') (hc : c ≤ c')
    (hδ : 0 < δ) (hδone : δ ≤ 1) :
    arithmeticInverseBudget K c δ ≤ arithmeticInverseBudget K' c' δ := by
  unfold arithmeticInverseBudget
  have hinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδone
  exact mul_le_mul (by exact_mod_cast hK) (pow_le_pow_right₀ hinv hc)
    (by positivity) (by positivity)

theorem typeIInverseTaskClause_mono
    {d K K' c c' : ℕ}
    (hclause : typeIInverseTaskClause d K c)
    (hK : K ≤ K') (hc : c ≤ c') :
    typeIInverseTaskClause d K' c' := by
  intro X H P δ A_I f hX hH hHX hP hδ hδsmall hf hlarge
  have hδone : δ ≤ 1 := by
    have := hδsmall.trans_le (min_le_left (1 / 2 : ℝ) _)
    linarith
  have hbudget := arithmeticInverseBudget_mono hK hc hδ hδone
  rcases hclause X H P δ A_I f hX hH hHX hP hδ hδsmall hf hlarge with
    hshort | ⟨r, hrone, hrbound, hbin⟩
  · left
    exact hshort.trans (mul_le_mul_of_nonneg_right hbudget (by linarith [hf.2.2.1]))
  · right
    exact ⟨r, hrone, hrbound.trans hbudget, hbin.trans hbudget⟩

theorem typeI2InverseTaskClause_mono
    {d K K' c c' : ℕ}
    (hclause : typeI2InverseTaskClause d K c)
    (hK : K ≤ K') (hc : c ≤ c') :
    typeI2InverseTaskClause d K' c' := by
  intro X H P δ A_I2 f hX hH hHX hP hδ hδsmall hf hlarge
  have hδone : δ ≤ 1 := by
    have := hδsmall.trans_le (min_le_left (1 / 2 : ℝ) _)
    linarith
  have hbudget := arithmeticInverseBudget_mono hK hc hδ hδone
  rcases hclause X H P δ A_I2 f hX hH hHX hP hδ hδsmall hf hlarge with
    hshort | ⟨r, hrone, hrbound, hbin⟩
  · left
    have hXnonneg : 0 ≤ (X : ℝ) := by exact_mod_cast (le_trans (by omega : (0 : ℤ) ≤ 3) hX)
    have hAInonneg : 0 ≤ A_I2 := by linarith [hf.2.2.1]
    calc
      (H : ℝ) ≤ arithmeticInverseBudget K c δ *
          Real.rpow (X : ℝ) (1 / 3 : ℝ) *
          Real.rpow A_I2 (2 / 3 : ℝ) := hshort
      _ ≤ arithmeticInverseBudget K' c' δ *
          Real.rpow (X : ℝ) (1 / 3 : ℝ) *
          Real.rpow A_I2 (2 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hXnonneg _))
          (Real.rpow_nonneg hAInonneg _)
  · right
    exact ⟨r, hrone, hrbound.trans hbudget, hbin.trans hbudget⟩

theorem typeIIInverseTaskClause_mono
    {d K K' c c' : ℕ}
    (hclause : typeIIInverseTaskClause d K c)
    (hK : K ≤ K') (hc : c ≤ c') :
    typeIIInverseTaskClause d K' c' := by
  intro X H P δ Aminus Aplus f hX hH hHX hP hδ hδsmall hf hlarge
  have hδone : δ ≤ 1 := by
    have := hδsmall.trans_le (min_le_left (1 / 2 : ℝ) _)
    linarith
  have hbudget := arithmeticInverseBudget_mono hK hc hδ hδone
  rcases hclause X H P δ Aminus Aplus f hX hH hHX hP hδ hδsmall hf hlarge with
    hshort | ⟨Q, hQone, hQbound, hQcoeff⟩
  · left
    have hscaleNonneg : 0 ≤ max Aplus ((X : ℝ) / Aminus) :=
      le_trans (by linarith [hf.2.2.2.1] : 0 ≤ Aplus) (le_max_left _ _)
    exact hshort.trans (mul_le_mul_of_nonneg_right hbudget hscaleNonneg)
  · right
    refine ⟨Q, hQone, hQbound.trans hbudget, ?_⟩
    intro j hjone hjd
    exact (hQcoeff j hjone hjd).trans (by
      have hXnonneg : 0 ≤ (X : ℝ) := by
        exact_mod_cast (le_trans (by omega : (0 : ℤ) ≤ 3) hX)
      have hHnonneg : 0 ≤ (H : ℝ) ^ (j + 1) := by positivity
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbudget hXnonneg) hHnonneg)

/-- The exact four-way maximum constant from `lu:inverse-discharge`. -/
def scalarInverseConstant (d : ℕ) : ℕ :=
  max 2 (max (typeIArithmeticConstantNat d)
    (max (typeI2ArithmeticConstantNat d)
      (2 * 8 ^ bilinearInverseExponent d * bilinearInverseConstant d)))

/-- The exact four-way maximum exponent from `lu:inverse-discharge`. -/
def scalarInverseExponent (d : ℕ) : ℕ :=
  max 1 (max (typeIArithmeticExponent d)
    (max (typeI2ArithmeticExponent d) (3 * bilinearInverseExponent d)))

theorem scalarInverseConstant_ge_two (d : ℕ) :
    2 ≤ scalarInverseConstant d := by simp [scalarInverseConstant]

theorem scalarInverseExponent_ge_one (d : ℕ) :
    1 ≤ scalarInverseExponent d := by simp [scalarInverseExponent]

theorem typeIArithmeticConstantNat_le_scalarInverseConstant (d : ℕ) :
    typeIArithmeticConstantNat d ≤ scalarInverseConstant d := by
  simp [scalarInverseConstant]

theorem typeI2ArithmeticConstantNat_le_scalarInverseConstant (d : ℕ) :
    typeI2ArithmeticConstantNat d ≤ scalarInverseConstant d := by
  simp [scalarInverseConstant]

theorem bilinearTypeIIConstant_le_scalarInverseConstant (d : ℕ) :
    2 * 8 ^ bilinearInverseExponent d * bilinearInverseConstant d ≤
      scalarInverseConstant d := by
  simp [scalarInverseConstant]

theorem typeIArithmeticExponent_le_scalarInverseExponent (d : ℕ) :
    typeIArithmeticExponent d ≤ scalarInverseExponent d := by
  simp [scalarInverseExponent]

theorem typeI2ArithmeticExponent_le_scalarInverseExponent (d : ℕ) :
    typeI2ArithmeticExponent d ≤ scalarInverseExponent d := by
  simp [scalarInverseExponent]

theorem bilinearTypeIIExponent_le_scalarInverseExponent (d : ℕ) :
    3 * bilinearInverseExponent d ≤ scalarInverseExponent d := by
  simp [scalarInverseExponent]

/-- Manifest-facing discharge of the exact proposition `INV`. -/
theorem scalarInverseClauses : arithmeticInverseTasks := by
  intro d hd
  refine ⟨scalarInverseConstant d, scalarInverseExponent d,
    scalarInverseConstant_ge_two d, scalarInverseExponent_ge_one d, ?_, ?_, ?_⟩
  · exact typeIInverseTaskClause_mono (typeIInverseTask_exact d hd)
      (typeIArithmeticConstantNat_le_scalarInverseConstant d)
      (typeIArithmeticExponent_le_scalarInverseExponent d)
  · exact typeI2InverseTaskClause_mono (typeI2InverseTask_exact d hd)
      (typeI2ArithmeticConstantNat_le_scalarInverseConstant d)
      (typeI2ArithmeticExponent_le_scalarInverseExponent d)
  · exact typeIIInverseTaskClause_mono
      (typeIIInverseOfBilinear d (bilinearInverseConstant d)
        (bilinearInverseExponent d) (bilinearCoefficientBound_exactConstants d hd))
      (bilinearTypeIIConstant_le_scalarInverseConstant d)
      (bilinearTypeIIExponent_le_scalarInverseExponent d)

#print axioms scalarInverseClauses

end

end FractionalPrimes.Literature.Uniformity

