module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalNormalizedMeanSquare
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Constants for the scalar trilinear Dirichlet mean

The exact constants in `ldm:constants`, together with the elementary
comparisons needed to dominate the existing normalized large-value and
mean-square constants in the next estimate.
-/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletMean

open scoped BigOperators

/-- The divisor exponent for the square of a factor with coefficient
exponent `C`. -/
def E (C : ℕ) : ℕ := 2 ^ (4 * C + 2) - 1

/-- The logarithmic exponent in the factor-and-square level estimate. -/
def b (C : ℕ) : ℕ := 3 * E C + 1

/-- The common level-set and mean-square constant from `ldm:constants`. -/
def K (C : ℕ) : ℝ := (2 : ℝ) ^ (b C + 40) * (3 : ℝ) ^ b C

/-- The final trilinear constant from `ldm:constants`. -/
def J (C : ℕ) : ℝ := (2 : ℝ) ^ 8 * K C

/-- The four constants bundled by the exact `ldm:constants` definition. -/
structure FactorMeanConstants where
  E : ℕ
  b : ℕ
  K : ℝ
  J : ℝ

/-- Exact bundle of the constants `E_C`, `b_C`, `K_C`, and `J_C`. -/
def constants (C : ℕ) : FactorMeanConstants where
  E := E C
  b := b C
  K := K C
  J := J C

@[simp] theorem constants_E (C : ℕ) : (constants C).E = E C := rfl
@[simp] theorem constants_b (C : ℕ) : (constants C).b = b C := rfl
@[simp] theorem constants_K (C : ℕ) : (constants C).K = K C := rfl
@[simp] theorem constants_J (C : ℕ) : (constants C).J = J C := rfl

/-- The exact coefficient condition for one factor in `ldm:constants`. -/
def factorCoefficientBound (C : ℕ) (N : ℝ) (coeff : ℕ → ℂ) : Prop :=
  ∀ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
    ‖coeff n‖ ≤
      (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C

/-- The finite frequency polynomial associated with a coefficient family,
including the factor `n^(-1/2)` in the source definition. -/
noncomputable def factorPolynomial (N : ℝ) (coeff : ℕ → ℂ) : ℝ → ℂ :=
  FractionalPrimes.Literature.LargeValues.dirichletPolynomial N
    (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff)

/-- Multiplication by a smaller coefficient modulus preserves the factor
coefficient hypothesis. -/
theorem factorCoefficientBound_of_norm_le
    {C : ℕ} {N : ℝ} {coeff coeff' : ℕ → ℂ}
    (hcoeff : factorCoefficientBound C N coeff)
    (hsmall : ∀ n ∈ FractionalPrimes.Literature.LargeValues.dirichletIndices N,
      ‖coeff' n‖ ≤ ‖coeff n‖) :
    factorCoefficientBound C N coeff' := by
  intro n hn
  exact (hsmall n hn).trans (hcoeff n hn)

/-- The unit phase `n^(iτ)` used to shift a factor does not change the
coefficient hypothesis. -/
noncomputable def factorTwistMultiplier (τ : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * (τ : ℂ) * (Real.log (n : ℝ) : ℂ))

theorem factorTwistMultiplier_norm (τ : ℝ) (n : ℕ) :
    ‖factorTwistMultiplier τ n‖ = 1 := by
  rw [factorTwistMultiplier, Complex.norm_exp]
  have hre :
      (Complex.I * (τ : ℂ) * (Real.log (n : ℝ) : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre, Real.exp_zero]

theorem factorCoefficientBound_twist
    {C : ℕ} {N τ : ℝ} {coeff : ℕ → ℂ}
    (hcoeff : factorCoefficientBound C N coeff) :
    factorCoefficientBound C N
      (fun n => coeff n * factorTwistMultiplier τ n) := by
  intro n hn
  rw [norm_mul, factorTwistMultiplier_norm]
  simpa only [mul_one] using hcoeff n hn

/-- Every factor polynomial in this convention is a finite continuous
frequency polynomial. -/
theorem factorPolynomial_continuous (N : ℝ) (coeff : ℕ → ℂ) :
    Continuous (factorPolynomial N coeff) := by
  classical
  unfold factorPolynomial FractionalPrimes.Literature.LargeValues.dirichletPolynomial
  refine continuous_finsetSum _ ?_
  intro n hn
  exact FractionalPrimes.Literature.LargeValues.dirichletTerm_continuous
    (FractionalPrimes.Literature.LargeValues.normalizedDirichletCoeff coeff) n

/-- The square exponent agrees exactly with the existing normalized divisor
exponent for coefficients of size `d₂(n)^(2C+1)`. -/
theorem E_eq_normalizedDivisorExponent_square (C : ℕ) :
    E C = FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent
      (2 * C + 1) := by
  change 2 ^ (4 * C + 2) - 1 = 2 ^ (2 * (2 * C + 1)) - 1
  rw [show 4 * C + 2 = 2 * (2 * C + 1) by omega]

/-- The single-factor normalized divisor exponent is no larger than the
square-factor exponent. -/
theorem normalizedDivisorExponent_le_E (C : ℕ) :
    FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C ≤ E C := by
  have hexp : 2 * C ≤ 4 * C + 2 := by omega
  have hpow : 2 ^ (2 * C) ≤ 2 ^ (4 * C + 2) :=
    pow_le_pow_right' (a := (2 : ℕ)) (by omega) hexp
  simpa [E,
    FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent] using
      Nat.sub_le_sub_right hpow 1

/-- The common log exponent dominates the one-factor and square-factor
normalized level exponents. -/
theorem normalizedLogExponent_bounds (C : ℕ) :
    3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 1 ≤ b C ∧
      2 ^ (2 * C) ≤ b C := by
  have hE := normalizedDivisorExponent_le_E C
  constructor
  · dsimp [b]
    omega
  · have hEbig : 2 ^ (2 * C) ≤ E C := by
      have hpow : 2 ^ (2 * C + 1) ≤ 2 ^ (4 * C + 2) := by
        exact pow_le_pow_right' (a := (2 : ℕ)) (by omega) (by omega)
      have hpowSucc : 2 ^ (2 * C + 1) = 2 * 2 ^ (2 * C) := by
        rw [pow_succ]
        ring
      rw [E]
      rw [hpowSucc] at hpow
      have hbase : 1 ≤ 2 ^ (2 * C) := one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
      omega
    dsimp [b]
    omega

/-- The `ldm:constants` prefactor dominates the single-factor level-set
prefactor supplied by `lgv:normalized`. -/
theorem K_dominates_normalizedLevelConstant (C : ℕ) :
    2 * (2 : ℝ) ^
        (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 28) ≤
      K C := by
  have hD := normalizedDivisorExponent_le_E C
  have hexp :
      3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 29 ≤
        b C + 40 := by
    dsimp [b]
    omega
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
  have hthree : 1 ≤ (3 : ℝ) ^ b C := one_le_pow₀ (by norm_num)
  calc
    2 * (2 : ℝ) ^
        (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 28) =
        (2 : ℝ) ^
          (3 * FractionalPrimes.Literature.LargeValues.normalizedDivisorExponent C + 29) := by
            rw [pow_succ]
            ring
    _ ≤ (2 : ℝ) ^ (b C + 40) := hpow
    _ ≤ (2 : ℝ) ^ (b C + 40) * (3 : ℝ) ^ b C := by
          calc
            _ = (2 : ℝ) ^ (b C + 40) * 1 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hthree (by positivity)
    _ = K C := rfl

/-- The square-factor level estimate, including the dyadic split and the
`192` loss in its second term, is absorbed by `K_C`. -/
theorem K_dominates_squareLevelConstant (C : ℕ) :
    192 * 2 * (2 : ℝ) ^ (3 * E C + 28) * (3 : ℝ) ^ b C ≤ K C := by
  have hexp : b C + 40 = 3 * E C + 41 := by
    simp [b]
  have hpow :
      (192 : ℝ) * 2 * (2 : ℝ) ^ (3 * E C + 28) ≤
        (2 : ℝ) ^ (3 * E C + 41) := by
    have hnum : (192 : ℝ) * 2 ≤ (2 : ℝ) ^ 13 := by norm_num
    have hprod := mul_le_mul_of_nonneg_right hnum
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (3 * E C + 28))
    calc
      _ = (192 : ℝ) * 2 * (2 : ℝ) ^ (3 * E C + 28) := rfl
      _ ≤ (2 : ℝ) ^ 13 * (2 : ℝ) ^ (3 * E C + 28) := hprod
      _ = (2 : ℝ) ^ (3 * E C + 41) := by
        rw [← pow_add]
        congr 1
        omega
  change 192 * 2 * (2 : ℝ) ^ (3 * E C + 28) * (3 : ℝ) ^ b C ≤
    (2 : ℝ) ^ (b C + 40) * (3 : ℝ) ^ b C
  rw [hexp]
  calc
    _ ≤ (2 : ℝ) ^ (3 * E C + 41) * (3 : ℝ) ^ b C :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = K C := rfl

/-- The normalized mean-square prefactor is dominated by `K_C`. -/
theorem K_dominates_meanSquareConstant (C : ℕ) :
    (2 : ℝ) ^ (2 ^ (2 * C) + 5) ≤ K C := by
  have hexp : 2 * C + 1 ≤ 4 * C + 2 := by omega
  have hpowStep : 2 ^ (2 * C + 1) ≤ 2 ^ (4 * C + 2) :=
    pow_le_pow_right' (a := (2 : ℕ)) (by omega) hexp
  have hpowSucc : 2 ^ (2 * C + 1) = 2 * 2 ^ (2 * C) := by
    rw [pow_succ]
    ring
  have hEbig : 2 ^ (2 * C) ≤ E C := by
    rw [E]
    rw [hpowSucc] at hpowStep
    have hbase : 1 ≤ 2 ^ (2 * C) := one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
    omega
  have hExponent : 2 ^ (2 * C) + 5 ≤ b C + 40 := by
    dsimp [b]
    omega
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hExponent
  have hthree : 1 ≤ (3 : ℝ) ^ b C := one_le_pow₀ (by norm_num)
  calc
    _ ≤ (2 : ℝ) ^ (b C + 40) := hpow
    _ ≤ (2 : ℝ) ^ (b C + 40) * (3 : ℝ) ^ b C := by
          calc
            _ = (2 : ℝ) ^ (b C + 40) * 1 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hthree (by positivity)
    _ = K C := rfl

/-- The trilinear constant leaves room for both the small-factor contribution
and all dyadic product cells: `6K + 128K ≤ J`. -/
theorem J_dominates_smallAndCellPrefactors (C : ℕ) :
    6 * K C + 128 * K C ≤ J C := by
  have hK : 0 ≤ K C := by
    dsimp [K]
    positivity
  dsimp [J]
  nlinarith

/-- All constants in the trilinear package are positive. -/
theorem constants_positive (C : ℕ) :
    0 < E C ∧ 0 < b C ∧ 0 < K C ∧ 0 < J C := by
  have hexp : 2 ≤ 4 * C + 2 := by omega
  have hpow : 2 ≤ 2 ^ (4 * C + 2) := by
    calc
      2 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (4 * C + 2) :=
        pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hexp
  have hE : 0 < E C := by
    dsimp [E]
    omega
  have hb : 0 < b C := by dsimp [b, E]; omega
  have hK : 0 < K C := by
    dsimp [K]
    positivity
  have hJ : 0 < J C := by
    dsimp [J, K]
    positivity
  exact ⟨hE, hb, hK, hJ⟩

end FractionalPrimes.Literature.DirichletMean

end

#print axioms FractionalPrimes.Literature.DirichletMean.E_eq_normalizedDivisorExponent_square
#print axioms FractionalPrimes.Literature.DirichletMean.normalizedDivisorExponent_le_E
#print axioms FractionalPrimes.Literature.DirichletMean.normalizedLogExponent_bounds
#print axioms FractionalPrimes.Literature.DirichletMean.K_dominates_normalizedLevelConstant
#print axioms FractionalPrimes.Literature.DirichletMean.K_dominates_squareLevelConstant
#print axioms FractionalPrimes.Literature.DirichletMean.K_dominates_meanSquareConstant
#print axioms FractionalPrimes.Literature.DirichletMean.J_dominates_smallAndCellPrefactors
#print axioms FractionalPrimes.Literature.DirichletMean.factorCoefficientBound_of_norm_le
#print axioms FractionalPrimes.Literature.DirichletMean.factorCoefficientBound_twist
#print axioms FractionalPrimes.Literature.DirichletMean.factorPolynomial_continuous
