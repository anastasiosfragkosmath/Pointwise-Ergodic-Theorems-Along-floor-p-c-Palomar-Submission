module

public import FractionalPrimes.Literature.Hyperbola.GeometricData
public import FractionalPrimes.Literature.Polynomial.PolynomialInverseBudgets
public import FractionalPrimes.Literature.Polynomial.PolynomialProductRecurrenceBudgets

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

/-! Exact natural-coefficient budgets from blueprint `lpi:i2-budgets`. -/

/-- The fixed geometric parameter `K₀=2`. -/
def typeI2KZeroValue : ℕ := 2

/-- The fixed value `D=8K₀²`. -/
def typeI2DValue : ℕ := 8 * typeI2KZeroValue ^ 2

/-- The fixed value `E=3+K₀²`. -/
def typeI2EValue : ℕ := 3 + typeI2KZeroValue ^ 2

/-- The fixed value `C_line=8(E+D²)+1`. -/
def typeI2CLineValue : ℕ :=
  8 * (typeI2EValue + typeI2DValue ^ 2) + 1

/-- The fixed value `C_point=64(1+E)+144D(1+D)`. -/
def typeI2CPointValue : ℕ :=
  64 * (1 + typeI2EValue) +
    144 * typeI2DValue * (1 + typeI2DValue)

/-- The fixed value `G=C_geo=2(C_point+C_line)+8+E`. -/
def typeI2GValue : ℕ :=
  2 * (typeI2CPointValue + typeI2CLineValue) + 8 + typeI2EValue

/-- The fixed value `B₀=E+4`. -/
def typeI2BZeroValue : ℕ := typeI2EValue + 4

/-- The fixed value `C_count=6+C_point B₀`. -/
def typeI2CCountValue : ℕ :=
  6 + typeI2CPointValue * typeI2BZeroValue

/-- `t=4B₀Gx³`. -/
noncomputable def typeI2TPolynomial : Polynomial ℕ :=
  C (4 * typeI2BZeroValue * typeI2GValue) * X ^ 3

/-- `B=G_{2d}(t)`. -/
noncomputable def typeI2BPolynomial (d : ℕ) : Polynomial ℕ :=
  (inverseBoundGPolynomial (2 * d)).comp typeI2TPolynomial

/-- `z=16BB₀²G²x⁶`. -/
noncomputable def typeI2ZetaPolynomial (d : ℕ) : Polynomial ℕ :=
  C (16 * typeI2BZeroValue ^ 2 * typeI2GValue ^ 2) *
    typeI2BPolynomial d * X ^ 6

/-- `A=1+∑_{j=1}^d A_j(z)`. -/
noncomputable def typeI2APolynomial (d : ℕ) : Polynomial ℕ :=
  1 + ∑ j ∈ Finset.Icc 1 d,
    (productRecurrenceAPolynomial j).comp (typeI2ZetaPolynomial d)

/-- `R=1+∑_{j=1}^d B_j(z)`. -/
noncomputable def typeI2RPolynomial (d : ℕ) : Polynomial ℕ :=
  1 + ∑ j ∈ Finset.Icc 1 d,
    (productRecurrenceBPolynomial j).comp (typeI2ZetaPolynomial d)

/-- `C=1+d(2592t²)^d`. -/
noncomputable def typeI2CPolynomial (d : ℕ) : Polynomial ℕ :=
  1 + C d * (C 2592 * typeI2TPolynomial ^ 2) ^ d

/-- The exact recursion `W₀=B`,
`W_{k+1}=(16^d+1)RCW_k²`. -/
noncomputable def typeI2WPolynomial (d : ℕ) : ℕ → Polynomial ℕ
  | 0 => typeI2BPolynomial d
  | k + 1 =>
      C (16 ^ d + 1) * typeI2RPolynomial d * typeI2CPolynomial d *
        typeI2WPolynomial d k ^ 2

/-- `Z=1+36t+256zA²CW_d²`. -/
noncomputable def typeI2CapitalZPolynomial (d : ℕ) : Polynomial ℕ :=
  1 + C 36 * typeI2TPolynomial +
    C 256 * typeI2ZetaPolynomial d * typeI2APolynomial d ^ 2 *
      typeI2CPolynomial d * typeI2WPolynomial d d ^ 2

/-- The polynomial `I_d(x²)` occurring in `J_d`. -/
noncomputable def typeI2InverseAtSquarePolynomial (d : ℕ) : Polynomial ℕ :=
  (inverseBoundIPolynomial d).comp (X ^ 2)

/-- `J_d(x)=E_d[16I_d(x²)²+4Z²+W_d+I_d(x²)+16]`. -/
noncomputable def typeI2JPolynomial (d : ℕ) : Polynomial ℕ :=
  C (inverseBoundEValue d) *
    (C 16 * typeI2InverseAtSquarePolynomial d ^ 2 +
      C 4 * typeI2CapitalZPolynomial d ^ 2 +
      typeI2WPolynomial d d + typeI2InverseAtSquarePolynomial d + C 16)

/-- The polynomial `J_d(1024x⁵)`. -/
noncomputable def typeI2JScaledPolynomial (d : ℕ) : Polynomial ℕ :=
  (typeI2JPolynomial d).comp (C 1024 * X ^ 5)

/-- The polynomial `524288 C_count² x¹³`. -/
noncomputable def typeI2DensityPolynomial : Polynomial ℕ :=
  C (524288 * typeI2CCountValue ^ 2) * X ^ 13

/-- The substitution
`V_d(J_d(1024x⁵),524288 C_count²x¹³)`. -/
noncomputable def typeI2VPolynomial (d : ℕ) : Polynomial ℕ :=
  MvPolynomial.eval₂Hom (Nat.castRingHom (Polynomial ℕ))
    (fun i : Fin 2 =>
      if i = 0 then typeI2JScaledPolynomial d else typeI2DensityPolynomial)
    (inverseBoundVPolynomial d)

/-- The final polynomial
`I_d^(2)(x)=E_d[16+J_d(1024x⁵)+V_d(J_d(1024x⁵),
524288 C_count²x¹³)]`. -/
noncomputable def typeI2BoundPolynomial (d : ℕ) : Polynomial ℕ :=
  C (inverseBoundEValue d) *
    (C 16 + typeI2JScaledPolynomial d + typeI2VPolynomial d)

/-- Exact polynomial package for blueprint `lpi:i2-budgets`. -/
structure TypeI2BoundPolynomialData (d : ℕ) where
  E : ℕ
  CPoint : ℕ
  CGeo : ℕ
  G : ℕ
  BZero : ℕ
  CCount : ℕ
  t : Polynomial ℕ
  B : Polynomial ℕ
  z : Polynomial ℕ
  A : Polynomial ℕ
  R : Polynomial ℕ
  C : Polynomial ℕ
  W : ℕ → Polynomial ℕ
  Z : Polynomial ℕ
  J : Polynomial ℕ
  I2 : Polynomial ℕ

/-- Every displayed budget in `lpi:i2-budgets`, as an explicitly determined
natural-coefficient polynomial. -/
noncomputable def typeI2BoundPolynomials (d : ℕ) :
    TypeI2BoundPolynomialData d where
  E := typeI2EValue
  CPoint := typeI2CPointValue
  CGeo := typeI2GValue
  G := typeI2GValue
  BZero := typeI2BZeroValue
  CCount := typeI2CCountValue
  t := typeI2TPolynomial
  B := typeI2BPolynomial d
  z := typeI2ZetaPolynomial d
  A := typeI2APolynomial d
  R := typeI2RPolynomial d
  C := typeI2CPolynomial d
  W := typeI2WPolynomial d
  Z := typeI2CapitalZPolynomial d
  J := typeI2JPolynomial d
  I2 := typeI2BoundPolynomial d

/-- Real evaluation of a natural-coefficient budget polynomial. -/
noncomputable def typeI2PolynomialEval (p : Polynomial ℕ) (x : ℝ) : ℝ :=
  p.eval₂ (Nat.castRingHom ℝ) x

noncomputable def typeI2T (x : ℝ) : ℝ :=
  typeI2PolynomialEval typeI2TPolynomial x

noncomputable def typeI2B (d : ℕ) (x : ℝ) : ℝ :=
  typeI2PolynomialEval (typeI2BPolynomial d) x

noncomputable def typeI2Zeta (d : ℕ) (x : ℝ) : ℝ :=
  typeI2PolynomialEval (typeI2ZetaPolynomial d) x

noncomputable def typeI2A (d : ℕ) (x : ℝ) : ℝ :=
  typeI2PolynomialEval (typeI2APolynomial d) x

noncomputable def typeI2R (d : ℕ) (x : ℝ) : ℝ :=
  typeI2PolynomialEval (typeI2RPolynomial d) x

noncomputable def typeI2C (d : ℕ) (x : ℝ) : ℝ :=
  typeI2PolynomialEval (typeI2CPolynomial d) x

noncomputable def typeI2W (d k : ℕ) (x : ℝ) : ℝ :=
  typeI2PolynomialEval (typeI2WPolynomial d k) x

noncomputable def typeI2CapitalZ (d : ℕ) (x : ℝ) : ℝ :=
  typeI2PolynomialEval (typeI2CapitalZPolynomial d) x

noncomputable def typeI2J (d : ℕ) (x : ℝ) : ℝ :=
  typeI2PolynomialEval (typeI2JPolynomial d) x

noncomputable def typeI2JScaled (d : ℕ) (x : ℝ) : ℝ :=
  typeI2PolynomialEval (typeI2JScaledPolynomial d) x

noncomputable def typeI2Density (x : ℝ) : ℝ :=
  typeI2PolynomialEval typeI2DensityPolynomial x

noncomputable def typeI2V (d : ℕ) (x : ℝ) : ℝ :=
  typeI2PolynomialEval (typeI2VPolynomial d) x

/-- Real evaluation of the final `I_d^(2)` polynomial. -/
noncomputable def typeI2Bound (d : ℕ) (x : ℝ) : ℝ :=
  typeI2PolynomialEval (typeI2BoundPolynomial d) x

theorem typeI2T_eval (x : ℝ) :
    typeI2T x =
      4 * (typeI2BZeroValue : ℝ) * (typeI2GValue : ℝ) * x ^ 3 := by
  simp [typeI2T, typeI2PolynomialEval, typeI2TPolynomial,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow]

theorem typeI2B_eval (d : ℕ) (x : ℝ) :
    typeI2B d x = inverseBoundG (2 * d) (typeI2T x) := by
  simp [typeI2B, typeI2PolynomialEval, typeI2BPolynomial,
    inverseBoundG, typeI2T, Polynomial.eval₂_comp]

theorem typeI2Zeta_eval (d : ℕ) (x : ℝ) :
    typeI2Zeta d x =
      16 * typeI2B d x * (typeI2BZeroValue : ℝ) ^ 2 *
        (typeI2GValue : ℝ) ^ 2 * x ^ 6 := by
  simp [typeI2Zeta, typeI2PolynomialEval, typeI2ZetaPolynomial,
    typeI2B, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  ring_nf
  exact Or.inl trivial

theorem typeI2A_eval (d : ℕ) (x : ℝ) :
    typeI2A d x =
      1 + ∑ j ∈ Finset.Icc 1 d, productRecurrenceA j (typeI2Zeta d x) := by
  simp [typeI2A, typeI2PolynomialEval, typeI2APolynomial,
    productRecurrenceA, typeI2Zeta, Polynomial.eval₂_comp,
    Polynomial.eval₂_finsetSum]

theorem typeI2R_eval (d : ℕ) (x : ℝ) :
    typeI2R d x =
      1 + ∑ j ∈ Finset.Icc 1 d, productRecurrenceB j (typeI2Zeta d x) := by
  simp [typeI2R, typeI2PolynomialEval, typeI2RPolynomial,
    productRecurrenceB, typeI2Zeta, Polynomial.eval₂_comp,
    Polynomial.eval₂_finsetSum]

theorem typeI2C_eval (d : ℕ) (x : ℝ) :
    typeI2C d x = 1 + (d : ℝ) * (2592 * typeI2T x ^ 2) ^ d := by
  simp [typeI2C, typeI2PolynomialEval, typeI2CPolynomial, typeI2T,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]

@[simp] theorem typeI2W_zero_eval (d : ℕ) (x : ℝ) :
    typeI2W d 0 x = typeI2B d x := by
  rfl

theorem typeI2W_succ_eval (d k : ℕ) (x : ℝ) :
    typeI2W d (k + 1) x =
      (16 ^ d + 1 : ℝ) * typeI2R d x * typeI2C d x *
        typeI2W d k x ^ 2 := by
  simp [typeI2W, typeI2WPolynomial, typeI2PolynomialEval,
    typeI2R, typeI2C, Polynomial.eval₂_mul, Polynomial.eval₂_pow]

theorem typeI2CapitalZ_eval (d : ℕ) (x : ℝ) :
    typeI2CapitalZ d x =
      1 + 36 * typeI2T x +
        256 * typeI2Zeta d x * typeI2A d x ^ 2 * typeI2C d x *
          typeI2W d d x ^ 2 := by
  simp [typeI2CapitalZ, typeI2CapitalZPolynomial, typeI2PolynomialEval,
    typeI2T, typeI2Zeta, typeI2A, typeI2C, typeI2W,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]

private theorem typeI2_eval_mvp_substitution
    (p : InverseBudgetBivariate) (P Q : Polynomial ℕ) (x : ℝ) :
    typeI2PolynomialEval
        (MvPolynomial.eval₂Hom (Nat.castRingHom (Polynomial ℕ))
          (fun i : Fin 2 => if i = 0 then P else Q) p) x =
      inverseBoundBivariateEval p
        (typeI2PolynomialEval P x) (typeI2PolynomialEval Q x) := by
  let φ : Polynomial ℕ →+* ℝ :=
    Polynomial.eval₂RingHom (Nat.castRingHom ℝ) x
  have hcomp : φ.comp (Nat.castRingHom (Polynomial ℕ)) =
      Nat.castRingHom ℝ := by
    ext n
    simp [φ, Polynomial.eval₂RingHom]
  change φ (MvPolynomial.eval₂ (Nat.castRingHom (Polynomial ℕ))
      (fun i : Fin 2 => if i = 0 then P else Q) p) = _
  rw [MvPolynomial.hom_eval₂, hcomp]
  congr 1
  funext i
  fin_cases i <;>
    simp [φ, Polynomial.eval₂RingHom, typeI2PolynomialEval]

theorem typeI2J_eval (d : ℕ) (x : ℝ) :
    typeI2J d x = (inverseBoundEValue d : ℝ) *
      (16 * inverseBoundI d (x ^ 2) ^ 2 +
        4 * typeI2CapitalZ d x ^ 2 + typeI2W d d x +
        inverseBoundI d (x ^ 2) + 16) := by
  simp [typeI2J, typeI2JPolynomial, typeI2InverseAtSquarePolynomial,
    typeI2PolynomialEval, inverseBoundI, typeI2CapitalZ, typeI2W,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_comp]

theorem typeI2JScaled_eval (d : ℕ) (x : ℝ) :
    typeI2JScaled d x = typeI2J d (1024 * x ^ 5) := by
  simp [typeI2JScaled, typeI2JScaledPolynomial, typeI2J,
    typeI2PolynomialEval, Polynomial.eval₂_comp, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow]

theorem typeI2Density_eval (x : ℝ) :
    typeI2Density x =
      524288 * (typeI2CCountValue : ℝ) ^ 2 * x ^ 13 := by
  simp [typeI2Density, typeI2DensityPolynomial, typeI2PolynomialEval,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow]

theorem typeI2V_eval (d : ℕ) (x : ℝ) :
    typeI2V d x = inverseBoundV d (typeI2JScaled d x) (typeI2Density x) := by
  exact typeI2_eval_mvp_substitution (inverseBoundVPolynomial d)
    (typeI2JScaledPolynomial d) typeI2DensityPolynomial x

theorem typeI2Bound_eval (d : ℕ) (x : ℝ) :
    typeI2Bound d x = (inverseBoundEValue d : ℝ) *
      (16 + typeI2J d (1024 * x ^ 5) +
        inverseBoundV d (typeI2J d (1024 * x ^ 5))
          (524288 * (typeI2CCountValue : ℝ) ^ 2 * x ^ 13)) := by
  change (typeI2BoundPolynomial d).eval₂ (Nat.castRingHom ℝ) x = _
  simp only [typeI2BoundPolynomial, Polynomial.eval₂_mul,
    Polynomial.eval₂_add, Polynomial.eval₂_C]
  change (inverseBoundEValue d : ℝ) *
      (16 + typeI2JScaled d x + typeI2V d x) = _
  rw [typeI2JScaled_eval, typeI2V_eval]
  rw [typeI2JScaled_eval, typeI2Density_eval]

/-- The fixed natural constants are exactly the `K₀=2` hyperbola constants
after casting to the reals. -/
theorem typeI2_fixed_geometric_constants :
    (typeI2EValue : ℝ) =
        FractionalPrimes.Literature.Hyperbola.E 2 ∧
    (typeI2CPointValue : ℝ) =
        FractionalPrimes.Literature.Hyperbola.C_point 2 ∧
    (typeI2GValue : ℝ) =
        FractionalPrimes.Literature.Hyperbola.C_geo 2 := by
  norm_num [typeI2EValue, typeI2DValue, typeI2KZeroValue,
    typeI2CLineValue, typeI2CPointValue, typeI2GValue,
    FractionalPrimes.Literature.Hyperbola.E,
    FractionalPrimes.Literature.Hyperbola.D,
    FractionalPrimes.Literature.Hyperbola.C_line,
    FractionalPrimes.Literature.Hyperbola.C_point,
    FractionalPrimes.Literature.Hyperbola.C_geo]

/-- Every coefficient in the final two univariate budgets is nonnegative
after casting to the reals; this is structural from their `ℕ` coefficients. -/
theorem typeI2BoundPolynomials_coeff_nonneg (d n : ℕ) :
    0 ≤ ((((typeI2BoundPolynomials d).J.coeff n : ℕ) : ℝ)) ∧
      0 ≤ ((((typeI2BoundPolynomials d).I2.coeff n : ℕ) : ℝ)) := by
  exact ⟨Nat.cast_nonneg _, Nat.cast_nonneg _⟩

end FractionalPrimes.Literature.Polynomial
