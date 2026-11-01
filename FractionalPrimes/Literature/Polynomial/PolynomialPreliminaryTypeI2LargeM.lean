module

public import FractionalPrimes.Literature.Polynomial.PolynomialPreliminaryTypeI2
public import FractionalPrimes.Literature.Polynomial.PolynomialRecurrenceDenseInterpolation
public import FractionalPrimes.Literature.Polynomial.PolynomialCoefficientNorm

/-!
# Large-scale numerical preparation for preliminary Type I₂

This file isolates the budget and fourth-root inequalities used at the start
of the large-`M` branch of blueprint node `lpi:preliminary-I2`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

private theorem preliminaryLargeM_natPolynomialEval_nonneg
    (p : Polynomial ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ p.eval₂ (Nat.castRingHom ℝ) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval₂_add]
      exact add_nonneg hp hq
  | monomial n c =>
      rw [Polynomial.eval₂_monomial]
      exact mul_nonneg (Nat.cast_nonneg c) (pow_nonneg hx n)

private theorem preliminaryLargeM_typeI2T_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ typeI2T x := by
  exact preliminaryLargeM_natPolynomialEval_nonneg typeI2TPolynomial x hx

/-- The approved `t=4B₀Gx³` budget is at least one for `x≥1`. -/
theorem typeI2T_ge_one (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ typeI2T x := by
  rw [typeI2T_eval]
  norm_num [typeI2BZeroValue, typeI2GValue, typeI2CPointValue,
    typeI2CLineValue, typeI2EValue, typeI2DValue, typeI2KZeroValue]
  have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx
  nlinarith

private theorem preliminaryLargeM_typeI2B_nonneg (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ typeI2B d x := by
  exact preliminaryLargeM_natPolynomialEval_nonneg (typeI2BPolynomial d) x hx

private theorem preliminaryLargeM_typeI2Zeta_nonneg
    (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ typeI2Zeta d x := by
  exact preliminaryLargeM_natPolynomialEval_nonneg (typeI2ZetaPolynomial d) x hx

private theorem preliminaryLargeM_typeI2A_nonneg (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ typeI2A d x := by
  exact preliminaryLargeM_natPolynomialEval_nonneg (typeI2APolynomial d) x hx

private theorem preliminaryLargeM_typeI2C_nonneg (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ typeI2C d x := by
  exact preliminaryLargeM_natPolynomialEval_nonneg (typeI2CPolynomial d) x hx

private theorem preliminaryLargeM_typeI2W_nonneg
    (d k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ typeI2W d k x := by
  exact preliminaryLargeM_natPolynomialEval_nonneg (typeI2WPolynomial d k) x hx

private theorem preliminaryLargeM_inverseBoundI_nonneg
    (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ inverseBoundI d x := by
  exact preliminaryLargeM_natPolynomialEval_nonneg (inverseBoundIPolynomial d) x hx

/-- The approved `J_d` budget contains its literal constant term `16`. -/
theorem typeI2J_ge_sixteen (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    16 ≤ typeI2J d x := by
  rw [typeI2J_eval]
  have hE : 1 ≤ (inverseBoundEValue d : ℝ) := by
    exact_mod_cast inverseBoundE_ge_one d
  have hI : 0 ≤ inverseBoundI d (x ^ 2) :=
    preliminaryLargeM_inverseBoundI_nonneg d (x ^ 2) (sq_nonneg x)
  have hW : 0 ≤ typeI2W d d x :=
    preliminaryLargeM_typeI2W_nonneg d d x hx
  have hinner : 0 ≤
      16 * inverseBoundI d (x ^ 2) ^ 2 +
        4 * typeI2CapitalZ d x ^ 2 + typeI2W d d x +
        inverseBoundI d (x ^ 2) + 16 := by
    positivity
  have hscale :
      16 * inverseBoundI d (x ^ 2) ^ 2 +
          4 * typeI2CapitalZ d x ^ 2 + typeI2W d d x +
          inverseBoundI d (x ^ 2) + 16 ≤
        (inverseBoundEValue d : ℝ) *
          (16 * inverseBoundI d (x ^ 2) ^ 2 +
            4 * typeI2CapitalZ d x ^ 2 + typeI2W d d x +
            inverseBoundI d (x ^ 2) + 16) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hE) hinner]
  calc
    16 ≤ 16 * inverseBoundI d (x ^ 2) ^ 2 +
        4 * typeI2CapitalZ d x ^ 2 + typeI2W d d x +
        inverseBoundI d (x ^ 2) + 16 := by
      nlinarith [sq_nonneg (inverseBoundI d (x ^ 2)),
        sq_nonneg (typeI2CapitalZ d x)]
    _ ≤ _ := hscale

/-- The approved `J_d` budget contains the exact term `4 Z²` needed to
force the long hyperbola-progression scale. -/
theorem typeI2J_ge_four_capitalZ_sq (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    4 * typeI2CapitalZ d x ^ 2 ≤ typeI2J d x := by
  rw [typeI2J_eval]
  have hE : 1 ≤ (inverseBoundEValue d : ℝ) := by
    exact_mod_cast inverseBoundE_ge_one d
  have hI : 0 ≤ inverseBoundI d (x ^ 2) :=
    preliminaryLargeM_inverseBoundI_nonneg d (x ^ 2) (sq_nonneg x)
  have hW : 0 ≤ typeI2W d d x :=
    preliminaryLargeM_typeI2W_nonneg d d x hx
  have hinner : 0 ≤
      16 * inverseBoundI d (x ^ 2) ^ 2 +
        4 * typeI2CapitalZ d x ^ 2 + typeI2W d d x +
        inverseBoundI d (x ^ 2) + 16 := by
    positivity
  have hscale :
      16 * inverseBoundI d (x ^ 2) ^ 2 +
          4 * typeI2CapitalZ d x ^ 2 + typeI2W d d x +
          inverseBoundI d (x ^ 2) + 16 ≤
        (inverseBoundEValue d : ℝ) *
          (16 * inverseBoundI d (x ^ 2) ^ 2 +
            4 * typeI2CapitalZ d x ^ 2 + typeI2W d d x +
            inverseBoundI d (x ^ 2) + 16) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hE) hinner]
  calc
    4 * typeI2CapitalZ d x ^ 2 ≤
        16 * inverseBoundI d (x ^ 2) ^ 2 +
          4 * typeI2CapitalZ d x ^ 2 + typeI2W d d x +
          inverseBoundI d (x ^ 2) + 16 := by
      nlinarith [sq_nonneg (inverseBoundI d (x ^ 2))]
    _ ≤ _ := hscale

/-- The large-scale threshold `Z` is at least one. -/
theorem typeI2CapitalZ_ge_one (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    1 ≤ typeI2CapitalZ d x := by
  rw [typeI2CapitalZ_eval]
  have hT := preliminaryLargeM_typeI2T_nonneg x hx
  have hz := preliminaryLargeM_typeI2Zeta_nonneg d x hx
  have hA := preliminaryLargeM_typeI2A_nonneg d x hx
  have hC := preliminaryLargeM_typeI2C_nonneg d x hx
  have hW := preliminaryLargeM_typeI2W_nonneg d d x hx
  have hprod : 0 ≤
      256 * typeI2Zeta d x * typeI2A d x ^ 2 * typeI2C d x *
        typeI2W d d x ^ 2 := by positivity
  nlinarith

/-- The threshold `Z` contains the literal term `36t`; this is the inequality
used to deduce `τL>36` from `L>Z` and `τ=t⁻¹`. -/
theorem typeI2CapitalZ_ge_thirtySixT
    (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    36 * typeI2T x ≤ typeI2CapitalZ d x := by
  rw [typeI2CapitalZ_eval]
  have hT := preliminaryLargeM_typeI2T_nonneg x hx
  have hz := preliminaryLargeM_typeI2Zeta_nonneg d x hx
  have hA := preliminaryLargeM_typeI2A_nonneg d x hx
  have hC := preliminaryLargeM_typeI2C_nonneg d x hx
  have hW := preliminaryLargeM_typeI2W_nonneg d d x hx
  have hprod : 0 ≤
      256 * typeI2Zeta d x * typeI2A d x ^ 2 * typeI2C d x *
        typeI2W d d x ^ 2 := by positivity
  nlinarith

private theorem preliminaryLargeM_rpow_one_third_cube
    (X : ℝ) (hX : 0 ≤ X) :
    (Real.rpow X (1 / 3 : ℝ)) ^ 3 = X := by
  have hnat : (Real.rpow X (1 / 3 : ℝ)) ^ 3 =
      Real.rpow (Real.rpow X (1 / 3 : ℝ)) (3 : ℝ) :=
    (Real.rpow_natCast (Real.rpow X (1 / 3 : ℝ)) 3).symm
  have hrpow : Real.rpow (Real.rpow X (1 / 3 : ℝ)) (3 : ℝ) = X := by
    simpa [show (1 / 3 : ℝ)⁻¹ = 3 by norm_num] using
      (Real.rpow_rpow_inv hX (by norm_num : (1 / 3 : ℝ) ≠ 0))
  rw [hnat, hrpow]

/-- Failure of the approved short-interval alternative forces the cubic
inequality needed for admissible fourth-root hyperbola geometry. -/
theorem preliminaryTypeI2_nonexception_cubic_lower
    (d : ℕ) (x X H : ℝ) (hx : 0 ≤ x) (hX : 0 ≤ X)
    (hlength : typeI2J d x * Real.rpow X (1 / 3 : ℝ) < H) :
    16 * X ≤ H ^ 3 := by
  let y : ℝ := Real.rpow X (1 / 3 : ℝ)
  have hy0 : 0 ≤ y := Real.rpow_nonneg hX _
  have hy3 : y ^ 3 = X := by
    simpa [y] using preliminaryLargeM_rpow_one_third_cube X hX
  have hJ : 16 ≤ typeI2J d x := typeI2J_ge_sixteen d x hx
  have h16 : 16 * y < H := by
    apply lt_of_le_of_lt _ hlength
    exact mul_le_mul_of_nonneg_right hJ hy0
  have hH0 : 0 ≤ H := by nlinarith
  have hpow : (16 * y) ^ 3 ≤ H ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hy0) h16.le 3
  rw [show (16 * y) ^ 3 = 4096 * y ^ 3 by ring, hy3] at hpow
  nlinarith

/-- The same nonexceptional inequality supplies exactly
`2(HX)^(1/4) ≤ H`, the remaining hypothesis of the checked large-`M`
geometric-data constructor. -/
theorem preliminaryTypeI2_nonexception_twiceFourthRoot_le
    (d : ℕ) (x X H : ℝ) (hx : 0 ≤ x) (hX : 0 ≤ X)
    (hH : 0 ≤ H)
    (hlength : typeI2J d x * Real.rpow X (1 / 3 : ℝ) < H) :
    2 * Real.sqrt (Real.sqrt (H * X)) ≤ H := by
  have hHX := preliminaryTypeI2_nonexception_cubic_lower
    d x X H hx hX hlength
  let s : ℝ := Real.sqrt (Real.sqrt (H * X))
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = Real.sqrt (H * X) := by
    dsimp [s]
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs4 : s ^ 4 = H * X := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (H * X)) ^ 2 := by rw [hs2]
      _ = H * X := Real.sq_sqrt (mul_nonneg hH hX)
  have hHX4 : 16 * H * X ≤ H ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hHX hH
    nlinarith
  have hfourth : (2 * s) ^ 4 ≤ H ^ 4 := by
    rw [show (2 * s) ^ 4 = 16 * s ^ 4 by ring, hs4]
    nlinarith
  have hfourth' : ((2 * s) ^ 2) ^ 2 ≤ (H ^ 2) ^ 2 := by
    nlinarith [hfourth]
  have hsq : (2 * s) ^ 2 ≤ H ^ 2 :=
    (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mp hfourth'
  have hbase : 2 * s ≤ H :=
    (sq_le_sq₀ (by positivity) hH).mp hsq
  simpa [s] using hbase

/-- In the large-`M` regime, the floor defining `Q` retains at least half of
the unfloored quotient. This is the exact floor estimate used in the source. -/
theorem preliminaryTypeI2LargeM_floor_lower
    (X H M : ℝ)
    (hX : 1 ≤ X) (hH : 1 ≤ H)
    (hMlarge : 2 * Real.sqrt (Real.sqrt (H * X)) ≤ M) :
    M / (2 * Real.sqrt (Real.sqrt (H * X))) ≤
      (Nat.floor (M / Real.sqrt (Real.sqrt (H * X))) : ℝ) := by
  let Dfourth : ℝ := Real.sqrt (Real.sqrt (H * X))
  have hHXone : 1 ≤ H * X := by nlinarith [mul_le_mul hH hX (by norm_num) (by linarith)]
  have hsqrtHXone : 1 ≤ Real.sqrt (H * X) := by
    simpa using Real.sqrt_le_sqrt hHXone
  have hDone : 1 ≤ Dfourth := by
    simpa [Dfourth] using Real.sqrt_le_sqrt hsqrtHXone
  have hDpos : 0 < Dfourth := by linarith
  have hMpos : 0 < M := by nlinarith [hMlarge, hDpos]
  have hratio0 : 0 ≤ M / Dfourth := div_nonneg hMpos.le hDpos.le
  have hratio2 : 2 ≤ M / Dfourth := by
    apply (le_div_iff₀ hDpos).2
    simpa [Dfourth] using hMlarge
  let Q : ℕ := Nat.floor (M / Dfourth)
  have hfloorlt : M / Dfourth < (Q : ℝ) + 1 := by
    dsimp [Q]
    exact Nat.lt_floor_add_one _
  have hhalf : (M / Dfourth) / 2 ≤ (Q : ℝ) := by
    nlinarith [hratio2, hfloorlt]
  change M / (2 * Dfourth) ≤ (Q : ℝ)
  rw [show 2 * Dfourth = Dfourth * 2 by ring, ← div_div]
  exact hhalf

/-- The two rectangle side lengths used by product recurrence after the
ordinary hyperbola pigeonhole step. -/
def typeI2LargeMRecurrenceNOne (Q : ℕ) : ℕ := Q

noncomputable def typeI2LargeMRecurrenceNTwo
    (X M : ℝ) (Q : ℕ) : ℕ :=
  Nat.ceil ((typeI2EValue : ℝ) * (X / M ^ 2) * (Q : ℝ))

/-- The numerical core of the product-recurrence scale comparison.  It is
stated separately so that the exact floor and ceiling facts can be supplied
without rebuilding the algebra in the degree descent. -/
theorem typeI2LargeM_recurrenceScaleProduct_lower
    (X H M : ℝ) (Q N₂ : ℕ)
    (hX : 0 < X) (hH : 0 < H) (hM : 0 < M)
    (hQ : M / (2 * Real.sqrt (Real.sqrt (H * X))) ≤ (Q : ℝ))
    (hN₂ : X / M ^ 2 * (Q : ℝ) ≤ (N₂ : ℝ)) :
    H / 16 ≤ H ^ 2 * X * (Q : ℝ) ^ 4 / M ^ 4 ∧
      H ^ 2 * X * (Q : ℝ) ^ 4 / M ^ 4 ≤
        (H * (Q : ℝ) / M) ^ 2 *
          (typeI2LargeMRecurrenceNOne Q : ℝ) * (N₂ : ℝ) := by
  let Dfourth : ℝ := Real.sqrt (Real.sqrt (H * X))
  have hDpos : 0 < Dfourth := by
    dsimp [Dfourth]
    positivity
  have hD2 : Dfourth ^ 2 = Real.sqrt (H * X) := by
    dsimp [Dfourth]
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hD4 : Dfourth ^ 4 = H * X := by
    calc
      Dfourth ^ 4 = (Dfourth ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (H * X)) ^ 2 := by rw [hD2]
      _ = H * X := Real.sq_sqrt (mul_nonneg hH.le hX.le)
  have hQ' : M / (2 * Dfourth) ≤ (Q : ℝ) := by
    simpa [Dfourth] using hQ
  have hQpow : (M / (2 * Dfourth)) ^ 4 ≤ (Q : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hQ' 4
  have hbasepow :
      (M / (2 * Dfourth)) ^ 4 = M ^ 4 / (16 * (H * X)) := by
    rw [div_pow, show (2 * Dfourth) ^ 4 = 16 * Dfourth ^ 4 by ring, hD4]
  have hfactor0 : 0 ≤ H ^ 2 * X / M ^ 4 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hQpow hfactor0
  constructor
  · calc
      H / 16 = (H ^ 2 * X / M ^ 4) *
          (M / (2 * Dfourth)) ^ 4 := by
        rw [hbasepow]
        field_simp [ne_of_gt hM, ne_of_gt hH, ne_of_gt hX]
      _ ≤ (H ^ 2 * X / M ^ 4) * (Q : ℝ) ^ 4 := hscaled
      _ = H ^ 2 * X * (Q : ℝ) ^ 4 / M ^ 4 := by ring
  · have hmult := mul_le_mul_of_nonneg_left hN₂
        (mul_nonneg (sq_nonneg (H * (Q : ℝ) / M))
          (Nat.cast_nonneg Q))
    calc
      H ^ 2 * X * (Q : ℝ) ^ 4 / M ^ 4 =
          ((H * (Q : ℝ) / M) ^ 2 * (Q : ℝ)) *
            (X / M ^ 2 * (Q : ℝ)) := by
        field_simp [ne_of_gt hM]
      _ ≤ ((H * (Q : ℝ) / M) ^ 2 * (Q : ℝ)) * (N₂ : ℝ) := hmult
      _ = (H * (Q : ℝ) / M) ^ 2 *
          (typeI2LargeMRecurrenceNOne Q : ℝ) * (N₂ : ℝ) := by
        rfl

theorem typeI2LargeMRecurrenceNTwo_lower
    (X M : ℝ) (Q : ℕ) (hX : 0 ≤ X) (hM : 0 < M) :
    X / M ^ 2 * (Q : ℝ) ≤
      (typeI2LargeMRecurrenceNTwo X M Q : ℝ) := by
  have hE : (1 : ℝ) ≤ (typeI2EValue : ℝ) := by
    norm_num [typeI2EValue, typeI2KZeroValue]
  have huQ0 : 0 ≤ X / M ^ 2 * (Q : ℝ) := by positivity
  calc
    X / M ^ 2 * (Q : ℝ) = 1 * (X / M ^ 2 * (Q : ℝ)) := by ring
    _ ≤ (typeI2EValue : ℝ) * (X / M ^ 2 * (Q : ℝ)) :=
      mul_le_mul_of_nonneg_right hE huQ0
    _ = (typeI2EValue : ℝ) * (X / M ^ 2) * (Q : ℝ) := by ring
    _ ≤ (Nat.ceil ((typeI2EValue : ℝ) *
          (X / M ^ 2) * (Q : ℝ)) : ℝ) := Nat.le_ceil _
    _ = (typeI2LargeMRecurrenceNTwo X M Q : ℝ) := by
      rfl

/-- The source-exact scale chain
`L² N₁ N₂ ≥ H² X Q⁴/M⁴ ≥ H/16` for the actual floor and ceiling
parameters of the large-`M` branch. -/
theorem preliminaryTypeI2LargeM_recurrenceScaleProduct_lower
    (X H M : ℝ) (hX : 1 ≤ X) (hH : 1 ≤ H)
    (hMlarge : 2 * Real.sqrt (Real.sqrt (H * X)) ≤ M) :
    let Q : ℕ := Nat.floor (M / Real.sqrt (Real.sqrt (H * X)))
    let N₁ : ℕ := typeI2LargeMRecurrenceNOne Q
    let N₂ : ℕ := typeI2LargeMRecurrenceNTwo X M Q
    H / 16 ≤ H ^ 2 * X * (Q : ℝ) ^ 4 / M ^ 4 ∧
      H ^ 2 * X * (Q : ℝ) ^ 4 / M ^ 4 ≤
        (H * (Q : ℝ) / M) ^ 2 * (N₁ : ℝ) * (N₂ : ℝ) := by
  let Dfourth : ℝ := Real.sqrt (Real.sqrt (H * X))
  let Q : ℕ := Nat.floor (M / Dfourth)
  let N₁ : ℕ := typeI2LargeMRecurrenceNOne Q
  let N₂ : ℕ := typeI2LargeMRecurrenceNTwo X M Q
  have hDpos : 0 < Dfourth := by
    dsimp [Dfourth]
    positivity
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity : 0 < 2 * Dfourth)
    (by simpa [Dfourth] using hMlarge)
  have hQlower : M / (2 * Dfourth) ≤ (Q : ℝ) := by
    simpa [Dfourth, Q] using
      preliminaryTypeI2LargeM_floor_lower X H M hX hH hMlarge
  have hN₂lower : X / M ^ 2 * (Q : ℝ) ≤ (N₂ : ℝ) := by
    simpa [N₂] using typeI2LargeMRecurrenceNTwo_lower X M Q (by linarith) hMpos
  simpa [Dfourth, Q, N₁, N₂] using
    typeI2LargeM_recurrenceScaleProduct_lower X H M Q N₂
      (by linarith) (by linarith) hMpos hQlower hN₂lower

/-- Failure of the approved short alternative makes the hyperbola scale
`L=HQ/M` strictly larger than the exact threshold `Z`. -/
theorem preliminaryTypeI2LargeM_scale_gt_capitalZ
    (d : ℕ) (x X H M : ℝ)
    (hx : 0 ≤ x) (hX : 1 ≤ X) (hH : 1 ≤ H)
    (hMlarge : 2 * Real.sqrt (Real.sqrt (H * X)) ≤ M)
    (hlength : typeI2J d x * Real.rpow X (1 / 3 : ℝ) < H) :
    typeI2CapitalZ d x <
      H * (Nat.floor (M / Real.sqrt (Real.sqrt (H * X))) : ℝ) / M := by
  let Z : ℝ := typeI2CapitalZ d x
  let R : ℝ := Real.rpow X (1 / 3 : ℝ)
  let Dfourth : ℝ := Real.sqrt (Real.sqrt (H * X))
  let Q : ℕ := Nat.floor (M / Dfourth)
  have hXpos : 0 < X := by linarith
  have hHpos : 0 < H := by linarith
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact Real.rpow_nonneg hXpos.le _
  have hR3 : R ^ 3 = X := by
    simpa [R] using preliminaryLargeM_rpow_one_third_cube X hXpos.le
  have hZone : 1 ≤ Z := by
    simpa [Z] using typeI2CapitalZ_ge_one d x hx
  have hJZ : 4 * Z ^ 2 ≤ typeI2J d x := by
    simpa [Z] using typeI2J_ge_four_capitalZ_sq d x hx
  have hZR : 4 * Z ^ 2 * R < H := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hJZ hR0) hlength
  have hZRcube : (4 * Z ^ 2 * R) ^ 3 < H ^ 3 :=
    pow_lt_pow_left₀ hZR (by positivity) (by norm_num)
  have hcube : 64 * Z ^ 6 * X < H ^ 3 := by
    rw [show (4 * Z ^ 2 * R) ^ 3 = 64 * Z ^ 6 * R ^ 3 by ring,
      hR3] at hZRcube
    exact hZRcube
  have hsmallCoeff : 16 * Z ^ 4 * X ≤ 64 * Z ^ 6 * X := by
    have hfour : 1 ≤ 4 * Z ^ 2 := by nlinarith [sq_nonneg Z]
    have hnonneg : 0 ≤ 16 * Z ^ 4 * X := by positivity
    calc
      16 * Z ^ 4 * X = (16 * Z ^ 4 * X) * 1 := by ring
      _ ≤ (16 * Z ^ 4 * X) * (4 * Z ^ 2) :=
        mul_le_mul_of_nonneg_left hfour hnonneg
      _ = 64 * Z ^ 6 * X := by ring
  have hcubic : 16 * Z ^ 4 * X < H ^ 3 :=
    lt_of_le_of_lt hsmallCoeff hcube
  have hD2 : Dfourth ^ 2 = Real.sqrt (H * X) := by
    dsimp [Dfourth]
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hD4 : Dfourth ^ 4 = H * X := by
    calc
      Dfourth ^ 4 = (Dfourth ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (H * X)) ^ 2 := by rw [hD2]
      _ = H * X := Real.sq_sqrt (mul_nonneg hHpos.le hXpos.le)
  have hDpos : 0 < Dfourth := by
    dsimp [Dfourth]
    positivity
  have hfourth : (2 * Z * Dfourth) ^ 4 < H ^ 4 := by
    have hmul := mul_lt_mul_of_pos_left hcubic hHpos
    rw [show (2 * Z * Dfourth) ^ 4 = 16 * Z ^ 4 * Dfourth ^ 4 by ring,
      hD4]
    nlinarith
  have hZD : 2 * Z * Dfourth < H :=
    lt_of_pow_lt_pow_left₀ 4 hHpos.le hfourth
  have hZhalf : Z < H / (2 * Dfourth) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * Dfourth)).2
    nlinarith
  have hMpos : 0 < M := by nlinarith [hMlarge, hDpos]
  have hQlower : M / (2 * Dfourth) ≤ (Q : ℝ) := by
    simpa [Dfourth, Q] using
      preliminaryTypeI2LargeM_floor_lower X H M hX hH hMlarge
  have hscale := mul_le_mul_of_nonneg_left hQlower (div_nonneg hHpos.le hMpos.le)
  have hrewrite :
      (H / M) * (M / (2 * Dfourth)) = H / (2 * Dfourth) := by
    field_simp [ne_of_gt hMpos, ne_of_gt hDpos]
  have hscale' : H / (2 * Dfourth) ≤ H * (Q : ℝ) / M := by
    rw [← hrewrite]
    convert hscale using 1 <;> ring
  exact lt_of_lt_of_le hZhalf hscale'

/-- With `tau=t⁻¹`, the same scale inequality gives the literal source
threshold `tau L > 36`. -/
theorem preliminaryTypeI2LargeM_inverseT_mul_scale_gt_thirtySix
    (d : ℕ) (x X H M : ℝ)
    (hx : 0 < x) (hX : 1 ≤ X) (hH : 1 ≤ H)
    (hMlarge : 2 * Real.sqrt (Real.sqrt (H * X)) ≤ M)
    (hlength : typeI2J d x * Real.rpow X (1 / 3 : ℝ) < H) :
    36 < (typeI2T x)⁻¹ *
      (H * (Nat.floor (M / Real.sqrt (Real.sqrt (H * X))) : ℝ) / M) := by
  let L : ℝ :=
    H * (Nat.floor (M / Real.sqrt (Real.sqrt (H * X))) : ℝ) / M
  have hZL : typeI2CapitalZ d x < L := by
    simpa [L] using preliminaryTypeI2LargeM_scale_gt_capitalZ
      d x X H M hx.le hX hH hMlarge hlength
  have hTL : 36 * typeI2T x < L :=
    lt_of_le_of_lt (typeI2CapitalZ_ge_thirtySixT d x hx.le) hZL
  have hTpos : 0 < typeI2T x := by
    rw [typeI2T_eval]
    norm_num [typeI2BZeroValue, typeI2GValue, typeI2CPointValue,
      typeI2CLineValue, typeI2EValue, typeI2DValue, typeI2KZeroValue]
    positivity
  calc
    36 = (typeI2T x)⁻¹ * (36 * typeI2T x) := by
      field_simp [ne_of_gt hTpos]
    _ < (typeI2T x)⁻¹ * L :=
      mul_lt_mul_of_pos_left hTL (inv_pos.mpr hTpos)

/-- The quadratic product-coordinate polynomial attached to a lattice line
`(m₀+qk,n₀-ak)`. -/
noncomputable def hyperbolaProductPolynomial
    (m₀ n₀ q a : ℤ) : Polynomial ℝ :=
  monomial 0 ((m₀ : ℝ) * (n₀ : ℝ)) +
    monomial 1 ((q : ℝ) * (n₀ : ℝ) - (m₀ : ℝ) * (a : ℝ)) +
      monomial 2 (-((q : ℝ) * (a : ℝ)))

theorem hyperbolaProductPolynomial_eval
    (m₀ n₀ q a : ℤ) (k : ℝ) :
    (hyperbolaProductPolynomial m₀ n₀ q a).eval k =
      ((m₀ : ℝ) + (q : ℝ) * k) * ((n₀ : ℝ) - (a : ℝ) * k) := by
  simp [hyperbolaProductPolynomial]
  ring

theorem hyperbolaProductPolynomial_natDegree_le_two
    (m₀ n₀ q a : ℤ) :
    (hyperbolaProductPolynomial m₀ n₀ q a).natDegree ≤ 2 := by
  have h0 :
      (monomial 0 ((m₀ : ℝ) * (n₀ : ℝ))).natDegree ≤ 2 :=
    (Polynomial.natDegree_monomial_le _).trans (by omega)
  have h1 :
      (monomial 1 ((q : ℝ) * (n₀ : ℝ) - (m₀ : ℝ) * (a : ℝ))).natDegree ≤ 2 :=
    (Polynomial.natDegree_monomial_le _).trans (by omega)
  have h2 :
      (monomial 2 (-((q : ℝ) * (a : ℝ)))).natDegree ≤ 2 :=
    Polynomial.natDegree_monomial_le _
  exact Polynomial.natDegree_add_le_of_degree_le
    (Polynomial.natDegree_add_le_of_degree_le h0 h1) h2

theorem hyperbolaProductPolynomial_coeff_two
    (m₀ n₀ q a : ℤ) :
    (hyperbolaProductPolynomial m₀ n₀ q a).coeff 2 =
      -((q : ℝ) * (a : ℝ)) := by
  simp only [hyperbolaProductPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_monomial]
  norm_num

/-- Centering the product coordinate at an integer `Y` preserves degree two
and its exact leading coefficient. -/
noncomputable def hyperbolaCenteredProductPolynomial
    (m₀ n₀ q a Y : ℤ) : Polynomial ℝ :=
  hyperbolaProductPolynomial m₀ n₀ q a - C (Y : ℝ)

/-- The same centered product polynomial over the integers.  This is the
source of the integer-coefficient terms discarded during degree descent. -/
noncomputable def hyperbolaCenteredProductPolynomialInt
    (m₀ n₀ q a Y : ℤ) : Polynomial ℤ :=
  monomial 0 (m₀ * n₀) +
    monomial 1 (q * n₀ - m₀ * a) +
      monomial 2 (-(q * a)) - C Y

theorem hyperbolaCenteredProductPolynomial_map_intCast
    (m₀ n₀ q a Y : ℤ) :
    (hyperbolaCenteredProductPolynomialInt m₀ n₀ q a Y).map
        (Int.castRingHom ℝ) =
      hyperbolaCenteredProductPolynomial m₀ n₀ q a Y := by
  simp [hyperbolaCenteredProductPolynomialInt,
    hyperbolaCenteredProductPolynomial, hyperbolaProductPolynomial]

/-- Every coefficient of every power of the centered product map is the cast
of an integer coefficient. -/
theorem hyperbolaCenteredProductPolynomial_power_coeff_isInt
    (m₀ n₀ q a Y : ℤ) (j i : ℕ) :
    ∃ z : ℤ,
      ((hyperbolaCenteredProductPolynomial m₀ n₀ q a Y) ^ j).coeff i =
        (z : ℝ) := by
  refine ⟨((hyperbolaCenteredProductPolynomialInt m₀ n₀ q a Y) ^ j).coeff i,
    ?_⟩
  rw [← hyperbolaCenteredProductPolynomial_map_intCast]
  rw [← Polynomial.map_pow, Polynomial.coeff_map]
  rfl

theorem hyperbolaCenteredProductPolynomial_eval
    (m₀ n₀ q a Y : ℤ) (k : ℝ) :
    (hyperbolaCenteredProductPolynomial m₀ n₀ q a Y).eval k =
      ((m₀ : ℝ) + (q : ℝ) * k) * ((n₀ : ℝ) - (a : ℝ) * k) - Y := by
  simp [hyperbolaCenteredProductPolynomial, hyperbolaProductPolynomial_eval]

theorem hyperbolaCenteredProductPolynomial_natDegree_le_two
    (m₀ n₀ q a Y : ℤ) :
    (hyperbolaCenteredProductPolynomial m₀ n₀ q a Y).natDegree ≤ 2 := by
  rw [hyperbolaCenteredProductPolynomial, Polynomial.natDegree_sub_C]
  exact hyperbolaProductPolynomial_natDegree_le_two m₀ n₀ q a

theorem hyperbolaCenteredProductPolynomial_coeff_two
    (m₀ n₀ q a Y : ℤ) :
    (hyperbolaCenteredProductPolynomial m₀ n₀ q a Y).coeff 2 =
      -((q : ℝ) * (a : ℝ)) := by
  rw [hyperbolaCenteredProductPolynomial, Polynomial.coeff_sub,
    hyperbolaProductPolynomial_coeff_two]
  rw [Polynomial.coeff_C_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0), sub_zero]

/-- A product coordinate lying in `(X,X+H]`, when centered at `floor X`,
lies in `[0,2H]` for `H≥1`. -/
theorem abs_hyperbolaCenteredProductPolynomial_eval_le
    (m₀ n₀ q a : ℤ) (X H : ℝ) (hH : 1 ≤ H)
    (k : ℕ)
    (hstrip :
      X < ((m₀ : ℝ) + (q : ℝ) * (k : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (k : ℝ)) ∧
      ((m₀ : ℝ) + (q : ℝ) * (k : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (k : ℝ)) ≤ X + H) :
    |(hyperbolaCenteredProductPolynomial m₀ n₀ q a (Int.floor X)).eval
        (k : ℝ)| ≤ 2 * H := by
  rw [hyperbolaCenteredProductPolynomial_eval]
  have hfloorle : (Int.floor X : ℝ) ≤ X := Int.floor_le X
  have hfloorlt : X < (Int.floor X : ℝ) + 1 := Int.lt_floor_add_one X
  have hnonneg :
      0 ≤ ((m₀ : ℝ) + (q : ℝ) * (k : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (k : ℝ)) - (Int.floor X : ℝ) := by
    linarith [hstrip.1]
  rw [abs_of_nonneg hnonneg]
  linarith [hstrip.2]

/-- The degree-two, density-one specialization of dense interpolation used
for every retained hyperbola direction. The literal constant is `864`. -/
theorem quadraticPolynomial_coefficients_of_bounded_interval
    (K : ℕ) (hK : 36 ≤ K) (H : ℝ) (hH : 0 ≤ H)
    (V : Polynomial ℝ) (hVdeg : V.natDegree ≤ 2)
    (hEval : ∀ n ∈ Finset.Icc 1 K, |V.eval (n : ℝ)| ≤ 2 * H) :
    ∀ j ≤ 2, (K : ℝ) ^ j * |V.coeff j| ≤ 864 * H := by
  have hKone : 1 ≤ K := by omega
  let S : Finset ℕ := Finset.Icc 1 K
  have hSsubset : S ⊆ Finset.Icc 1 K := by simp [S]
  have hScard : (1 : ℝ) * (K : ℝ) ≤ (S.card : ℝ) := by
    simp [S, Nat.card_Icc, hKone]
  have hlen :
      (4 : ℝ) * (((2 + 1 : ℕ) : ℝ) ^ 2) / 1 ≤ (K : ℝ) := by
    norm_num
    exact_mod_cast hK
  have hinterp := interpolateDenseSet
    (d := 2) (N := K) (η := (1 : ℝ)) (E := 2 * H)
    (by norm_num) hKone (by norm_num) (by norm_num) hlen
    S hSsubset hScard V hVdeg (by simpa [S] using hEval) (by positivity)
  intro j hj
  have h := hinterp j hj
  norm_num at h ⊢
  nlinarith

/-- Transport the preceding `K`-scale coefficient estimate to the ambient
scale `L`. This is the exact `864 H t²` estimate used after
`K ≥ t⁻¹L`. -/
theorem quadraticPolynomial_coefficients_at_ambient_scale
    (K : ℕ) (hK : 36 ≤ K) (H L t : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (ht : 1 ≤ t)
    (hLK : L ≤ t * (K : ℝ))
    (V : Polynomial ℝ) (hVdeg : V.natDegree ≤ 2)
    (hEval : ∀ n ∈ Finset.Icc 1 K, |V.eval (n : ℝ)| ≤ 2 * H) :
    ∀ j ≤ 2, L ^ j * |V.coeff j| ≤ 864 * H * t ^ 2 := by
  have hbase := quadraticPolynomial_coefficients_of_bounded_interval
    K hK H hH V hVdeg hEval
  intro j hj
  have hK0 : 0 ≤ (K : ℝ) := by positivity
  have ht0 : 0 ≤ t := by linarith
  have hpow : L ^ j ≤ (t * (K : ℝ)) ^ j :=
    pow_le_pow_left₀ hL hLK j
  have htpow : t ^ j ≤ t ^ 2 :=
    pow_le_pow_right₀ ht hj
  calc
    L ^ j * |V.coeff j| ≤
        (t * (K : ℝ)) ^ j * |V.coeff j| :=
      mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
    _ = t ^ j * ((K : ℝ) ^ j * |V.coeff j|) := by ring
    _ ≤ t ^ j * (864 * H) :=
      mul_le_mul_of_nonneg_left (hbase j hj) (pow_nonneg ht0 _)
    _ ≤ t ^ 2 * (864 * H) :=
      mul_le_mul_of_nonneg_right htpow (by positivity)
    _ = 864 * H * t ^ 2 := by ring

/-- Summing the three coefficient estimates for a quadratic gives the exact
`2592 H t²` weighted-coefficient bound used in the degree descent. -/
theorem quadraticPolynomial_weightedCoefficientSum_le
    (K : ℕ) (hK : 36 ≤ K) (H L t : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (ht : 1 ≤ t)
    (hLK : L ≤ t * (K : ℝ))
    (V : Polynomial ℝ) (hVdeg : V.natDegree ≤ 2)
    (hEval : ∀ n ∈ Finset.Icc 1 K, |V.eval (n : ℝ)| ≤ 2 * H) :
    polynomialWeightedCoefficientSum L V ≤ 2592 * H * t ^ 2 := by
  have hcoeff := quadraticPolynomial_coefficients_at_ambient_scale
    K hK H L t hH hL ht hLK V hVdeg hEval
  rw [polynomialWeightedCoefficientSum,
    tsum_eq_sum (s := Finset.range 3) (fun n hn => by
      have hn3 : 3 ≤ n := by simpa [Finset.mem_range] using hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hVdeg (by omega))]
      simp)]
  calc
    ∑ n ∈ Finset.range 3, L ^ n * |V.coeff n| ≤
        ∑ _n ∈ Finset.range 3, 864 * H * t ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact hcoeff n (by
        have hn3 : n < 3 := by simpa [Finset.mem_range] using hn
        omega)
    _ = 2592 * H * t ^ 2 := by
      norm_num [Finset.sum_range_succ]
      ring

/-- After normalizing by `H⁻¹`, the weighted coefficient sum of the
`j`-th power is bounded by the exact blueprint quantity
`(2592 t²)^j`. -/
theorem quadraticPolynomial_normalized_power_weightedCoefficientSum_le
    (K : ℕ) (hK : 36 ≤ K) (H L t : ℝ)
    (hH : 1 ≤ H) (hL : 0 ≤ L) (ht : 1 ≤ t)
    (hLK : L ≤ t * (K : ℝ))
    (V : Polynomial ℝ) (hVdeg : V.natDegree ≤ 2)
    (hEval : ∀ n ∈ Finset.Icc 1 K, |V.eval (n : ℝ)| ≤ 2 * H)
    (j : ℕ) :
    H⁻¹ ^ j * polynomialWeightedCoefficientSum L (V ^ j) ≤
      (2592 * t ^ 2) ^ j := by
  have hbase :
      polynomialWeightedCoefficientSum L V ≤ 2592 * H * t ^ 2 :=
    quadraticPolynomial_weightedCoefficientSum_le
      K hK H L t (by linarith) hL ht hLK V hVdeg hEval
  have hW0 : 0 ≤ polynomialWeightedCoefficientSum L V :=
    polynomialWeightedCoefficientSum_nonneg L hL V
  have hpower :
      polynomialWeightedCoefficientSum L (V ^ j) ≤
        (2592 * H * t ^ 2) ^ j :=
    (polynomialWeightedCoefficientSum_pow_le L hL V j).trans
      (pow_le_pow_left₀ hW0 hbase j)
  calc
    H⁻¹ ^ j * polynomialWeightedCoefficientSum L (V ^ j) ≤
        H⁻¹ ^ j * (2592 * H * t ^ 2) ^ j :=
      mul_le_mul_of_nonneg_left hpower
        (pow_nonneg (inv_nonneg.mpr (by linarith)) _)
    _ = (H⁻¹ * (2592 * H * t ^ 2)) ^ j :=
      (mul_pow H⁻¹ (2592 * H * t ^ 2) j).symm
    _ = (2592 * t ^ 2) ^ j := by
      congr 1
      field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hH)]

/-- The exact coefficient bound for a hyperbola product map on a full
partition progression, centered at `floor X`. -/
theorem hyperbolaCenteredProductPolynomial_coefficients_at_ambient_scale
    (m₀ n₀ q a : ℤ) (K : ℕ) (hK : 36 ≤ K)
    (X H L t : ℝ) (hH : 1 ≤ H) (hL : 0 ≤ L) (ht : 1 ≤ t)
    (hLK : L ≤ t * (K : ℝ))
    (hstrip : ∀ k ∈ Finset.Icc 1 K,
      X < ((m₀ : ℝ) + (q : ℝ) * (k : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (k : ℝ)) ∧
      ((m₀ : ℝ) + (q : ℝ) * (k : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (k : ℝ)) ≤ X + H) :
    ∀ j ≤ 2,
      L ^ j *
          |(hyperbolaCenteredProductPolynomial m₀ n₀ q a (Int.floor X)).coeff j| ≤
        864 * H * t ^ 2 := by
  apply quadraticPolynomial_coefficients_at_ambient_scale
    K hK H L t (by linarith) hL ht hLK
    (hyperbolaCenteredProductPolynomial m₀ n₀ q a (Int.floor X))
    (hyperbolaCenteredProductPolynomial_natDegree_le_two _ _ _ _ _)
  intro k hk
  exact abs_hyperbolaCenteredProductPolynomial_eval_le
    m₀ n₀ q a X H hH k (hstrip k hk)

/-- Exact normalized finite-product coefficient bound for the centered
hyperbola product map. -/
theorem hyperbolaCenteredProductPolynomial_normalized_power_coefficientSum_le
    (m₀ n₀ q a : ℤ) (K : ℕ) (hK : 36 ≤ K)
    (X H L t : ℝ) (hH : 1 ≤ H) (hL : 0 ≤ L) (ht : 1 ≤ t)
    (hLK : L ≤ t * (K : ℝ))
    (hstrip : ∀ k ∈ Finset.Icc 1 K,
      X < ((m₀ : ℝ) + (q : ℝ) * (k : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (k : ℝ)) ∧
      ((m₀ : ℝ) + (q : ℝ) * (k : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (k : ℝ)) ≤ X + H)
    (j : ℕ) :
    H⁻¹ ^ j * polynomialWeightedCoefficientSum L
        ((hyperbolaCenteredProductPolynomial
          m₀ n₀ q a (Int.floor X)) ^ j) ≤
      (2592 * t ^ 2) ^ j := by
  apply quadraticPolynomial_normalized_power_weightedCoefficientSum_le
    K hK H L t hH hL ht hLK
    (hyperbolaCenteredProductPolynomial m₀ n₀ q a (Int.floor X))
    (hyperbolaCenteredProductPolynomial_natDegree_le_two _ _ _ _ _)
  intro k hk
  exact abs_hyperbolaCenteredProductPolynomial_eval_le
    m₀ n₀ q a X H hH k (hstrip k hk)

/-- The checked geometric-data constructor with its fourth-root hypothesis
discharged directly from failure of the approved short-interval alternative. -/
theorem preliminaryTypeI2LargeMGeometricData_of_nonexception
    (d : ℕ) (x X H M : ℝ) (J : Set ℝ)
    (hx : 0 ≤ x)
    (hX : 1 ≤ X) (hH : 1 ≤ H)
    (hroot : Real.rpow X (1 / 3 : ℝ) ≤ H)
    (hHupper : H ≤ X)
    (hMupper : M ≤ 2 * Real.sqrt X)
    (hJconvex : Set.OrdConnected J)
    (hJsubset : J ⊆ Set.Ioc M (2 * M))
    (hMlarge : 2 * Real.sqrt (Real.sqrt (H * X)) ≤ M)
    (hlength : typeI2J d x * Real.rpow X (1 / 3 : ℝ) < H) :
    ∃ g : Hyperbola.geometricData,
      g.K₀ = 2 ∧ g.X = X ∧ g.H = H ∧ g.M = M ∧ g.J = J ∧
        g.Q = Nat.floor (M / Real.sqrt (Real.sqrt (H * X))) := by
  apply preliminaryTypeI2LargeMGeometricData X H M J hX hH hroot hHupper
    hMupper hJconvex hJsubset hMlarge
  exact preliminaryTypeI2_nonexception_twiceFourthRoot_le
    d x X H hx (by linarith) (by linarith) hlength

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.typeI2J_ge_sixteen
#print axioms FractionalPrimes.Literature.Polynomial.typeI2T_ge_one
#print axioms FractionalPrimes.Literature.Polynomial.typeI2J_ge_four_capitalZ_sq
#print axioms FractionalPrimes.Literature.Polynomial.typeI2CapitalZ_ge_one
#print axioms FractionalPrimes.Literature.Polynomial.typeI2CapitalZ_ge_thirtySixT
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2_nonexception_cubic_lower
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2_nonexception_twiceFourthRoot_le
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_floor_lower
#print axioms FractionalPrimes.Literature.Polynomial.typeI2LargeM_recurrenceScaleProduct_lower
#print axioms FractionalPrimes.Literature.Polynomial.typeI2LargeMRecurrenceNTwo_lower
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_recurrenceScaleProduct_lower
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_scale_gt_capitalZ
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeM_inverseT_mul_scale_gt_thirtySix
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaProductPolynomial_eval
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaProductPolynomial_natDegree_le_two
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaProductPolynomial_coeff_two
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_eval
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_map_intCast
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_power_coeff_isInt
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_natDegree_le_two
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_coeff_two
#print axioms FractionalPrimes.Literature.Polynomial.abs_hyperbolaCenteredProductPolynomial_eval_le
#print axioms FractionalPrimes.Literature.Polynomial.quadraticPolynomial_coefficients_of_bounded_interval
#print axioms FractionalPrimes.Literature.Polynomial.quadraticPolynomial_coefficients_at_ambient_scale
#print axioms FractionalPrimes.Literature.Polynomial.quadraticPolynomial_weightedCoefficientSum_le
#print axioms FractionalPrimes.Literature.Polynomial.quadraticPolynomial_normalized_power_weightedCoefficientSum_le
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_coefficients_at_ambient_scale
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_normalized_power_coefficientSum_le
#print axioms FractionalPrimes.Literature.Polynomial.preliminaryTypeI2LargeMGeometricData_of_nonexception
