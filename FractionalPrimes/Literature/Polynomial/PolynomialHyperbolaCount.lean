module

public import FractionalPrimes.Literature.Hyperbola.HyperbolaPointBound
public import FractionalPrimes.Literature.Polynomial.PolynomialTypeI2Budgets
public import FractionalPrimes.Literature.Polynomial.PolynomialTypeI2SmallScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open Set

private theorem hyperbola_count_cubic_lower
    (X H : ℝ) (hX : 1 ≤ X)
    (hH : 16 * Real.rpow X (1 / 3 : ℝ) ≤ H) :
    16 * X ≤ H ^ 3 := by
  have hXpos : 0 < X := by linarith
  let y : ℝ := Real.rpow X (1 / 3 : ℝ)
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact Real.rpow_nonneg (by linarith) _
  have hy1 : 1 ≤ y := by
    dsimp [y]
    exact Real.one_le_rpow hX (by norm_num)
  have hcube : (Real.rpow X (1 / 3 : ℝ)) ^ 3 = X := by
    have hnat : (Real.rpow X (1 / 3 : ℝ)) ^ 3 =
        Real.rpow (Real.rpow X (1 / 3 : ℝ)) (3 : ℝ) :=
      (Real.rpow_natCast (Real.rpow X (1 / 3 : ℝ)) 3).symm
    have hrpow : Real.rpow (Real.rpow X (1 / 3 : ℝ)) (3 : ℝ) = X := by
      simpa [show (1 / 3 : ℝ)⁻¹ = 3 by norm_num] using
        (Real.rpow_rpow_inv (by linarith : 0 ≤ X)
          (by norm_num : (1 / 3 : ℝ) ≠ 0))
    rw [hnat, hrpow]
  have hy3 : y ^ 3 = X := by simpa [y] using hcube
  have hHpos : 0 < H := by nlinarith [hH]
  let A := 16 * y
  have hAleH : A ≤ H := by simpa [A, y] using hH
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA2 : A ^ 2 ≤ H ^ 2 :=
    (sq_le_sq₀ hA0 hHpos.le).2 hAleH
  have hA3 : A ^ 3 ≤ H ^ 3 := by
    calc
      A ^ 3 = A ^ 2 * A := by ring
      _ ≤ H ^ 2 * A := mul_le_mul_of_nonneg_right hA2 hA0
      _ ≤ H ^ 2 * H := mul_le_mul_of_nonneg_left hAleH (sq_nonneg H)
      _ = H ^ 3 := by ring
  dsimp [A] at hA3
  rw [show (16 * y) ^ 3 = 4096 * y ^ 3 by ring, hy3] at hA3
  nlinarith

private theorem hyperbola_count_twice_fourth_root_le
    (X H : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H)
    (hHX : 16 * X ≤ H ^ 3) :
    2 * Real.sqrt (Real.sqrt (H * X)) ≤ H := by
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

/-- The exact two-branch lattice count in blueprint `lpi:hyperbola-count`.
The interval hypothesis is expressed as order-convexity together with the
approved containment in `(M,2M]`. -/
theorem hyperbolaCountAllScales
    (X H M : ℝ) (J : Set ℝ)
    (hX : 1 ≤ X)
    (hHlower : 16 * Real.rpow X (1 / 3 : ℝ) ≤ H)
    (hHupper : H ≤ X)
    (hMlower : (1 / 2 : ℝ) ≤ M)
    (hMupper : M ≤ 2 * Real.sqrt X)
    (hJconvex : Set.OrdConnected J)
    (hJsubset : J ⊆ Set.Ioc M (2 * M)) :
    ((Hyperbola.hyperbolaLatticeSet X H J).ncard : ℝ) ≤
      (typeI2CCountValue : ℝ) * H := by
  classical
  have hHcube := hyperbola_count_cubic_lower X H hX hHlower
  have hroot0 : 0 ≤ Real.rpow X (1 / 3 : ℝ) :=
    Real.rpow_nonneg (by linarith : 0 ≤ X) _
  have hroot1 : 1 ≤ Real.rpow X (1 / 3 : ℝ) :=
    Real.one_le_rpow hX (by norm_num)
  have hHone : 1 ≤ H := by nlinarith [hHlower, hroot1]
  have hHpos : 0 < H := by linarith
  have hHnonneg : 0 ≤ H := hHpos.le
  let Dfourth : ℝ := Real.sqrt (Real.sqrt (H * X))
  by_cases hsmall : M < 2 * Dfourth
  · have hsmallCount :=
      smallM_hyperbolaLatticeCount X H M J hX hHcube hMlower hsmall hJsubset
    have hCcount6 : (6 : ℝ) ≤ (typeI2CCountValue : ℝ) := by
      norm_num [typeI2CCountValue, typeI2CPointValue, typeI2BZeroValue,
        typeI2EValue, typeI2DValue, typeI2KZeroValue]
    calc
      ((Hyperbola.hyperbolaLatticeSet X H J).ncard : ℝ) ≤ 6 * H := hsmallCount
      _ ≤ (typeI2CCountValue : ℝ) * H :=
        mul_le_mul_of_nonneg_right hCcount6 hHnonneg
  · have hMlarge : 2 * Dfourth ≤ M := le_of_not_gt hsmall
    have hHXone : 1 ≤ H * X := by
      have hmul := mul_le_mul hHone hX (by norm_num) (by linarith)
      nlinarith [hmul]
    have hsqrtHXone : 1 ≤ Real.sqrt (H * X) := by
      simpa using Real.sqrt_le_sqrt hHXone
    have hDfourthone : 1 ≤ Dfourth := by
      simpa [Dfourth] using Real.sqrt_le_sqrt hsqrtHXone
    have hMone : 1 ≤ M := by nlinarith [hMlarge, hDfourthone]
    have hDpos : 0 < Dfourth := by linarith
    have hMpos : 0 < M := by linarith
    have hratio0 : 0 ≤ M / Dfourth := div_nonneg hMpos.le hDpos.le
    have hratio2 : 2 ≤ M / Dfourth :=
      (le_div_iff₀ hDpos).2 (by simpa using hMlarge)
    let Q : ℕ := Nat.floor (M / Dfourth)
    have hQtwo : 2 ≤ Q := by
      dsimp [Q]
      exact Nat.le_floor hratio2
    have hQpos : 0 < Q := by omega
    have hQupper : (Q : ℝ) ≤ M / Dfourth := by
      dsimp [Q]
      exact Nat.floor_le hratio0
    have hHfourth : 2 * Dfourth ≤ H := by
      have h := hyperbola_count_twice_fourth_root_le X H
        (by linarith) hHnonneg hHcube
      simpa [Dfourth] using h
    have htwoDpos : 0 < 2 * Dfourth := by positivity
    have hMQhalf : M / H ≤ M / (2 * Dfourth) := by
      apply (div_le_div_iff₀ hHpos htwoDpos).2
      nlinarith [hHfourth, hMpos]
    have hfloorlt : M / Dfourth < (Q : ℝ) + 1 := by
      dsimp [Q]
      exact Nat.lt_floor_add_one (M / Dfourth)
    have hhalf_le_Q : (M / Dfourth) / 2 ≤ (Q : ℝ) := by
      nlinarith [hratio2, hfloorlt]
    have hMQleQ : M / H ≤ (Q : ℝ) := by
      calc
        M / H ≤ M / (2 * Dfourth) := hMQhalf
        _ = (M / Dfourth) / 2 := by
          field_simp [ne_of_gt hDpos]
        _ ≤ (Q : ℝ) := hhalf_le_Q
    let g : Hyperbola.HyperbolaGeometricData :=
      { K₀ := 2
        X := X
        H := H
        M := M
        Q := Q
        J := J
        K₀_ge_one := by norm_num
        X_ge_one := hX
        H_ge_one := hHone
        M_ge_one := hMone
        Q_pos := hQpos
        J_orderConvex := hJconvex
        J_subset := hJsubset
        X_cuberoot_le_H := by
          nlinarith [hroot1, hHlower]
        H_le_X := hHupper
        M_le_K₀_sqrtX := by simpa using hMupper
        M_div_H_le_Q := hMQleQ
        Q_le_M_div_fourthRoot := by simpa [Dfourth] using hQupper }
    have hlargeGeom :
        ((Hyperbola.hyperbolaLatticeSet X H J).ncard : ℝ) ≤
          Hyperbola.C_point 2 * (Hyperbola.E 2 + (2 : ℝ) ^ 2) * H := by
      have h := Hyperbola.hyperbolaPointBound g
      change ((Hyperbola.hyperbolaLatticeSet X H J).ncard : ℝ) ≤ _ at h
      exact h
    have hCpoint : (typeI2CPointValue : ℝ) = Hyperbola.C_point 2 :=
      typeI2_fixed_geometric_constants.2.1
    have hBzero :
        (typeI2BZeroValue : ℝ) =
          Hyperbola.E 2 + (2 : ℝ) ^ 2 := by
      norm_num [typeI2BZeroValue, typeI2EValue, typeI2KZeroValue,
        Hyperbola.E]
    have hCcountFormula :
        (typeI2CCountValue : ℝ) =
          6 + (typeI2CPointValue : ℝ) * (typeI2BZeroValue : ℝ) := by
      norm_num [typeI2CCountValue]
    have hconstant :
        Hyperbola.C_point 2 * (Hyperbola.E 2 + (2 : ℝ) ^ 2) ≤
          (typeI2CCountValue : ℝ) := by
      rw [← hCpoint, ← hBzero, hCcountFormula]
      linarith
    calc
      ((Hyperbola.hyperbolaLatticeSet X H J).ncard : ℝ) ≤
          Hyperbola.C_point 2 * (Hyperbola.E 2 + (2 : ℝ) ^ 2) * H :=
        hlargeGeom
      _ ≤ (typeI2CCountValue : ℝ) * H :=
        mul_le_mul_of_nonneg_right hconstant hHnonneg

#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCountAllScales

end FractionalPrimes.Literature.Polynomial
