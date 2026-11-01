module

public import FractionalPrimes.Literature.MSZ.FiniteGridMaximalData
public import FractionalPrimes.Literature.MSZ.LocalizedInterpolation

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open scoped ENNReal

noncomputable section

/-- The coefficient from localized interpolation, specialized to the grid
choices `N = 2^l`, `E₀ = max 1 D · 2^{-l}`, `B = 2 B_{K,L}`, and
`A = 2^{-l/2} a_{j,l}`. The identity is valid when `a j l = 0`. -/
theorem mszLocalizedGridCoefficient_eq
    (A : AdmissibleData) (K L l : ℕ) (j : ℤ) :
    localInterpolationC A.q *
        (max 1 (max (A.P (localInterpolationR A.q))
          (A.P (localInterpolationRPrime A.q))) : ℝ) ^ (2 - A.q) *
        ((((2 ^ l : ℕ) : ℝ) *
          (max 1 A.D * (2 : ℝ) ^ (-(l : ℤ))) *
          (2 * mszFiniteGridMaximalConstant A K L)) ^ ((2 - A.q) / 2)) *
        ((2 : ℝ) ^ (-(l : ℝ) / 2) * A.a j l) ^ (A.q - 1) =
      (localInterpolationC A.q *
          (max 1 (max (A.P (localInterpolationR A.q))
            (A.P (localInterpolationRPrime A.q))) : ℝ) ^ (2 - A.q) *
          (2 * max 1 A.D) ^ ((2 - A.q) / 2)) *
        (mszFiniteGridMaximalConstant A K L) ^ ((2 - A.q) / 2) *
        (2 : ℝ) ^ (-((A.q - 1) * (l : ℝ)) / 2) *
        (A.a j l) ^ (A.q - 1) := by
  have hDbar : 0 ≤ max 1 A.D :=
    le_trans (by norm_num) (le_max_left 1 A.D)
  have hBone : 1 ≤ mszFiniteGridMaximalConstant A K L := by
    dsimp [mszFiniteGridMaximalConstant]
    exact le_max_left _ _
  have hBnonneg : 0 ≤ mszFiniteGridMaximalConstant A K L :=
    le_trans (by norm_num) hBone
  have ha : 0 ≤ A.a j l := A.a_nonneg j l
  have hDyadic :
      ((2 ^ l : ℕ) : ℝ) * (2 : ℝ) ^ (-(l : ℤ)) = 1 := by
    calc
      _ = (2 : ℝ) ^ (l : ℤ) * (2 : ℝ) ^ (-(l : ℤ)) := by
        rw [Nat.cast_pow, zpow_natCast]
        rfl
      _ = (2 : ℝ) ^ ((l : ℤ) + (-(l : ℤ))) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = 1 := by simp
  have hMass :
      ((2 ^ l : ℕ) : ℝ) *
          (max 1 A.D * (2 : ℝ) ^ (-(l : ℤ))) *
          (2 * mszFiniteGridMaximalConstant A K L) =
        (2 * max 1 A.D) * mszFiniteGridMaximalConstant A K L := by
    calc
      _ = (((2 ^ l : ℕ) : ℝ) * (2 : ℝ) ^ (-(l : ℤ))) *
          (max 1 A.D) * (2 * mszFiniteGridMaximalConstant A K L) := by ring
      _ = 1 * (max 1 A.D) *
          (2 * mszFiniteGridMaximalConstant A K L) := by rw [hDyadic]
      _ = (2 * max 1 A.D) * mszFiniteGridMaximalConstant A K L := by ring
  have hDirectBase : 0 ≤ (2 : ℝ) ^ (-(l : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hDirectScale :
      ((2 : ℝ) ^ (-(l : ℝ) / 2)) ^ (A.q - 1) =
        (2 : ℝ) ^ (-((A.q - 1) * (l : ℝ)) / 2) := by
    rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))
      (-(l : ℝ) / 2) (A.q - 1)]
    congr 1
    ring
  rw [hMass,
    Real.mul_rpow (mul_nonneg (by norm_num) hDbar) hBnonneg,
    Real.mul_rpow hDirectBase ha,
    hDirectScale]
  ring

end

end FractionalPrimes.Literature.MSZ

end
