module

public import FractionalPrimes.Literature.JSW.Conventions
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Half-open dyadic averages on the line

This file defines the dyadic cells, their unique half-open selector, the
averaging operators `E_m`, their differences, and the increasing-filtration
notation used in `lj:dyadic-definition`.
-/

@[expose] public section

open MeasureTheory Set

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The half-open dyadic cell with scale `2^m` and integer index `j`. -/
def dyadicInterval (m j : ℤ) : Set ℝ :=
  Set.Ico ((j : ℝ) * (2 : ℝ) ^ m) (((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m)

/-- The index of the half-open dyadic cell containing `x`. -/
def dyadicIntervalIndex (m : ℤ) (x : ℝ) : ℤ :=
  Int.floor (x / (2 : ℝ) ^ m)

private theorem dyadicScale_pos (m : ℤ) : 0 < (2 : ℝ) ^ m :=
  zpow_pos (by norm_num) m

/-- Every point belongs to the cell selected by the floor convention. -/
theorem mem_dyadicIntervalIndex (m : ℤ) (x : ℝ) :
    x ∈ dyadicInterval m (dyadicIntervalIndex m x) := by
  have hs : 0 < (2 : ℝ) ^ m := dyadicScale_pos m
  have hfloorle :
      (Int.floor (x / (2 : ℝ) ^ m) : ℝ) ≤ x / (2 : ℝ) ^ m := Int.floor_le _
  have hfloorlt :
      x / (2 : ℝ) ^ m < (Int.floor (x / (2 : ℝ) ^ m) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  rw [dyadicInterval, Set.mem_Ico]
  constructor
  · calc
      (Int.floor (x / (2 : ℝ) ^ m) : ℝ) * (2 : ℝ) ^ m ≤
          (x / (2 : ℝ) ^ m) * (2 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hfloorle hs.le
      _ = x := div_mul_cancel₀ x hs.ne'
  · calc
      x = (x / (2 : ℝ) ^ m) * (2 : ℝ) ^ m :=
        (div_mul_cancel₀ x hs.ne').symm
      _ < (((dyadicIntervalIndex m x + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) :=
        by
          have hi : dyadicIntervalIndex m x = Int.floor (x / (2 : ℝ) ^ m) := rfl
          rw [hi, Int.cast_add, Int.cast_one]
          exact mul_lt_mul_of_pos_right hfloorlt hs

/-- A point lies in exactly one cell of each dyadic scale. -/
theorem existsUnique_dyadicInterval (m : ℤ) (x : ℝ) :
    ∃! j : ℤ, x ∈ dyadicInterval m j := by
  refine ⟨dyadicIntervalIndex m x, mem_dyadicIntervalIndex m x, ?_⟩
  intro j hj
  have hs : 0 < (2 : ℝ) ^ m := dyadicScale_pos m
  rw [dyadicInterval, Set.mem_Ico] at hj
  change j = Int.floor (x / (2 : ℝ) ^ m)
  symm
  apply (Int.floor_eq_iff).2
  constructor
  · apply (le_div_iff₀ hs).2
    simpa using hj.1
  · apply (div_lt_iff₀ hs).2
    simpa using hj.2

/-- The family of dyadic cells at scale `2^m`. -/
def dyadicIntervals (m : ℤ) : Set (Set ℝ) :=
  Set.range (dyadicInterval m)

/-- The dyadic averaging operator `E_m`, normalized by the cell length. -/
def dyadicAverage (m : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((2 : ℝ) ^ m)⁻¹ •
    ∫ y in dyadicInterval m (dyadicIntervalIndex m x), f y ∂volume

/-- The dyadic difference `Δ_m = E_{m-1} - E_m`. -/
def dyadicDifference (m : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  dyadicAverage (m - 1) f x - dyadicAverage m f x

/-- The increasing-filtration averages `P_n = E_{-n}`. -/
def dyadicIncreasingAverage (n : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  dyadicAverage (-n) f x

/-- The increments `d_n = P_n - P_{n-1}` of the increasing filtration. -/
def dyadicMartingaleDifference (n : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  dyadicIncreasingAverage n f x - dyadicIncreasingAverage (n - 1) f x

end

#print axioms FractionalPrimes.Literature.JSW.mem_dyadicIntervalIndex
#print axioms FractionalPrimes.Literature.JSW.existsUnique_dyadicInterval
#print axioms FractionalPrimes.Literature.JSW.dyadicAverage

end FractionalPrimes.Literature.JSW

end
