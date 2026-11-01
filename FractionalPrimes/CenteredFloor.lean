module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

@[expose] public section

namespace FractionalPrimes

/-- The half-shift of a number in the centered unit interval lies in `[0,1)`,
so its integer floor is zero. This is the scalar floor fact needed to show
the chosen representative is fixed on `[-1/2,1/2)`. -/
theorem centeredHalfShift_floor_eq_zero {ξ : ℝ}
    (hξ : -(1 / 2 : ℝ) ≤ ξ ∧ ξ < 1 / 2) :
    ⌊ξ + 1 / 2⌋ = 0 := by
  rcases hξ with ⟨hlo, hhi⟩
  have hlo' : 0 ≤ ξ + 1 / 2 := by
    have h := add_le_add_left hlo (1 / 2 : ℝ)
    calc
      0 = -(1 / 2 : ℝ) + 1 / 2 := by ring
      _ ≤ ξ + 1 / 2 := h
  have hhi' : ξ + 1 / 2 < 1 := by
    have h := add_lt_add_left hhi (1 / 2 : ℝ)
    calc
      ξ + 1 / 2 < (1 / 2 : ℝ) + 1 / 2 := h
      _ = 1 := by ring
  have hloCast : ((0 : ℤ) : ℝ) ≤ ξ + 1 / 2 := by
    exact_mod_cast hlo'
  have hhiCast : ξ + 1 / 2 < ((0 : ℤ) : ℝ) + 1 := by
    simpa using hhi'
  rw [Int.floor_eq_iff]
  exact ⟨hloCast, hhiCast⟩

end FractionalPrimes
