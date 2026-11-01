module

public import FractionalPrimes.Literature.Uniformity.ArithmeticTypeDecomposition

/-!
# Dyadic scale bounds for the distinguished grouped factor

This file isolates the source step converting absence of the type-I
grouping predicate into the exact scale range required by
`originalLongFactorOfMobiusGoal`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Twisted

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

theorem selectedDyadicFactors_get_of_mem
    {X : ℝ} (fs : List (DyadicArithmeticFactor X))
    (s : Finset (Fin fs.length)) {i : Fin fs.length} (hi : i ∈ s) :
    ∃ j : Fin (selectedDyadicFactors fs s).length,
      (selectedDyadicFactors fs s).get j = fs.get i := by
  have hmem : fs.get i ∈ selectedDyadicFactors fs s := by
    rw [selectedDyadicFactors]
    exact List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩
  exact List.mem_iff_get.mp hmem

/-- The list position selected from a finite set still remembers the
original label, even when distinct labels carry equal factor values. -/
theorem selectedDyadicFactors_get_with_label
    {X : ℝ} (fs : List (DyadicArithmeticFactor X))
    (s : Finset (Fin fs.length)) {i : Fin fs.length} (hi : i ∈ s) :
    ∃ j : ℕ, ∃ hj : j < s.toList.length,
      s.toList[j]'hj = i ∧
        (selectedDyadicFactors fs s)[j]'
          (by simpa [selectedDyadicFactors] using hj) = fs.get i := by
  have hmem : i ∈ s.toList := by simpa using hi
  obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨j, hj, hji, ?_⟩
  simp [selectedDyadicFactors, hji]

theorem groupedFactorOriginalScaleBounds
    {X N : ℝ} (hX : 1 ≤ X) {k : ℕ}
    (w : GroupingPredicates k) (hnotI : ¬ w.I (5 / 8))
    (i : Fin k) (hi : (1 / 80 : ℝ) ≤ w.weight i)
    (hscale : normalizedExponentConstant⁻¹ * X ^ w.weight i ≤ N ∧
      N ≤ normalizedExponentConstant * X ^ w.weight i) :
    (2 ^ 23 : ℝ)⁻¹ * X ^ (1 / 80 : ℝ) ≤ N ∧
      N ≤ (2 ^ 23 : ℝ) * X ^ (3 / 8 : ℝ) := by
  have hweight : w.weight i < (3 / 8 : ℝ) := by
    by_contra hnot
    have hge : (3 / 8 : ℝ) ≤ w.weight i := le_of_not_gt hnot
    apply hnotI
    refine ⟨i, ?_⟩
    norm_num
    exact hge
  have hC : 0 < normalizedExponentConstant := by
    norm_num [normalizedExponentConstant]
  have hlowPow : X ^ (1 / 80 : ℝ) ≤ X ^ w.weight i :=
    Real.rpow_le_rpow_of_exponent_le hX hi
  have huppPow : X ^ w.weight i ≤ X ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX hweight.le
  constructor
  · calc
      (2 ^ 23 : ℝ)⁻¹ * X ^ (1 / 80 : ℝ) =
          normalizedExponentConstant⁻¹ * X ^ (1 / 80 : ℝ) := by
            simp [normalizedExponentConstant]
      _ ≤ normalizedExponentConstant⁻¹ * X ^ w.weight i :=
        mul_le_mul_of_nonneg_left hlowPow (by positivity)
      _ ≤ N := hscale.1
  · calc
      N ≤ normalizedExponentConstant * X ^ w.weight i := hscale.2
      _ ≤ normalizedExponentConstant * X ^ (3 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left huppPow hC.le
      _ = (2 ^ 23 : ℝ) * X ^ (3 / 8 : ℝ) := by
        simp [normalizedExponentConstant]

end FractionalPrimes.Literature.Twisted

#print axioms FractionalPrimes.Literature.Twisted.selectedDyadicFactors_get_with_label
#print axioms FractionalPrimes.Literature.Twisted.groupedFactorOriginalScaleBounds

