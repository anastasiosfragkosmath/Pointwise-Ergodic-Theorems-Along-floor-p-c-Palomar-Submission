module

public import FractionalPrimes.Literature.MSZ.FiniteGridIncrementContract

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open scoped ENNReal

/-! Exact `D 2^{-l}` and `\overline D 2^{-l}` mass bounds for the
approved finite-grid increment kernels. -/

/-- The grid-increment kernel mass is at most `D·2^(−l)`, retaining the
sharp constant from the time-regularity hypothesis. -/
theorem mszGridIncrementKernel_mass_le_D (A : AdmissibleData)
    (k : ℤ) (l m : ℕ) :
    integerKernelL1Mass (mszGridIncrementKernel A.kernel k l m) ≤
      A.D * (2 : ℝ) ^ (-(l : ℤ)) := by
  let K₂ := (A.kernel (mszGridTime k l (m + 1))).toIntegerL1Kernel
  let K₁ := (A.kernel (mszGridTime k l m)).toIntegerL1Kernel
  have hmass : integerKernelL1Mass (mszGridIncrementKernel A.kernel k l m) =
      ‖convolutionL1Operator (mszGridIncrementKernel A.kernel k l m)‖ := by
    unfold integerKernelL1Mass
    exact (convolutionL1Operator_norm_eq _).symm
  have hclm : convolutionL1Operator (mszGridIncrementKernel A.kernel k l m) =
      mszKernelL1Operator (A.kernel (mszGridTime k l (m + 1))) -
        mszKernelL1Operator (A.kernel (mszGridTime k l m)) := by
    simpa [mszGridIncrementKernel, K₂, K₁, mszKernelL1Operator] using
      convolutionL1Operator_difference K₂ K₁
  have hratio := mszGridIncrementOperatorNorm_le_timeRatio A k l m
  have hscaled : A.D *
      (((2 : ℚ) ^ (k - (l : ℤ)) : ℚ) : ℝ) /
        ((mszGridTime k l m).val : ℝ) ≤
      A.D * (2 : ℝ) ^ (-(l : ℤ)) := by
    have h := mul_le_mul_of_nonneg_left
      (mszGridTime_meshRatio_le k l m) A.D_nonneg
    calc
      A.D * (((2 : ℚ) ^ (k - (l : ℤ)) : ℚ) : ℝ) /
          ((mszGridTime k l m).val : ℝ) =
        A.D * ((((2 : ℚ) ^ (k - (l : ℤ)) : ℚ) : ℝ) /
          ((mszGridTime k l m).val : ℝ)) := by ring
      _ ≤ A.D * (2 : ℝ) ^ (-(l : ℤ)) := by
        simpa [Rat.cast_zpow] using h
  calc
    integerKernelL1Mass (mszGridIncrementKernel A.kernel k l m) =
        ‖convolutionL1Operator (mszGridIncrementKernel A.kernel k l m)‖ := hmass
    _ = ‖mszKernelL1Operator (A.kernel (mszGridTime k l (m + 1))) -
        mszKernelL1Operator (A.kernel (mszGridTime k l m))‖ := by rw [hclm]
    _ ≤ A.D * (((2 : ℚ) ^ (k - (l : ℤ)) : ℚ) : ℝ) /
        ((mszGridTime k l m).val : ℝ) := hratio
    _ ≤ A.D * (2 : ℝ) ^ (-(l : ℤ)) := hscaled

/-- The family mass bound required by `lm:finiteBounds`, with the approved
constant `E₀=\overline D 2^{-l}` and the exact increment index set. -/
theorem mszFiniteGridIncrementMass_le_E0
    (A : AdmissibleData) (K l : ℕ) :
    ∀ i ∈ mszFiniteGridIncrementIndices K l,
      integerKernelL1Mass
        (integerKernelDifference
          (mszAdmissibleIntegerKernel A (mszFiniteGridIncrementRightTime l i))
          (mszAdmissibleIntegerKernel A (mszFiniteGridIncrementLeftTime l i))) ≤
        max 1 A.D * (2 : ℝ) ^ (-(l : ℤ)) := by
  let E := mszFiniteGridIncrementIndices K l
  let κ := mszAdmissibleIntegerKernel A
  let left := mszFiniteGridIncrementLeftTime l
  let right := mszFiniteGridIncrementRightTime l
  have hmass : ∀ i ∈ E,
      integerKernelL1Mass (integerKernelDifference (κ (right i)) (κ (left i))) ≤
        A.D * (2 : ℝ) ^ (-(l : ℤ)) := by
    intro i hi
    simpa [κ, left, right, mszAdmissibleIntegerKernel,
      mszFiniteGridIncrementLeftTime, mszFiniteGridIncrementRightTime,
      mszGridIncrementKernel] using
        mszGridIncrementKernel_mass_le_D A i.1 l i.2.val
  have hE0 := finiteIncrementKernelMass_le_E0 E A.D A.D_nonneg l
    κ left right hmass
  intro i hi
  simpa [E, κ, left, right] using hE0 i hi

end FractionalPrimes.Literature.MSZ

end
