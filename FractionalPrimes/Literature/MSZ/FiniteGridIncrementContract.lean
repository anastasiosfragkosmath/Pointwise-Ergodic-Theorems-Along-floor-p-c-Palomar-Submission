module

public import FractionalPrimes.Literature.MSZ.FiniteGridMaximalData

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open scoped ENNReal

/-! The finite-grid kernel contract for the positive majorant in `lm:finiteBounds`. -/

/-- Every increment kernel in the approved finite family is pointwise
dominated, after positive convolution against a nonnegative input, by the
finite-family positive majorant. -/
theorem mszFiniteGridIncrementPositiveConvolution_le_majorant
    (A : AdmissibleData) (K L l : ℕ)
    (h : lp (fun _ : ℤ => ℝ) (mszQExponent A))
    (_hh : ∀ x, 0 ≤ h x)
    (i : ℤ × Fin (2 ^ l))
    (hi : i ∈ mszFiniteGridIncrementIndices K l) (x : ℤ) :
    integerKernelPositiveConvolution
        (mszGridIncrementKernel A.kernel i.1 l i.2.val) h x ≤
      mszFiniteGridIncrementPositiveMajorant A K L l h x := by
  change integerKernelPositiveConvolution
      (integerKernelDifference
        (mszAdmissibleIntegerKernel A (mszFiniteGridIncrementRightTime l i))
        (mszAdmissibleIntegerKernel A (mszFiniteGridIncrementLeftTime l i))) h x ≤
    finiteIncrementKernelPositiveMajorant
      (mszFiniteGridIncrementIndices K l)
      (mszFiniteGridIncrementIndices_nonempty K l)
      (mszAdmissibleIntegerKernel A)
      (mszFiniteGridIncrementLeftTime l)
      (mszFiniteGridIncrementRightTime l) h x
  exact Finset.le_sup' (s := mszFiniteGridIncrementIndices K l)
    (f := fun j => integerKernelPositiveConvolution
      (integerKernelDifference
        (mszAdmissibleIntegerKernel A (mszFiniteGridIncrementRightTime l j))
        (mszAdmissibleIntegerKernel A (mszFiniteGridIncrementLeftTime l j))) h x) hi

end FractionalPrimes.Literature.MSZ

end
