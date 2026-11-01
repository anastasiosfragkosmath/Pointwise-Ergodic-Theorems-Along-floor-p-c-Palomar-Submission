module

public import FractionalPrimes.Literature.MSZ.FiniteGridIncrementMassBound

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open scoped ENNReal

/-! Assembly of the approved `lm:finiteBounds` statement from the
finite-grid maximal, endpoint, positive-majorant, and increment-mass clauses. -/

/-- The approved finite-grid bounds: the unit-ball maximal norm is finite,
and every level-`l` increment family with `l ≤ L` has the exact kernel-mass
and positive-maximal-majorant bounds required by `lm:vectorLower`. -/
theorem mszFiniteGridBounds (A : AdmissibleData) (K L : ℕ) :
    mszFiniteGridMaximalNorm A K L ≤
        ENNReal.ofReal
          (((mszFiniteTimeGrid K L).card : ℝ) ^ (1 / A.q)) ∧
    mszFiniteGridMaximalNorm A K L ≠ ∞ ∧
    ∀ l, l ≤ L →
      (∀ i ∈ mszFiniteGridIncrementIndices K l,
        integerKernelL1Mass (mszGridIncrementKernel A.kernel i.1 l i.2.val) ≤
          max 1 A.D * (2 : ℝ) ^ (-(l : ℤ))) ∧
      ∀ h : lp (fun _ : ℤ => ℝ) (mszQExponent A),
        (∀ x, 0 ≤ h x) →
        (∀ i ∈ mszFiniteGridIncrementIndices K l, ∀ x,
          integerKernelPositiveConvolution
              (mszGridIncrementKernel A.kernel i.1 l i.2.val) h x ≤
            mszFiniteGridIncrementPositiveMajorant A K L l h x) ∧
        ∃ G : lp (fun _ : ℤ => ℝ) (mszQExponent A),
          (∀ x, G x = mszFiniteGridIncrementPositiveMajorant A K L l h x) ∧
          ‖G‖ ≤ 2 * mszFiniteGridMaximalConstant A K L * ‖h‖ := by
  refine ⟨mszFiniteGridMaximalNorm_le A K L,
    mszFiniteGridMaximalNorm_ne_top A K L, ?_⟩
  intro l hl
  refine ⟨?_, ?_⟩
  · intro i hi
    exact mszFiniteGridIncrementMass_le_E0 A K l i hi
  · intro h hh
    refine ⟨?_, ?_⟩
    · intro i hi x
      exact mszFiniteGridIncrementPositiveConvolution_le_majorant
        A K L l h hh i hi x
    · exact mszFiniteGridIncrementPositiveMajorant_exists
        A K L l hl h hh

end FractionalPrimes.Literature.MSZ

end
