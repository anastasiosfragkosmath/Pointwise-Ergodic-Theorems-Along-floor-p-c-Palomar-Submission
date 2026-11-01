module

public import FractionalPrimes.Literature.MSZ.FiniteGridMaximalData
public import FractionalPrimes.Literature.MSZ.VectorConvolutionLower

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open scoped ENNReal NNReal

noncomputable section

/-- The raw finite-grid positive majorant is exactly the finite maximum of
the same increment convolutions over the subtype index used by localized
interpolation. -/
theorem mszFiniteGridIncrementPositiveMajorant_eq_positiveConvolutionMax
    (A : AdmissibleData) (K L l : ℕ)
    (h : lp (fun _ : ℤ => ℝ) (mszQExponent A))
    (hh : ∀ x, 0 ≤ h x) :
    mszFiniteGridIncrementPositiveMajorant A K L l h =
      integerKernelPositiveConvolutionMax
        (fun i : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)} × Fin (2 ^ l) =>
          mszGridIncrementKernel A.kernel i.1.1 l i.2.val) h hh := by
  classical
  funext x
  let I : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let E := mszFiniteGridIncrementIndices K l
  have hE : E.Nonempty := mszFiniteGridIncrementIndices_nonempty K l
  let ι : Type := {k : ℤ // k ∈ I} × Fin (2 ^ l)
  let ιRaw : Type := {e : ℤ × Fin (2 ^ l) // e ∈ E}
  let idx : ι ≃ ιRaw :=
    { toFun := fun i =>
        ⟨(i.1.1, i.2), by
          simpa [E, mszFiniteGridIncrementIndices, I] using
            (Finset.mk_mem_product i.1.2 (Finset.mem_univ i.2))⟩
      invFun := fun e =>
        (⟨e.1.1, by
            have he : e.1 ∈ I.product Finset.univ := by
              simpa [E, mszFiniteGridIncrementIndices, I] using e.2
            exact (Finset.mem_product.mp he).1⟩,
          e.1.2)
      left_inv := by
        rintro ⟨⟨k, hk⟩, m⟩
        rfl
      right_inv := by
        rintro ⟨⟨k, m⟩, he⟩
        rfl }
  let f : ℤ × Fin (2 ^ l) → ℝ := fun e =>
    integerKernelPositiveConvolution
      (integerKernelDifference
        (mszAdmissibleIntegerKernel A (mszFiniteGridIncrementRightTime l e))
        (mszAdmissibleIntegerKernel A (mszFiniteGridIncrementLeftTime l e))) h x
  let c : ι → ℝ≥0 := fun i =>
    ⟨integerKernelPositiveConvolution
        (mszGridIncrementKernel A.kernel i.1.1 l i.2.val) h x,
      integerKernelPositiveConvolution_nonneg
        (K := mszGridIncrementKernel A.kernel i.1.1 l i.2.val)
        (h := h) hh x⟩
  change E.sup' hE f = ↑(Finset.univ.sup c)
  have hval (i : ι) : f (idx i).1 = (c i : ℝ) := by
    rcases i with ⟨⟨k, hk⟩, m⟩
    simp [f, c, idx, mszFiniteGridIncrementRightTime,
      mszFiniteGridIncrementLeftTime, mszAdmissibleIntegerKernel,
      mszGridIncrementKernel]
    rfl
  have hmajorant_nonneg : 0 ≤ E.sup' hE f := by
    change 0 ≤ mszFiniteGridIncrementPositiveMajorant A K L l h x
    simpa [mszFiniteGridIncrementPositiveMajorant, f, E] using
      (finiteIncrementKernelPositiveMajorant_nonneg
        (mszFiniteGridIncrementIndices K l)
        (mszFiniteGridIncrementIndices_nonempty K l)
        (mszAdmissibleIntegerKernel A)
        (mszFiniteGridIncrementLeftTime l)
        (mszFiniteGridIncrementRightTime l) h hh x)
  have hmajorant_le : E.sup' hE f ≤ ↑(Finset.univ.sup c) := by
    apply Finset.sup'_le
    intro e he
    let i : ι := idx.symm ⟨e, he⟩
    have hidx : idx i = ⟨e, he⟩ := by
      dsimp [i]
      exact Equiv.apply_symm_apply idx ⟨e, he⟩
    have hterm : f e = (c i : ℝ) := by
      simpa only [hidx] using hval i
    rw [hterm]
    exact_mod_cast Finset.le_sup (Finset.mem_univ i)
  have hmax_le : ↑(Finset.univ.sup c) ≤ E.sup' hE f := by
    have hsup : Finset.univ.sup c ≤
        (⟨E.sup' hE f, hmajorant_nonneg⟩ : ℝ≥0) := by
      apply Finset.sup_le_iff.mpr
      intro i _
      have hraw : f (idx i).1 ≤ E.sup' hE f :=
        Finset.le_sup' (s := E) (f := f) (idx i).2
      have hraw' : (c i : ℝ) ≤ E.sup' hE f := by
        rw [← hval i]
        exact hraw
      exact_mod_cast hraw'
    calc
      ↑(Finset.univ.sup c) ≤
          ↑(⟨E.sup' hE f, hmajorant_nonneg⟩ : ℝ≥0) := NNReal.coe_mono hsup
      _ = E.sup' hE f := rfl
  exact le_antisymm hmajorant_le hmax_le

end

end FractionalPrimes.Literature.MSZ

end
