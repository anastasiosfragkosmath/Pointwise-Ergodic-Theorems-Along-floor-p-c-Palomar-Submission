module

public import FractionalPrimes.Literature.MSZ.DyadicChaining
public import FractionalPrimes.Literature.MSZ.AdmissibleData

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open scoped BigOperators ENNReal

noncomputable section

/-! The source finite short variation is the finite `ℓ²` sum over dyadic
blocks of their normalized-grid `2`-variations.  This file identifies the
normalized grid with the exact MSZ time parameter and defines that observable.
-/

/-- Exact time identification for a depth-`L` grid point:
`mszGridTime k L m = 2^k (1 + m 2^{-L})`. -/
theorem mszGridTime_eq_affine_dyadicGridPoint (k : ℤ) (L m : ℕ) :
    (mszGridTime k L m).val =
      (2 : ℚ) ^ k * (1 + dyadicGridPoint L m) := by
  rw [mszGridTime_val]
  have hpow :
      ((2 ^ L : ℕ) : ℚ) * (2 : ℚ) ^ (k - (L : ℤ)) = (2 : ℚ) ^ k := by
    calc
      _ = (2 : ℚ) ^ (L : ℤ) * (2 : ℚ) ^ (k - (L : ℤ)) := by
        rw [Nat.cast_pow, zpow_natCast]
        norm_num
      _ = (2 : ℚ) ^ ((L : ℤ) + (k - (L : ℤ))) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      _ = (2 : ℚ) ^ k := by
        congr 1
        omega
  have hden : ((2 ^ L : ℕ) : ℚ) ≠ 0 := by positivity
  have hdenCast : ((2 ^ L : ℕ) : ℚ) = (2 : ℚ) ^ L := by norm_cast
  have hm :
      (m : ℚ) * (2 : ℚ) ^ (k - (L : ℤ)) =
        (2 : ℚ) ^ k * ((m : ℚ) / ((2 ^ L : ℕ) : ℚ)) := by
    rw [← hpow]
    field_simp
  unfold dyadicGridPoint
  calc
    ((2 ^ L + m : ℕ) : ℚ) * (2 : ℚ) ^ (k - (L : ℤ)) =
        ((2 ^ L : ℕ) : ℚ) * (2 : ℚ) ^ (k - (L : ℤ)) +
          (m : ℚ) * (2 : ℚ) ^ (k - (L : ℤ)) := by
            push_cast
            ring
    _ = (2 : ℚ) ^ k +
          (2 : ℚ) ^ k * ((m : ℚ) / ((2 ^ L : ℕ) : ℚ)) := by
            rw [hpow, hm]
    _ = (2 : ℚ) ^ k *
          (1 + (m : ℚ) / (2 : ℚ) ^ L) := by
            calc
              _ = (2 : ℚ) ^ k *
                  (1 + (m : ℚ) / ((2 ^ L : ℕ) : ℚ)) := by ring
              _ = (2 : ℚ) ^ k *
                  (1 + (m : ℚ) / (2 : ℚ) ^ L) := congrArg
                    (fun d : ℚ => (2 : ℚ) ^ k * (1 + (m : ℚ) / d)) hdenCast

/-- The canonical index witnessing that a subtype point belongs to the
normalized depth-`L` dyadic grid. -/
noncomputable def mszDyadicGridPointIndex (L : ℕ)
    (t : {t : ℚ // t ∈ dyadicGridTimes L}) : ℕ :=
  Classical.choose (show ∃ m, m ≤ 2 ^ L ∧ dyadicGridPoint L m = t.1 by
    simpa only [dyadicGridTimes, Set.mem_ofPred_eq] using t.2)

theorem mszDyadicGridPointIndex_spec (L : ℕ)
    (t : {t : ℚ // t ∈ dyadicGridTimes L}) :
    mszDyadicGridPointIndex L t ≤ 2 ^ L ∧
      dyadicGridPoint L (mszDyadicGridPointIndex L t) = t.1 :=
  Classical.choose_spec (show ∃ m, m ≤ 2 ^ L ∧ dyadicGridPoint L m = t.1 by
    simpa only [dyadicGridTimes, Set.mem_ofPred_eq] using t.2)

/-- The approved MSZ time corresponding to a normalized grid point under
the affine block map `t ↦ 2^k (1+t)`. -/
noncomputable def mszGridTimeAffine (k : ℤ) (L : ℕ)
    (t : {t : ℚ // t ∈ dyadicGridTimes L}) : MSZTime :=
  mszGridTime k L (mszDyadicGridPointIndex L t)

theorem mszGridTimeAffine_val (k : ℤ) (L : ℕ)
    (t : {t : ℚ // t ∈ dyadicGridTimes L}) :
    (mszGridTimeAffine k L t).val = (2 : ℚ) ^ k * (1 + t.1) := by
  rw [mszGridTimeAffine, mszGridTime_eq_affine_dyadicGridPoint]
  rw [(mszDyadicGridPointIndex_spec L t).2]

/-- On the canonical subtype representative of `m 2^{-L}`, the affine time
is exactly the original `mszGridTime k L m`. -/
theorem mszGridTimeAffine_eq_gridTime (k : ℤ) (L m : ℕ)
    (hm : m ≤ 2 ^ L) :
    mszGridTimeAffine k L
        ⟨dyadicGridPoint L m, ⟨m, hm, rfl⟩⟩ = mszGridTime k L m := by
  apply Subtype.ext
  rw [mszGridTimeAffine_val]
  exact (mszGridTime_eq_affine_dyadicGridPoint k L m).symm

/-- The MSZ averaging family restricted to the block
`2^k (1 + G_L)`, represented on its normalized subtype grid. -/
noncomputable def mszFiniteShortBlockValues
    (A : AdmissibleData) (k : ℤ) (L : ℕ) (f : ℤ → ℂ) (x : ℤ)
    (t : {t : ℚ // t ∈ dyadicGridTimes L}) : ℂ :=
  mszKernelAverage (A.kernel (mszGridTimeAffine k L t)) f x

@[simp] theorem mszFiniteShortBlockValues_gridPoint
    (A : AdmissibleData) (k : ℤ) (L m : ℕ) (f : ℤ → ℂ) (x : ℤ)
    (hm : m ≤ 2 ^ L) :
    mszFiniteShortBlockValues A k L f x
        ⟨dyadicGridPoint L m, ⟨m, hm, rfl⟩⟩ =
      mszKernelAverage (A.kernel (mszGridTime k L m)) f x := by
  rw [mszFiniteShortBlockValues, mszGridTimeAffine_eq_gridTime k L m hm]

/-- The exact homogeneous `2`-variation on one source block
`2^k (1 + G_L)`, using the established normalized-grid variation. -/
noncomputable def mszFiniteShortBlockVariation
    (A : AdmissibleData) (k : ℤ) (L : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  dyadicGridVariationTwoSubtype L (mszFiniteShortBlockValues A k L f x)

/-- The block variation is finite.  This justifies taking its `toReal` in the
source finite short-variation norm: the normalized grid chaining estimate
bounds it by an `ENNReal.ofReal` of a finite real sum. -/
theorem mszFiniteShortBlockVariation_ne_top
    (A : AdmissibleData) (k : ℤ) (L : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    mszFiniteShortBlockVariation A k L f x ≠ ⊤ := by
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  exact dyadicGridVariationTwoSubtype_le L
    (mszFiniteShortBlockValues A k L f x)

/-- The source finite short-variation observable: the finite `ℓ²` norm over
`-K ≤ k ≤ K` of the per-block `2`-variations. The block variations are stored
in `ℝ≥0∞`; the chaining bound above proves they are finite before their real
values enter this norm. -/
noncomputable def mszFiniteShortVariation
    (A : AdmissibleData) (K L : ℕ) (f : ℤ → ℂ) : ℤ → ℝ :=
  fun x => Real.sqrt
    (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (mszFiniteShortBlockVariation A k L f x).toReal ^ 2)

end

end FractionalPrimes.Literature.MSZ

end
