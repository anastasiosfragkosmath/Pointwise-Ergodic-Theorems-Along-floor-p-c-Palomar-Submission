module

public import FractionalPrimes.Literature.MSZ.LocalizedGridFiniteShortVariation
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open scoped BigOperators ENNReal

noncomputable section

/-! The pointwise aggregate chaining inequality used at the end of the finite
short-variation argument. First apply normalized-grid chaining in each
dyadic block, then use Minkowski in the finite scale coordinate. -/

/-- The level-l finite square function from lm:finiteVariation. -/
noncomputable def mszFiniteVariationLevelSquareFunction
    (A : AdmissibleData) (K l : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℝ :=
  Real.sqrt (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
    ∑ m ∈ Finset.range (2 ^ l),
      ‖mszGridIncrement A.kernel k l m f x‖ ^ 2)

private theorem mszFiniteShortBlockValues_levelPoint
    (A : AdmissibleData) (k : ℤ) (L l m : ℕ) (f : ℤ → ℂ) (x : ℤ)
    (hl : l ≤ L) (hm : m < 2 ^ l) :
    mszFiniteShortBlockValues A k L f x (dyadicGridLevelPoint L l m) =
      mszKernelAverage (A.kernel (mszGridTime k l m)) f x := by
  have htime : mszGridTimeAffine k L
      ⟨(m : ℚ) / (2 ^ l : ℚ), dyadicGridTimes_levelPoint_mem hl hm⟩ =
        mszGridTime k l m := by
    apply Subtype.ext
    rw [mszGridTimeAffine_val, mszGridTime_eq_affine_dyadicGridPoint]
    rfl
  rw [mszFiniteShortBlockValues, dyadicGridLevelPoint_valid hl hm, htime]

private theorem mszFiniteShortBlockValues_levelSuccessorPoint
    (A : AdmissibleData) (k : ℤ) (L l m : ℕ) (f : ℤ → ℂ) (x : ℤ)
    (hl : l ≤ L) (hm : m < 2 ^ l) :
    mszFiniteShortBlockValues A k L f x
        (dyadicGridLevelSuccessorPoint L l m) =
      mszKernelAverage (A.kernel (mszGridTime k l (m + 1))) f x := by
  have htime : mszGridTimeAffine k L
      ⟨((m + 1 : ℕ) : ℚ) / (2 ^ l : ℚ),
        dyadicGridTimes_levelSuccessor_mem hl hm⟩ =
        mszGridTime k l (m + 1) := by
    apply Subtype.ext
    rw [mszGridTimeAffine_val, mszGridTime_eq_affine_dyadicGridPoint]
    rfl
  rw [mszFiniteShortBlockValues,
    dyadicGridLevelSuccessorPoint_valid hl hm, htime]

/-- In one dyadic block, the real variation is bounded by its levelwise
square increments, with the exact sqrt 2 constant from finite-grid chaining. -/
theorem mszFiniteShortBlockVariation_toReal_le_levelSum
    (A : AdmissibleData) (k : ℤ) (L : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    (mszFiniteShortBlockVariation A k L f x).toReal ≤
      Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
        Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
          ‖mszGridIncrement A.kernel k l m f x‖ ^ 2) := by
  let g := mszFiniteShortBlockValues A k L f x
  have hchain := dyadicGridVariationTwoSubtype_le L g
  have hsum :
      (∑ l ∈ Finset.range (L + 1),
        Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
          ‖mszFiniteShortBlockValues A k L f x
              (dyadicGridLevelSuccessorPoint L l m) -
            mszFiniteShortBlockValues A k L f x
              (dyadicGridLevelPoint L l m)‖ ^ 2)) =
      ∑ l ∈ Finset.range (L + 1),
        Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
          ‖mszGridIncrement A.kernel k l m f x‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro l hl
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    have hlL : l ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hmPow : m < 2 ^ l := Finset.mem_range.mp hm
    rw [mszFiniteShortBlockValues_levelSuccessorPoint A k L l m f x hlL hmPow,
      mszFiniteShortBlockValues_levelPoint A k L l m f x hlL hmPow,
      mszGridIncrement]
    simp only [Pi.sub_apply]
  have hchain' :
      mszFiniteShortBlockVariation A k L f x ≤
        ENNReal.ofReal (Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
          Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
            ‖mszGridIncrement A.kernel k l m f x‖ ^ 2)) := by
    simpa only [mszFiniteShortBlockVariation, g, hsum] using hchain
  have hsumNonneg : 0 ≤ ∑ l ∈ Finset.range (L + 1),
      Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
        ‖mszGridIncrement A.kernel k l m f x‖ ^ 2) :=
    Finset.sum_nonneg fun l hl => Real.sqrt_nonneg _
  have hcoeffNonneg : 0 ≤ Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
      Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
        ‖mszGridIncrement A.kernel k l m f x‖ ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) hsumNonneg
  have hreal :=
    (ENNReal.toReal_le_toReal
      (mszFiniteShortBlockVariation_ne_top A k L f x)
      ENNReal.ofReal_ne_top).mpr hchain'
  simpa only [ENNReal.toReal_ofReal hcoeffNonneg] using hreal

/-- The source finite short variation is pointwise bounded by the sum of its
level square functions. This is the aggregate finite-k Minkowski step in
lm:finiteVariation, before taking the spatial lp norm. -/
theorem mszFiniteShortVariation_le_sqrtTwo_sumLevelSquareFunctions
    (A : AdmissibleData) (K L : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    mszFiniteShortVariation A K L f x ≤
      Real.sqrt 2 * ∑ l ∈ Finset.range (L + 1),
        mszFiniteVariationLevelSquareFunction A K l f x := by
  classical
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let ι := {k : ℤ // k ∈ s}
  let levels : Finset ℕ := Finset.range (L + 1)
  let b : ι → ℝ := fun k => (mszFiniteShortBlockVariation A k.1 L f x).toReal
  let c : ℕ → ι → ℝ := fun l k =>
    Real.sqrt (∑ m ∈ Finset.range (2 ^ l),
      ‖mszGridIncrement A.kernel k.1 l m f x‖ ^ 2)
  let d : ι → ℝ := fun k => Real.sqrt 2 * ∑ l ∈ levels, c l k
  have hb_nonneg (k : ι) : 0 ≤ b k := ENNReal.toReal_nonneg
  have hc_nonneg (l : ℕ) (k : ι) : 0 ≤ c l k := Real.sqrt_nonneg _
  have hd_nonneg (k : ι) : 0 ≤ d k := by
    dsimp [d]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (Finset.sum_nonneg fun l hl => hc_nonneg l k)
  have hbd (k : ι) : b k ≤ d k := by
    dsimp [b, d, c, levels]
    exact mszFiniteShortBlockVariation_toReal_le_levelSum A k.1 L f x
  have hsq : (∑ k : ι, b k ^ 2) ≤ ∑ k : ι, d k ^ 2 := by
    apply Finset.sum_le_sum
    intro k hk
    nlinarith [hb_nonneg k, hd_nonneg k, hbd k]
  have hleftSum :
      (∑ k ∈ s, (mszFiniteShortBlockVariation A k L f x).toReal ^ 2) =
        ∑ k : ι, b k ^ 2 := by
    symm
    exact Finset.sum_coe_sort s
      (fun k : ℤ => (mszFiniteShortBlockVariation A k L f x).toReal ^ 2)
  have hlevelSquare (l : ℕ) :
      mszFiniteVariationLevelSquareFunction A K l f x =
        Real.sqrt (∑ k : ι, c l k ^ 2) := by
    dsimp [mszFiniteVariationLevelSquareFunction, c, s, ι]
    congr 1
    calc
      (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ∑ m ∈ Finset.range (2 ^ l),
            ‖mszGridIncrement A.kernel k l m f x‖ ^ 2) =
        ∑ k : {k : ℤ // k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)},
          ∑ m ∈ Finset.range (2 ^ l),
            ‖mszGridIncrement A.kernel k.1 l m f x‖ ^ 2 := by
          symm
          exact Finset.sum_coe_sort (Finset.Icc (-(K : ℤ)) (K : ℤ))
            (fun k : ℤ => ∑ m ∈ Finset.range (2 ^ l),
              ‖mszGridIncrement A.kernel k l m f x‖ ^ 2)
      _ = ∑ k : ι, c l k ^ 2 := by
          apply Finset.sum_congr rfl
          intro k hk
          dsimp [c]
          rw [Real.sq_sqrt]
          exact Finset.sum_nonneg fun m hm => sq_nonneg _
  let V : ℕ → PiLp 2 (fun _ : ι => ℝ) := fun l =>
    WithLp.toLp 2 (c l)
  have hVnorm (l : ℕ) :
      ‖V l‖ = mszFiniteVariationLevelSquareFunction A K l f x := by
    rw [hlevelSquare]
    simp [V, PiLp.norm_eq_of_L2, Real.norm_eq_abs,
      abs_of_nonneg (hc_nonneg l _)]
  have htriangle : ‖∑ l ∈ levels, V l‖ ≤ ∑ l ∈ levels, ‖V l‖ :=
    norm_sum_le _ _
  have hdNorm :
      Real.sqrt (∑ k : ι, d k ^ 2) =
        Real.sqrt 2 * ‖∑ l ∈ levels, V l‖ := by
    calc
      Real.sqrt (∑ k : ι, d k ^ 2) = ‖WithLp.toLp 2 d‖ := by
        simp [PiLp.norm_eq_of_L2, Real.norm_eq_abs,
          abs_of_nonneg (hd_nonneg _)]
      _ = ‖Real.sqrt 2 • ∑ l ∈ levels, V l‖ := by
        congr 1
        ext k
        simp [d, V, Finset.sum_apply]
      _ = Real.sqrt 2 * ‖∑ l ∈ levels, V l‖ := by
        rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hMinkowski :
      Real.sqrt (∑ k : ι, d k ^ 2) ≤
        Real.sqrt 2 * ∑ l ∈ levels,
          mszFiniteVariationLevelSquareFunction A K l f x := by
    rw [hdNorm]
    exact mul_le_mul_of_nonneg_left
      (calc
        ‖∑ l ∈ levels, V l‖ ≤ ∑ l ∈ levels, ‖V l‖ := htriangle
        _ = ∑ l ∈ levels, mszFiniteVariationLevelSquareFunction A K l f x := by
          apply Finset.sum_congr rfl
          intro l hl
          exact hVnorm l)
      (Real.sqrt_nonneg _)
  change Real.sqrt (∑ k ∈ s,
    (mszFiniteShortBlockVariation A k L f x).toReal ^ 2) ≤ _
  rw [hleftSum]
  exact (Real.sqrt_le_sqrt hsq).trans hMinkowski

end

end FractionalPrimes.Literature.MSZ

end

