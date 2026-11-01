module

public import FractionalPrimes.Literature.Uniformity.VariationAbelMultiplier

/-!
# Selecting a residue prefix by variation

This file formalizes blueprint lemma `lhg:residue-prefix`.  A residue prefix
stores both the full residue slice and its chosen initial segment, so its exact
spacing is visible to downstream lattice-progression arguments.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Hyperbola

open FractionalPrimes.Literature.Uniformity

noncomputable section

/-- An initial segment of one residue class in a finite integer interval.
The full class and the prefix both use the exact positive step `q`. -/
structure ResiduePrefixData (I : FiniteIntegerInterval) (q : ℕ)
    (hq : 0 < q) where
  residue : ℕ
  residue_lt : residue < q
  start : ℤ
  fullLength : ℕ
  prefixLength : ℕ
  prefix_le_full : prefixLength ≤ fullLength
  full_class :
    arithmeticProgressionPoints start q hq fullLength =
      (I.points.filter fun n => n ≡ (residue : ℤ) [ZMOD (q : ℤ)])

/-- The selected prefix itself. -/
def ResiduePrefixData.points {I : FiniteIntegerInterval} {q : ℕ}
    {hq : 0 < q} (P : ResiduePrefixData I q hq) : Finset ℤ :=
  arithmeticProgressionPoints P.start q hq P.prefixLength

private theorem arithmeticProgressionPoints_mono_length
    (a : ℤ) (d : ℕ) (hd : 0 < d) {K L : ℕ} (hKL : K ≤ L) :
    arithmeticProgressionPoints a d hd K ⊆
      arithmeticProgressionPoints a d hd L := by
  intro x hx
  simp only [arithmeticProgressionPoints, Finset.mem_image,
    Finset.mem_range] at hx ⊢
  rcases hx with ⟨j, hj, rfl⟩
  exact ⟨j, lt_of_lt_of_le hj hKL, rfl⟩

/-- Every stored residue prefix is contained in its ambient interval. -/
theorem ResiduePrefixData.points_subset {I : FiniteIntegerInterval} {q : ℕ}
    {hq : 0 < q} (P : ResiduePrefixData I q hq) : P.points ⊆ I.points := by
  have hprefix : P.points ⊆
      arithmeticProgressionPoints P.start q hq P.fullLength := by
    exact arithmeticProgressionPoints_mono_length P.start q hq P.prefix_le_full
  intro n hn
  have hnfull := hprefix hn
  rw [P.full_class] at hnfull
  exact (Finset.mem_filter.mp hnfull).1

/-- The exact residue-prefix selection lemma `lhg:residue-prefix`.

The first conclusion is unconditional and permits the empty prefix.  The last
conclusion says that whenever the weighted sum is positive and the variation
is at most `B > 0`, this same selected prefix is nonempty and its unweighted
sum has norm at least the weighted norm divided by `B`. -/
theorem selectResiduePrefix
    (I : FiniteIntegerInterval)
    (b F : {n : ℤ // n ∈ I.points} → ℂ)
    (q : ℕ) (hq : 0 < q) :
    ∃ P : ResiduePrefixData I q hq,
      P.points ⊆ I.points ∧
      ‖∑ n ∈ I.points,
          extendByZero I.points b n * extendByZero I.points F n‖ ≤
        finiteResidueClassVariation I (extendByZero I.points b) q *
          ‖∑ n ∈ P.points, extendByZero I.points F n‖ ∧
      ∀ B : ℝ, 0 < B →
        0 < ‖∑ n ∈ I.points,
          extendByZero I.points b n * extendByZero I.points F n‖ →
        finiteResidueClassVariation I (extendByZero I.points b) q ≤ B →
          P.points.Nonempty ∧
            ‖∑ n ∈ I.points,
                extendByZero I.points b n * extendByZero I.points F n‖ / B ≤
              ‖∑ n ∈ P.points, extendByZero I.points F n‖ := by
  classical
  let b' : ℤ → ℂ := extendByZero I.points b
  let F' : ℤ → ℂ := extendByZero I.points F
  have hexact (r : ℕ) : ∃ a : ℤ, ∃ L : ℕ,
      arithmeticProgressionPoints a q hq L =
        (I.points.filter fun n => n ≡ (r : ℤ) [ZMOD (q : ℤ)]) :=
    finiteInterval_residueFilter_eq_arithmeticProgressionPoints I (r : ℤ) q hq
  let start : ℕ → ℤ := fun r => Classical.choose (hexact r)
  let fullLength : ℕ → ℕ := fun r =>
    Classical.choose (Classical.choose_spec (hexact r))
  have hfull (r : ℕ) :
      arithmeticProgressionPoints (start r) q hq (fullLength r) =
        (I.points.filter fun n => n ≡ (r : ℤ) [ZMOD (q : ℤ)]) := by
    exact Classical.choose_spec (Classical.choose_spec (hexact r))
  have hprefixExists (r : ℕ) : ∃ K : ℕ, K ≤ fullLength r ∧
      ‖∑ n ∈ arithmeticProgressionPoints (start r) q hq (fullLength r),
          b' n * F' n‖ ≤
        finiteOrderedTotalVariation
            (arithmeticProgressionPoints (start r) q hq (fullLength r)) b' *
          ‖∑ n ∈ arithmeticProgressionPoints (start r) q hq K, F' n‖ :=
    exists_arithmeticProgressionPrefix_sum_mul_bound
      (start r) q hq (fullLength r) F' b'
  let prefixLength : ℕ → ℕ := fun r => Classical.choose (hprefixExists r)
  have hprefixLe (r : ℕ) : prefixLength r ≤ fullLength r :=
    (Classical.choose_spec (hprefixExists r)).1
  have hprefixBound (r : ℕ) :
      ‖∑ n ∈ arithmeticProgressionPoints (start r) q hq (fullLength r),
          b' n * F' n‖ ≤
        finiteOrderedTotalVariation
            (arithmeticProgressionPoints (start r) q hq (fullLength r)) b' *
          ‖∑ n ∈ arithmeticProgressionPoints (start r) q hq (prefixLength r),
            F' n‖ :=
    (Classical.choose_spec (hprefixExists r)).2
  let value : ℕ → ℝ := fun r =>
    ‖∑ n ∈ arithmeticProgressionPoints (start r) q hq (prefixLength r), F' n‖
  have hresidues : (Finset.range q).Nonempty :=
    ⟨0, Finset.mem_range.mpr hq⟩
  obtain ⟨r₀, hr₀, hmax⟩ :=
    Finset.exists_mem_eq_sup' hresidues value
  have hmaximal (r : ℕ) (hr : r ∈ Finset.range q) : value r ≤ value r₀ := by
    rw [← hmax]
    exact Finset.le_sup' value hr
  let P : ResiduePrefixData I q hq :=
    { residue := r₀
      residue_lt := Finset.mem_range.mp hr₀
      start := start r₀
      fullLength := fullLength r₀
      prefixLength := prefixLength r₀
      prefix_le_full := hprefixLe r₀
      full_class := hfull r₀ }
  have hlocal (r : ℕ) (hr : r ∈ Finset.range q) :
      ‖∑ n ∈ I.points.filter
            (fun n => n ≡ (r : ℤ) [ZMOD (q : ℤ)]), b' n * F' n‖ ≤
        finiteOrderedTotalVariation
            (I.points.filter fun n => n ≡ (r : ℤ) [ZMOD (q : ℤ)]) b' *
          value r₀ := by
    calc
      ‖∑ n ∈ I.points.filter
            (fun n => n ≡ (r : ℤ) [ZMOD (q : ℤ)]), b' n * F' n‖ =
          ‖∑ n ∈ arithmeticProgressionPoints (start r) q hq (fullLength r),
            b' n * F' n‖ := by rw [hfull r]
      _ ≤ finiteOrderedTotalVariation
            (arithmeticProgressionPoints (start r) q hq (fullLength r)) b' *
          ‖∑ n ∈ arithmeticProgressionPoints (start r) q hq (prefixLength r),
            F' n‖ := hprefixBound r
      _ = finiteOrderedTotalVariation
            (I.points.filter fun n => n ≡ (r : ℤ) [ZMOD (q : ℤ)]) b' *
          value r := by rw [hfull r]
      _ ≤ finiteOrderedTotalVariation
            (I.points.filter fun n => n ≡ (r : ℤ) [ZMOD (q : ℤ)]) b' *
          value r₀ :=
        mul_le_mul_of_nonneg_left (hmaximal r hr)
          (finiteOrderedTotalVariation_nonneg _ _)
  have hsplit := sum_eq_sum_residue_filters I.points q hq
    (fun n => b' n * F' n)
  have hbase :
      ‖∑ n ∈ I.points, b' n * F' n‖ ≤
        finiteResidueClassVariation I b' q *
          ‖∑ n ∈ P.points, F' n‖ := by
    calc
      ‖∑ n ∈ I.points, b' n * F' n‖ =
          ‖∑ r ∈ Finset.range q,
            ∑ n ∈ I.points.filter
              (fun n => n ≡ (r : ℤ) [ZMOD (q : ℤ)]), b' n * F' n‖ :=
        congrArg norm hsplit
      _ ≤ ∑ r ∈ Finset.range q,
          ‖∑ n ∈ I.points.filter
            (fun n => n ≡ (r : ℤ) [ZMOD (q : ℤ)]), b' n * F' n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ r ∈ Finset.range q,
          finiteOrderedTotalVariation
              (I.points.filter fun n => n ≡ (r : ℤ) [ZMOD (q : ℤ)]) b' *
            value r₀ := Finset.sum_le_sum fun r hr => hlocal r hr
      _ = finiteResidueClassVariation I b' q * value r₀ := by
        rw [finiteResidueClassVariation, Finset.sum_mul]
      _ = finiteResidueClassVariation I b' q *
          ‖∑ n ∈ P.points, F' n‖ := by
        rfl
  refine ⟨P, P.points_subset, ?_, ?_⟩
  · simpa [b', F'] using hbase
  · intro B hB hpositive hvariation
    have hbase' :
        ‖∑ n ∈ I.points,
            extendByZero I.points b n * extendByZero I.points F n‖ ≤
          finiteResidueClassVariation I (extendByZero I.points b) q *
            ‖∑ n ∈ P.points, extendByZero I.points F n‖ := by
      simpa [b', F'] using hbase
    have hBproduct :
        ‖∑ n ∈ I.points,
            extendByZero I.points b n * extendByZero I.points F n‖ ≤
          B * ‖∑ n ∈ P.points, extendByZero I.points F n‖ :=
      hbase'.trans
        (mul_le_mul_of_nonneg_right hvariation (norm_nonneg _))
    have hlower :
        ‖∑ n ∈ I.points,
            extendByZero I.points b n * extendByZero I.points F n‖ / B ≤
          ‖∑ n ∈ P.points, extendByZero I.points F n‖ :=
      (div_le_iff₀ hB).2 (by simpa [mul_comm] using hBproduct)
    have hprefixPositive :
        0 < ‖∑ n ∈ P.points, extendByZero I.points F n‖ := by
      by_contra hnot
      have hzero : ‖∑ n ∈ P.points, extendByZero I.points F n‖ = 0 :=
        le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
      rw [hzero, mul_zero] at hBproduct
      exact (not_lt_of_ge hBproduct) hpositive
    have hnonempty : P.points.Nonempty := by
      by_contra hempty
      have hpoints : P.points = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      simp [hpoints] at hprefixPositive
    exact ⟨hnonempty, hlower⟩

end

end FractionalPrimes.Literature.Hyperbola

#print axioms FractionalPrimes.Literature.Hyperbola.selectResiduePrefix
