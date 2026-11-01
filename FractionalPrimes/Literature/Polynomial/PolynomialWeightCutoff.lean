module

public import FractionalPrimes.Literature.Uniformity.ArithmeticTypes
public import FractionalPrimes.Literature.Uniformity.FiniteVariationProduct
public import FractionalPrimes.Literature.Uniformity.TotalVariationCalculusPackage

/-!
# Interval cutoff for positive-integer residue variation

This file formalizes the exact interval-truncation estimate in blueprint
item `lpi:weight-cutoff`, using the inhomogeneous variation conventions of
`lu:ap-tv`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open scoped ENNReal

noncomputable section

/-- The indicator of a real interval, sampled on the integer line. -/
private noncomputable def intervalIndicator (J : Set ℝ) (n : ℤ) : ℂ := by
  classical
  exact if (n : ℝ) ∈ J then 1 else 0

/-- Multiply a positive-integer weight by the indicator of a real interval. -/
noncomputable def intervalWeightRestriction (J : Set ℝ)
    (b : ComplexPositiveIntegerFunction) : ComplexPositiveIntegerFunction := by
  classical
  exact fun n => if (n.1 : ℝ) ∈ J then b n else 0

private theorem listAdjacentVariation_cons (g : ℤ → ℂ) (a : ℤ)
    (l : List ℤ) :
    listAdjacentVariation g (a :: l) =
      (match l with
       | [] => 0
       | b :: _ => ‖g b - g a‖) + listAdjacentVariation g l := by
  cases l <;> simp [listAdjacentVariation, List.consecutivePairs,
    List.zip, List.tail]

private theorem list_foldl_max_le_iff (l : List ℝ) (b c : ℝ) :
    l.foldl max b ≤ c ↔ b ≤ c ∧ ∀ x ∈ l, x ≤ c := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
      simp [List.foldl_cons, ih, and_assoc, and_left_comm, and_comm]

private theorem listAdjacentVariation_intervalIndicator_eq_zero_of_outside
    (J : Set ℝ) :
    ∀ l : List ℤ, (∀ n ∈ l, (n : ℝ) ∉ J) →
      listAdjacentVariation (intervalIndicator J) l = 0 := by
  classical
  intro l
  induction l with
  | nil => intro _; simp [listAdjacentVariation]
  | cons a l ih =>
      intro hall
      have haOut := hall a (by simp)
      have htail : ∀ n ∈ l, (n : ℝ) ∉ J := by
        intro n hn
        exact hall n (by simp [hn])
      rw [listAdjacentVariation_cons]
      cases l with
      | nil => simp [listAdjacentVariation]
      | cons b bs =>
          have hbOut := hall b (by simp)
          simp [intervalIndicator, haOut, hbOut, ih htail]

/-- Along a sorted finite list, membership in an order-convex real set changes
at most twice.  If the first point is in the set, it changes at most once. -/
private theorem intervalIndicatorVariation_bounds
    (J : Set ℝ)
    (hJ : ∀ ⦃x y z : ℝ⦄, x ∈ J → y ∈ J → x ≤ z → z ≤ y → z ∈ J) :
    ∀ (a : ℤ) (l : List ℤ), List.Pairwise (· ≤ ·) (a :: l) →
      listAdjacentVariation (intervalIndicator J) (a :: l) ≤ 2 ∧
        ((a : ℝ) ∈ J →
          listAdjacentVariation (intervalIndicator J) (a :: l) ≤ 1) := by
  intro a l
  induction l generalizing a with
  | nil =>
      intro _
      constructor <;> simp [listAdjacentVariation, List.consecutivePairs,
        List.zip, List.tail]
  | cons b bs ih =>
      intro hsorted
      have hpair := List.pairwise_cons.mp hsorted
      have hab : a ≤ b := hpair.1 b (by simp)
      have htail := ih b hpair.2
      by_cases haJ : (a : ℝ) ∈ J
      · by_cases hbJ : (b : ℝ) ∈ J
        · have htailOne := htail.2 hbJ
          have hwhole :
              listAdjacentVariation (intervalIndicator J) (a :: b :: bs) =
                listAdjacentVariation (intervalIndicator J) (b :: bs) := by
            rw [listAdjacentVariation_cons]
            simp [intervalIndicator, haJ, hbJ]
          rw [hwhole]
          exact ⟨htailOne.trans (by norm_num), fun _ => htailOne⟩
        · have htailOutside : ∀ c ∈ b :: bs, (c : ℝ) ∉ J := by
            intro c hc hcJ
            rcases List.mem_cons.mp hc with rfl | hcbs
            · exact hbJ hcJ
            · have hbc : b ≤ c :=
                (List.pairwise_cons.mp hpair.2).1 c hcbs
              exact hbJ (hJ haJ hcJ (by exact_mod_cast hab) (by exact_mod_cast hbc))
          have htailZero :
              listAdjacentVariation (intervalIndicator J) (b :: bs) = 0 :=
            listAdjacentVariation_intervalIndicator_eq_zero_of_outside
              J (b :: bs) htailOutside
          have hwhole :
              listAdjacentVariation (intervalIndicator J) (a :: b :: bs) = 1 := by
            rw [listAdjacentVariation_cons]
            simp [intervalIndicator, haJ, hbJ, htailZero]
          rw [hwhole]
          exact ⟨by norm_num, fun _ => by norm_num⟩
      · by_cases hbJ : (b : ℝ) ∈ J
        · have htailOne := htail.2 hbJ
          have hwholeBound :
              listAdjacentVariation (intervalIndicator J) (a :: b :: bs) ≤ 2 := by
            rw [listAdjacentVariation_cons]
            simp [intervalIndicator, haJ, hbJ]
            linarith
          exact ⟨hwholeBound, fun h => by simp_all⟩
        · have hwholeBound :
              listAdjacentVariation (intervalIndicator J) (a :: b :: bs) ≤ 2 := by
            rw [listAdjacentVariation_cons]
            simp [intervalIndicator, haJ, hbJ]
            exact htail.1
          exact ⟨hwholeBound, fun h => by simp_all⟩

/-- The finite inhomogeneous variation of an interval indicator is at most
three: its supremum term is at most one, and its two boundary jumps account
for at most two more. -/
private theorem finiteOrderedTotalVariation_intervalIndicator_le_three
    (J : Set ℝ)
    (hJ : ∀ ⦃x y z : ℝ⦄, x ∈ J → y ∈ J → x ≤ z → z ≤ y → z ∈ J)
    (S : Finset ℤ) :
    finiteOrderedTotalVariation S (intervalIndicator J) ≤ 3 := by
  unfold finiteOrderedTotalVariation
  have hsup : listSupNorm (intervalIndicator J) (S.sort (· ≤ ·)) ≤ 1 := by
    unfold listSupNorm
    apply (list_foldl_max_le_iff _ _ _).2
    refine ⟨by norm_num, ?_⟩
    intro x hx
    rcases List.mem_map.mp hx with ⟨n, hn, rfl⟩
    change ‖intervalIndicator J n‖ ≤ 1
    by_cases hnJ : (n : ℝ) ∈ J <;> simp [intervalIndicator, hnJ]
  have hvar :
      listAdjacentVariation (intervalIndicator J) (S.sort (· ≤ ·)) ≤ 2 := by
    cases hsort : S.sort (· ≤ ·) with
    | nil => simp [hsort, listAdjacentVariation]
    | cons a l =>
        have hp : List.Pairwise (· ≤ ·) (a :: l) := by
          rw [← hsort]
          exact Finset.pairwise_sort S (· ≤ ·)
        simpa [hsort] using
          (intervalIndicatorVariation_bounds J hJ a l hp).1
  linarith

/-- Cutting off a finite sequence to an interval costs at most a factor three
in the exact inhomogeneous finite variation. -/
private theorem finiteOrderedTotalVariation_intervalWeight_le
    (J : Set ℝ)
    (hJ : ∀ ⦃x y z : ℝ⦄, x ∈ J → y ∈ J → x ≤ z → z ≤ y → z ∈ J)
    (S : Finset ℤ) (b : ℤ → ℂ) :
    finiteOrderedTotalVariation S
        (fun n => b n * intervalIndicator J n) ≤
      3 * finiteOrderedTotalVariation S b := by
  calc
    finiteOrderedTotalVariation S (fun n => b n * intervalIndicator J n) ≤
        finiteOrderedTotalVariation S b *
          finiteOrderedTotalVariation S (intervalIndicator J) :=
      finiteOrderedTotalVariation_mul_le S b (intervalIndicator J)
    _ ≤ finiteOrderedTotalVariation S b * 3 :=
      mul_le_mul_of_nonneg_left
        (finiteOrderedTotalVariation_intervalIndicator_le_three J hJ S)
        (finiteOrderedTotalVariation_nonneg S b)
    _ = 3 * finiteOrderedTotalVariation S b := by ring

/-- Restricting an interval-weighted sequence to one arbitrary ordered set
costs at most a factor three, including when either extended variation is
infinite. -/
private theorem orderedTotalVariation_intervalWeight_le
    (J : Set ℝ)
    (hJ : ∀ ⦃x y z : ℝ⦄, x ∈ J → y ∈ J → x ≤ z → z ≤ y → z ∈ J)
    (P : Set ℤ) (b : ℤ → ℂ) :
    orderedTotalVariation P (fun n => b n * intervalIndicator J n) ≤
      3 * orderedTotalVariation P b := by
  unfold orderedTotalVariation
  refine iSup_le fun F => ?_
  have hfinite := finiteOrderedTotalVariation_intervalWeight_le J hJ F.1 b
  have hbound :
      ENNReal.ofReal
          (finiteOrderedTotalVariation F.1
            (fun n => b n * intervalIndicator J n)) ≤
        (3 : ℝ≥0∞) *
          ENNReal.ofReal (finiteOrderedTotalVariation F.1 b) := by
    calc
      _ ≤ ENNReal.ofReal
          (3 * finiteOrderedTotalVariation F.1 b) :=
        ENNReal.ofReal_le_ofReal hfinite
      _ = (3 : ℝ≥0∞) *
          ENNReal.ofReal (finiteOrderedTotalVariation F.1 b) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
  calc
    ENNReal.ofReal
        (finiteOrderedTotalVariation F.1
          (fun n => b n * intervalIndicator J n)) ≤
      (3 : ℝ≥0∞) * ENNReal.ofReal
        (finiteOrderedTotalVariation F.1 b) := hbound
    _ ≤ (3 : ℝ≥0∞) *
        (⨆ G : {G : Finset ℤ // ∀ n ∈ G, n ∈ P},
          ENNReal.ofReal (finiteOrderedTotalVariation G.1 b)) :=
      mul_le_mul le_rfl (le_iSup_of_le F le_rfl) (by simp) (by simp)

/-- Zero extension commutes with multiplying by an interval indicator. -/
private theorem complexPositiveIntegerZeroExtension_intervalWeight
    (J : Set ℝ) (b : ComplexPositiveIntegerFunction) :
    complexPositiveIntegerZeroExtension (intervalWeightRestriction J b) =
      fun n => complexPositiveIntegerZeroExtension b n *
        intervalIndicator J n := by
  funext n
  by_cases hn : 0 < n
  · have hncast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hn.le)
    simp [complexPositiveIntegerZeroExtension, intervalWeightRestriction,
      intervalIndicator, hn]
    rw [hncast]
  · simp [complexPositiveIntegerZeroExtension, intervalWeightRestriction,
      intervalIndicator, hn]

/-- The approved `lpi:weight-cutoff` estimate: restricting a positive-integer
weight to any real interval multiplies its residue-class inhomogeneous
variation by at most three. The supremum convention in
`orderedTotalVariation` makes the statement valid for infinite variation as
well. -/
theorem intervalWeightVariation
    (J : Set ℝ)
    (hJ : ∀ ⦃x y z : ℝ⦄, x ∈ J → y ∈ J → x ≤ z → z ≤ y → z ∈ J)
    (b : ComplexPositiveIntegerFunction) (q : ℕ) (hq : 0 < q) :
    complexPositiveIntegerResidueVariation (intervalWeightRestriction J b) q hq ≤
      3 * complexPositiveIntegerResidueVariation b q hq := by
  rw [complexPositiveIntegerResidueVariation,
    complexPositiveIntegerResidueVariation]
  rw [complexPositiveIntegerZeroExtension_intervalWeight]
  unfold positiveIntegerResidueTotalVariation residueClassTotalVariation
  calc
    _ ≤ ∑ a ∈ Finset.range q,
        (3 : ℝ≥0∞) * orderedTotalVariation
          ({n : ℤ | 0 < n} ∩ integerResidueClass q a)
          (complexPositiveIntegerZeroExtension b) := by
      apply Finset.sum_le_sum
      intro a ha
      exact orderedTotalVariation_intervalWeight_le J hJ
        ({n : ℤ | 0 < n} ∩ integerResidueClass q a)
        (complexPositiveIntegerZeroExtension b)
    _ = (3 : ℝ≥0∞) * ∑ a ∈ Finset.range q,
          orderedTotalVariation
            ({n : ℤ | 0 < n} ∩ integerResidueClass q a)
            (complexPositiveIntegerZeroExtension b) := by
      rw [Finset.mul_sum]

end

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.intervalWeightVariation
