module

public import FractionalPrimes.Literature.Uniformity.FiniteVariationProduct

/-!
# Extended and residue-class total-variation product bounds

This module lifts the exact finite product inequality to the supremum over
finite subsets and then to the finite sum over residue classes, as required
by the product clause of blueprint lemma `lu:tv-calculus`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

/-- The inhomogeneous total variation on an arbitrary ordered subset is
submultiplicative under pointwise multiplication. -/
theorem orderedTotalVariation_mul_le (P : Set ℤ) (g h : ℤ → ℂ) :
    orderedTotalVariation P (fun n => g n * h n) ≤
      orderedTotalVariation P g * orderedTotalVariation P h := by
  unfold orderedTotalVariation
  refine iSup_le fun F => ?_
  have hg : ENNReal.ofReal (finiteOrderedTotalVariation F.1 g) ≤
      ⨆ G : {G : Finset ℤ // ∀ n ∈ G, n ∈ P},
        ENNReal.ofReal (finiteOrderedTotalVariation G.1 g) :=
    le_iSup_of_le F le_rfl
  have hh : ENNReal.ofReal (finiteOrderedTotalVariation F.1 h) ≤
      ⨆ G : {G : Finset ℤ // ∀ n ∈ G, n ∈ P},
        ENNReal.ofReal (finiteOrderedTotalVariation G.1 h) :=
    le_iSup_of_le F le_rfl
  calc
    ENNReal.ofReal (finiteOrderedTotalVariation F.1 (fun n => g n * h n)) ≤
        ENNReal.ofReal (finiteOrderedTotalVariation F.1 g) *
          ENNReal.ofReal (finiteOrderedTotalVariation F.1 h) := by
      calc
        ENNReal.ofReal (finiteOrderedTotalVariation F.1 (fun n => g n * h n)) ≤
            ENNReal.ofReal
              (finiteOrderedTotalVariation F.1 g * finiteOrderedTotalVariation F.1 h) :=
          ENNReal.ofReal_le_ofReal (finiteOrderedTotalVariation_mul_le F.1 g h)
        _ = ENNReal.ofReal (finiteOrderedTotalVariation F.1 g) *
            ENNReal.ofReal (finiteOrderedTotalVariation F.1 h) :=
          ENNReal.ofReal_mul (finiteOrderedTotalVariation_nonneg F.1 g)
    _ ≤
        (⨆ G : {G : Finset ℤ // ∀ n ∈ G, n ∈ P},
          ENNReal.ofReal (finiteOrderedTotalVariation G.1 g)) *
        (⨆ G : {G : Finset ℤ // ∀ n ∈ G, n ∈ P},
          ENNReal.ofReal (finiteOrderedTotalVariation G.1 h)) :=
      mul_le_mul hg hh (by simp) (by simp)

/-- The residue-class inhomogeneous total variation is submultiplicative.
The estimate is the diagonal-sum bound from the approved blueprint. -/
theorem residueClassTotalVariation_mul_le (P : Set ℤ) (g h : ℤ → ℂ)
    (q : ℕ) (hq : 0 < q) :
    residueClassTotalVariation P (fun n => g n * h n) q hq ≤
      residueClassTotalVariation P g q hq * residueClassTotalVariation P h q hq := by
  unfold residueClassTotalVariation
  calc
    (∑ a ∈ Finset.range q,
        orderedTotalVariation (P ∩ integerResidueClass q a) (fun n => g n * h n)) ≤
      ∑ a ∈ Finset.range q,
        orderedTotalVariation (P ∩ integerResidueClass q a) g *
          orderedTotalVariation (P ∩ integerResidueClass q a) h := by
      apply Finset.sum_le_sum
      intro a ha
      exact orderedTotalVariation_mul_le (P ∩ integerResidueClass q a) g h
    _ ≤
        (∑ a ∈ Finset.range q,
          orderedTotalVariation (P ∩ integerResidueClass q a) g) *
        (∑ a ∈ Finset.range q,
          orderedTotalVariation (P ∩ integerResidueClass q a) h) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.single_le_sum
        (f := fun b : ℕ =>
          orderedTotalVariation (P ∩ integerResidueClass q a) g *
            orderedTotalVariation (P ∩ integerResidueClass q b) h)
        (fun b hb => by positivity) ha

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.orderedTotalVariation_mul_le
#print axioms FractionalPrimes.Literature.Uniformity.residueClassTotalVariation_mul_le
