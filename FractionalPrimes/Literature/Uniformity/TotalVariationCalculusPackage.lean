module

public import FractionalPrimes.Literature.Uniformity.VariationRestriction
public import FractionalPrimes.Literature.Uniformity.ENNRealVariationProduct
public import FractionalPrimes.Literature.Uniformity.VariationAbelMultiplier
public import FractionalPrimes.Literature.Uniformity.VariationCalculusC1

/-!
# Aggregate package for `lu:tv-calculus`

The fields below retain the four clauses of the approved lemma: restriction,
residue-class product, the finite-interval maximal multiplier estimate, and
the C¹ variation bound.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

/-- Restricting the underlying ordered set cannot increase its extended
total variation. -/
theorem orderedTotalVariation_mono_of_subset {A B : Set ℤ}
    (hAB : A ⊆ B) (g : ℤ → ℂ) :
    orderedTotalVariation A g ≤ orderedTotalVariation B g := by
  unfold orderedTotalVariation
  refine iSup_le fun F => ?_
  let G : {G : Finset ℤ // ∀ n ∈ G, n ∈ B} :=
    ⟨F.1, fun n hn => hAB (F.2 n hn)⟩
  exact le_iSup_of_le G le_rfl

/-- The exact verified clauses of blueprint lemma `lu:tv-calculus`. -/
structure TotalVariationCalculus where
  /-- Extended inhomogeneous variation is monotone under restriction. -/
  restriction : ∀ (A B : Set ℤ), A ⊆ B → ∀ g : ℤ → ℂ,
    orderedTotalVariation A g ≤ orderedTotalVariation B g
  /-- Residue-class variation is submultiplicative. -/
  product : ∀ (P : Set ℤ) (g h : ℤ → ℂ) (q : ℕ) (hq : 0 < q),
    residueClassTotalVariation P (fun n => g n * h n) q hq ≤
      residueClassTotalVariation P g q hq * residueClassTotalVariation P h q hq
  /-- Abel summation bounds the maximal progression sum after multiplying by
  a coefficient sequence by its exact finite residue-class variation. -/
  maximal_multiplier : ∀ (I : FiniteIntegerInterval)
    (f : {n : ℤ // n ∈ I.points} → ℂ) (g : ℤ → ℂ)
    (q : ℕ) (_hq : 0 < q),
      progressionMaximalSum I (fun n => f n * g n.1) ≤
        finiteResidueClassVariation I g q * progressionMaximalSum I f
  /-- C¹ variation estimate on integer points in a real interval. -/
  calculus : ∀ {u v : ℝ} (_huv : u ≤ v) (g : ℝ → ℂ)
    (_hg : ContDiffOn ℝ 1 g (Set.Icc u v)) (P : Set ℤ)
    (_hP : ∀ n ∈ P, (n : ℝ) ∈ Set.Icc u v),
      orderedTotalVariation P (fun n : ℤ => g n) ≤
        ENNReal.ofReal (intervalNormSup u v g +
          ∫ t in u..v, ‖derivWithin g (Set.Icc u v) t‖)

/-- Manifest-facing package for the approved `lu:tv-calculus` lemma. -/
theorem totalVariationCalculus : TotalVariationCalculus where
  restriction := fun A B hAB g =>
    orderedTotalVariation_mono_of_subset (A := A) (B := B) hAB g
  product := fun P g h q hq => residueClassTotalVariation_mul_le P g h q hq
  maximal_multiplier := fun I f g q hq =>
    progressionMaximalSum_mul_le_finiteResidueClassVariation I f g q hq
  calculus := fun huv g hg P hP =>
    orderedTotalVariation_le_sup_add_integral huv g hg P hP

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.totalVariationCalculus
