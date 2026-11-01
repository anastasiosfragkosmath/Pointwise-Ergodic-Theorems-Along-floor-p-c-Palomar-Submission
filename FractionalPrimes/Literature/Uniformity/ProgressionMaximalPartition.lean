module

public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalRestriction

/-!
# Finite-partition subadditivity for the progression maximal sum

The partition is represented by a finite family of pairwise-disjoint finite
arithmetic progressions whose union is the interval carrier. Empty parts and an
empty carrier are allowed.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

private theorem intersection_mem_arithmeticProgressionsWithin
    (P Q : Finset ℤ) (hP : isFiniteArithmeticProgression P)
    (hQ : isFiniteArithmeticProgression Q) :
    P ∩ Q ∈ arithmeticProgressionsWithin Q := by
  classical
  rcases hP with ⟨a, d, hd, L, hP⟩
  rcases hQ with ⟨b, e, he, M, hQ⟩
  have hclass : P ∩ Q = ∅ ∨ isFiniteArithmeticProgression (P ∩ Q) := by
    simpa [hP, hQ] using
      (arithmeticProgressionPoints_inter_eq_empty_or_isFiniteArithmeticProgression
        a b d e hd he L M)
  rcases hclass with hempty | hAP
  · rw [hempty]
    exact empty_mem_arithmeticProgressionsWithin Q
  · rw [arithmeticProgressionsWithin, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, hAP⟩

private theorem sum_extendByZero_interval_eq_part
    (I P Q : Finset ℤ) (f : {n : ℤ // n ∈ I} → ℂ)
    (hPI : P ⊆ I) :
    (∑ n ∈ Q ∩ P, extendByZero I f n) =
      ∑ n ∈ Q ∩ P, extendByZero P
        (fun x => extendByZero I f x.1) n := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  rcases Finset.mem_inter.mp hn with ⟨_, hnP⟩
  simp [extendByZero, hPI hnP, hnP]

/-- Finite progression partition subadditivity.  The partition data explicitly
records disjointness, union equal to the interval carrier, containment in the
carrier, and the arithmetic-progression property of every part. -/
theorem progressionMaximalSum_le_sum_finiteProgressionPartition
    (I : FiniteIntegerInterval) (parts : Finset (Finset ℤ))
    (hparts_subset : ∀ P ∈ parts, P ⊆ I.points)
    (hparts_disjoint : ∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q)
    (hparts_cover : parts.biUnion id = I.points)
    (hparts_AP : ∀ P ∈ parts, isFiniteArithmeticProgression P)
    (f : {n : ℤ // n ∈ I.points} → ℂ) :
    progressionMaximalSum I f ≤
      ∑ P ∈ parts,
        progressionMaximalSumOnFiniteSet P
          (fun n => extendByZero I.points f n.1) := by
  classical
  unfold progressionMaximalSum
  apply Finset.sup'_le
  intro Q hQ
  have hQmem := Finset.mem_filter.mp hQ
  have hQI : Q ⊆ I.points := Finset.mem_powerset.mp hQmem.1
  have hQAP : isFiniteArithmeticProgression Q := hQmem.2
  let R (P : Finset ℤ) := Q ∩ P
  have hR_union : parts.biUnion R = Q := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_biUnion.mp hn with ⟨P, hP, hnP⟩
      exact (Finset.mem_inter.mp hnP).1
    · intro hnQ
      have hnI : n ∈ I.points := hQI hnQ
      have hnParts : n ∈ parts.biUnion id := by
        rw [hparts_cover]
        exact hnI
      rcases Finset.mem_biUnion.mp hnParts with ⟨P, hP, hnP⟩
      exact Finset.mem_biUnion.mpr
        ⟨P, hP, Finset.mem_inter.mpr ⟨hnQ, by simpa using hnP⟩⟩
  have hR_disjoint : (parts : Set (Finset ℤ)).PairwiseDisjoint R := by
    intro P hP Q' hQ' hne
    apply Finset.disjoint_left.mpr
    intro n hnP hnQ
    exact Finset.disjoint_left.mp (hparts_disjoint P hP Q' hQ' hne)
      (Finset.mem_inter.mp hnP).2 (Finset.mem_inter.mp hnQ).2
  have hsum :
      (∑ n ∈ Q, extendByZero I.points f n) =
        ∑ P ∈ parts, ∑ n ∈ R P, extendByZero I.points f n := by
    calc
      (∑ n ∈ Q, extendByZero I.points f n) =
          ∑ n ∈ parts.biUnion R, extendByZero I.points f n := by
            rw [← hR_union]
      _ = ∑ P ∈ parts, ∑ n ∈ R P, extendByZero I.points f n :=
        Finset.sum_biUnion hR_disjoint
  have htriangle :
      ‖∑ n ∈ Q, extendByZero I.points f n‖ ≤
        ∑ P ∈ parts, ‖∑ n ∈ R P, extendByZero I.points f n‖ := by
    rw [hsum]
    exact norm_sum_le _ _
  have htermwise :
      (∑ P ∈ parts, ‖∑ n ∈ R P, extendByZero I.points f n‖) ≤
        ∑ P ∈ parts,
          progressionMaximalSumOnFiniteSet P
            (fun n => extendByZero I.points f n.1) := by
    apply Finset.sum_le_sum
    intro P hP
    have hPI : P ⊆ I.points := hparts_subset P hP
    have hPAP : isFiniteArithmeticProgression P := hparts_AP P hP
    have hRmem : R P ∈ arithmeticProgressionsWithin P := by
      simpa [R] using
        (intersection_mem_arithmeticProgressionsWithin Q P hQAP hPAP)
    have hsumR :
        (∑ n ∈ R P, extendByZero I.points f n) =
          ∑ n ∈ R P, extendByZero P
            (fun n => extendByZero I.points f n.1) n := by
      exact sum_extendByZero_interval_eq_part I.points P Q f hPI
    rw [hsumR]
    unfold progressionMaximalSumOnFiniteSet
    exact Finset.le_sup'
      (fun S => ‖∑ n ∈ S, extendByZero P
        (fun n => extendByZero I.points f n.1) n‖) hRmem
  exact le_trans htriangle htermwise

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.progressionMaximalSum_le_sum_finiteProgressionPartition
