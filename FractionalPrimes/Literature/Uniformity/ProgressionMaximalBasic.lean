module

public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalAndTV

/-!
# Elementary verified bounds for the progression maximal sum

This file develops the first, intersection-free clauses of blueprint item
`lu:maximal-basic`.  It is deliberately separate from the progression
intersection classification currently being proved.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

theorem progressionMaximalSum_nonneg (I : FiniteIntegerInterval)
    (f : {n : ℤ // n ∈ I.points} → ℂ) :
    0 ≤ progressionMaximalSum I f := by
  have hempty := empty_mem_arithmeticProgressionsWithin I.points
  unfold progressionMaximalSum
  calc
    0 ≤ (fun P => ‖∑ n ∈ P, extendByZero I.points f n‖) ∅ := norm_nonneg _
    _ ≤ _ := Finset.le_sup'
      (fun P => ‖∑ n ∈ P, extendByZero I.points f n‖) hempty

theorem progressionMaximalSum_interval_lower (I : FiniteIntegerInterval)
    (f : {n : ℤ // n ∈ I.points} → ℂ) :
    ‖∑ x ∈ I.points.attach, f x‖ ≤ progressionMaximalSum I f := by
  have hsum' :
      (∑ x ∈ I.points.attach, extendByZero I.points f x.1) =
        ∑ x ∈ I.points.attach, f x := by
    simp [extendByZero]
  rw [← hsum', Finset.sum_attach]
  unfold progressionMaximalSum
  exact Finset.le_sup'
    (fun P => ‖∑ n ∈ P, extendByZero I.points f n‖)
    (FiniteIntegerInterval.points_mem_arithmeticProgressionsWithin I)

private theorem sum_norm_extendByZero_eq_interval (I : FiniteIntegerInterval)
    (f : {n : ℤ // n ∈ I.points} → ℂ) :
    (∑ n ∈ I.points, ‖extendByZero I.points f n‖) =
      ∑ x ∈ I.points.attach, ‖f x‖ := by
  calc
    (∑ n ∈ I.points, ‖extendByZero I.points f n‖) =
        ∑ x ∈ I.points.attach, ‖extendByZero I.points f x.1‖ := by
      rw [← Finset.sum_attach]
    _ = ∑ x ∈ I.points.attach, ‖f x‖ := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [extendByZero]

theorem progressionMaximalSum_le_interval_norm_sum (I : FiniteIntegerInterval)
    (f : {n : ℤ // n ∈ I.points} → ℂ) :
    progressionMaximalSum I f ≤ ∑ x ∈ I.points.attach, ‖f x‖ := by
  classical
  unfold progressionMaximalSum
  apply Finset.sup'_le
  intro P hP
  have hsubset : P ⊆ I.points :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
  calc
    ‖∑ n ∈ P, extendByZero I.points f n‖
        ≤ ∑ n ∈ P, ‖extendByZero I.points f n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ I.points, ‖extendByZero I.points f n‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro n hnI hnP
        exact norm_nonneg _)
    _ = ∑ x ∈ I.points.attach, ‖f x‖ := sum_norm_extendByZero_eq_interval I f

theorem progressionMaximalSum_add_le (I : FiniteIntegerInterval)
    (f g : {n : ℤ // n ∈ I.points} → ℂ) :
    progressionMaximalSum I (f + g) ≤
      progressionMaximalSum I f + progressionMaximalSum I g := by
  classical
  unfold progressionMaximalSum
  apply Finset.sup'_le
  intro P hP
  have hsubset : P ⊆ I.points :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
  have hsum :
      (∑ n ∈ P, extendByZero I.points (f + g) n) =
        (∑ n ∈ P, extendByZero I.points f n) +
          (∑ n ∈ P, extendByZero I.points g n) := by
    calc
      (∑ n ∈ P, extendByZero I.points (f + g) n) =
          ∑ n ∈ P, (extendByZero I.points f n + extendByZero I.points g n) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [extendByZero, hsubset hn]
      _ = _ := Finset.sum_add_distrib
  have hmaxf := Finset.le_sup'
    (fun Q => ‖∑ n ∈ Q, extendByZero I.points f n‖) hP
  have hmaxg := Finset.le_sup'
    (fun Q => ‖∑ n ∈ Q, extendByZero I.points g n‖) hP
  rw [hsum]
  calc
    ‖(∑ n ∈ P, extendByZero I.points f n) +
        (∑ n ∈ P, extendByZero I.points g n)‖ ≤
        ‖∑ n ∈ P, extendByZero I.points f n‖ +
          ‖∑ n ∈ P, extendByZero I.points g n‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hmaxf hmaxg

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.progressionMaximalSum_nonneg
#print axioms FractionalPrimes.Literature.Uniformity.progressionMaximalSum_interval_lower
#print axioms FractionalPrimes.Literature.Uniformity.progressionMaximalSum_le_interval_norm_sum
#print axioms FractionalPrimes.Literature.Uniformity.progressionMaximalSum_add_le
