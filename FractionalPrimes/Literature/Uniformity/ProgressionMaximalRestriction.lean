module

public import FractionalPrimes.Literature.Uniformity.ProgressionMaximalBasic
public import FractionalPrimes.Literature.Uniformity.ProgressionIntersection

/-!
# Restriction of the progression maximal sum to an arithmetic progression

This module proves the restriction clause of `lu:maximal-basic`.  The
right-hand maximal sum is represented by a separate finite-AP helper because
the base maximal sum is defined on `FiniteIntegerInterval` carriers.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

noncomputable section

/-- The maximal sum over all arithmetic-progression subsets of a finite set.
When the carrier is itself an arithmetic progression, this is the blueprint's
`M_{P₀}` (the maximum over subprogressions of `P₀`). -/
def progressionMaximalSumOnFiniteSet (P₀ : Finset ℤ)
    (f : {n : ℤ // n ∈ P₀} → ℂ) : ℝ :=
  (arithmeticProgressionsWithin P₀).sup'
    (arithmeticProgressionsWithin_nonempty P₀)
    (fun Q => ‖∑ n ∈ Q, extendByZero P₀ f n‖)

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

private theorem sum_indicator_extendByZero_eq_inter
    (I P Q : Finset ℤ) (f : {n : ℤ // n ∈ I} → ℂ)
    (hPI : P ⊆ I) (hQI : Q ⊆ I) :
    (∑ n ∈ Q, extendByZero I
      (fun x => if hx : x.1 ∈ P then f ⟨x.1, hPI hx⟩ else 0) n) =
      ∑ n ∈ Q ∩ P, extendByZero P
        (fun x => f ⟨x.1, hPI x.2⟩) n := by
  classical
  have hsub : Q ∩ P ⊆ Q := Finset.inter_subset_left
  calc
    (∑ n ∈ Q, extendByZero I
        (fun x => if hx : x.1 ∈ P then f ⟨x.1, hPI hx⟩ else 0) n) =
      ∑ n ∈ Q ∩ P, extendByZero I
        (fun x => if hx : x.1 ∈ P then f ⟨x.1, hPI hx⟩ else 0) n := by
          symm
          apply Finset.sum_subset hsub
          intro n hnQ hnnot
          have hnP : n ∉ P := by
            intro hnP
            exact hnnot (Finset.mem_inter.mpr ⟨hnQ, hnP⟩)
          simp [extendByZero, hQI hnQ, hnP]
    _ = ∑ n ∈ Q ∩ P, extendByZero P
        (fun x => f ⟨x.1, hPI x.2⟩) n := by
          apply Finset.sum_congr rfl
          intro n hn
          rcases Finset.mem_inter.mp hn with ⟨hnQ, hnP⟩
          simp [extendByZero, hQI hnQ]

/-- If `P₀` is an arithmetic progression contained in `I`, then testing the
interval maximal sum on `f` restricted to `P₀` gives exactly the maximal sum
over subprogressions of `P₀`.  The indicator is encoded by zero extension
outside `P₀`; length-zero progressions are included. -/
theorem progressionMaximalSum_restrict_to_progression
    (I : FiniteIntegerInterval) (P₀ : Finset ℤ)
    (hP₀ : isFiniteArithmeticProgression P₀)
    (hP₀I : P₀ ⊆ I.points)
    (f : {n : ℤ // n ∈ I.points} → ℂ) :
    progressionMaximalSum I
        (fun n => if hn : n.1 ∈ P₀ then f ⟨n.1, hP₀I hn⟩ else 0) =
      progressionMaximalSumOnFiniteSet P₀
        (fun n => f ⟨n.1, hP₀I n.2⟩) := by
  classical
  let fI : {n : ℤ // n ∈ I.points} → ℂ := fun n =>
    if hn : n.1 ∈ P₀ then f ⟨n.1, hP₀I hn⟩ else 0
  let fP : {n : ℤ // n ∈ P₀} → ℂ := fun n => f ⟨n.1, hP₀I n.2⟩
  have hleI : progressionMaximalSum I fI ≤ progressionMaximalSumOnFiniteSet P₀ fP := by
    unfold progressionMaximalSum
    apply Finset.sup'_le
    intro Q hQ
    have hQmem := Finset.mem_filter.mp hQ
    have hQI : Q ⊆ I.points := Finset.mem_powerset.mp hQmem.1
    have hQAP : isFiniteArithmeticProgression Q := hQmem.2
    let R := Q ∩ P₀
    have hRfam : R ∈ arithmeticProgressionsWithin P₀ := by
      simpa [R] using
        (intersection_mem_arithmeticProgressionsWithin Q P₀ hQAP hP₀)
    have hsum := sum_indicator_extendByZero_eq_inter
      I.points P₀ Q f hP₀I hQI
    change ‖∑ n ∈ Q, extendByZero I.points fI n‖ ≤ _
    rw [hsum]
    unfold progressionMaximalSumOnFiniteSet
    exact Finset.le_sup'
      (fun S => ‖∑ n ∈ S, extendByZero P₀ fP n‖) hRfam
  have hleP : progressionMaximalSumOnFiniteSet P₀ fP ≤ progressionMaximalSum I fI := by
    unfold progressionMaximalSumOnFiniteSet
    apply Finset.sup'_le
    intro R hR
    have hRmem := Finset.mem_filter.mp hR
    have hRP₀ : R ⊆ P₀ := Finset.mem_powerset.mp hRmem.1
    have hRI : R ⊆ I.points := hRP₀.trans hP₀I
    have hRfam : R ∈ arithmeticProgressionsWithin I.points := by
      rw [arithmeticProgressionsWithin, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hRI, hRmem.2⟩
    have hsum := sum_indicator_extendByZero_eq_inter
      I.points P₀ R f hP₀I hRI
    have hinter : R ∩ P₀ = R := Finset.inter_eq_left.mpr hRP₀
    have hsum' :
        (∑ n ∈ R, extendByZero I.points fI n) =
          ∑ n ∈ R, extendByZero P₀ fP n := by
      simpa [hinter, fI, fP] using hsum
    change ‖∑ n ∈ R, extendByZero P₀ fP n‖ ≤ _
    rw [← hsum']
    unfold progressionMaximalSum
    exact Finset.le_sup'
      (fun Q => ‖∑ n ∈ Q, extendByZero I.points fI n‖) hRfam
  change progressionMaximalSum I fI = progressionMaximalSumOnFiniteSet P₀ fP
  exact le_antisymm hleI hleP

end

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.progressionMaximalSum_restrict_to_progression
