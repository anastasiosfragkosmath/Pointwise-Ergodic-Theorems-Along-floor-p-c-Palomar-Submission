module

public import FractionalPrimes.Literature.Uniformity.DivisorFunctions
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Ordered tuple interpretation of the divisor function

For a positive integer `n`, `divisorFunction k n` is the number of ordered
`k`-tuples of positive integers with product `n`.  This is the explanatory
tuple-count characterization in blueprint item `lu:divisors`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

/-- Ordered `k`-tuples of positive integers with product `n`. -/
def divisorFactorTuples (k n : ℕ) :=
  {v : Fin k → PositiveInteger // (∏ i : Fin k, (v i).1) = n}

theorem divisorFactorTuples_finite (k n : ℕ) :
    Finite (divisorFactorTuples k n) := by
  classical
  apply Finite.of_injective
    (fun (v : divisorFactorTuples k n) (i : Fin k) =>
      (⟨(v.1 i).1, by
      have hprod : (v.1 i).1 ≤ ∏ j : Fin k, (v.1 j).1 := by
        simpa using
          (Finset.single_le_prod
            (s := Finset.univ) (f := fun j : Fin k => (v.1 j).1)
            (fun j hj => Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (v.1 j).2))
            (Finset.mem_univ i))
      rw [v.2] at hprod
      exact Nat.lt_succ_of_le hprod⟩ : Fin (n + 1)))
  intro v w h
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact congrArg Fin.val (congrFun h i)

noncomputable instance divisorFactorTuplesFintype (k n : ℕ) :
    Fintype (divisorFactorTuples k n) := by
  haveI : Finite (divisorFactorTuples k n) := divisorFactorTuples_finite k n
  exact Fintype.ofFinite (divisorFactorTuples k n)

/-- A natural divisor of the fixed positive integer `n`. -/
abbrev PositiveDivisor (n : PositiveInteger) := {d : ℕ // d ∈ n.1.divisors}

private def splitLastFactorTuple (k : ℕ) (n : PositiveInteger) :
    divisorFactorTuples (k + 1) n.1 ≃
      Σ d : PositiveDivisor n, divisorFactorTuples k d.1 := by
  classical
  refine
    { toFun := fun v => ?_
      invFun := fun q => ?_
      left_inv := ?_
      right_inv := ?_ }
  · let dval : ℕ := ∏ i : Fin k, (v.1 i.castSucc).1
    have hprod := v.2
    rw [Fin.prod_univ_castSucc] at hprod
    have hdmem : dval ∈ n.1.divisors := by
      apply Nat.mem_divisors.mpr
      refine ⟨?_, Nat.ne_of_gt n.2⟩
      refine ⟨(v.1 (Fin.last k)).1, ?_⟩
      dsimp [dval] at hprod ⊢
      exact hprod.symm
    exact ⟨⟨dval, hdmem⟩,
      ⟨fun i => v.1 i.castSucc, by rfl⟩⟩
  · let tailTuple := q.2
    let last : PositiveInteger :=
      ⟨n.1 / q.1.1,
        Nat.div_pos (Nat.le_of_dvd n.2 (Nat.dvd_of_mem_divisors q.1.2))
          (Nat.pos_of_mem_divisors q.1.2)⟩
    refine ⟨Fin.snoc tailTuple.1 last, ?_⟩
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, tailTuple.2]
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors q.1.2)
  · intro v
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      have hprod := v.2
      rw [Fin.prod_univ_castSucc] at hprod
      have htailmem : (∏ j : Fin k, (v.1 j.castSucc).1) ∈ n.1.divisors := by
        apply Nat.mem_divisors.mpr
        refine ⟨?_, Nat.ne_of_gt n.2⟩
        refine ⟨(v.1 (Fin.last k)).1, ?_⟩
        exact hprod.symm
      have hquot : n.1 / (∏ j : Fin k, (v.1 j.castSucc).1) =
          (v.1 (Fin.last k)).1 := by
        apply (Nat.div_eq_iff_eq_mul_left
          (Finset.prod_pos fun j hj => (v.1 j.castSucc).2)
          (Nat.dvd_of_mem_divisors htailmem)).2
        simpa [Nat.mul_comm] using hprod.symm
      exact Subtype.ext hquot
    · simp only [Fin.snoc_castSucc]
  · rintro ⟨d, tail⟩
    let last : PositiveInteger :=
      ⟨n.1 / d.1,
        Nat.div_pos (Nat.le_of_dvd n.2 (Nat.dvd_of_mem_divisors d.2))
          (Nat.pos_of_mem_divisors d.2)⟩
    let f : Fin (k + 1) → PositiveInteger := Fin.snoc tail.1 last
    let p : ℕ := ∏ i : Fin k, (f i.castSucc).1
    have hp : p = d.1 := by
      dsimp [p, f]
      simp only [Fin.snoc_castSucc]
      exact tail.2
    have hmem : p ∈ n.1.divisors := by
      rw [hp]
      exact d.2
    apply Sigma.subtype_ext
    · apply Subtype.ext
      exact hp
    · funext i
      simp only [Fin.snoc_castSucc]

/-- The count of ordered positive `k`-factorizations of `n` is the `k`-fold
divisor function.  This includes `k = 0`, with the empty product convention,
and hence in particular gives the blueprint's stated `k ≥ 1` interpretation. -/
theorem divisorFunction_eq_card_factorTuples (k : ℕ) (n : PositiveInteger) :
    divisorFunction k n = Fintype.card (divisorFactorTuples k n.1) := by
  classical
  revert n
  induction k with
  | zero =>
      intro n
      rw [divisorFunction_zero]
      by_cases hn : n.1 = 1
      · have hcard : Fintype.card (divisorFactorTuples 0 n.1) = 1 := by
          apply Fintype.card_eq_one_iff.mpr
          refine ⟨⟨Fin.elim0, by simp [hn]⟩, ?_⟩
          intro a
          apply Subtype.ext
          funext i
          exact Fin.elim0 i
        rw [hcard]
        simp [divisorDeltaOne, hn]
      · have hcard : Fintype.card (divisorFactorTuples 0 n.1) = 0 := by
          apply Fintype.card_eq_zero_iff.mpr
          exact ⟨fun v => hn (by simpa [divisorFactorTuples] using v.2.symm)⟩
        rw [hcard]
        simp [divisorDeltaOne, hn]
  | succ k ih =>
      intro n
      rw [divisorFunction_succ, positiveDirichletConvolution_eq_divisor_sum]
      rw [Fintype.card_congr (splitLastFactorTuple k n)]
      rw [Fintype.card_sigma]
      simp only [Finset.univ_eq_attach]
      rw [← Finset.sum_attach (s := n.1.divisors)
        (f := fun d => divisorConvolutionSummand (divisorFunction k) divisorOne n d)]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← ih ⟨d.1, Nat.pos_of_mem_divisors d.2⟩]
      simp [divisorConvolutionSummand, divisorOne, d.2]

end FractionalPrimes.Literature.Uniformity

end

#print axioms FractionalPrimes.Literature.Uniformity.divisorFunction_eq_card_factorTuples
