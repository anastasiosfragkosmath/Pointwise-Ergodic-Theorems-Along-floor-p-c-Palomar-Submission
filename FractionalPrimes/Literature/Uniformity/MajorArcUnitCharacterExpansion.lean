module

public import FractionalPrimes.Literature.Uniformity.MajorArcTask
public import FractionalPrimes.Literature.Twisted.CharacterDataAdapter

/-! Exact finite character expansion for the unit-residue `Λ - Cr_X`
coefficient in `lu:major-arcs-task`. This is coefficient bookkeeping only;
it gives no estimate for the resulting character-twisted sums. -/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Uniformity

open FractionalPrimes.Literature.Twisted
open scoped BigOperators

/-- On the exact source interval `(X,X+H]`, the `Λ - Cr_X` sum in a unit
residue class is the normalized average of its Dirichlet-character twists.
The Cramér term is the same strict-cutoff model used by `majorArcTask`. -/
theorem majorArcUnitLambdaMinusCramer_characterExpansion
    (X H q : ℕ) (a : ℤ) (hq : 0 < q)
    (ha : IsCoprime a (q : ℤ)) :
    (∑ n ∈ ((majorArcInterval X H).points.filter
        (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)])),
        ((paperLambda n - paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ)) =
      (∑ χ : BlueprintCharacter q,
        star (evalInt χ a) *
          ∑ n ∈ (majorArcInterval X H).points,
            ((paperLambda n - paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ) *
              evalInt χ n) / (q.totient : ℂ) := by
  classical
  let s := (majorArcInterval X H).points
  let f : ℤ → ℂ := fun n =>
    ((paperLambda n - paperShortBlockCramerWeight (X : ℝ) n : ℝ) : ℂ)
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hq))
  have hpoint : ∀ n ∈ s,
      (if n ≡ a [ZMOD (q : ℤ)] then f n else 0) =
        f n *
          ((∑ χ : BlueprintCharacter q,
              star (evalInt χ a) * evalInt χ n) / (q.totient : ℂ)) := by
    intro n hn
    have horth := integer_character_orthogonality_indicator hq a n ha
    have hmod : ((a : ZMod q) = (n : ZMod q)) ↔
        n ≡ a [ZMOD (q : ℤ)] := by
      rw [ZMod.intCast_eq_intCast_iff]
      constructor <;> intro h <;> exact Int.ModEq.symm h
    by_cases h : n ≡ a [ZMOD (q : ℤ)]
    · have hEq : (a : ZMod q) = (n : ZMod q) := hmod.mpr h
      have horth' : (1 : ℂ) =
          (∑ χ : BlueprintCharacter q,
            star (evalInt χ a) * evalInt χ n) / (q.totient : ℂ) := by
        simpa [hEq] using horth
      rw [if_pos h]
      calc
        f n = f n * 1 := by simp
        _ = f n *
            ((∑ χ : BlueprintCharacter q,
                star (evalInt χ a) * evalInt χ n) / (q.totient : ℂ)) := by
          rw [← horth']
    · have hNe : (a : ZMod q) ≠ (n : ZMod q) := by
        intro hEq
        exact h (hmod.mp hEq)
      have horth' : (0 : ℂ) =
          (∑ χ : BlueprintCharacter q,
            star (evalInt χ a) * evalInt χ n) / (q.totient : ℂ) := by
        simpa [hNe] using horth
      rw [if_neg h]
      calc
        0 = f n * 0 := by simp
        _ = f n *
            ((∑ χ : BlueprintCharacter q,
                star (evalInt χ a) * evalInt χ n) / (q.totient : ℂ)) := by
          rw [← horth']
  have hchar :
      (∑ n ∈ s, f n *
        (∑ χ : BlueprintCharacter q,
          star (evalInt χ a) * evalInt χ n)) =
      ∑ χ : BlueprintCharacter q,
        star (evalInt χ a) * ∑ n ∈ s, f n * evalInt χ n := by
    calc
      (∑ n ∈ s, f n *
          (∑ χ : BlueprintCharacter q,
            star (evalInt χ a) * evalInt χ n)) =
        ∑ n ∈ s, ∑ χ : BlueprintCharacter q,
          f n * (star (evalInt χ a) * evalInt χ n) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.mul_sum]
      _ = ∑ χ : BlueprintCharacter q, ∑ n ∈ s,
          f n * (star (evalInt χ a) * evalInt χ n) := by
            rw [Finset.sum_comm]
      _ = ∑ χ : BlueprintCharacter q,
          star (evalInt χ a) * ∑ n ∈ s, f n * evalInt χ n := by
            apply Finset.sum_congr rfl
            intro χ hχ
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            ring
  change
    (∑ n ∈ s.filter (fun n : ℤ => n ≡ a [ZMOD (q : ℤ)]), f n) =
      (∑ χ : BlueprintCharacter q,
        star (evalInt χ a) * ∑ n ∈ s, f n * evalInt χ n) /
          (q.totient : ℂ)
  rw [Finset.sum_filter]
  calc
    (∑ n ∈ s, if n ≡ a [ZMOD (q : ℤ)] then f n else 0) =
        ∑ n ∈ s,
          f n *
            ((∑ χ : BlueprintCharacter q,
                star (evalInt χ a) * evalInt χ n) / (q.totient : ℂ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n hn
    _ = (∑ n ∈ s, f n *
          (∑ χ : BlueprintCharacter q,
            star (evalInt χ a) * evalInt χ n)) / (q.totient : ℂ) := by
      calc
        _ = ∑ n ∈ s,
              (f n *
                (∑ χ : BlueprintCharacter q,
                  star (evalInt χ a) * evalInt χ n)) / (q.totient : ℂ) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := by rw [Finset.sum_div]
    _ = _ := by rw [hchar]

#print axioms
  FractionalPrimes.Literature.Uniformity.majorArcUnitLambdaMinusCramer_characterExpansion

end FractionalPrimes.Literature.Uniformity

end
