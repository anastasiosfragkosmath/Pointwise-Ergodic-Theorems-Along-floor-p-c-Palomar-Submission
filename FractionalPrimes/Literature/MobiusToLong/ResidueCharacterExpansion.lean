module

public import FractionalPrimes.Literature.Twisted.CharacterDataAdapter

@[expose] public section

noncomputable section

open Finset
open FractionalPrimes.Literature.Twisted

namespace FractionalPrimes.Literature.MobiusToLong

/-- Exact finite character expansion for a unit residue class.  This is the
weighted-sum form of the character orthogonality identity used in
`lml:usw-from-muf`; no arithmetic estimate is assumed here. -/
theorem finiteResidueSum_eq_character_average {q : ℕ} (hq : 0 < q)
    (a : ℤ) (ha : IsCoprime a (q : ℤ)) (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ s,
      (if (a : ZMod q) = ((n : ℤ) : ZMod q) then f n else 0)) =
      (∑ χ : BlueprintCharacter q,
        star (evalInt χ a) *
          ∑ n ∈ s, f n * evalInt χ (n : ℤ)) / (q.totient : ℂ) := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hq))
  calc
    (∑ n ∈ s,
        (if (a : ZMod q) = ((n : ℤ) : ZMod q) then f n else 0)) =
        ∑ n ∈ s, f n *
          ((∑ χ : BlueprintCharacter q,
              star (evalInt χ a) * evalInt χ (n : ℤ)) / (q.totient : ℂ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have horth := integer_character_orthogonality_indicator hq a (n : ℤ) ha
      by_cases h : (a : ZMod q) = ((n : ℤ) : ZMod q)
      · rw [if_pos h]
        have horth' : (1 : ℂ) =
            (∑ χ : BlueprintCharacter q,
              star (evalInt χ a) * evalInt χ (n : ℤ)) / (q.totient : ℂ) := by
          simpa [h] using horth
        calc
          f n = f n * 1 := by simp
          _ = f n *
              ((∑ χ : BlueprintCharacter q,
                  star (evalInt χ a) * evalInt χ (n : ℤ)) / (q.totient : ℂ)) := by
            rw [← horth']
      · rw [if_neg h]
        have hneq : (a : ZMod q) ≠ (n : ZMod q) := by
          simpa using h
        have horth' : (0 : ℂ) =
            (∑ χ : BlueprintCharacter q,
              star (evalInt χ a) * evalInt χ (n : ℤ)) / (q.totient : ℂ) := by
          simpa [hneq] using horth
        calc
          0 = f n * 0 := by simp
          _ = f n *
              ((∑ χ : BlueprintCharacter q,
                  star (evalInt χ a) * evalInt χ (n : ℤ)) / (q.totient : ℂ)) := by
            rw [← horth']
    _ = ∑ n ∈ s, (f n *
          (∑ χ : BlueprintCharacter q,
            star (evalInt χ a) * evalInt χ (n : ℤ))) / (q.totient : ℂ) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = (∑ n ∈ s, f n *
          (∑ χ : BlueprintCharacter q,
            star (evalInt χ a) * evalInt χ (n : ℤ))) / (q.totient : ℂ) := by
      rw [Finset.sum_div]
    _ = (∑ χ : BlueprintCharacter q,
          ∑ n ∈ s, f n *
            (star (evalInt χ a) * evalInt χ (n : ℤ))) / (q.totient : ℂ) := by
      congr 1
      calc
        (∑ n ∈ s, f n *
            (∑ χ : BlueprintCharacter q,
              star (evalInt χ a) * evalInt χ (n : ℤ))) =
            ∑ n ∈ s, ∑ χ : BlueprintCharacter q,
              f n * (star (evalInt χ a) * evalInt χ (n : ℤ)) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mul_sum]
        _ = ∑ χ : BlueprintCharacter q, ∑ n ∈ s,
              f n * (star (evalInt χ a) * evalInt χ (n : ℤ)) := by
          rw [Finset.sum_comm]
    _ = (∑ χ : BlueprintCharacter q,
          star (evalInt χ a) * ∑ n ∈ s, f n * evalInt χ (n : ℤ)) /
            (q.totient : ℂ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

#print axioms finiteResidueSum_eq_character_average

end FractionalPrimes.Literature.MobiusToLong
