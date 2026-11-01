module

public import FractionalPrimes.Literature.MobiusToLong.CharacterPrimeCorrectionIdentity
public import FractionalPrimes.Literature.LongArithmetic.NonunitResidueCoprimality

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.LongArithmetic

open Finset
open FractionalPrimes.Literature.MobiusToLong

private theorem nonunitLambda_nonneg (n : ℕ) : 0 ≤ vonMangoldtWeight n := by
  simpa [vonMangoldtWeight] using ArithmeticFunction.vonMangoldt_nonneg

/-- The von Mangoldt sum in one integer residue class, with the paper's
positive-integer and real-floor endpoint convention. -/
def nonunitLambdaResidueSum (q : ℕ) (a : ℤ) (Y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
    if (n : ℤ) ≡ a [ZMOD (q : ℤ)] then vonMangoldtWeight n else 0

/-- Exact non-coprime von Mangoldt residue bound `lal:nonunit-lambda`.
The condition `Int.gcd a q > 1` is the integer-gcd form of a nonunit
residue class. -/
theorem nonunitVonMangoldtBound
    {Y : ℝ} (hY : 2 ≤ Y) {q : ℕ} (hq : 1 ≤ q) {a : ℤ}
    (ha : 1 < Int.gcd a (q : ℤ)) :
    0 ≤ nonunitLambdaResidueSum q a Y ∧
      nonunitLambdaResidueSum q a Y ≤
        (Real.log (q : ℝ) / Real.log 2) * Real.log Y := by
  classical
  have hqpos : 0 < q := by omega
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq2 : 2 ≤ q := by
    by_contra hq2
    have hqone : q = 1 := by omega
    subst q
    simp at ha
  have hq1 : 1 ≤ q := by omega
  have hlogq : Real.log 2 ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq2)
  have hlogY : Real.log 2 ≤ Real.log Y :=
    Real.log_le_log (by norm_num) hY
  have hratio : 1 ≤ Real.log (q : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlog2pos).2 (by simpa using hlogq)
  have hsmallBound : Real.log 2 ≤
      (Real.log (q : ℝ) / Real.log 2) * Real.log Y := by
    calc
      Real.log 2 = 1 * Real.log 2 := by ring
      _ ≤ (Real.log (q : ℝ) / Real.log 2) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hratio hlog2pos.le
      _ ≤ (Real.log (q : ℝ) / Real.log 2) * Real.log Y :=
        mul_le_mul_of_nonneg_left hlogY (div_nonneg
          (Real.log_nonneg (by exact_mod_cast hq1)) hlog2pos.le)
  have hnonneg : 0 ≤ nonunitLambdaResidueSum q a Y := by
    unfold nonunitLambdaResidueSum
    apply Finset.sum_nonneg
    intro n hn
    by_cases hmod : (n : ℤ) ≡ a [ZMOD (q : ℤ)]
    · simp [hmod, nonunitLambda_nonneg]
    · simp [hmod]
  have hupper : nonunitLambdaResidueSum q a Y ≤
      (Real.log (q : ℝ) / Real.log 2) * Real.log Y := by
    by_cases hY3 : 3 ≤ Y
    · let S : Finset ℕ := Finset.Icc 1 (Nat.floor Y)
      have hterm (n : ℕ) (hn : n ∈ S) :
          (if (n : ℤ) ≡ a [ZMOD (q : ℤ)] then vonMangoldtWeight n else 0) ≤
            vonMangoldtWeight n - vonMangoldtWeight n *
              (if Nat.Coprime n q then (1 : ℝ) else 0) := by
        by_cases hmod : (n : ℤ) ≡ a [ZMOD (q : ℤ)]
        · have hnoncop := nonunitResidue_not_coprime ha hmod
          rw [if_pos hmod, if_neg hnoncop]
          simp
        · by_cases hcop : Nat.Coprime n q
          · rw [if_neg hmod, if_pos hcop]
            simp
          · rw [if_neg hmod, if_neg hcop]
            simp [nonunitLambda_nonneg]
      have hsumTerm :
          nonunitLambdaResidueSum q a Y ≤
            ∑ n ∈ S, (vonMangoldtWeight n - vonMangoldtWeight n *
              (if Nat.Coprime n q then (1 : ℝ) else 0)) := by
        unfold nonunitLambdaResidueSum
        apply Finset.sum_le_sum
        intro n hn
        exact hterm n (by simpa [S] using hn)
      have hsumEq :
          (∑ n ∈ S, (vonMangoldtWeight n - vonMangoldtWeight n *
            (if Nat.Coprime n q then (1 : ℝ) else 0))) =
            (∑ n ∈ S, vonMangoldtWeight n) -
              (∑ n ∈ S, vonMangoldtWeight n *
                (if Nat.Coprime n q then (1 : ℝ) else 0)) := by
        rw [Finset.sum_sub_distrib]
      have hbound := (principalCharacterMissingMass_le hY3 hq).2
      change nonunitLambdaResidueSum q a Y ≤
        (Real.log (q : ℝ) / Real.log 2) * Real.log Y
      rw [hsumEq] at hsumTerm
      have hbound' :
          (∑ n ∈ S, vonMangoldtWeight n) -
              (∑ n ∈ S, vonMangoldtWeight n *
                (if Nat.Coprime n q then (1 : ℝ) else 0)) ≤
            (Real.log (q : ℝ) / Real.log 2) * Real.log Y := by
        simpa [S] using hbound
      exact hsumTerm.trans hbound'
    · have hYlt3 : Y < 3 := by linarith
      have hfloor : Nat.floor Y ≤ 2 := by
        have hlt : Nat.floor Y < 3 :=
          (Nat.floor_lt (by linarith : 0 ≤ Y)).2 hYlt3
        omega
      have hsumAll :
          (∑ n ∈ Finset.Icc 1 (Nat.floor Y), vonMangoldtWeight n) ≤
            Real.log 2 := by
        have hLambdaOne : vonMangoldtWeight 1 = 0 := by
          rw [vonMangoldtWeight]
          exact ArithmeticFunction.vonMangoldt_apply_one
        have hLambdaTwo : vonMangoldtWeight 2 = Real.log 2 := by
          rw [vonMangoldtWeight]
          exact ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
        calc
          _ ≤ ∑ n ∈ Finset.Icc 1 2, vonMangoldtWeight n := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_right hfloor)
            intro n hn hnot
            exact nonunitLambda_nonneg n
          _ = Real.log 2 := by
            rw [show Finset.Icc 1 2 = {1, 2} by
              ext n
              simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
              omega]
            rw [Finset.sum_insert (by simp : (1 : ℕ) ∉ ({2} : Finset ℕ))]
            rw [Finset.sum_singleton, hLambdaOne, hLambdaTwo]
            ring
      have hsumClass : nonunitLambdaResidueSum q a Y ≤
          ∑ n ∈ Finset.Icc 1 (Nat.floor Y), vonMangoldtWeight n := by
        unfold nonunitLambdaResidueSum
        apply Finset.sum_le_sum
        intro n hn
        by_cases hmod : (n : ℤ) ≡ a [ZMOD (q : ℤ)]
        · simp [hmod]
        · simp [hmod, nonunitLambda_nonneg]
      exact hsumClass.trans (hsumAll.trans hsmallBound)
  exact ⟨hnonneg, hupper⟩

/-- The same nonunit bound applies to every finite subsum of the residue
class, as stated after `lal:nonunit-lambda`. -/
theorem nonunitVonMangoldtSubsumBound
    {Y : ℝ} (hY : 2 ≤ Y) {q : ℕ} (hq : 1 ≤ q) {a : ℤ}
    (ha : 1 < Int.gcd a (q : ℤ)) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 (Nat.floor Y))
    (hres : ∀ n ∈ S, (n : ℤ) ≡ a [ZMOD (q : ℤ)]) :
    0 ≤ (∑ n ∈ S, vonMangoldtWeight n) ∧
      (∑ n ∈ S, vonMangoldtWeight n) ≤
        (Real.log (q : ℝ) / Real.log 2) * Real.log Y := by
  classical
  have hclass := nonunitVonMangoldtBound hY hq ha
  have hnonneg : 0 ≤ ∑ n ∈ S, vonMangoldtWeight n :=
    Finset.sum_nonneg fun n hn => nonunitLambda_nonneg n
  have hle : (∑ n ∈ S, vonMangoldtWeight n) ≤
      nonunitLambdaResidueSum q a Y := by
    unfold nonunitLambdaResidueSum
    calc
      _ = ∑ n ∈ S, (if (n : ℤ) ≡ a [ZMOD (q : ℤ)] then
          vonMangoldtWeight n else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [hres n hn]
      _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
          (if (n : ℤ) ≡ a [ZMOD (q : ℤ)] then vonMangoldtWeight n else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg hS (by
          intro n hn hnot
          by_cases hmod : (n : ℤ) ≡ a [ZMOD (q : ℤ)]
          · simp [hmod, nonunitLambda_nonneg]
          · simp [hmod])
      _ = _ := rfl
  exact ⟨hnonneg, hle.trans hclass.2⟩

end FractionalPrimes.Literature.LongArithmetic

#print axioms FractionalPrimes.Literature.LongArithmetic.nonunitVonMangoldtBound
#print axioms FractionalPrimes.Literature.LongArithmetic.nonunitVonMangoldtSubsumBound
