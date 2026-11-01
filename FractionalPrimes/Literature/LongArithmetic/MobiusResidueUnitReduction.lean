module

public import FractionalPrimes.Core
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.ZMod.Basic

/-!
# Exact reduction of Möbius sums in nonunit residue classes

This module formalizes the finite residue-class reduction in `lal:nonunit-mobius`.
The real cutoff is retained through `Nat.floor`, and the unit remainders are
the representatives in `[0,q)` congruent to `a / gcd a q` modulo
`q / gcd a q`.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace FractionalPrimes.Literature.LongArithmetic

/-- The Möbius sum over `1 ≤ n ≤ N` in the natural residue class `a mod q`. -/
def mobiusResidueSumNat (q a N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    if n % q = a then (ArithmeticFunction.moebius n : ℝ) else 0

/-- The real-cutoff Möbius sum with the paper's inclusive `n ≤ Y` convention. -/
def mobiusResidueSumReal (q a : ℕ) (Y : ℝ) : ℝ :=
  mobiusResidueSumNat q a (Nat.floor Y)

/-- The permitted unit remainders in the exact gcd reduction. -/
def mobiusResidueUnitRemainders (q a : ℕ) : Finset ℕ :=
  let g := Nat.gcd a q
  (Finset.range q).filter fun b =>
    Nat.Coprime b q ∧ b % (q / g) = a / g

private theorem gcd_pos_of_modulus_pos {q a : ℕ} (hq : 0 < q) :
    0 < Nat.gcd a q :=
  Nat.gcd_pos_of_pos_right a hq

private theorem gcd_le_of_lt {q a : ℕ} (ha : a < q) : Nat.gcd a q ≤ q :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (by omega)) (Nat.gcd_dvd_right a q)

private theorem gcd_div_representations {q a : ℕ} (hq : 0 < q) :
    let g := Nat.gcd a q
    a = (a / g) * g ∧ q = (q / g) * g := by
  dsimp
  have hgpos : 0 < Nat.gcd a q := gcd_pos_of_modulus_pos hq
  constructor
  · exact (Nat.div_mul_cancel (Nat.gcd_dvd_left a q)).symm
  · exact (Nat.div_mul_cancel (Nat.gcd_dvd_right a q)).symm

private theorem gcd_dvd_of_residue {q a n : ℕ} (hres : n % q = a) :
    Nat.gcd a q ∣ n := by
  have hnexp : n = n % q + q * (n / q) := (Nat.mod_add_div n q).symm
  rw [hnexp, hres]
  exact Nat.dvd_add (Nat.gcd_dvd_left a q)
    (dvd_mul_of_dvd_left (Nat.gcd_dvd_right a q) _)

private theorem reducedResidue_lt {q a : ℕ} (hq : 0 < q) (ha : a < q) :
    a / Nat.gcd a q < q / Nat.gcd a q := by
  have hgpos : 0 < Nat.gcd a q := gcd_pos_of_modulus_pos hq
  have hmul : (a / Nat.gcd a q) * Nat.gcd a q <
      (q / Nat.gcd a q) * Nat.gcd a q := by
    calc
      (a / Nat.gcd a q) * Nat.gcd a q = a :=
        Nat.div_mul_cancel (Nat.gcd_dvd_left a q)
      _ < q := ha
      _ = (q / Nat.gcd a q) * Nat.gcd a q :=
        (Nat.div_mul_cancel (Nat.gcd_dvd_right a q)).symm
  exact (Nat.mul_lt_mul_right hgpos).mp hmul

private theorem residue_div_gcd_iff {q a n : ℕ} (hq : 0 < q) (ha : a < q)
    (hdiv : Nat.gcd a q ∣ n) :
    n % q = a ↔ (n / Nat.gcd a q) % (q / Nat.gcd a q) = a / Nat.gcd a q := by
  let g := Nat.gcd a q
  let q₀ := q / g
  let a₀ := a / g
  have hgpos : 0 < g := gcd_pos_of_modulus_pos hq
  have hqrep : q = g * q₀ := by
    dsimp [q₀]
    rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right a q)]
  have harep : a = g * a₀ := by
    dsimp [a₀]
    rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left a q)]
  have ha₀ : a₀ < q₀ := by
    dsimp [a₀, q₀]
    exact reducedResidue_lt hq ha
  have hnrep : n = g * (n / g) := by
    calc
      n = (n / g) * g := (Nat.div_mul_cancel hdiv).symm
      _ = g * (n / g) := Nat.mul_comm _ _
  have hresModEq : n ≡ a [MOD q] ↔ n / g ≡ a₀ [MOD q₀] := by
    have hcancel : g * (n / g) ≡ g * a₀ [MOD g * q₀] ↔
        n / g ≡ a₀ [MOD q₀] :=
      Nat.ModEq.mul_left_cancel_iff' (Nat.ne_of_gt hgpos)
    have hrewrite : n ≡ a [MOD q] ↔
        g * (n / g) ≡ g * a₀ [MOD g * q₀] := by
      conv_lhs => rw [hnrep, harep, hqrep]
    exact hrewrite.trans hcancel
  have hres : n % q = a ↔ n ≡ a [MOD q] := by
    simp only [Nat.ModEq, Nat.mod_eq_of_lt ha]
  have hres₀ : (n / g) % q₀ = a₀ ↔ n / g ≡ a₀ [MOD q₀] := by
    simp only [Nat.ModEq, Nat.mod_eq_of_lt ha₀]
  exact hres.trans (hresModEq.trans hres₀.symm)

private theorem mobiusResidueUnitRemainders_card_le {q a : ℕ}
    (hq : 0 < q) (ha : a < q) :
    (mobiusResidueUnitRemainders q a).card ≤ Nat.gcd a q := by
  classical
  let g := Nat.gcd a q
  let q₀ := q / g
  let a₀ := a / g
  have hgpos : 0 < g := gcd_pos_of_modulus_pos hq
  have hq₀pos : 0 < q₀ := by
    dsimp [q₀]
    exact Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right a q)) hgpos
  have hqrep : q = g * q₀ := by
    dsimp [q₀]
    rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right a q)]
  have hmod : ∀ b ∈ mobiusResidueUnitRemainders q a, b % q₀ = a₀ := by
    intro b hb
    simpa [mobiusResidueUnitRemainders, g, q₀, a₀] using
      (Finset.mem_filter.mp hb).2.2
  have hmaps : Set.MapsTo (fun b : ℕ => b / q₀)
      (mobiusResidueUnitRemainders q a) (Finset.range g) := by
    intro b hb
    change b / q₀ ∈ Finset.range g
    have hbq : b < q := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    rw [hqrep] at hbq
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hq₀pos).2
    simpa [Nat.mul_comm] using hbq
  have hinj : (mobiusResidueUnitRemainders q a : Set ℕ).InjOn (fun b => b / q₀) := by
    intro b₁ hb₁ b₂ hb₂ hquot
    have hb₁mod := hmod b₁ hb₁
    have h₁ := Nat.mod_add_div b₁ q₀
    have h₂ := Nat.mod_add_div b₂ q₀
    change b₁ / q₀ = b₂ / q₀ at hquot
    rw [hb₁mod, hquot] at h₁
    rw [hmod b₂ hb₂] at h₂
    exact h₁.symm.trans h₂
  simpa [g] using Finset.card_le_card_of_injOn (fun b : ℕ => b / q₀)
    hmaps hinj

private theorem mobiusResidueSumNat_eq_filtered (q a N : ℕ) :
    mobiusResidueSumNat q a N =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = a),
        (ArithmeticFunction.moebius n : ℝ) := by
  simp [mobiusResidueSumNat, Finset.sum_filter]

private theorem mobiusResidueFilteredSum_drop_nonunit
    {q a N : ℕ} (hq : 0 < q) (ha : a < q)
    (hsq : Squarefree (Nat.gcd a q)) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = a),
      (ArithmeticFunction.moebius n : ℝ)) =
    (∑ n ∈ ((Finset.Icc 1 N).filter (fun n => n % q = a)).filter
      (fun n => Nat.Coprime (n / Nat.gcd a q) q),
      (ArithmeticFunction.moebius n : ℝ)) := by
  classical
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hres : n % q = a
  · by_cases hcop : Nat.Coprime (n / Nat.gcd a q) q
    · simp [hres, hcop]
    · have hgdiv : Nat.gcd a q ∣ n := gcd_dvd_of_residue hres
      have hred := (residue_div_gcd_iff hq ha hgdiv).mp hres
      have hq₀cop : Nat.Coprime (n / Nat.gcd a q)
          (q / Nat.gcd a q) := by
        rw [← ZMod.coprime_mod_iff_coprime]
        simpa [hred] using
          (Nat.coprime_div_gcd_div_gcd (gcd_pos_of_modulus_pos hq))
      have hgcop : ¬ Nat.Coprime (n / Nat.gcd a q) (Nat.gcd a q) := by
        intro hg
        apply hcop
        have hqrep : q = Nat.gcd a q * (q / Nat.gcd a q) := by
          rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right a q)]
        have hprod : Nat.Coprime (n / Nat.gcd a q)
            (Nat.gcd a q * (q / Nat.gcd a q)) := by
          rw [Nat.coprime_comm, Nat.coprime_mul_iff_left]
          exact ⟨hg.symm, hq₀cop.symm⟩
        rw [← hqrep] at hprod
        exact hprod
      have hnsq : ¬ Squarefree n := by
        intro hnSq
        have hmul : n = Nat.gcd a q * (n / Nat.gcd a q) := by
          calc
            n = (n / Nat.gcd a q) * Nat.gcd a q :=
              (Nat.div_mul_cancel hgdiv).symm
            _ = Nat.gcd a q * (n / Nat.gcd a q) := Nat.mul_comm _ _
        have hcop' : Nat.Coprime (Nat.gcd a q) (n / Nat.gcd a q) := by
          rw [hmul] at hnSq
          have := (Nat.squarefree_mul_iff).mp hnSq
          exact this.1
        exact hgcop hcop'.symm
      simp [hres, hcop, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
  · simp [hres]

private theorem mobiusResidueUnitRemainders_sum_bij
    {q a N : ℕ} (hq : 0 < q) (ha : a < q)
    (hsq : Squarefree (Nat.gcd a q)) :
    (∑ n ∈ ((Finset.Icc 1 N).filter (fun n => n % q = a)).filter
      (fun n => Nat.Coprime (n / Nat.gcd a q) q),
      (ArithmeticFunction.moebius n : ℝ)) =
    (ArithmeticFunction.moebius (Nat.gcd a q) : ℝ) *
      (∑ b ∈ mobiusResidueUnitRemainders q a,
        ∑ m ∈ Finset.Icc 1 (N / Nat.gcd a q),
          if m % q = b then (ArithmeticFunction.moebius m : ℝ) else 0) := by
  classical
  let g := Nat.gcd a q
  let B := mobiusResidueUnitRemainders q a
  let S := ((Finset.Icc 1 N).filter (fun n => n % q = a)).filter
    (fun n => Nat.Coprime (n / g) q)
  let T := B.sigma (fun b => (Finset.Icc 1 (N / g)).filter (fun m => m % q = b))
  have hgpos : 0 < g := gcd_pos_of_modulus_pos hq
  have hq₀dvd : q / g ∣ q := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a q)
  have hmulSum :
      (∑ n ∈ S, (ArithmeticFunction.moebius n : ℝ)) =
        ∑ n ∈ S, (ArithmeticFunction.moebius g : ℝ) *
          (ArithmeticFunction.moebius (n / g) : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnres, hcop⟩
    have hres := (Finset.mem_filter.mp hnres).2
    have hgdiv : g ∣ n := gcd_dvd_of_residue hres
    have hmul : n = g * (n / g) := by
      calc
        n = (n / g) * g := (Nat.div_mul_cancel hgdiv).symm
        _ = g * (n / g) := Nat.mul_comm _ _
    have hmg : Nat.Coprime (n / g) g :=
      Nat.Coprime.of_dvd_right (Nat.gcd_dvd_right a q) hcop
    have hμmul : (ArithmeticFunction.moebius (g * (n / g)) : ℝ) =
        (ArithmeticFunction.moebius g : ℝ) *
          (ArithmeticFunction.moebius (n / g) : ℝ) := by
      have hμ := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_moebius hmg.symm
      simpa only [Int.cast_mul, ArithmeticFunction.intCoe_apply] using
        congrArg (fun z : ℤ => (z : ℝ)) hμ
    conv_lhs => rw [hmul]
    exact hμmul
  have hsumBij :
      (∑ n ∈ S, (ArithmeticFunction.moebius g : ℝ) *
          (ArithmeticFunction.moebius (n / g) : ℝ)) =
        ∑ x ∈ T, (ArithmeticFunction.moebius g : ℝ) *
          (ArithmeticFunction.moebius x.2 : ℝ) := by
    refine Finset.sum_bij (fun n _ => ⟨n / g % q, n / g⟩) ?_ ?_ ?_ ?_
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnres, hnunit⟩
      rcases Finset.mem_filter.mp hnres with ⟨hnI, hres⟩
      have hgdiv : g ∣ n := gcd_dvd_of_residue hres
      have hmul : n = g * (n / g) := by
        calc
          n = (n / g) * g := (Nat.div_mul_cancel hgdiv).symm
          _ = g * (n / g) := Nat.mul_comm _ _
      have hred := (residue_div_gcd_iff hq ha hgdiv).mp hres
      have hbmem : n / g % q ∈ B := by
        simp only [B, mobiusResidueUnitRemainders, Finset.mem_filter,
          Finset.mem_range]
        refine ⟨Nat.mod_lt _ hq, ?_, ?_⟩
        · rw [ZMod.coprime_mod_iff_coprime]
          exact hnunit
        · rw [Nat.mod_mod_of_dvd _ hq₀dvd]
          exact hred
      have hnI' := Finset.mem_Icc.mp hnI
      have hg_le_n : g ≤ n := Nat.le_of_dvd hnI'.1 hgdiv
      have hmpos : 0 < n / g := Nat.div_pos hg_le_n hgpos
      have hmle : n / g ≤ N / g := by
        apply (Nat.le_div_iff_mul_le hgpos).2
        calc
          (n / g) * g = n := Nat.div_mul_cancel hgdiv
          _ ≤ N := hnI'.2
      exact Finset.mem_sigma.mpr ⟨hbmem,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmpos, hmle⟩, rfl⟩⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      have hm : n₁ / g = n₂ / g := congrArg Sigma.snd heq
      have hres₁ := (Finset.mem_filter.mp (Finset.mem_filter.mp hn₁).1).2
      have hres₂ := (Finset.mem_filter.mp (Finset.mem_filter.mp hn₂).1).2
      have hd₁ : g ∣ n₁ := gcd_dvd_of_residue hres₁
      have hd₂ : g ∣ n₂ := gcd_dvd_of_residue hres₂
      have hn₁' : n₁ = g * (n₁ / g) := by
        calc
          n₁ = (n₁ / g) * g := (Nat.div_mul_cancel hd₁).symm
          _ = g * (n₁ / g) := Nat.mul_comm _ _
      have hn₂' : n₂ = g * (n₂ / g) := by
        calc
          n₂ = (n₂ / g) * g := (Nat.div_mul_cancel hd₂).symm
          _ = g * (n₂ / g) := Nat.mul_comm _ _
      rw [hn₁', hn₂', hm]
    · intro x hx
      rcases Finset.mem_sigma.mp hx with ⟨hb, hm⟩
      rcases Finset.mem_filter.mp hm with ⟨hmI, hmb⟩
      have hb' : Nat.Coprime x.1 q ∧ x.1 % (q / g) = a / g := by
        simpa [B, mobiusResidueUnitRemainders, g] using
          (Finset.mem_filter.mp hb).2
      have hmred : x.2 % (q / g) = a / g := by
        calc
          x.2 % (q / g) = (x.2 % q) % (q / g) :=
            (Nat.mod_mod_of_dvd x.2 hq₀dvd).symm
          _ = x.1 % (q / g) := by rw [hmb]
          _ = a / g := hb'.2
      have hmq : Nat.Coprime x.2 q := by
        rw [← ZMod.coprime_mod_iff_coprime]
        simpa [hmb] using hb'.1
      have hdiv : g ∣ g * x.2 := ⟨x.2, by simp⟩
      have hquot : (g * x.2) / g = x.2 := by
        calc
          (g * x.2) / g = (x.2 * g) / g := by rw [Nat.mul_comm]
          _ = x.2 := Nat.mul_div_left _ hgpos
      have hnres : (g * x.2) % q = a := by
        apply (residue_div_gcd_iff hq ha hdiv).2
        change ((g * x.2) / g) % (q / g) = a / g
        rw [hquot]
        exact hmred
      have hnI' := Finset.mem_Icc.mp hmI
      have hmul_le : g * x.2 ≤ N := by
        have h := (Nat.le_div_iff_mul_le hgpos).mp hnI'.2
        simpa [Nat.mul_comm] using h
      have hnI : g * x.2 ∈ Finset.Icc 1 N :=
        Finset.mem_Icc.mpr ⟨Nat.mul_pos hgpos hnI'.1, hmul_le⟩
      have hnunit : Nat.Coprime ((g * x.2) / g) q := by
        rw [hquot]
        exact hmq
      have hnS : g * x.2 ∈ S := by
        change g * x.2 ∈
          ((Finset.Icc 1 N).filter (fun n => n % q = a)).filter
            (fun n => Nat.Coprime (n / g) q)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hnI, hnres⟩, hnunit⟩
      refine ⟨g * x.2, hnS, ?_⟩
      apply Sigma.ext
      · simp [hquot, hnres, hmb]
      · simp [hquot]
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnres, hnunit⟩
      have hres := (Finset.mem_filter.mp hnres).2
      have hgdiv : g ∣ n := gcd_dvd_of_residue hres
      have hmul : n = g * (n / g) := by
        calc
          n = (n / g) * g := (Nat.div_mul_cancel hgdiv).symm
          _ = g * (n / g) := Nat.mul_comm _ _
      rw [hmul]
  have htarget :
      (∑ x ∈ T, (ArithmeticFunction.moebius g : ℝ) *
          (ArithmeticFunction.moebius x.2 : ℝ)) =
        (ArithmeticFunction.moebius g : ℝ) *
          (∑ b ∈ B, ∑ m ∈ Finset.Icc 1 (N / g),
            if m % q = b then (ArithmeticFunction.moebius m : ℝ) else 0) := by
    dsimp [T]
    rw [Finset.sum_sigma]
    simp only [Finset.sum_filter]
    calc
      (∑ b ∈ B, ∑ m ∈ Finset.Icc 1 (N / g),
        if m % q = b then (ArithmeticFunction.moebius g : ℝ) *
          (ArithmeticFunction.moebius m : ℝ) else 0) =
        ∑ b ∈ B, (ArithmeticFunction.moebius g : ℝ) *
          (∑ m ∈ Finset.Icc 1 (N / g),
            if m % q = b then (ArithmeticFunction.moebius m : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro b hb
            calc
              (∑ m ∈ Finset.Icc 1 (N / g),
                if m % q = b then (ArithmeticFunction.moebius g : ℝ) *
                  (ArithmeticFunction.moebius m : ℝ) else 0) =
                  ∑ m ∈ Finset.Icc 1 (N / g),
                    (ArithmeticFunction.moebius g : ℝ) *
                      (if m % q = b then (ArithmeticFunction.moebius m : ℝ) else 0) := by
                apply Finset.sum_congr rfl
                intro m hm
                by_cases h : m % q = b <;> simp [h]
              _ = (ArithmeticFunction.moebius g : ℝ) *
                    (∑ m ∈ Finset.Icc 1 (N / g),
                      if m % q = b then (ArithmeticFunction.moebius m : ℝ) else 0) := by
                rw [Finset.mul_sum]
      _ = (ArithmeticFunction.moebius g : ℝ) *
          (∑ b ∈ B, ∑ m ∈ Finset.Icc 1 (N / g),
            if m % q = b then (ArithmeticFunction.moebius m : ℝ) else 0) := by
            rw [← Finset.mul_sum]
  calc
    _ = ∑ n ∈ S, (ArithmeticFunction.moebius n : ℝ) := rfl
    _ = ∑ n ∈ S, (ArithmeticFunction.moebius g : ℝ) *
          (ArithmeticFunction.moebius (n / g) : ℝ) := hmulSum
    _ = ∑ x ∈ T, (ArithmeticFunction.moebius g : ℝ) *
          (ArithmeticFunction.moebius x.2 : ℝ) := hsumBij
    _ = (ArithmeticFunction.moebius g : ℝ) *
          (∑ b ∈ B, ∑ m ∈ Finset.Icc 1 (N / g),
            if m % q = b then (ArithmeticFunction.moebius m : ℝ) else 0) := htarget

/-- Exact Möbius reduction for a nonunit residue class.  In the squarefree
case, the sum is the Möbius value of the gcd times the sum of the unit classes
whose representatives lift `a / gcd(a,q)` modulo `q / gcd(a,q)`.  The set of
such unit representatives has cardinality at most the gcd.  The statement
includes `a = 0` and `q = 1` whenever `0 ≤ a < q`.
-/
theorem mobiusResidueUnitReduction {q a : ℕ} (hq : 0 < q) (ha : a < q)
    (Y : ℝ) (hY : 1 ≤ Y) :
    (¬ Squarefree (Nat.gcd a q) → mobiusResidueSumReal q a Y = 0) ∧
    (Squarefree (Nat.gcd a q) →
      (mobiusResidueUnitRemainders q a).card ≤ Nat.gcd a q ∧
        mobiusResidueSumReal q a Y =
          (ArithmeticFunction.moebius (Nat.gcd a q) : ℝ) *
            (∑ b ∈ mobiusResidueUnitRemainders q a,
              mobiusResidueSumReal q b (Y / (Nat.gcd a q : ℝ)))) := by
  constructor
  · intro hnot
    rw [mobiusResidueSumReal, mobiusResidueSumNat]
    apply Finset.sum_eq_zero
    intro n hn
    by_cases hres : n % q = a
    · have hgdiv : Nat.gcd a q ∣ n := by
        have hnexp : n = n % q + q * (n / q) :=
          (Nat.mod_add_div n q).symm
        rw [hres] at hnexp
        rw [hnexp]
        exact Nat.dvd_add (Nat.gcd_dvd_left a q)
          (dvd_mul_of_dvd_left (Nat.gcd_dvd_right a q) _)
      have hnsq : ¬ Squarefree n := by
        intro hn
        exact hnot (hn.squarefree_of_dvd hgdiv)
      simp [hres, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
    · simp [hres]
  · intro hsq
    have hcard := mobiusResidueUnitRemainders_card_le hq ha
    let N := Nat.floor Y
    have hsum : mobiusResidueSumNat q a N =
        (ArithmeticFunction.moebius (Nat.gcd a q) : ℝ) *
          (∑ b ∈ mobiusResidueUnitRemainders q a,
            mobiusResidueSumNat q b (N / Nat.gcd a q)) := by
      calc
        mobiusResidueSumNat q a N =
            ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = a),
              (ArithmeticFunction.moebius n : ℝ) :=
          mobiusResidueSumNat_eq_filtered q a N
        _ = ∑ n ∈ ((Finset.Icc 1 N).filter (fun n => n % q = a)).filter
              (fun n => Nat.Coprime (n / Nat.gcd a q) q),
              (ArithmeticFunction.moebius n : ℝ) :=
          mobiusResidueFilteredSum_drop_nonunit hq ha hsq
        _ = (ArithmeticFunction.moebius (Nat.gcd a q) : ℝ) *
              (∑ b ∈ mobiusResidueUnitRemainders q a,
                ∑ m ∈ Finset.Icc 1 (N / Nat.gcd a q),
                  if m % q = b then (ArithmeticFunction.moebius m : ℝ) else 0) :=
          mobiusResidueUnitRemainders_sum_bij hq ha hsq
        _ = (ArithmeticFunction.moebius (Nat.gcd a q) : ℝ) *
              (∑ b ∈ mobiusResidueUnitRemainders q a,
                mobiusResidueSumNat q b (N / Nat.gcd a q)) := by
          simp [mobiusResidueSumNat]
    -- The real cutoff on the reduced side is exactly the natural quotient
    -- of `floor Y`, by Mathlib's floor-of-division identity.
    have hfloor : Nat.floor (Y / (Nat.gcd a q : ℝ)) =
        Nat.floor Y / Nat.gcd a q := by
      rw [Nat.floor_div_natCast]
    simp only [mobiusResidueSumReal, hfloor]
    exact ⟨hcard, hsum⟩

#print axioms mobiusResidueUnitReduction

end FractionalPrimes.Literature.LongArithmetic
