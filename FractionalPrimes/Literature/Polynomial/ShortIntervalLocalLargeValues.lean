module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalNaturalKernelTransfer
public import FractionalPrimes.Literature.Polynomial.ShortIntervalLargeValueDualCauchy
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The exact local large-values estimate `lgv:local-large-values`, following
the finite Cauchy--Schwarz, Gram-kernel, and separated-point packing proof.

Blueprint: `expanded-blueprint.tex:5527-5562`.
Astra: `blueprint-sources 2/literature-expansion/sections/dirichlet-large-values.tex:122-156`.
-/

@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.LargeValues

open FractionalPrimes
open scoped BigOperators
open scoped ComplexConjugate

private lemma reciprocal_le_log_ratio (k : ℕ) (hk : 0 < k) :
    (1 : ℝ) / ((k : ℝ) + 1) ≤ Real.log (((k : ℝ) + 1) / k) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hkR hk1)
  rw [Real.log_div hkR.ne' hk1.ne'] at h
  have hratio : ((k : ℝ) / ((k : ℝ) + 1)) - 1 =
      -(1 / ((k : ℝ) + 1)) := by field_simp <;> ring
  rw [Real.log_div hk1.ne' hkR.ne']
  linarith

private lemma shifted_harmonic_sum_le_log (m : ℕ) :
    (∑ k ∈ Finset.range m, (1 : ℝ) / ((k : ℝ) + 2)) ≤
      Real.log ((m + 1 : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hmpos : 0 < m + 1 := by omega
      have hstep := reciprocal_le_log_ratio (m + 1) hmpos
      have hcast1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
        push_cast
        ring
      have hcast2 : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by
        rw [hcast1]
        ring
      have hlogratio :
          Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) =
            Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1) := by
        rw [Real.log_div (by positivity) (by positivity)]
      have hstep' :
          (1 : ℝ) / ((m : ℝ) + 2) ≤
            Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) := by
        rw [← hcast2, ← hcast1]
        exact hstep
      calc
        (∑ k ∈ Finset.range m, (1 : ℝ) / ((k : ℝ) + 2)) +
            (1 : ℝ) / ((m : ℝ) + 2) ≤
          Real.log ((m + 1 : ℕ) : ℝ) +
            Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) := add_le_add ih hstep'
        _ = Real.log ((m + 2 : ℕ) : ℝ) := by
          rw [hlogratio]
          rw [hcast1]
          have hcast3 : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by
            push_cast
            ring
          rw [hcast3]
          ring

private lemma separated_reciprocal_sum_shifted
    (b : ℕ) (S : Finset ℝ)
    (hb : ∀ x ∈ S, (b : ℝ) ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    (∑ x ∈ S, (1 : ℝ) / (1 + x)) ≤
      ∑ k ∈ Finset.range S.card, (1 : ℝ) / (1 + ((b + k : ℕ) : ℝ)) := by
  classical
  revert b hb hsep
  let P : Finset ℝ → Prop := fun S =>
    ∀ (b : ℕ), (∀ x ∈ S, (b : ℝ) ≤ x) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
        (∑ x ∈ S, (1 : ℝ) / (1 + x)) ≤
          ∑ k ∈ Finset.range S.card, (1 : ℝ) / (1 + ((b + k : ℕ) : ℝ))
  change P S
  refine Finset.strongInductionOn S ?_
  intro S ih b hb hsep
  by_cases hS : S.Nonempty
  · let x₀ := S.min' hS
    have hx₀mem : x₀ ∈ S := by simpa [x₀] using Finset.min'_mem S hS
    have hx₀lower : (b : ℝ) ≤ x₀ := hb x₀ hx₀mem
    have htail : S.erase x₀ ⊂ S := Finset.erase_ssubset hx₀mem
    have htailBound : ∀ x ∈ S.erase x₀, ((b + 1 : ℕ) : ℝ) ≤ x := by
      intro x hx
      have hxS : x ∈ S := (Finset.mem_erase.mp hx).2
      have hne : x₀ ≠ x := ((Finset.mem_erase.mp hx).1).symm
      have hx₀x : x₀ ≤ x := Finset.min'_le S x hxS
      have hgap := hsep x₀ hx₀mem x hxS hne
      have hdist : |x₀ - x| = x - x₀ := by
        rw [abs_of_nonpos (sub_nonpos.mpr hx₀x)]
        ring
      rw [hdist] at hgap
      exact_mod_cast (by nlinarith : (b : ℝ) + 1 ≤ x)
    have htailSep : ∀ x ∈ S.erase x₀, ∀ y ∈ S.erase x₀,
        x ≠ y → 1 ≤ |x - y| := by
      intro x hx y hy hxy
      exact hsep x ((Finset.mem_erase.mp hx).2)
        y ((Finset.mem_erase.mp hy).2) hxy
    have hind := ih (S.erase x₀) htail (b + 1) htailBound htailSep
    have hmain : (1 : ℝ) / (1 + x₀) ≤ 1 / (1 + (b : ℝ)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith [hx₀lower]
    have hsumErase :
        (∑ x ∈ S, (1 : ℝ) / (1 + x)) =
          (1 : ℝ) / (1 + x₀) +
            ∑ x ∈ S.erase x₀, (1 : ℝ) / (1 + x) := by
      calc
        (∑ x ∈ S, (1 : ℝ) / (1 + x)) =
            (∑ x ∈ S.erase x₀, (1 : ℝ) / (1 + x)) +
              (1 : ℝ) / (1 + x₀) :=
          (Finset.sum_erase_add S (fun x => (1 : ℝ) / (1 + x)) hx₀mem).symm
        _ = (1 : ℝ) / (1 + x₀) +
            ∑ x ∈ S.erase x₀, (1 : ℝ) / (1 + x) := add_comm _ _
    have hcardErase : (S.erase x₀).card + 1 = S.card := by
      rw [Finset.card_erase_of_mem hx₀mem]
      exact Nat.sub_add_cancel (Finset.one_le_card.mpr hS)
    have hsumRight :
        (∑ k ∈ Finset.range S.card, (1 : ℝ) /
            (1 + ((b + k : ℕ) : ℝ))) =
          1 / (1 + (b : ℝ)) +
            ∑ k ∈ Finset.range (S.erase x₀).card,
              (1 : ℝ) / (1 + (((b + 1) + k : ℕ) : ℝ)) := by
      rw [← hcardErase, Finset.sum_range_succ']
      simp only [Nat.cast_zero, Nat.add_zero]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      congr 2
      exact_mod_cast (show b + (k + 1) = (b + 1) + k by omega)
    calc
      (∑ x ∈ S, (1 : ℝ) / (1 + x)) =
          (1 : ℝ) / (1 + x₀) +
            ∑ x ∈ S.erase x₀, (1 : ℝ) / (1 + x) := hsumErase
      _ ≤ 1 / (1 + (b : ℝ)) +
            ∑ k ∈ Finset.range (S.erase x₀).card,
              (1 : ℝ) / (1 + (((b + 1) + k : ℕ) : ℝ)) :=
        add_le_add hmain hind
      _ = ∑ k ∈ Finset.range S.card, (1 : ℝ) /
            (1 + ((b + k : ℕ) : ℝ)) := hsumRight.symm
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

private lemma separated_reciprocal_sum_le_log
    (S : Finset ℝ)
    (hpos : ∀ x ∈ S, (1 : ℝ) ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    (∑ x ∈ S, (1 : ℝ) / (1 + x)) ≤ Real.log ((S.card + 1 : ℕ) : ℝ) := by
  calc
    (∑ x ∈ S, (1 : ℝ) / (1 + x)) ≤
        ∑ k ∈ Finset.range S.card, (1 : ℝ) / (1 + ((1 + k : ℕ) : ℝ)) :=
      separated_reciprocal_sum_shifted 1 S (by simpa using hpos) hsep
    _ = ∑ k ∈ Finset.range S.card, (1 : ℝ) / ((k : ℝ) + 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hden : (1 : ℝ) + ((1 + k : ℕ) : ℝ) = (k : ℝ) + 2 := by
        push_cast
        ring
      rw [hden]
    _ ≤ Real.log ((S.card + 1 : ℕ) : ℝ) := shifted_harmonic_sum_le_log S.card

private lemma side_reciprocal_sum_le_log
    {R : ℕ} (t : Fin R → ℝ) (i : Fin R) (S : Finset (Fin R))
    (hsep : ∀ j k, j ≠ k → 1 ≤ |t j - t k|)
    (hside : ∀ j ∈ S, t j < t i)
    (hcard : S.card + 1 ≤ R) :
    (∑ j ∈ S, (1 : ℝ) / (1 + |t i - t j|)) ≤ Real.log (R : ℝ) := by
  classical
  let d : Fin R → ℝ := fun j => t i - t j
  let D : Finset ℝ := S.image d
  have hinj : Set.InjOn d (↑S) := by
    intro j hj k hk hjk
    have ht : t j = t k := by dsimp [d] at hjk; linarith
    apply Fin.ext
    by_contra hne
    have hjk' : j ≠ k := by
      intro h
      exact hne (congrArg Fin.val h)
    have hgap := hsep j k hjk'
    simp [ht] at hgap
    norm_num at hgap
  have hsumImage :
      (∑ x ∈ D, (1 : ℝ) / (1 + x)) =
        ∑ j ∈ S, (1 : ℝ) / (1 + d j) := by
    dsimp [D, d]
    exact Finset.sum_image hinj
  have hpos : ∀ x ∈ D, (1 : ℝ) ≤ x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    have hji : j ≠ i := by
      intro h
      have := hside j hj
      simpa [h] using this
    have hgap := hsep j i hji
    have hdist : |t j - t i| = t i - t j := by
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt (hside j hj)))]
      ring
    dsimp [d]
    rw [← hdist]
    exact hgap
  have hsepD : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → 1 ≤ |x - y| := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨k, hk, rfl⟩
    have hjk : j ≠ k := by
      intro h
      apply hxy
      simp [d, h]
    have hgap := hsep j k hjk
    have hdist : |(t i - t j) - (t i - t k)| = |t j - t k| := by
      rw [show (t i - t j) - (t i - t k) = -(t j - t k) by ring, abs_neg]
    rw [hdist]
    exact hgap
  have hsumSource :
      (∑ j ∈ S, (1 : ℝ) / (1 + |t i - t j|)) =
        ∑ x ∈ D, (1 : ℝ) / (1 + x) := by
    calc
      (∑ j ∈ S, (1 : ℝ) / (1 + |t i - t j|)) =
          ∑ j ∈ S, (1 : ℝ) / (1 + d j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hdist : |t i - t j| = t i - t j :=
          abs_of_nonneg (sub_nonneg.mpr (le_of_lt (hside j hj)))
        simp only [d, hdist]
      _ = ∑ x ∈ D, (1 : ℝ) / (1 + x) := hsumImage.symm
  have hlogD :
      (∑ x ∈ D, (1 : ℝ) / (1 + x)) ≤ Real.log ((D.card + 1 : ℕ) : ℝ) :=
    separated_reciprocal_sum_le_log D hpos hsepD
  have hcardD : D.card + 1 ≤ R := by
    rw [Finset.card_image_of_injOn hinj]
    exact hcard
  have hcastD : ((D.card + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hcardD
  have hDpos : 0 < ((D.card + 1 : ℕ) : ℝ) := by positivity
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (by omega : 1 ≤ R))
  calc
    (∑ j ∈ S, (1 : ℝ) / (1 + |t i - t j|)) =
        ∑ x ∈ D, (1 : ℝ) / (1 + x) := hsumSource
    _ ≤ Real.log ((D.card + 1 : ℕ) : ℝ) := hlogD
    _ ≤ Real.log (R : ℝ) := Real.log_le_log hDpos hcastD

private lemma separated_reciprocal_row
    {R : ℕ} (t : Fin R → ℝ) (i : Fin R)
    (hR : 1 ≤ R)
    (hsep : ∀ j k, j ≠ k → 1 ≤ |t j - t k|) :
    (∑ j : Fin R, (1 : ℝ) / (1 + |t i - t j|)) ≤
      1 + 2 * Real.log (R : ℝ) := by
  classical
  let off : Finset (Fin R) := Finset.univ.erase i
  let left : Finset (Fin R) := off.filter (fun j => t j < t i)
  let right : Finset (Fin R) := off.filter (fun j => t i < t j)
  let f : Fin R → ℝ := fun j => (1 : ℝ) / (1 + |t i - t j|)
  have hcardOff : off.card + 1 = R := by
    dsimp [off]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have hcardLeft : left.card + 1 ≤ R := by
    calc
      left.card + 1 ≤ off.card + 1 := Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) 1
      _ = R := hcardOff
  have hcardRight : right.card + 1 ≤ R := by
    calc
      right.card + 1 ≤ off.card + 1 := Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) 1
      _ = R := hcardOff
  have hnotLeft : off.filter (fun j => ¬ t j < t i) = right := by
    calc
      off.filter (fun j => ¬ t j < t i) =
          off.filter (fun j => t i < t j) := by
        apply Finset.filter_congr
        intro j hj
        have hji : j ≠ i := by simpa [off] using hj
        have hneq : t j ≠ t i := by
          intro heq
          have hgap := hsep j i hji
          rw [heq] at hgap
          norm_num at hgap
        constructor
        · intro hjnot
          exact lt_of_le_of_ne (le_of_not_gt hjnot) hneq.symm
        · intro hgt
          exact not_lt.mpr hgt.le
      _ = right := rfl
  have hsplitOff :
      (∑ j ∈ off, f j) =
        (∑ j ∈ left, f j) + ∑ j ∈ right, f j := by
    calc
      (∑ j ∈ off, f j) =
          (∑ j ∈ left, f j) +
            ∑ j ∈ off.filter (fun j => ¬ t j < t i), f j := by
        dsimp [left]
        exact (Finset.sum_filter_add_sum_filter_not off
          (fun j => t j < t i) f).symm
      _ = (∑ j ∈ left, f j) + ∑ j ∈ right, f j := by rw [hnotLeft]
  have hleft := side_reciprocal_sum_le_log t i left hsep
    (by intro j hj; exact (Finset.mem_filter.mp hj).2) hcardLeft
  let tneg : Fin R → ℝ := fun j => -t j
  have hsepNeg : ∀ j k, j ≠ k → 1 ≤ |tneg j - tneg k| := by
    intro j k hjk
    have hgap := hsep j k hjk
    have hdist : |tneg j - tneg k| = |t j - t k| := by
      dsimp [tneg]
      rw [show -t j - -t k = -(t j - t k) by ring, abs_neg]
    rw [hdist]
    exact hgap
  have hright := side_reciprocal_sum_le_log tneg i right hsepNeg
    (by
      intro j hj
      have hlt := (Finset.mem_filter.mp hj).2
      dsimp [tneg]
      linarith)
    hcardRight
  have hsplitUniv :
      (∑ j : Fin R, f j) = f i + ∑ j ∈ off, f j := by
    calc
      (∑ j : Fin R, f j) = (∑ j ∈ off, f j) + f i :=
        (Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)).symm
      _ = f i + ∑ j ∈ off, f j := add_comm _ _
  change (∑ j : Fin R, f j) ≤ 1 + 2 * Real.log (R : ℝ)
  have hleft' : (∑ j ∈ left, f j) ≤ Real.log (R : ℝ) := by
    simpa [f] using hleft
  have hright' : (∑ j ∈ right, f j) ≤ Real.log (R : ℝ) := by
    calc
      (∑ j ∈ right, f j) =
          ∑ j ∈ right, (1 : ℝ) / (1 + |tneg i - tneg j|) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        dsimp [tneg]
        rw [show -t i - -t j = -(t i - t j) by ring, abs_neg]
      _ ≤ Real.log (R : ℝ) := hright
  have hfi : f i = 1 := by simp [f]
  calc
    (∑ j : Fin R, f j) = f i + (∑ j ∈ left, f j) + ∑ j ∈ right, f j := by
      rw [hsplitUniv, hsplitOff]
      ring
    _ ≤ 1 + 2 * Real.log (R : ℝ) := by rw [hfi]; linarith

private lemma normSq_sum_expand_fin {R : ℕ} (f : Fin R → ℂ) :
    Complex.normSq (∑ i : Fin R, f i) =
      ∑ i : Fin R, ∑ j : Fin R, (conj (f i) * f j).re := by
  classical
  have hcomplex :
      conj (∑ i : Fin R, f i) * ∑ i : Fin R, f i =
        ∑ i : Fin R, ∑ j : Fin R, conj (f i) * f j := by
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  calc
    Complex.normSq (∑ i : Fin R, f i) =
        (conj (∑ i : Fin R, f i) * ∑ i : Fin R, f i).re := by
      have h := congrArg Complex.re
        (Complex.normSq_eq_conj_mul_self (z := ∑ i : Fin R, f i))
      simpa using h
    _ = (∑ i : Fin R, ∑ j : Fin R, conj (f i) * f j).re := by rw [hcomplex]
    _ = ∑ i : Fin R, ∑ j : Fin R, (conj (f i) * f j).re := by
      rw [Complex.re_sum]
      simp_rw [Complex.re_sum]

private def dualPhaseTerm {R : ℕ} (t : Fin R → ℝ) (c : Fin R → ℂ)
    (n : ℕ) (j : Fin R) : ℂ :=
  c j * Complex.exp (-Complex.I * (t j : ℂ) * (Real.log (n : ℝ) : ℂ))

private lemma exp_phase_difference (x y z : ℝ) :
    conj (Complex.exp (-Complex.I * (x : ℂ) * (z : ℂ))) *
      Complex.exp (-Complex.I * (y : ℂ) * (z : ℂ)) =
        Complex.exp (Complex.I * ((x - y : ℝ) : ℂ) * (z : ℂ)) := by
  rw [← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_neg]
  calc
    _ = Complex.exp (Complex.I * (x : ℂ) * (z : ℂ)) *
        Complex.exp (-Complex.I * (y : ℂ) * (z : ℂ)) := by ring
    _ = Complex.exp (Complex.I * (x : ℂ) * (z : ℂ) +
        -Complex.I * (y : ℂ) * (z : ℂ)) := by rw [← Complex.exp_add]
    _ = Complex.exp (Complex.I * ((x - y : ℝ) : ℂ) * (z : ℂ)) := by
      congr 1
      push_cast
      ring

private lemma dualGramEntryBound
    {R : ℕ} (N : ℝ) (t : Fin R → ℝ) (c : Fin R → ℂ)
    (hN : 2 ≤ N) (hunit : ∀ j, ‖c j‖ = 1) (i j : Fin R) :
    (∑ n ∈ dirichletIndices N,
      (conj (dualPhaseTerm t c n i) * dualPhaseTerm t c n j).re) ≤
        64 * (N / (1 + |t i - t j|) + Real.sqrt |t i - t j|) := by
  classical
  let q : ℂ := conj (c i) * c j
  let e : ℕ → ℂ := fun n =>
    Complex.exp (Complex.I * ((t i - t j : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ))
  have hterm (n : ℕ) :
      conj (dualPhaseTerm t c n i) * dualPhaseTerm t c n j = q * e n := by
    dsimp [dualPhaseTerm, q, e]
    calc
      _ = (conj (c i) * c j) *
          (conj (Complex.exp (-Complex.I * (t i : ℂ) *
            (Real.log (n : ℝ) : ℂ))) *
            Complex.exp (-Complex.I * (t j : ℂ) *
              (Real.log (n : ℝ) : ℂ))) := by
        simp only [map_mul]
        ring
      _ = (conj (c i) * c j) *
          Complex.exp (Complex.I * ((t i - t j : ℝ) : ℂ) *
            (Real.log (n : ℝ) : ℂ)) := by rw [exp_phase_difference]
      _ = q * e n := rfl
  have hsum :
      (∑ n ∈ dirichletIndices N,
        (conj (dualPhaseTerm t c n i) * dualPhaseTerm t c n j).re) =
          (q * ∑ n ∈ dirichletIndices N, e n).re := by
    simp_rw [hterm]
    rw [← Complex.re_sum, ← Finset.mul_sum]
  have hq : ‖q‖ = 1 := by
    dsimp [q]
    rw [norm_mul, RCLike.norm_conj, hunit i, hunit j]
    norm_num
  have hkernel := gramKernelBound_nat N (t i - t j) hN
  calc
    (∑ n ∈ dirichletIndices N,
      (conj (dualPhaseTerm t c n i) * dualPhaseTerm t c n j).re) =
        (q * ∑ n ∈ dirichletIndices N, e n).re := hsum
    _ ≤ ‖q * ∑ n ∈ dirichletIndices N, e n‖ := Complex.re_le_norm _
    _ = ‖∑ n ∈ dirichletIndices N, e n‖ := by rw [norm_mul, hq, one_mul]
    _ ≤ 64 * (N / (1 + |t i - t j|) + Real.sqrt |t i - t j|) := by
      simpa [e] using hkernel

private lemma dualExponentialSquareSum_bound
    {R : ℕ} (N : ℝ) (t : Fin R → ℝ) (c : Fin R → ℂ)
    (hN : 2 ≤ N) (hunit : ∀ j, ‖c j‖ = 1) :
    (∑ n ∈ dirichletIndices N,
      ‖∑ j : Fin R, dualPhaseTerm t c n j‖ ^ 2) ≤
        ∑ i : Fin R, ∑ j : Fin R,
          64 * (N / (1 + |t i - t j|) + Real.sqrt |t i - t j|) := by
  classical
  let pair (n : ℕ) (i j : Fin R) :=
    (conj (dualPhaseTerm t c n i) * dualPhaseTerm t c n j).re
  have hexpand :
      (∑ n ∈ dirichletIndices N,
        ‖∑ j : Fin R, dualPhaseTerm t c n j‖ ^ 2) =
          ∑ n ∈ dirichletIndices N, ∑ i : Fin R, ∑ j : Fin R, pair n i j := by
    apply Finset.sum_congr rfl
    intro n hn
    calc
      ‖∑ j : Fin R, dualPhaseTerm t c n j‖ ^ 2 =
          Complex.normSq (∑ j : Fin R, dualPhaseTerm t c n j) :=
        (Complex.normSq_eq_norm_sq _).symm
      _ = ∑ i : Fin R, ∑ j : Fin R, pair n i j := by
        simpa [pair] using normSq_sum_expand_fin (fun j => dualPhaseTerm t c n j)
  have hswap :
      (∑ n ∈ dirichletIndices N, ∑ i : Fin R, ∑ j : Fin R, pair n i j) =
        ∑ i : Fin R, ∑ j : Fin R,
          ∑ n ∈ dirichletIndices N, pair n i j := by
    calc
      _ = ∑ i : Fin R, ∑ n ∈ dirichletIndices N, ∑ j : Fin R, pair n i j := by
        rw [Finset.sum_comm]
      _ = ∑ i : Fin R, ∑ j : Fin R,
          ∑ n ∈ dirichletIndices N, pair n i j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
  calc
    (∑ n ∈ dirichletIndices N,
      ‖∑ j : Fin R, dualPhaseTerm t c n j‖ ^ 2) =
        ∑ i : Fin R, ∑ j : Fin R,
          ∑ n ∈ dirichletIndices N, pair n i j := by rw [hexpand, hswap]
    _ ≤ ∑ i : Fin R, ∑ j : Fin R,
          64 * (N / (1 + |t i - t j|) + Real.sqrt |t i - t j|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simpa [pair] using dualGramEntryBound N t c hN hunit i j

private lemma phaseCompensator (z : ℂ) (hz : z ≠ 0) :
    (conj z / (‖z‖ : ℂ)) * z = (‖z‖ : ℂ) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hprod : conj z * z = ((‖z‖ : ℝ) ^ 2 : ℂ) := by
    calc
      conj z * z = z * conj z := by ring
      _ = (Complex.normSq z : ℂ) := Complex.mul_conj z
      _ = ((‖z‖ : ℝ) ^ 2 : ℂ) := by exact_mod_cast Complex.normSq_eq_norm_sq z
  calc
    (conj z / (‖z‖ : ℂ)) * z = (conj z * z) / (‖z‖ : ℂ) := by ring
    _ = ((‖z‖ : ℝ) ^ 2 : ℂ) / (‖z‖ : ℂ) := by rw [hprod]
    _ = (‖z‖ : ℂ) := by
      have hnC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp

private lemma phaseCompensator_norm (z : ℂ) (hz : z ≠ 0) :
    ‖conj z / (‖z‖ : ℂ)‖ = 1 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg z), div_self hn.ne']

/-- The finite local large-values estimate `lgv:local-large-values`. -/
theorem localLargeValueBound
    (N u S V : ℝ) (a : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ)
    (hN : 2 ≤ N) (hR : 1 ≤ R) (hV : 0 < V) (_hS : 0 ≤ S)
    (hG : 0 < dirichletEnergy N a)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|)
    (htime : ∀ j, u ≤ t j ∧ t j ≤ u + S)
    (hlarge : ∀ j, V ≤ ‖dirichletPolynomial N a (t j)‖)
    (hshort : Real.sqrt S ≤ V ^ 2 / (128 * dirichletEnergy N a)) :
    (R : ℝ) ≤
      128 * N * dirichletEnergy N a / V ^ 2 * (1 + 2 * Real.log (R : ℝ)) := by
  classical
  let c : Fin R → ℂ := fun j =>
    conj (dirichletPolynomial N a (t j)) /
      (‖dirichletPolynomial N a (t j)‖ : ℂ)
  have hDne (j : Fin R) : dirichletPolynomial N a (t j) ≠ 0 := by
    intro hz
    have hj := hlarge j
    rw [hz, norm_zero] at hj
    linarith
  have hunit : ∀ j, ‖c j‖ = 1 := by
    intro j
    dsimp [c]
    exact phaseCompensator_norm _ (hDne j)
  have halign :
      (∑ j : Fin R, c j * dirichletPolynomial N a (t j)) =
        ∑ j : Fin R, (‖dirichletPolynomial N a (t j)‖ : ℂ) := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [c]
    exact phaseCompensator _ (hDne j)
  have hsumLower :
      (R : ℝ) * V ≤ ∑ j : Fin R, ‖dirichletPolynomial N a (t j)‖ := by
    calc
      (R : ℝ) * V = ∑ j : Fin R, V := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∑ j : Fin R, ‖dirichletPolynomial N a (t j)‖ :=
        Finset.sum_le_sum (fun j _ => hlarge j)
  have hsumNonneg :
      0 ≤ ∑ j : Fin R, ‖dirichletPolynomial N a (t j)‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hcastSum :
      (∑ j : Fin R, (‖dirichletPolynomial N a (t j)‖ : ℂ)) =
        ((∑ j : Fin R, ‖dirichletPolynomial N a (t j)‖ : ℝ) : ℂ) := by
    exact (map_sum (algebraMap ℝ ℂ)
      (fun j : Fin R => ‖dirichletPolynomial N a (t j)‖) Finset.univ).symm
  have hnormAligned :
      ‖∑ j : Fin R, c j * dirichletPolynomial N a (t j)‖ =
        ∑ j : Fin R, ‖dirichletPolynomial N a (t j)‖ := by
    rw [halign, hcastSum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsumNonneg]
  have hnormLower :
      (R : ℝ) * V ≤
        ‖∑ j : Fin R, c j * dirichletPolynomial N a (t j)‖ := by
    calc
      (R : ℝ) * V ≤ ∑ j : Fin R, ‖dirichletPolynomial N a (t j)‖ := hsumLower
      _ = ‖∑ j : Fin R, c j * dirichletPolynomial N a (t j)‖ := hnormAligned.symm
  have hsquareLower :
      ((R : ℝ) * V) ^ 2 ≤
        ‖∑ j : Fin R, c j * dirichletPolynomial N a (t j)‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hnormLower
  have hdual := dirichletPolynomialDualCauchy N a R t c
  have hdualKernel := dualExponentialSquareSum_bound N t c hN hunit
  have hrecip :
      (∑ i : Fin R, ∑ j : Fin R, (1 : ℝ) / (1 + |t i - t j|)) ≤
        (R : ℝ) * (1 + 2 * Real.log (R : ℝ)) := by
    calc
      (∑ i : Fin R, ∑ j : Fin R, (1 : ℝ) / (1 + |t i - t j|)) ≤
          ∑ i : Fin R, (1 + 2 * Real.log (R : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact separated_reciprocal_row t i hR hsep
      _ = (R : ℝ) * (1 + 2 * Real.log (R : ℝ)) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  have hrootPoint (i j : Fin R) :
      Real.sqrt |t i - t j| ≤ Real.sqrt S := by
    have hdist : |t i - t j| ≤ S := by
      apply abs_le.mpr
      constructor <;> have hi := htime i <;> have hj := htime j <;> linarith
    exact Real.sqrt_le_sqrt hdist
  have hroot :
      (∑ i : Fin R, ∑ j : Fin R, Real.sqrt |t i - t j|) ≤
        (R : ℝ) ^ 2 * Real.sqrt S := by
    calc
      (∑ i : Fin R, ∑ j : Fin R, Real.sqrt |t i - t j|) ≤
          ∑ i : Fin R, ∑ j : Fin R, Real.sqrt S := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hrootPoint i j
      _ = (R : ℝ) ^ 2 * Real.sqrt S := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  have hsumDoubleMul (C : ℝ) (g : Fin R → Fin R → ℝ) :
      (∑ i : Fin R, ∑ j : Fin R, C * g i j) =
        C * (∑ i : Fin R, ∑ j : Fin R, g i j) := by
    calc
      (∑ i : Fin R, ∑ j : Fin R, C * g i j) =
          ∑ i : Fin R, C * ∑ j : Fin R, g i j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum]
      _ = C * (∑ i : Fin R, ∑ j : Fin R, g i j) := by rw [← Finset.mul_sum]
  have hkernelDecomp :
      (∑ i : Fin R, ∑ j : Fin R,
        64 * (N / (1 + |t i - t j|) + Real.sqrt |t i - t j|)) =
          64 * N * (∑ i : Fin R, ∑ j : Fin R,
            (1 : ℝ) / (1 + |t i - t j|)) +
            64 * (∑ i : Fin R, ∑ j : Fin R, Real.sqrt |t i - t j|) := by
    calc
      _ = ∑ i : Fin R, ∑ j : Fin R,
          ((64 * N) * ((1 : ℝ) / (1 + |t i - t j|)) +
            64 * Real.sqrt |t i - t j|) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i : Fin R,
            ((∑ j : Fin R, (64 * N) * ((1 : ℝ) / (1 + |t i - t j|))) +
              ∑ j : Fin R, 64 * Real.sqrt |t i - t j|) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_add_distrib
      _ = (∑ i : Fin R, ∑ j : Fin R,
            (64 * N) * ((1 : ℝ) / (1 + |t i - t j|))) +
            ∑ i : Fin R, ∑ j : Fin R, 64 * Real.sqrt |t i - t j| :=
          Finset.sum_add_distrib
      _ = 64 * N * (∑ i : Fin R, ∑ j : Fin R,
            (1 : ℝ) / (1 + |t i - t j|)) +
            64 * (∑ i : Fin R, ∑ j : Fin R, Real.sqrt |t i - t j|) := by
        rw [hsumDoubleMul, hsumDoubleMul]
  have hkernelUpper :
      (∑ n ∈ dirichletIndices N,
        ‖∑ j : Fin R, dualPhaseTerm t c n j‖ ^ 2) ≤
          64 * (N * (R : ℝ) * (1 + 2 * Real.log (R : ℝ)) +
            (R : ℝ) ^ 2 * Real.sqrt S) := by
    calc
      (∑ n ∈ dirichletIndices N,
        ‖∑ j : Fin R, dualPhaseTerm t c n j‖ ^ 2) ≤
          ∑ i : Fin R, ∑ j : Fin R,
            64 * (N / (1 + |t i - t j|) + Real.sqrt |t i - t j|) := hdualKernel
      _ = 64 * (N * (∑ i : Fin R, ∑ j : Fin R,
            (1 : ℝ) / (1 + |t i - t j|)) +
            ∑ i : Fin R, ∑ j : Fin R, Real.sqrt |t i - t j|) := by
        rw [hkernelDecomp]
        ring
      _ ≤ 64 * (N * (R : ℝ) * (1 + 2 * Real.log (R : ℝ)) +
            (R : ℝ) ^ 2 * Real.sqrt S) := by
        have hNnonneg : 0 ≤ N := by linarith
        have hinside := add_le_add
          (mul_le_mul_of_nonneg_left hrecip hNnonneg) hroot
        have hmul := mul_le_mul_of_nonneg_left hinside
          (by norm_num : (0 : ℝ) ≤ 64)
        exact hmul.trans (le_of_eq (by ring))
  have hmaster :
      ((R : ℝ) * V) ^ 2 ≤
        dirichletEnergy N a *
          (∑ n ∈ dirichletIndices N,
            ‖∑ j : Fin R, dualPhaseTerm t c n j‖ ^ 2) := by
    calc
      ((R : ℝ) * V) ^ 2 ≤
          ‖∑ j : Fin R, c j * dirichletPolynomial N a (t j)‖ ^ 2 := hsquareLower
      _ ≤ dirichletEnergy N a *
          (∑ n ∈ dirichletIndices N,
            ‖∑ j : Fin R,
              c j * Complex.exp (-Complex.I * (t j : ℂ) *
                (Real.log (n : ℝ) : ℂ))‖ ^ 2) := hdual
      _ = dirichletEnergy N a *
          (∑ n ∈ dirichletIndices N,
            ‖∑ j : Fin R, dualPhaseTerm t c n j‖ ^ 2) := by
        congr 2
  have hmaster' :
      ((R : ℝ) * V) ^ 2 ≤
        64 * dirichletEnergy N a *
          (N * (R : ℝ) * (1 + 2 * Real.log (R : ℝ)) +
            (R : ℝ) ^ 2 * Real.sqrt S) := by
    calc
      ((R : ℝ) * V) ^ 2 ≤
          dirichletEnergy N a *
            (∑ n ∈ dirichletIndices N,
              ‖∑ j : Fin R, dualPhaseTerm t c n j‖ ^ 2) := hmaster
      _ ≤ dirichletEnergy N a *
            (64 * (N * (R : ℝ) * (1 + 2 * Real.log (R : ℝ)) +
              (R : ℝ) ^ 2 * Real.sqrt S)) :=
        mul_le_mul_of_nonneg_left hkernelUpper hG.le
      _ = 64 * dirichletEnergy N a *
            (N * (R : ℝ) * (1 + 2 * Real.log (R : ℝ)) +
              (R : ℝ) ^ 2 * Real.sqrt S) := by ring
  have hshortTerm :
      64 * dirichletEnergy N a * (R : ℝ) ^ 2 * Real.sqrt S ≤
        ((R : ℝ) * V) ^ 2 / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hshort
      (by positivity : 0 ≤ 64 * dirichletEnergy N a * (R : ℝ) ^ 2)
    calc
      64 * dirichletEnergy N a * (R : ℝ) ^ 2 * Real.sqrt S =
          64 * dirichletEnergy N a * (R : ℝ) ^ 2 * Real.sqrt S := rfl
      _ ≤ 64 * dirichletEnergy N a * (R : ℝ) ^ 2 *
          (V ^ 2 / (128 * dirichletEnergy N a)) := by nlinarith [hmul]
      _ = ((R : ℝ) * V) ^ 2 / 2 := by
        field_simp [hG.ne']
        norm_num
  have hquad :
      ((R : ℝ) * V) ^ 2 ≤
        64 * N * dirichletEnergy N a * (R : ℝ) *
          (1 + 2 * Real.log (R : ℝ)) + (((R : ℝ) * V) ^ 2) / 2 := by
    calc
      ((R : ℝ) * V) ^ 2 ≤
          64 * dirichletEnergy N a *
            (N * (R : ℝ) * (1 + 2 * Real.log (R : ℝ)) +
              (R : ℝ) ^ 2 * Real.sqrt S) := hmaster'
      _ ≤ 64 * N * dirichletEnergy N a * (R : ℝ) *
            (1 + 2 * Real.log (R : ℝ)) + (((R : ℝ) * V) ^ 2) / 2 := by
        nlinarith [hshortTerm]
  have hquad' :
      ((R : ℝ) * V) ^ 2 ≤
        128 * N * dirichletEnergy N a * (R : ℝ) *
          (1 + 2 * Real.log (R : ℝ)) := by linarith
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hR)
  have hcancel :
      (R : ℝ) * V ^ 2 ≤
        128 * N * dirichletEnergy N a * (1 + 2 * Real.log (R : ℝ)) := by
    apply le_of_mul_le_mul_left ?_ hRpos
    nlinarith [hquad']
  have hV2 : 0 < V ^ 2 := pow_pos hV 2
  calc
    (R : ℝ) = ((R : ℝ) * V ^ 2) / V ^ 2 := by field_simp [hV2.ne']
    _ ≤ (128 * N * dirichletEnergy N a *
          (1 + 2 * Real.log (R : ℝ))) / V ^ 2 := div_le_div_of_nonneg_right hcancel (le_of_lt hV2)
    _ = 128 * N * dirichletEnergy N a / V ^ 2 *
          (1 + 2 * Real.log (R : ℝ)) := by ring

#print axioms localLargeValueBound

end FractionalPrimes.Literature.LargeValues
