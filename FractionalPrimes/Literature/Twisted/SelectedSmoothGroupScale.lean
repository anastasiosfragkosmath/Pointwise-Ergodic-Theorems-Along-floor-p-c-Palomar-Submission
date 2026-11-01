module

public import FractionalPrimes.Literature.Uniformity.ArithmeticGrouping
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Small-factor geometry for the selected smooth group

This file isolates the elementary scale-selection step in `lda:small-group`.
The selected group is exactly the first set in the `IImaj (5/8)` partition.
It proves its source mass range, nonemptiness, factor-count bound, and the
source scale window for one elementary factor.  The analytic short-interval
estimate for the resulting group convolution is a separate conditional
argument.
-/

@[expose] public section

noncomputable section

open Finset
open FractionalPrimes.Literature.Uniformity.Combinatorics

namespace FractionalPrimes.Literature.Twisted

private theorem selectedSmoothSubsetWeight_union_disjoint {k : ℕ}
    (w : GroupingPredicates k) {s t : Finset (Fin k)} (hst : Disjoint s t) :
    subsetWeightSum w (s ∪ t) = subsetWeightSum w s + subsetWeightSum w t := by
  simp [subsetWeightSum, Finset.sum_union hst]

private theorem selectedSmoothSubsetWeight_univ {k : ℕ}
    (w : GroupingPredicates k) :
    subsetWeightSum w (Finset.univ : Finset (Fin k)) = 1 := by
  simpa [subsetWeightSum] using w.weight_sum_eq_one

private theorem selectedSmoothGroup_nonempty_of_positive_weight {k : ℕ}
    (w : GroupingPredicates k) (I : Finset (Fin k))
    (hI : 0 < subsetWeightSum w I) : 0 < I.card := by
  by_contra h
  have hIempty : I = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos h)
  simp [hIempty, subsetWeightSum] at hI

/-- The first selected group in the exact three-way `5/8` grouping has a
factor in the scale window used by `lda:small-group`.  Here `N i=P^(w.weight
i)` is the exact scale parametrization from the smooth Heath--Brown grouping,
and `P` has the source component-product bounds.  The theorem retains the
other two groups and proves they are nonempty as well. -/
theorem selectedSmoothGroupSmallFactorScale
    {k : ℕ} {X P : ℝ} (w : GroupingPredicates k)
    (N : Fin k → ℝ) (hlen : k ≤ 20)
    (hX : ((2 : ℝ) ^ 22) ^ 5 ≤ X)
    (hP : ((2 : ℝ) ^ 22)⁻¹ * X ≤ P ∧ P ≤ (2 : ℝ) ^ 22 * X)
    (hN : ∀ i, N i = P ^ w.weight i)
    (hgroup : w.IImaj (5 / 8)) :
    ∃ I J J' : Finset (Fin k),
      Disjoint I J ∧ Disjoint I J' ∧ Disjoint J J' ∧
      I ∪ J ∪ J' = Finset.univ ∧
      (1 / 4 : ℝ) ≤ subsetWeightSum w I ∧
      subsetWeightSum w I ≤ 1 / 2 ∧
      (1 / 8 : ℝ) ≤ subsetWeightSum w J ∧
      (1 / 8 : ℝ) ≤ subsetWeightSum w J' ∧
      1 ≤ I.card ∧ I.card ≤ 20 ∧
      1 ≤ J.card ∧ 1 ≤ J'.card ∧
      ∃ i ∈ I,
        X ^ (1 / 100 : ℝ) ≤ N i ∧
        N i ≤ (2 : ℝ) ^ 11 * Real.sqrt X := by
  rcases hgroup with ⟨I, J, J', hIJ, hIJ', hJJ', hcover,
    hIlo, hIhi, hgap⟩
  norm_num at hIlo hIhi hgap
  let C : ℝ := (2 : ℝ) ^ 22
  have hXpos : 0 < X := by
    have : 0 < ((2 : ℝ) ^ 22) ^ 5 := by positivity
    linarith
  have hXbig : C ^ 5 ≤ X := by simpa [C, pow_mul] using hX
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCpow : C ^ 5 = (2 : ℝ) ^ 110 := by
    dsimp [C]
    norm_num [pow_mul]
  have hXpow : (2 : ℝ) ^ 110 ≤ X := by simpa [hCpow] using hXbig
  have hCidentity : C⁻¹ * (2 : ℝ) ^ 110 = (2 : ℝ) ^ 88 := by
    have hpow : (2 : ℝ) ^ 110 = (2 : ℝ) ^ 22 * (2 : ℝ) ^ 88 := by
      rw [← pow_add]
    rw [hpow]
    dsimp [C]
    field_simp
  have hPone : 1 ≤ P := by
    calc
      1 ≤ (2 : ℝ) ^ 88 := by norm_num
      _ = C⁻¹ * (2 : ℝ) ^ 110 := hCidentity.symm
      _ ≤ C⁻¹ * X := mul_le_mul_of_nonneg_left hXpow (by positivity)
      _ ≤ P := by simpa [C] using hP.1
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hPone
  have hCroot : C ^ (1 / 80 : ℝ) ≤ X ^ (1 / 400 : ℝ) := by
    have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ C ^ 5) hXbig
      (by norm_num : 0 ≤ (1 / 400 : ℝ))
    calc
      C ^ (1 / 80 : ℝ) = C ^ ((5 : ℝ) * (1 / 400 : ℝ)) := by
        congr 1 <;> norm_num
      _ = (C ^ 5) ^ (1 / 400 : ℝ) := by
        rw [Real.rpow_mul hCpos.le (5 : ℝ) (1 / 400 : ℝ)]
        rw [← Real.rpow_natCast C 5]
        rfl
      _ ≤ X ^ (1 / 400 : ℝ) := hroot
  have hCrootPos : 0 < C ^ (1 / 80 : ℝ) := Real.rpow_pos_of_pos hCpos _
  have hrootComp :
      1 ≤ (C ^ (1 / 80 : ℝ))⁻¹ * X ^ (1 / 400 : ℝ) := by
    calc
      1 = (C ^ (1 / 80 : ℝ))⁻¹ * C ^ (1 / 80 : ℝ) := by
        field_simp
      _ ≤ (C ^ (1 / 80 : ℝ))⁻¹ * X ^ (1 / 400 : ℝ) :=
        mul_le_mul_of_nonneg_left hCroot (inv_nonneg.mpr hCrootPos.le)
  have hminScale : X ^ (1 / 100 : ℝ) ≤ (C⁻¹ * X) ^ (1 / 80 : ℝ) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hCpos.le) hXpos.le,
      Real.inv_rpow hCpos.le]
    have hXsplit : X ^ (1 / 100 : ℝ) * X ^ (1 / 400 : ℝ) =
        X ^ (1 / 80 : ℝ) := by
      rw [← Real.rpow_add hXpos]
      congr 1 <;> norm_num
    calc
      X ^ (1 / 100 : ℝ) = X ^ (1 / 100 : ℝ) * 1 := by ring
      _ ≤ X ^ (1 / 100 : ℝ) *
          ((C ^ (1 / 80 : ℝ))⁻¹ * X ^ (1 / 400 : ℝ)) :=
        mul_le_mul_of_nonneg_left hrootComp
          (Real.rpow_nonneg hXpos.le _)
      _ = (C ^ (1 / 80 : ℝ))⁻¹ *
          (X ^ (1 / 100 : ℝ) * X ^ (1 / 400 : ℝ)) := by ring
      _ = (C ^ (1 / 80 : ℝ))⁻¹ * X ^ (1 / 80 : ℝ) := by rw [hXsplit]
  have hPmin : (C⁻¹ * X) ^ (1 / 80 : ℝ) ≤ P ^ (1 / 80 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hP.1 (by norm_num)
  have hPmax : P ^ (1 / 2 : ℝ) ≤ (C * X) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hPpos.le hP.2 (by norm_num)
  have hCsquare : C = ((2 : ℝ) ^ 11) ^ 2 := by
    dsimp [C]
    norm_num [pow_mul]
  have hCrootSqrt : Real.sqrt C = (2 : ℝ) ^ 11 := by
    rw [hCsquare, Real.sqrt_sq_eq_abs]
    norm_num
  have hPmaxSqrt : (C * X) ^ (1 / 2 : ℝ) =
      (2 : ℝ) ^ 11 * Real.sqrt X := by
    calc
      (C * X) ^ (1 / 2 : ℝ) = Real.sqrt (C * X) := by
        rw [← Real.sqrt_eq_rpow]
      _ = Real.sqrt C * Real.sqrt X := by
        rw [Real.sqrt_mul hCpos.le]
      _ = (2 : ℝ) ^ 11 * Real.sqrt X := by rw [hCrootSqrt]
  have hdisIJ' : Disjoint (I ∪ J) J' :=
    Finset.disjoint_union_left.mpr ⟨hIJ', hJJ'⟩
  have htotal : subsetWeightSum w I + subsetWeightSum w J +
      subsetWeightSum w J' = 1 := by
    calc
      subsetWeightSum w I + subsetWeightSum w J + subsetWeightSum w J' =
          subsetWeightSum w (I ∪ J) + subsetWeightSum w J' := by
            rw [selectedSmoothSubsetWeight_union_disjoint w hIJ]
      _ = subsetWeightSum w ((I ∪ J) ∪ J') :=
        (selectedSmoothSubsetWeight_union_disjoint w hdisIJ').symm
      _ = subsetWeightSum w (Finset.univ : Finset (Fin k)) := by
        rw [hcover]
      _ = 1 := selectedSmoothSubsetWeight_univ w
  have hrest : (1 / 2 : ℝ) ≤
      subsetWeightSum w J + subsetWeightSum w J' := by
    rw [← htotal]
    linarith
  have hgap' := abs_le.mp hgap
  have hJlo : (1 / 8 : ℝ) ≤ subsetWeightSum w J := by linarith
  have hJ'lo : (1 / 8 : ℝ) ≤ subsetWeightSum w J' := by linarith
  have hIcardpos : 0 < I.card :=
    selectedSmoothGroup_nonempty_of_positive_weight w I (by linarith)
  have hJcardpos : 0 < J.card :=
    selectedSmoothGroup_nonempty_of_positive_weight w J (by linarith)
  have hJ'cardpos : 0 < J'.card :=
    selectedSmoothGroup_nonempty_of_positive_weight w J' (by linarith)
  have hInonempty : I.Nonempty := Finset.card_pos.mp hIcardpos
  have hJnonempty : J.Nonempty := Finset.card_pos.mp hJcardpos
  have hJ'nonempty : J'.Nonempty := Finset.card_pos.mp hJ'cardpos
  have hIcardlo : 1 ≤ I.card := by
    have h := Finset.card_pos.mpr hInonempty
    omega
  have hJcardlo : 1 ≤ J.card := by
    have h := Finset.card_pos.mpr hJnonempty
    omega
  have hJ'cardlo : 1 ≤ J'.card := by
    have h := Finset.card_pos.mpr hJ'nonempty
    omega
  have hIcardhi : I.card ≤ 20 := by
    have hIcard : I.card ≤ k := by
      calc
        I.card ≤ (Finset.univ : Finset (Fin k)).card :=
          Finset.card_le_card (Finset.subset_univ I)
        _ = k := by simp
    omega
  have hαexists : ∃ i ∈ I, (1 / 80 : ℝ) ≤ w.weight i := by
    by_contra hnot
    push_neg at hnot
    have hsumlt : subsetWeightSum w I < (I.card : ℝ) / 80 := by
      calc
        subsetWeightSum w I < ∑ i ∈ I, (1 / 80 : ℝ) := by
          apply Finset.sum_lt_sum
          · intro i hi
            exact le_of_lt (hnot i hi)
          · obtain ⟨i, hi⟩ := hInonempty
            exact ⟨i, hi, hnot i hi⟩
        _ = (I.card : ℝ) / 80 := by simp [div_eq_mul_inv]
    have hIcardR : (I.card : ℝ) ≤ 20 := by exact_mod_cast hIcardhi
    have hsumUpper : (I.card : ℝ) / 80 ≤ 1 / 4 := by nlinarith
    linarith
  obtain ⟨i, hiI, hiweight⟩ := hαexists
  have hIweightle : w.weight i ≤ subsetWeightSum w I := by
    change w.weight i ≤ ∑ j ∈ I, w.weight j
    exact Finset.single_le_sum (fun j hj => w.weight_nonneg j) hiI
  have hNlower : X ^ (1 / 100 : ℝ) ≤ N i := by
    calc
      X ^ (1 / 100 : ℝ) ≤ (C⁻¹ * X) ^ (1 / 80 : ℝ) := hminScale
      _ ≤ P ^ (1 / 80 : ℝ) := hPmin
      _ ≤ P ^ w.weight i := Real.rpow_le_rpow_of_exponent_le hPone hiweight
      _ = N i := (hN i).symm
  have hNupper : N i ≤ (2 : ℝ) ^ 11 * Real.sqrt X := by
    calc
      N i ≤ P ^ subsetWeightSum w I := by
        rw [hN i]
        exact Real.rpow_le_rpow_of_exponent_le hPone hIweightle
      _ ≤ P ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hPone hIhi
      _ ≤ (C * X) ^ (1 / 2 : ℝ) := hPmax
      _ = (2 : ℝ) ^ 11 * Real.sqrt X := hPmaxSqrt
  refine ⟨I, J, J', hIJ, hIJ', hJJ', hcover, ?_, ?_, hJlo, hJ'lo,
    hIcardlo, hIcardhi, hJcardlo, hJ'cardlo, ⟨i, hiI, hNlower, hNupper⟩⟩
  · norm_num at hIlo ⊢
    exact hIlo
  · norm_num at hIhi ⊢
    exact hIhi

end FractionalPrimes.Literature.Twisted

#print axioms FractionalPrimes.Literature.Twisted.selectedSmoothGroupSmallFactorScale

end
