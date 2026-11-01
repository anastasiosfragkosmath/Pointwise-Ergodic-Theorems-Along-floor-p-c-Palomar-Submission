module

public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFactorAllocationIdentity
public import Mathlib.Tactic

/-! Exact finite dyadic-window decomposition for selected-group Mellin sums.

The selected-group source coefficients need not be supported in one
`(M,2M]` interval. This file records the finite block decomposition and the
exact allocation identity on each individual window. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.LargeValues
open FractionalPrimes.Literature.Twisted

/-- The Mellin Dirichlet polynomial restricted to an arbitrary real window
`(L,U]`. -/
noncomputable def factorPolynomialWindow (L U : ℝ) (coeff : ℕ → ℂ) : ℝ → ℂ :=
  fun t =>
    ∑ n ∈ factorExtractionRealInterval L U,
      LargeValues.dirichletTerm
        (LargeValues.normalizedDirichletCoeff coeff) n t

/-- For nonnegative `M`, the ordinary factor polynomial is the window
polynomial on its exact source interval `(M,2M]`. -/
theorem factorPolynomial_eq_factorPolynomialWindow
    {M : ℝ} (hM : 0 ≤ M) (coeff : ℕ → ℂ) :
    factorPolynomial M coeff = factorPolynomialWindow M (2 * M) coeff := by
  funext t
  unfold factorPolynomial factorPolynomialWindow
  rw [LargeValues.dirichletPolynomial,
    dirichletIndices_eq_factorExtractionRealInterval hM]

private theorem factorExtractionRealInterval_partition
    {L M U : ℝ} (hLM : L ≤ M) (hMU : M ≤ U) :
    factorExtractionRealInterval L U =
      factorExtractionRealInterval L M ∪ factorExtractionRealInterval M U := by
  rw [factorExtractionRealInterval, factorExtractionRealInterval,
    factorExtractionRealInterval]
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_union]
  have hfloorLM : Nat.floor L ≤ Nat.floor M := Nat.floor_mono hLM
  have hfloorMU : Nat.floor M ≤ Nat.floor U := Nat.floor_mono hMU
  omega

private theorem factorExtractionRealInterval_partition_disjoint
    {L M U : ℝ} :
    Disjoint (factorExtractionRealInterval L M)
      (factorExtractionRealInterval M U) := by
  rw [factorExtractionRealInterval, factorExtractionRealInterval]
  apply Finset.disjoint_left.mpr
  intro n hn₁ hn₂
  simp only [Finset.mem_Ioc] at hn₁ hn₂
  omega

/-- Exact finite sum decomposition for any summand on a real interval with
dyadic-ratio endpoints. -/
theorem factorExtractionRealInterval_sum_eq_sum_dyadicWindows
    {M : ℝ} (hM : 0 ≤ M) (k : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ factorExtractionRealInterval M ((2 : ℝ) ^ k * M), f n) =
      ∑ j ∈ Finset.range k,
        ∑ n ∈ factorExtractionRealInterval ((2 : ℝ) ^ j * M)
          (2 * ((2 : ℝ) ^ j * M)), f n := by
  classical
  induction k with
  | zero => simp [factorExtractionRealInterval]
  | succ k ih =>
      have hpowOne : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
        one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hleft : M ≤ (2 : ℝ) ^ k * M := by
        calc
          M = 1 * M := by ring
          _ ≤ (2 : ℝ) ^ k * M := mul_le_mul_of_nonneg_right hpowOne hM
      have hMblock : 0 ≤ (2 : ℝ) ^ k * M :=
        mul_nonneg (by positivity) hM
      have htop : (2 : ℝ) ^ (k + 1) * M =
          2 * ((2 : ℝ) ^ k * M) := by
        rw [pow_succ]
        ring
      have hright : (2 : ℝ) ^ k * M ≤
          (2 : ℝ) ^ (k + 1) * M := by
        rw [htop]
        nlinarith [hMblock]
      have hdis := factorExtractionRealInterval_partition_disjoint
        (L := M) (M := (2 : ℝ) ^ k * M)
        (U := (2 : ℝ) ^ (k + 1) * M)
      have hpartition := factorExtractionRealInterval_partition hleft hright
      calc
        (∑ n ∈ factorExtractionRealInterval M
            ((2 : ℝ) ^ (k + 1) * M), f n) =
            (∑ n ∈ factorExtractionRealInterval M ((2 : ℝ) ^ k * M), f n) +
              ∑ n ∈ factorExtractionRealInterval ((2 : ℝ) ^ k * M)
                (2 * ((2 : ℝ) ^ k * M)), f n := by
          rw [show factorExtractionRealInterval M
                ((2 : ℝ) ^ (k + 1) * M) =
              factorExtractionRealInterval M ((2 : ℝ) ^ k * M) ∪
                factorExtractionRealInterval ((2 : ℝ) ^ k * M)
                  ((2 : ℝ) ^ (k + 1) * M) by
                exact hpartition]
          rw [Finset.sum_union hdis, htop]
        _ =
            (∑ j ∈ Finset.range k,
              ∑ n ∈ factorExtractionRealInterval ((2 : ℝ) ^ j * M)
                (2 * ((2 : ℝ) ^ j * M)), f n) +
              ∑ n ∈ factorExtractionRealInterval ((2 : ℝ) ^ k * M)
                (2 * ((2 : ℝ) ^ k * M)), f n := by
          rw [ih]
        _ = ∑ j ∈ Finset.range (k + 1),
              ∑ n ∈ factorExtractionRealInterval ((2 : ℝ) ^ j * M)
                (2 * ((2 : ℝ) ^ j * M)), f n := by
          rw [Finset.sum_range_succ]

/-- The finite allocated Mellin polynomial on a broad interval is the exact
sum of its allocated polynomials on the dyadic subwindows. -/
theorem finiteAllocatedDirichletPolynomial_eq_sum_dyadicWindows
    {M : ℝ} {Q : ℕ} (hM : 0 ≤ M) (k : ℕ)
    (a : ArithmeticFunction ℂ) (r q : ℕ) (χ : BlueprintCharacter Q)
    (s : ℂ) :
    finiteAllocatedDirichletPolynomial a r q
        (factorExtractionRealInterval M ((2 : ℝ) ^ k * M)) χ s =
      ∑ j ∈ Finset.range k,
        finiteAllocatedDirichletPolynomial a r q
          (factorExtractionRealInterval ((2 : ℝ) ^ j * M)
            (2 * ((2 : ℝ) ^ j * M))) χ s := by
  classical
  unfold finiteAllocatedDirichletPolynomial
  exact factorExtractionRealInterval_sum_eq_sum_dyadicWindows hM k
    (fun n => a (r * n) * (if Nat.Coprime n q then 1 else 0) *
      evalInt χ (n : ℤ) * (n : ℂ) ^ (-s))

/-- Two finite cutoffs give the same allocated polynomial when each cutoff
contains every nonzero allocated coefficient of the other. -/
theorem finiteAllocatedDirichletPolynomial_eq_of_mutual_support
    {Q : ℕ} (a : ArithmeticFunction ℂ) (r q : ℕ)
    (χ : BlueprintCharacter Q) (s : ℂ) (S A : Finset ℕ)
    (hSA : ∀ n ∈ S, a (r * n) ≠ 0 → n ∈ A)
    (hAS : ∀ n ∈ A, a (r * n) ≠ 0 → n ∈ S) :
    finiteAllocatedDirichletPolynomial a r q S χ s =
      finiteAllocatedDirichletPolynomial a r q A χ s := by
  classical
  let term : ℕ → ℂ := fun n =>
    a (r * n) * (if Nat.Coprime n q then 1 else 0) *
      evalInt χ (n : ℤ) * (n : ℂ) ^ (-s)
  have hS :
      (∑ n ∈ S, term n) = ∑ n ∈ S ∩ A, term n := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro n hn hnnot
    have hnA : n ∉ A := by
      intro hnA
      exact hnnot (Finset.mem_inter.mpr ⟨hn, hnA⟩)
    have ha : a (r * n) = 0 := by
      by_contra hne
      exact hnA (hSA n hn hne)
    simp [term, ha]
  have hA :
      (∑ n ∈ S ∩ A, term n) = ∑ n ∈ A, term n := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro n hn hnnot
    have hnS : n ∉ S := by
      intro hnS
      exact hnnot (Finset.mem_inter.mpr ⟨hnS, hn⟩)
    have ha : a (r * n) = 0 := by
      by_contra hne
      exact hnS (hAS n hn hne)
    simp [term, ha]
  unfold finiteAllocatedDirichletPolynomial
  change (∑ n ∈ S, term n) = ∑ n ∈ A, term n
  exact hS.trans hA

/-- A quotient index whose allocated coefficient lies in `[M/C,C*M]`
belongs to the exact dyadic-ratio window beginning at `M/(4*C*r)`, provided
the selected block count reaches the stated upper endpoint. -/
theorem allocatedIndex_mem_dyadicWindow_of_scaledSupport
    {M C : ℝ} {r n k : ℕ}
    (hM : 0 < M) (hC : 1 ≤ C) (hr : 0 < r)
    (hcover : 4 * C ^ 2 ≤ (2 : ℝ) ^ k)
    (hsupport : M / C ≤ ((r * n : ℕ) : ℝ) ∧
      ((r * n : ℕ) : ℝ) ≤ C * M) :
    n ∈ factorExtractionRealInterval (M / (4 * C * (r : ℝ)))
      ((2 : ℝ) ^ k * (M / (4 * C * (r : ℝ)))) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    simp [hn0] at hsupport
    linarith [div_pos hM hCpos]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hdenom : 0 < C * (r : ℝ) := mul_pos hCpos hrR
  have hdenom4 : 0 < 4 * C * (r : ℝ) := by positivity
  have hquotLower : M / (C * (r : ℝ)) ≤ (n : ℝ) := by
    apply (div_le_iff₀ hdenom).2
    have hmul := mul_le_mul_of_nonneg_left hsupport.1 hCpos.le
    have hcancel : C * (M / C) = M := by
      field_simp [ne_of_gt hCpos]
    have hmul' : C * (M / C) ≤ (n : ℝ) * (C * (r : ℝ)) := by
      calc
        C * (M / C) ≤ C * ((r * n : ℕ) : ℝ) := hmul
        _ = (C * (r : ℝ)) * (n : ℝ) := by
          rw [Nat.cast_mul]
          ring
        _ = (n : ℝ) * (C * (r : ℝ)) := by ring
    calc
      M = C * (M / C) := hcancel.symm
      _ ≤ (n : ℝ) * (C * (r : ℝ)) := hmul'
  have hbaseLt : M / (4 * C * (r : ℝ)) < (n : ℝ) := by
    apply (div_lt_iff₀ hdenom4).2
    have hprod : 0 < C * (r : ℝ) * (n : ℝ) := mul_pos hdenom hnR
    have hstrict : C * (r : ℝ) * (n : ℝ) <
        4 * C * (r : ℝ) * (n : ℝ) := by nlinarith
    have hMlt : M < 4 * C * (r : ℝ) * (n : ℝ) := by
      have hle := hquotLower
      have hmul := mul_le_mul_of_nonneg_right hle hdenom4.le
      have hcancel : (M / (C * (r : ℝ))) *
          (4 * C * (r : ℝ)) = 4 * M := by
        field_simp [ne_of_gt hdenom]
      rw [hcancel] at hmul
      nlinarith
    simpa [mul_assoc, mul_left_comm, mul_comm] using hMlt
  have hupperNum :
      4 * C * (r : ℝ) * (n : ℝ) ≤ (2 : ℝ) ^ k * M := by
    have hmul := mul_le_mul_of_nonneg_left hsupport.2
      (show 0 ≤ 4 * C by positivity)
    calc
      4 * C * (r : ℝ) * (n : ℝ) =
          (4 * C) * ((r * n : ℕ) : ℝ) := by
        norm_num [Nat.cast_mul]
        ring
      _ ≤ (4 * C) * (C * M) := hmul
      _ = (4 * C ^ 2) * M := by ring
      _ ≤ (2 : ℝ) ^ k * M :=
        mul_le_mul_of_nonneg_right hcover hM.le
  have hupper : (n : ℝ) ≤
      ((2 : ℝ) ^ k * M) / (4 * C * (r : ℝ)) :=
    (le_div_iff₀ hdenom4).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hupperNum)
  have hupperEq :
      ((2 : ℝ) ^ k * M) / (4 * C * (r : ℝ)) =
        (2 : ℝ) ^ k * (M / (4 * C * (r : ℝ))) := by
    field_simp [ne_of_gt hdenom4]
  rw [factorExtractionRealInterval]
  exact (mem_factorExtractionRealInterval
    (div_nonneg hM.le (by positivity))
    (mul_nonneg (by positivity)
      (div_nonneg hM.le (by positivity))) n).2
      ⟨hbaseLt, hupper.trans_eq hupperEq⟩

/-- If the allocated source coefficients lie in the prescribed multiplicative
support range, the broad dyadic window beginning at `M/(4Cr)` contains every
nonzero quotient coefficient. Under an explicit finite cutoff, the window
allocation is exactly the original finite allocation. -/
theorem finiteAllocatedDirichletPolynomial_eq_of_scaledSupport
    {M C : ℝ} {r q Q k P : ℕ}
    (hM : 0 < M) (hC : 1 ≤ C) (hr : 0 < r)
    (hcover : 4 * C ^ 2 ≤ (2 : ℝ) ^ k)
    (a : ArithmeticFunction ℂ) (χ : BlueprintCharacter Q) (s : ℂ)
    (hcutoff : ∀ n, a (r * n) ≠ 0 → n ≤ P)
    (hsupport : ∀ n, a (r * n) ≠ 0 →
      M / C ≤ ((r * n : ℕ) : ℝ) ∧ ((r * n : ℕ) : ℝ) ≤ C * M) :
    finiteAllocatedDirichletPolynomial a r q (Finset.Icc 1 P) χ s =
      finiteAllocatedDirichletPolynomial a r q
        (factorExtractionRealInterval (M / (4 * C * (r : ℝ)))
          ((2 : ℝ) ^ k * (M / (4 * C * (r : ℝ)))) ) χ s := by
  classical
  let S := factorExtractionRealInterval (M / (4 * C * (r : ℝ)))
    ((2 : ℝ) ^ k * (M / (4 * C * (r : ℝ))))
  let A := Finset.Icc 1 P
  have hbasepos : 0 < M / (4 * C * (r : ℝ)) := by
    apply div_pos hM
    positivity
  have hAtoS : ∀ n ∈ A, a (r * n) ≠ 0 → n ∈ S := by
    intro n hn hcoeff
    dsimp [S]
    exact allocatedIndex_mem_dyadicWindow_of_scaledSupport
      hM hC hr hcover (hsupport n hcoeff)
  have hStoA : ∀ n ∈ S, a (r * n) ≠ 0 → n ∈ A := by
    intro n hn hcoeff
    have hnwindow :=
      (mem_factorExtractionRealInterval hbasepos.le
        (mul_nonneg (by positivity) hbasepos.le) n).1 hn
    have hnposR : 0 < (n : ℝ) := lt_trans hbasepos hnwindow.1
    have hnpos : 0 < n := by exact_mod_cast hnposR
    dsimp [A]
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hnpos, hcutoff n hcoeff⟩
  have hEq := finiteAllocatedDirichletPolynomial_eq_of_mutual_support
    a r q χ s A S hAtoS hStoA
  exact hEq

/-- An arbitrary finite Mellin window whose endpoints differ by a dyadic
factor is the exact sum of its consecutive half-open dyadic windows. -/
theorem factorPolynomialWindow_eq_sum_dyadicWindows
    {M : ℝ} (hM : 0 ≤ M) (k : ℕ) (coeff : ℕ → ℂ) (t : ℝ) :
    factorPolynomialWindow M ((2 : ℝ) ^ k * M) coeff t =
      ∑ j ∈ Finset.range k,
        factorPolynomial ((2 : ℝ) ^ j * M) coeff t := by
  classical
  induction k with
  | zero =>
      simp [factorPolynomialWindow, factorExtractionRealInterval]
  | succ k ih =>
      have hpowOne : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
        one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hleft : M ≤ (2 : ℝ) ^ k * M := by
        calc
          M = 1 * M := by ring
          _ ≤ (2 : ℝ) ^ k * M := mul_le_mul_of_nonneg_right hpowOne hM
      have hMblock : 0 ≤ (2 : ℝ) ^ k * M :=
        mul_nonneg (by positivity) hM
      have htop : (2 : ℝ) ^ (k + 1) * M =
          2 * ((2 : ℝ) ^ k * M) := by
        rw [pow_succ]
        ring
      have hright : (2 : ℝ) ^ k * M ≤
          (2 : ℝ) ^ (k + 1) * M := by
        rw [htop]
        nlinarith [hMblock]
      have hdis := factorExtractionRealInterval_partition_disjoint
        (L := M) (M := (2 : ℝ) ^ k * M)
        (U := (2 : ℝ) ^ (k + 1) * M)
      have hpartition := factorExtractionRealInterval_partition hleft hright
      calc
        factorPolynomialWindow M ((2 : ℝ) ^ (k + 1) * M) coeff t =
            factorPolynomialWindow M ((2 : ℝ) ^ k * M) coeff t +
              factorPolynomialWindow ((2 : ℝ) ^ k * M)
                (2 * ((2 : ℝ) ^ k * M)) coeff t := by
          unfold factorPolynomialWindow
          rw [show factorExtractionRealInterval M
                ((2 : ℝ) ^ (k + 1) * M) =
              factorExtractionRealInterval M ((2 : ℝ) ^ k * M) ∪
                factorExtractionRealInterval ((2 : ℝ) ^ k * M)
                  ((2 : ℝ) ^ (k + 1) * M) by
                exact hpartition]
          rw [Finset.sum_union hdis]
          rw [htop]
        _ =
            (∑ j ∈ Finset.range k,
              factorPolynomial ((2 : ℝ) ^ j * M) coeff t) +
                factorPolynomial ((2 : ℝ) ^ k * M) coeff t := by
          rw [ih]
          rw [← factorPolynomial_eq_factorPolynomialWindow hMblock coeff]
        _ = ∑ j ∈ Finset.range (k + 1),
              factorPolynomial ((2 : ℝ) ^ j * M) coeff t := by
          rw [Finset.sum_range_succ]

/-- On one exact dyadic window, multiplying the normalized selected-group
polynomial by its source scale gives precisely the allocated finite Mellin
sum on that same window. No support condition outside the window is needed. -/
theorem selectedGroupFactorPolynomial_eq_allocatedFactorWindow
    {M B T t : ℝ} {r q Q : ℕ}
    (hM : 0 < M) (hB : 0 < B)
    (a : ArithmeticFunction ℂ) (χ : BlueprintCharacter Q)
    (χcut : ℕ → ℂ)
    (hχcut : ∀ n, χcut n =
      if Nat.Coprime n q then evalInt χ (n : ℤ) else 0) :
    (B : ℂ) * factorPolynomial M
        (selectedGroupTrilinearCoeff B r (fun n => a n) χcut T) t =
      finiteAllocatedDirichletPolynomial a r q
        (factorExtractionRealInterval M (2 * M)) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
  classical
  let A := factorExtractionRealInterval M (2 * M)
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)
  let allocatedTerm : ℕ → ℂ := fun n =>
    a (r * n) * (if Nat.Coprime n q then 1 else 0) *
      evalInt χ (n : ℤ) * (n : ℂ) ^ (-s)
  let extractedTerm : ℕ → ℂ := fun n =>
    a (r * n) * factorExtractionMellinWeight χcut (t - T) n
  have hterm : ∀ n ∈ A, allocatedTerm n = extractedTerm n := by
    intro n hn
    have hnpos : 0 < n := by
      have hmem := (mem_factorExtractionRealInterval hM.le (by positivity) n).1 hn
      have hnR : 0 < (n : ℝ) := lt_trans hM hmem.1
      exact_mod_cast hnR
    have hexp :
        ((-(1 / 2 : ℂ)) - Complex.I * ((t - T : ℝ) : ℂ)) = -s := by
      dsimp [s]
      ring
    unfold allocatedTerm extractedTerm factorExtractionMellinWeight
    rw [dif_pos hnpos, hχcut n, hexp]
    by_cases hcop : Nat.Coprime n q
    · simp only [if_pos hcop, one_mul]
      ring
    · simp only [if_neg hcop, zero_mul, mul_zero]
  have hsum :
      finiteAllocatedDirichletPolynomial a r q A χ s =
        ∑ n ∈ A, extractedTerm n := by
    change (∑ n ∈ A, allocatedTerm n) =
      ∑ n ∈ A, extractedTerm n
    apply Finset.sum_congr rfl
    intro n hn
    exact hterm n hn
  have hblock := factorPolynomial_eq_selectedGroupMellinBlock
    (t := t) (T := T) hM hB r (fun n => a n) χcut
  calc
    (B : ℂ) * factorPolynomial M
        (selectedGroupTrilinearCoeff B r (fun n => a n) χcut T) t =
        ∑ n ∈ A, extractedTerm n := by
      rw [hblock]
      dsimp [A, extractedTerm]
      field_simp [Complex.ofReal_ne_zero.mpr hB.ne']
    _ = finiteAllocatedDirichletPolynomial a r q A χ s := hsum.symm

/-- Multiplying a broad dyadic window polynomial by its source normalization
equals the exact finite sum of its allocated Mellin polynomials on the
consecutive half-open dyadic blocks. -/
theorem selectedGroupFactorPolynomialWindow_eq_allocatedBlockSum
    {M B T t : ℝ} {r q Q : ℕ} (hM : 0 < M) (hB : 0 < B)
    (k : ℕ) (a : ArithmeticFunction ℂ) (χ : BlueprintCharacter Q)
    (χcut : ℕ → ℂ)
    (hχcut : ∀ n, χcut n =
      if Nat.Coprime n q then evalInt χ (n : ℤ) else 0) :
    (B : ℂ) * factorPolynomialWindow M ((2 : ℝ) ^ k * M)
        (selectedGroupTrilinearCoeff B r (fun n => a n) χcut T) t =
      ∑ i ∈ Finset.range k,
        finiteAllocatedDirichletPolynomial a r q
          (factorExtractionRealInterval ((2 : ℝ) ^ i * M)
            (2 * ((2 : ℝ) ^ i * M))) χ
          ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
  classical
  let coeff : ℕ → ℂ := selectedGroupTrilinearCoeff B r
    (fun n => a n) χcut T
  rw [factorPolynomialWindow_eq_sum_dyadicWindows hM.le k coeff t]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hMi : 0 < (2 : ℝ) ^ i * M := mul_pos (by positivity) hM
  simpa [coeff] using selectedGroupFactorPolynomial_eq_allocatedFactorWindow
    hMi hB a χ χcut hχcut

/-- The source-scaled selected-group polynomial on a whole dyadic-ratio
window equals the finite allocated Mellin polynomial on that full window. -/
theorem selectedGroupFactorPolynomialWindow_eq_allocatedWindow
    {M B T t : ℝ} {r q Q : ℕ} (hM : 0 < M) (hB : 0 < B)
    (k : ℕ) (a : ArithmeticFunction ℂ) (χ : BlueprintCharacter Q)
    (χcut : ℕ → ℂ)
    (hχcut : ∀ n, χcut n =
      if Nat.Coprime n q then evalInt χ (n : ℤ) else 0) :
    (B : ℂ) * factorPolynomialWindow M ((2 : ℝ) ^ k * M)
        (selectedGroupTrilinearCoeff B r (fun n => a n) χcut T) t =
      finiteAllocatedDirichletPolynomial a r q
        (factorExtractionRealInterval M ((2 : ℝ) ^ k * M)) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
  calc
    (B : ℂ) * factorPolynomialWindow M ((2 : ℝ) ^ k * M)
        (selectedGroupTrilinearCoeff B r (fun n => a n) χcut T) t =
      ∑ i ∈ Finset.range k,
        finiteAllocatedDirichletPolynomial a r q
          (factorExtractionRealInterval ((2 : ℝ) ^ i * M)
            (2 * ((2 : ℝ) ^ i * M))) χ
          ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) :=
      selectedGroupFactorPolynomialWindow_eq_allocatedBlockSum
        hM hB k a χ χcut hχcut
    _ = finiteAllocatedDirichletPolynomial a r q
        (factorExtractionRealInterval M ((2 : ℝ) ^ k * M)) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
      symm
      exact finiteAllocatedDirichletPolynomial_eq_sum_dyadicWindows
        hM.le k a r q χ _

/-- The source-scaled broad selected-group polynomial is the actual finite
`Icc 1 P` allocation whenever its coefficients satisfy the stated source
support and cutoff bounds. -/
theorem selectedGroupFactorPolynomialWindow_eq_allocatedCutoff_of_scaledSupport
    {M C B T t : ℝ} {r q Q k P : ℕ}
    (hM : 0 < M) (hC : 1 ≤ C) (hr : 0 < r)
    (hcover : 4 * C ^ 2 ≤ (2 : ℝ) ^ k) (hB : 0 < B)
    (a : ArithmeticFunction ℂ) (χ : BlueprintCharacter Q)
    (χcut : ℕ → ℂ)
    (hχcut : ∀ n, χcut n =
      if Nat.Coprime n q then evalInt χ (n : ℤ) else 0)
    (hcutoff : ∀ n, a (r * n) ≠ 0 → n ≤ P)
    (hsupport : ∀ n, a (r * n) ≠ 0 →
      M / C ≤ ((r * n : ℕ) : ℝ) ∧ ((r * n : ℕ) : ℝ) ≤ C * M) :
    (B : ℂ) * factorPolynomialWindow (M / (4 * C * (r : ℝ)))
        ((2 : ℝ) ^ k * (M / (4 * C * (r : ℝ))))
        (selectedGroupTrilinearCoeff B r (fun n => a n) χcut T) t =
      finiteAllocatedDirichletPolynomial a r q (Finset.Icc 1 P) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
  have hbase : 0 < M / (4 * C * (r : ℝ)) := by
    apply div_pos hM
    positivity
  have hwindow := selectedGroupFactorPolynomialWindow_eq_allocatedWindow
    (M := M / (4 * C * (r : ℝ))) (B := B) (T := T) (t := t)
    (r := r) (q := q) (Q := Q) hbase hB k a χ χcut hχcut
  rw [hwindow]
  exact (finiteAllocatedDirichletPolynomial_eq_of_scaledSupport
    hM hC hr hcover a χ _ hcutoff hsupport).symm

/-- Expanding three broad windows into their exact dyadic blocks and applying
the selected-group identity on each block gives the exact finite product
allocation sum. The coefficient functions retain their original allocation,
character, and archimedean-twist data. -/
theorem selectedGroupTripleWindowProduct_eq_allocatedBlockSum
    {M₁ M₂ M₃ B₁ B₂ B₃ T t : ℝ}
    {r₁ r₂ r₃ q₁ q₂ q₃ Q : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (hB₃ : 0 < B₃)
    (k₁ k₂ k₃ : ℕ)
    (a₁ a₂ a₃ : ArithmeticFunction ℂ)
    (χ : BlueprintCharacter Q)
    (χcut₁ χcut₂ χcut₃ : ℕ → ℂ)
    (hχcut₁ : ∀ n, χcut₁ n =
      if Nat.Coprime n q₁ then evalInt χ (n : ℤ) else 0)
    (hχcut₂ : ∀ n, χcut₂ n =
      if Nat.Coprime n q₂ then evalInt χ (n : ℤ) else 0)
    (hχcut₃ : ∀ n, χcut₃ n =
      if Nat.Coprime n q₃ then evalInt χ (n : ℤ) else 0) :
    ((B₁ * B₂ * B₃ : ℝ) : ℂ) *
        (factorPolynomialWindow M₁ ((2 : ℝ) ^ k₁ * M₁)
            (selectedGroupTrilinearCoeff B₁ r₁ (fun n => a₁ n)
              χcut₁ T) t *
          factorPolynomialWindow M₂ ((2 : ℝ) ^ k₂ * M₂)
            (selectedGroupTrilinearCoeff B₂ r₂ (fun n => a₂ n)
              χcut₂ T) t *
          factorPolynomialWindow M₃ ((2 : ℝ) ^ k₃ * M₃)
            (selectedGroupTrilinearCoeff B₃ r₃ (fun n => a₃ n)
              χcut₃ T) t) =
      ∑ i ∈ Finset.range k₁,
        ∑ j ∈ Finset.range k₂,
          ∑ k ∈ Finset.range k₃,
            finiteAllocatedDirichletPolynomial a₁ r₁ q₁
                (factorExtractionRealInterval ((2 : ℝ) ^ i * M₁)
                  (2 * ((2 : ℝ) ^ i * M₁))) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
              finiteAllocatedDirichletPolynomial a₂ r₂ q₂
                (factorExtractionRealInterval ((2 : ℝ) ^ j * M₂)
                  (2 * ((2 : ℝ) ^ j * M₂))) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
              finiteAllocatedDirichletPolynomial a₃ r₃ q₃
                (factorExtractionRealInterval ((2 : ℝ) ^ k * M₃)
                  (2 * ((2 : ℝ) ^ k * M₃))) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
  classical
  let c₁ : ℕ → ℂ := selectedGroupTrilinearCoeff B₁ r₁
    (fun n => a₁ n) χcut₁ T
  let c₂ : ℕ → ℂ := selectedGroupTrilinearCoeff B₂ r₂
    (fun n => a₂ n) χcut₂ T
  let c₃ : ℕ → ℂ := selectedGroupTrilinearCoeff B₃ r₃
    (fun n => a₃ n) χcut₃ T
  let f₁ : ℕ → ℂ := fun i => factorPolynomial ((2 : ℝ) ^ i * M₁) c₁ t
  let f₂ : ℕ → ℂ := fun j => factorPolynomial ((2 : ℝ) ^ j * M₂) c₂ t
  let f₃ : ℕ → ℂ := fun k => factorPolynomial ((2 : ℝ) ^ k * M₃) c₃ t
  have hwindow₁ := factorPolynomialWindow_eq_sum_dyadicWindows
    hM₁.le k₁ c₁ t
  have hwindow₂ := factorPolynomialWindow_eq_sum_dyadicWindows
    hM₂.le k₂ c₂ t
  have hwindow₃ := factorPolynomialWindow_eq_sum_dyadicWindows
    hM₃.le k₃ c₃ t
  have h12 :
      (∑ i ∈ Finset.range k₁, f₁ i) *
          (∑ j ∈ Finset.range k₂, f₂ j) =
        ∑ i ∈ Finset.range k₁,
          ∑ j ∈ Finset.range k₂, f₁ i * f₂ j := by
    calc
      _ = ∑ i ∈ Finset.range k₁,
            f₁ i * (∑ j ∈ Finset.range k₂, f₂ j) := Finset.sum_mul ..
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
  have h123 :
      ((∑ i ∈ Finset.range k₁, f₁ i) *
          (∑ j ∈ Finset.range k₂, f₂ j)) *
          (∑ k ∈ Finset.range k₃, f₃ k) =
        ∑ i ∈ Finset.range k₁,
          ∑ j ∈ Finset.range k₂,
            ∑ k ∈ Finset.range k₃,
              (f₁ i * f₂ j) * f₃ k := by
    calc
      _ = (∑ i ∈ Finset.range k₁,
            ∑ j ∈ Finset.range k₂, f₁ i * f₂ j) *
              (∑ k ∈ Finset.range k₃, f₃ k) := by rw [h12]
      _ = ∑ i ∈ Finset.range k₁,
            ∑ j ∈ Finset.range k₂,
              (f₁ i * f₂ j) *
                (∑ k ∈ Finset.range k₃, f₃ k) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
  have hscaled :
      ((B₁ * B₂ * B₃ : ℝ) : ℂ) *
          ((∑ i ∈ Finset.range k₁, f₁ i) *
            (∑ j ∈ Finset.range k₂, f₂ j) *
              (∑ k ∈ Finset.range k₃, f₃ k)) =
        ∑ i ∈ Finset.range k₁,
          ∑ j ∈ Finset.range k₂,
            ∑ k ∈ Finset.range k₃,
              (((B₁ : ℂ) * f₁ i) * ((B₂ : ℂ) * f₂ j)) *
                ((B₃ : ℂ) * f₃ k) := by
    rw [h123]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    ring
  have halloc₁ : ∀ i ∈ Finset.range k₁,
      (B₁ : ℂ) * f₁ i =
        finiteAllocatedDirichletPolynomial a₁ r₁ q₁
          (factorExtractionRealInterval ((2 : ℝ) ^ i * M₁)
            (2 * ((2 : ℝ) ^ i * M₁))) χ
          ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
    intro i hi
    have hMi : 0 < (2 : ℝ) ^ i * M₁ := mul_pos (by positivity) hM₁
    simpa [f₁, c₁] using selectedGroupFactorPolynomial_eq_allocatedFactorWindow
      hMi hB₁ a₁ χ χcut₁ hχcut₁
  have halloc₂ : ∀ j ∈ Finset.range k₂,
      (B₂ : ℂ) * f₂ j =
        finiteAllocatedDirichletPolynomial a₂ r₂ q₂
          (factorExtractionRealInterval ((2 : ℝ) ^ j * M₂)
            (2 * ((2 : ℝ) ^ j * M₂))) χ
          ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
    intro j hj
    have hMj : 0 < (2 : ℝ) ^ j * M₂ := mul_pos (by positivity) hM₂
    simpa [f₂, c₂] using selectedGroupFactorPolynomial_eq_allocatedFactorWindow
      hMj hB₂ a₂ χ χcut₂ hχcut₂
  have halloc₃ : ∀ k ∈ Finset.range k₃,
      (B₃ : ℂ) * f₃ k =
        finiteAllocatedDirichletPolynomial a₃ r₃ q₃
          (factorExtractionRealInterval ((2 : ℝ) ^ k * M₃)
            (2 * ((2 : ℝ) ^ k * M₃))) χ
          ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
    intro k hk
    have hMk : 0 < (2 : ℝ) ^ k * M₃ := mul_pos (by positivity) hM₃
    simpa [f₃, c₃] using selectedGroupFactorPolynomial_eq_allocatedFactorWindow
      hMk hB₃ a₃ χ χcut₃ hχcut₃
  calc
    _ = ((B₁ * B₂ * B₃ : ℝ) : ℂ) *
          ((∑ i ∈ Finset.range k₁, f₁ i) *
            (∑ j ∈ Finset.range k₂, f₂ j) *
              (∑ k ∈ Finset.range k₃, f₃ k)) := by
        rw [hwindow₁, hwindow₂, hwindow₃]
    _ = _ := by
      rw [hscaled]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [halloc₁ i hi, halloc₂ j hj, halloc₃ k hk]

/-- Under the explicit source support and finite-cutoff hypotheses for each
of the three factors, the product of the actual `Icc` allocations is the
exact sum of the allocation products on all dyadic support blocks. The
number of terms is the product of the three stated block counts. -/
theorem selectedGroupTripleCutoffProduct_eq_allocatedBlockSum_of_scaledSupport
    {M₁ M₂ M₃ C₁ C₂ C₃ B₁ B₂ B₃ T t : ℝ}
    {r₁ r₂ r₃ q₁ q₂ q₃ Q k₁ k₂ k₃ P₁ P₂ P₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hC₃ : 1 ≤ C₃)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (hcover₁ : 4 * C₁ ^ 2 ≤ (2 : ℝ) ^ k₁)
    (hcover₂ : 4 * C₂ ^ 2 ≤ (2 : ℝ) ^ k₂)
    (hcover₃ : 4 * C₃ ^ 2 ≤ (2 : ℝ) ^ k₃)
    (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (hB₃ : 0 < B₃)
    (a₁ a₂ a₃ : ArithmeticFunction ℂ) (χ : BlueprintCharacter Q)
    (χcut₁ χcut₂ χcut₃ : ℕ → ℂ)
    (hχcut₁ : ∀ n, χcut₁ n =
      if Nat.Coprime n q₁ then evalInt χ (n : ℤ) else 0)
    (hχcut₂ : ∀ n, χcut₂ n =
      if Nat.Coprime n q₂ then evalInt χ (n : ℤ) else 0)
    (hχcut₃ : ∀ n, χcut₃ n =
      if Nat.Coprime n q₃ then evalInt χ (n : ℤ) else 0)
    (hcutoff₁ : ∀ n, a₁ (r₁ * n) ≠ 0 → n ≤ P₁)
    (hcutoff₂ : ∀ n, a₂ (r₂ * n) ≠ 0 → n ≤ P₂)
    (hcutoff₃ : ∀ n, a₃ (r₃ * n) ≠ 0 → n ≤ P₃)
    (hsupport₁ : ∀ n, a₁ (r₁ * n) ≠ 0 →
      M₁ / C₁ ≤ ((r₁ * n : ℕ) : ℝ) ∧
        ((r₁ * n : ℕ) : ℝ) ≤ C₁ * M₁)
    (hsupport₂ : ∀ n, a₂ (r₂ * n) ≠ 0 →
      M₂ / C₂ ≤ ((r₂ * n : ℕ) : ℝ) ∧
        ((r₂ * n : ℕ) : ℝ) ≤ C₂ * M₂)
    (hsupport₃ : ∀ n, a₃ (r₃ * n) ≠ 0 →
      M₃ / C₃ ≤ ((r₃ * n : ℕ) : ℝ) ∧
        ((r₃ * n : ℕ) : ℝ) ≤ C₃ * M₃) :
    finiteAllocatedDirichletPolynomial a₁ r₁ q₁ (Finset.Icc 1 P₁) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
      finiteAllocatedDirichletPolynomial a₂ r₂ q₂ (Finset.Icc 1 P₂) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
      finiteAllocatedDirichletPolynomial a₃ r₃ q₃ (Finset.Icc 1 P₃) χ
        ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) =
      ∑ i ∈ Finset.range k₁,
        ∑ j ∈ Finset.range k₂,
          ∑ k ∈ Finset.range k₃,
            finiteAllocatedDirichletPolynomial a₁ r₁ q₁
                (factorExtractionRealInterval
                  ((2 : ℝ) ^ i * (M₁ / (4 * C₁ * (r₁ : ℝ))))
                  (2 * ((2 : ℝ) ^ i * (M₁ / (4 * C₁ * (r₁ : ℝ))))) ) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
              finiteAllocatedDirichletPolynomial a₂ r₂ q₂
                (factorExtractionRealInterval
                  ((2 : ℝ) ^ j * (M₂ / (4 * C₂ * (r₂ : ℝ))))
                  (2 * ((2 : ℝ) ^ j * (M₂ / (4 * C₂ * (r₂ : ℝ))))) ) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) *
              finiteAllocatedDirichletPolynomial a₃ r₃ q₃
                (factorExtractionRealInterval
                  ((2 : ℝ) ^ k * (M₃ / (4 * C₃ * (r₃ : ℝ))))
                  (2 * ((2 : ℝ) ^ k * (M₃ / (4 * C₃ * (r₃ : ℝ))))) ) χ
                ((1 / 2 : ℂ) + Complex.I * ((t - T : ℝ) : ℂ)) := by
  let W₁ : ℝ := M₁ / (4 * C₁ * (r₁ : ℝ))
  let W₂ : ℝ := M₂ / (4 * C₂ * (r₂ : ℝ))
  let W₃ : ℝ := M₃ / (4 * C₃ * (r₃ : ℝ))
  have hW₁ : 0 < W₁ := by dsimp [W₁]; apply div_pos hM₁; positivity
  have hW₂ : 0 < W₂ := by dsimp [W₂]; apply div_pos hM₂; positivity
  have hW₃ : 0 < W₃ := by dsimp [W₃]; apply div_pos hM₃; positivity
  let p₁ : ℝ → ℂ := factorPolynomialWindow W₁ ((2 : ℝ) ^ k₁ * W₁)
    (selectedGroupTrilinearCoeff B₁ r₁ (fun n => a₁ n) χcut₁ T)
  let p₂ : ℝ → ℂ := factorPolynomialWindow W₂ ((2 : ℝ) ^ k₂ * W₂)
    (selectedGroupTrilinearCoeff B₂ r₂ (fun n => a₂ n) χcut₂ T)
  let p₃ : ℝ → ℂ := factorPolynomialWindow W₃ ((2 : ℝ) ^ k₃ * W₃)
    (selectedGroupTrilinearCoeff B₃ r₃ (fun n => a₃ n) χcut₃ T)
  have hsource₁ := selectedGroupFactorPolynomialWindow_eq_allocatedCutoff_of_scaledSupport
    (M := M₁) (C := C₁) (B := B₁) (T := T) (t := t)
    (r := r₁) (q := q₁) (Q := Q) (k := k₁) (P := P₁)
    hM₁ hC₁ hr₁ hcover₁ hB₁ a₁ χ χcut₁ hχcut₁ hcutoff₁ hsupport₁
  have hsource₂ := selectedGroupFactorPolynomialWindow_eq_allocatedCutoff_of_scaledSupport
    (M := M₂) (C := C₂) (B := B₂) (T := T) (t := t)
    (r := r₂) (q := q₂) (Q := Q) (k := k₂) (P := P₂)
    hM₂ hC₂ hr₂ hcover₂ hB₂ a₂ χ χcut₂ hχcut₂ hcutoff₂ hsupport₂
  have hsource₃ := selectedGroupFactorPolynomialWindow_eq_allocatedCutoff_of_scaledSupport
    (M := M₃) (C := C₃) (B := B₃) (T := T) (t := t)
    (r := r₃) (q := q₃) (Q := Q) (k := k₃) (P := P₃)
    hM₃ hC₃ hr₃ hcover₃ hB₃ a₃ χ χcut₃ hχcut₃ hcutoff₃ hsupport₃
  have hblocks := selectedGroupTripleWindowProduct_eq_allocatedBlockSum
    (M₁ := W₁) (M₂ := W₂) (M₃ := W₃) (B₁ := B₁) (B₂ := B₂) (B₃ := B₃)
    (T := T) (t := t) (r₁ := r₁) (r₂ := r₂) (r₃ := r₃)
    (q₁ := q₁) (q₂ := q₂) (q₃ := q₃) (Q := Q)
    hW₁ hW₂ hW₃ hB₁ hB₂ hB₃ k₁ k₂ k₃ a₁ a₂ a₃ χ
    χcut₁ χcut₂ χcut₃ hχcut₁ hχcut₂ hχcut₃
  calc
    _ = ((B₁ : ℂ) * p₁ t) * ((B₂ : ℂ) * p₂ t) * ((B₃ : ℂ) * p₃ t) := by
      rw [← hsource₁, ← hsource₂, ← hsource₃]
    _ = ((B₁ * B₂ * B₃ : ℝ) : ℂ) * (p₁ t * p₂ t * p₃ t) := by
      push_cast
      ring
    _ = _ := by
      simpa [p₁, p₂, p₃, W₁, W₂, W₃] using hblocks

#print axioms factorPolynomialWindow_eq_sum_dyadicWindows
#print axioms finiteAllocatedDirichletPolynomial_eq_of_mutual_support
#print axioms allocatedIndex_mem_dyadicWindow_of_scaledSupport
#print axioms finiteAllocatedDirichletPolynomial_eq_of_scaledSupport
#print axioms selectedGroupFactorPolynomial_eq_allocatedFactorWindow
#print axioms selectedGroupFactorPolynomialWindow_eq_allocatedBlockSum
#print axioms selectedGroupFactorPolynomialWindow_eq_allocatedCutoff_of_scaledSupport
#print axioms selectedGroupTripleWindowProduct_eq_allocatedBlockSum
#print axioms selectedGroupTripleCutoffProduct_eq_allocatedBlockSum_of_scaledSupport

end FractionalPrimes.Literature.DirichletMean

end
