module

public import FractionalPrimes.Literature.Polynomial.PolynomialRecurrenceFejerKernel
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.Finset.Sort

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes

private theorem fejerSum_centeredFrequency (K : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range K, unitFrequencyPhase ((j : ℝ) * t)) =
      ∑ j ∈ Finset.range K,
        unitFrequencyPhase ((j : ℝ) * centeredFrequency t) := by
  classical
  let m : ℤ := Int.floor (t + 1 / 2)
  let c : ℝ := centeredFrequency t
  have ht : t = c + (m : ℝ) := by
    dsimp [c, centeredFrequency, m]
    ring
  apply Finset.sum_congr rfl
  intro j hj
  have harg : (j : ℝ) * t =
      (j : ℝ) * c + (((j : ℤ) * m : ℤ) : ℝ) := by
    rw [ht]
    push_cast
    ring
  rw [harg, unitFrequencyPhase_add, unitFrequencyPhase_int]
  simp [c]

private theorem norm_sq_sum_eq_re_pair {α : Type*} (s : Finset α)
    (f : α → ℂ) :
    ‖∑ a ∈ s, f a‖ ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, (star (f a) * f b).re := by
  classical
  calc
    ‖∑ a ∈ s, f a‖ ^ 2 = Complex.normSq (∑ a ∈ s, f a) :=
      (Complex.normSq_eq_norm_sq _).symm
    _ = (star (∑ a ∈ s, f a) * ∑ a ∈ s, f a).re := by
      have h := congrArg Complex.re
        (Complex.normSq_eq_conj_mul_self (z := ∑ a ∈ s, f a))
      simpa using h
    _ = ∑ a ∈ s, ∑ b ∈ s, (star (f a) * f b).re := by
      rw [star_sum, Finset.sum_mul]
      simp_rw [Finset.mul_sum, Complex.re_sum]

private theorem unitFrequencyPhase_pair (a b : ℝ) :
    (starRingEnd ℂ) (unitFrequencyPhase a) * unitFrequencyPhase b =
      unitFrequencyPhase (b - a) := by
  calc
    (starRingEnd ℂ) (unitFrequencyPhase a) * unitFrequencyPhase b =
        unitFrequencyPhase (-a) * unitFrequencyPhase b := by
          congr 1
          simpa using (unitFrequencyPhase_neg_eq_conj a).symm
    _ = unitFrequencyPhase ((-a) + b) := by
          rw [← unitFrequencyPhase_add]
    _ = unitFrequencyPhase (b - a) := by congr 1 <;> ring

private theorem fejerNegativeCorrelationNorm (N k : ℕ) (y : ℕ → ℝ) :
    ‖∑ n ∈ Finset.range N,
        unitFrequencyPhase (-((k : ℝ) * y (n + 1)))‖ =
      ‖∑ n ∈ Finset.range N,
        unitFrequencyPhase ((k : ℝ) * y (n + 1))‖ := by
  have hsum :
      (∑ n ∈ Finset.range N,
        unitFrequencyPhase (-((k : ℝ) * y (n + 1)))) =
        star (∑ n ∈ Finset.range N,
          unitFrequencyPhase ((k : ℝ) * y (n + 1))) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simpa using unitFrequencyPhase_neg_eq_conj ((k : ℝ) * y (n + 1))
  rw [hsum, norm_star]

/-- A positive-density collection of near-integer phases forces a small
positive integer frequency with a large normalized exponential sum. This is
the finite Fejér detection lemma used in the polynomial recurrence closure. -/
theorem fejerDetectsRecurrence
    {N : ℕ} (hN : 1 ≤ N)
    {δ ε : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ / 64)
    (y : ℕ → ℝ)
    (hgood : δ * (N : ℝ) ≤
      (((Finset.range N).filter
        (fun n => realDistanceToIntegers (y (n + 1)) ≤ ε)).card : ℝ)) :
    ∃ k : ℕ, 1 ≤ k ∧ k < Nat.ceil (16 / δ) ∧
      δ / 10 ≤ ‖(∑ n ∈ Finset.range N,
        unitFrequencyPhase ((k : ℝ) * y (n + 1))) / (N : ℂ)‖ := by
  classical
  let K : ℕ := Nat.ceil (16 / δ)
  let G : Finset ℕ := (Finset.range N).filter
    (fun n => realDistanceToIntegers (y (n + 1)) ≤ ε)
  let kernelSum : ℕ → ℂ := fun n =>
    ∑ j ∈ Finset.range K, unitFrequencyPhase ((j : ℝ) * y (n + 1))
  let H : ℝ := ∑ n ∈ Finset.range N, ‖kernelSum n‖ ^ 2
  have hKposNat : 0 < K := by
    dsimp [K]
    have hceil : 16 / δ ≤ (Nat.ceil (16 / δ) : ℝ) := Nat.le_ceil _
    have : 0 < 16 / δ := by positivity
    exact_mod_cast (lt_of_lt_of_le this hceil)
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast hKposNat
  have hKlower : 16 ≤ (K : ℝ) * δ := by
    have hceil : 16 / δ ≤ (K : ℝ) := by
      dsimp [K]
      exact Nat.le_ceil _
    calc
      16 = (16 / δ) * δ := by field_simp [ne_of_gt hδ]
      _ ≤ (K : ℝ) * δ := mul_le_mul_of_nonneg_right hceil hδ.le
  have hKceilUpper : (K : ℝ) < 16 / δ + 1 := by
    dsimp [K]
    exact Nat.ceil_lt_add_one (le_of_lt (by positivity))
  have hKdeltaUpper : (K : ℝ) * δ < 17 := by
    calc
      (K : ℝ) * δ < (16 / δ + 1) * δ :=
        mul_lt_mul_of_pos_right hKceilUpper hδ
      _ = 16 + δ := by field_simp [ne_of_gt hδ]
      _ < 17 := by linarith
  have hKε : (K : ℝ) * ε ≤ 17 / 64 := by
    calc
      (K : ℝ) * ε ≤ (K : ℝ) * (δ / 64) :=
        mul_le_mul_of_nonneg_left hεδ (Nat.cast_nonneg K)
      _ = ((K : ℝ) * δ) / 64 := by ring
      _ ≤ 17 / 64 := by
        apply div_le_div_of_nonneg_right hKdeltaUpper.le
        norm_num
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hGcard : δ * (N : ℝ) ≤ (G.card : ℝ) := by
    simpa [G] using hgood
  have hkernelGood (n : ℕ) (hn : n ∈ G) :
      (K : ℝ) ^ 2 / 4 ≤ ‖kernelSum n‖ ^ 2 := by
    have hdist :
        |centeredFrequency (y (n + 1))| ≤ ε := by
      rw [← realDistanceToIntegers_eq_abs_centered]
      exact (Finset.mem_filter.mp hn).2
    have hkernel := polynomialRecurrence_fejerKernel_lower K
      (by exact_mod_cast (show 1 ≤ K by omega)) hdist hKε
    rw [← fejerSum_centeredFrequency K (y (n + 1))] at hkernel
    have hmul := (le_div_iff₀ hKpos).mp hkernel
    dsimp [kernelSum]
    nlinarith [hmul]
  have hsumGood :
      (G.card : ℝ) * ((K : ℝ) ^ 2 / 4) ≤
        ∑ n ∈ G, ‖kernelSum n‖ ^ 2 := by
    calc
      (G.card : ℝ) * ((K : ℝ) ^ 2 / 4) =
          ∑ _n ∈ G, ((K : ℝ) ^ 2 / 4) := by simp
      _ ≤ ∑ n ∈ G, ‖kernelSum n‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact hkernelGood n hn
  have hsumSubset :
      (∑ n ∈ G, ‖kernelSum n‖ ^ 2) ≤ H := by
    dsimp [H]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact (Finset.mem_filter.mp hn).1
    · intro n hn hnot
      positivity
  have hHlower :
      4 * (N : ℝ) * (K : ℝ) ≤ H := by
    have hscaled :
        δ * (N : ℝ) * ((K : ℝ) ^ 2 / 4) ≤
          (G.card : ℝ) * ((K : ℝ) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_right hGcard (by positivity)
    have hcompare :
        4 * (N : ℝ) * (K : ℝ) ≤
          δ * (N : ℝ) * ((K : ℝ) ^ 2 / 4) := by
      have hmul := mul_le_mul_of_nonneg_right hKlower
        (show 0 ≤ (N : ℝ) * (K : ℝ) / 4 by positivity)
      nlinarith [hmul]
    dsimp [H]
    linarith [hcompare, hscaled, hsumGood, hsumSubset]
  by_contra hnone
  have hsmall (k : ℕ) (hk : k ∈ Finset.Ico 1 K) :
      ‖∑ n ∈ Finset.range N,
        unitFrequencyPhase ((k : ℝ) * y (n + 1))‖ <
          (δ / 10) * (N : ℝ) := by
    have hnot :
        ¬ δ / 10 ≤ ‖(∑ n ∈ Finset.range N,
          unitFrequencyPhase ((k : ℝ) * y (n + 1))) / (N : ℂ)‖ := by
      intro hbound
      apply hnone
      exact ⟨k, (Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2, hbound⟩
    have hdiv :
        ‖(∑ n ∈ Finset.range N,
          unitFrequencyPhase ((k : ℝ) * y (n + 1))) / (N : ℂ)‖ =
          ‖∑ n ∈ Finset.range N,
            unitFrequencyPhase ((k : ℝ) * y (n + 1))‖ / (N : ℝ) := by
      rw [norm_div, Complex.norm_natCast]
    rw [hdiv] at hnot
    exact (div_lt_iff₀ hNpos).mp (not_le.mp hnot)
  let corr : ℕ → ℕ → ℝ := fun j l =>
    ∑ n ∈ Finset.range N,
      (unitFrequencyPhase (((l : ℝ) - (j : ℝ)) * y (n + 1))).re
  have hcorrBound (j l : ℕ) (hj : j ∈ Finset.range K)
      (hl : l ∈ Finset.range K) :
      corr j l ≤ (if j = l then (N : ℝ) else 0) +
        (δ / 10) * (N : ℝ) := by
    by_cases heq : j = l
    · subst l
      have hnonneg : 0 ≤ (δ / 10) * (N : ℝ) := by positivity
      simp [corr, unitFrequencyPhase]
      exact hnonneg
    · rcases lt_or_gt_of_ne heq with hjl | hlj
      · let k := l - j
        have hkpos : 1 ≤ k := by dsimp [k]; omega
        have hklt : k < K := by
          dsimp [k]
          exact lt_of_le_of_lt (Nat.sub_le _ _) (Finset.mem_range.mp hl)
        have hk : k ∈ Finset.Ico 1 K := Finset.mem_Ico.mpr ⟨hkpos, hklt⟩
        have hcast : (l : ℝ) - (j : ℝ) = (k : ℝ) := by
          dsimp [k]
          rw [Nat.cast_sub (Nat.le_of_lt hjl)]
        have hcorrEq : corr j l =
            (∑ n ∈ Finset.range N,
              unitFrequencyPhase ((k : ℝ) * y (n + 1))).re := by
          dsimp [corr]
          rw [Complex.re_sum]
          apply Finset.sum_congr rfl
          intro n hn
          congr 1
          rw [hcast]
        have habs : |corr j l| ≤
            ‖∑ n ∈ Finset.range N,
              unitFrequencyPhase ((k : ℝ) * y (n + 1))‖ := by
          rw [hcorrEq]
          exact Complex.abs_re_le_norm _
        have hcorrsmall := hsmall k hk
        have hle : corr j l ≤ (δ / 10) * (N : ℝ) := by
          apply le_of_lt
          calc
            corr j l ≤ |corr j l| := le_abs_self _
            _ ≤ ‖∑ n ∈ Finset.range N,
                unitFrequencyPhase ((k : ℝ) * y (n + 1))‖ := habs
            _ < (δ / 10) * (N : ℝ) := hcorrsmall
        simpa [heq] using hle
      · let k := j - l
        have hkpos : 1 ≤ k := by dsimp [k]; omega
        have hklt : k < K := by
          dsimp [k]
          exact lt_of_le_of_lt (Nat.sub_le _ _) (Finset.mem_range.mp hj)
        have hk : k ∈ Finset.Ico 1 K := Finset.mem_Ico.mpr ⟨hkpos, hklt⟩
        have hcast : (l : ℝ) - (j : ℝ) = - (k : ℝ) := by
          dsimp [k]
          rw [Nat.cast_sub (Nat.le_of_lt hlj)]
          ring
        have hcorrEq : corr j l =
            (∑ n ∈ Finset.range N,
              unitFrequencyPhase (-((k : ℝ) * y (n + 1)))).re := by
          dsimp [corr]
          rw [Complex.re_sum]
          apply Finset.sum_congr rfl
          intro n hn
          congr 1
          rw [hcast]
          ring
        have hnormEq := fejerNegativeCorrelationNorm N k y
        have habs : |corr j l| ≤
            ‖∑ n ∈ Finset.range N,
              unitFrequencyPhase ((k : ℝ) * y (n + 1))‖ := by
          rw [hcorrEq, ← hnormEq]
          exact Complex.abs_re_le_norm _
        have hcorrsmall := hsmall k hk
        have hle : corr j l ≤ (δ / 10) * (N : ℝ) := by
          apply le_of_lt
          calc
            corr j l ≤ |corr j l| := le_abs_self _
            _ ≤ ‖∑ n ∈ Finset.range N,
                unitFrequencyPhase ((k : ℝ) * y (n + 1))‖ := habs
            _ < (δ / 10) * (N : ℝ) := hcorrsmall
        simpa [heq] using hle
  have hdiagSum :
      (∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
        (if j = l then (N : ℝ) else 0)) = (K : ℝ) * (N : ℝ) := by
    calc
      (∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
        (if j = l then (N : ℝ) else 0)) =
          ∑ j ∈ Finset.range K, (N : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [eq_comm, Finset.sum_ite_eq']
        simp [hj]
      _ = (K : ℝ) * (N : ℝ) := by simp
  have hconstantSum :
      (∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
        (δ / 10) * (N : ℝ)) =
        (K : ℝ) ^ 2 * ((δ / 10) * (N : ℝ)) := by
    simp
    ring
  have hcorrSumUpper :
      (∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, corr j l) ≤
        (K : ℝ) * (N : ℝ) +
          (K : ℝ) ^ 2 * ((δ / 10) * (N : ℝ)) := by
    calc
      (∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, corr j l) ≤
          ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
            ((if j = l then (N : ℝ) else 0) +
              (δ / 10) * (N : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro l hl
        exact hcorrBound j l hj hl
      _ = (K : ℝ) * (N : ℝ) +
          (K : ℝ) ^ 2 * ((δ / 10) * (N : ℝ)) := by
        simp_rw [Finset.sum_add_distrib]
        rw [hdiagSum, hconstantSum]
  have hExpand : H = ∑ j ∈ Finset.range K,
      ∑ l ∈ Finset.range K, corr j l := by
    have hExpand0 : H =
        ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range K,
          ∑ l ∈ Finset.range K,
            (star (unitFrequencyPhase ((j : ℝ) * y (n + 1))) *
              unitFrequencyPhase ((l : ℝ) * y (n + 1))).re := by
      dsimp [H, kernelSum]
      apply Finset.sum_congr rfl
      intro n hn
      simpa using norm_sq_sum_eq_re_pair (Finset.range K)
        (fun j => unitFrequencyPhase ((j : ℝ) * y (n + 1)))
    calc
      H = ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
          ∑ n ∈ Finset.range N,
            (star (unitFrequencyPhase ((j : ℝ) * y (n + 1))) *
              unitFrequencyPhase ((l : ℝ) * y (n + 1))).re := by
        rw [hExpand0, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
      _ = ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, corr j l := by
        dsimp [corr]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro n hn
        rw [unitFrequencyPhase_pair]
        congr 1
        ring
  have hfactor : 1 + (K : ℝ) * δ / 10 < 4 := by
    nlinarith [hKdeltaUpper]
  have hNKpos : 0 < (N : ℝ) * (K : ℝ) := mul_pos hNpos hKpos
  have hstrictUpper :
      (K : ℝ) * (N : ℝ) +
          (K : ℝ) ^ 2 * ((δ / 10) * (N : ℝ)) <
        4 * (N : ℝ) * (K : ℝ) := by
    calc
      (K : ℝ) * (N : ℝ) +
          (K : ℝ) ^ 2 * ((δ / 10) * (N : ℝ)) =
        (1 + (K : ℝ) * δ / 10) * ((N : ℝ) * (K : ℝ)) := by ring
      _ < 4 * ((N : ℝ) * (K : ℝ)) :=
        mul_lt_mul_of_pos_right hfactor hNKpos
      _ = 4 * (N : ℝ) * (K : ℝ) := by ring
  have hupper : H < 4 * (N : ℝ) * (K : ℝ) :=
    lt_of_le_of_lt (by rw [hExpand]; exact hcorrSumUpper) hstrictUpper
  linarith [hHlower, hupper]

end FractionalPrimes.Literature.Polynomial
