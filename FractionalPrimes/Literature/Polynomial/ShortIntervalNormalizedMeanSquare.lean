module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalDirichletSampleSquare
public import FractionalPrimes.Literature.Uniformity.DivisorMomentBound

/-! The mean-square contribution to the normalized divisor-bounded
large-value count in `lgv:normalized`. -/

@[expose] public section

open scoped BigOperators

namespace FractionalPrimes.Literature.LargeValues

noncomputable section

def normalizedDirichletCoeff (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  b n / (Real.sqrt (n : ℝ) : ℂ)

def normalizedDivisorExponent (C : ℕ) : ℕ :=
  2 ^ (2 * C) - 1

private lemma dirichletIndices_subset_floor (N : ℝ) (hN : 0 ≤ N) :
    dirichletIndices N ⊆ Finset.Icc 1 (Nat.floor (2 * N)) := by
  intro n hn
  rw [dirichletIndices, Finset.mem_filter, Finset.mem_range] at hn
  rcases hn with ⟨hnrange, hleft⟩
  rw [Finset.mem_Icc]
  constructor
  · have hnpos : 0 < (n : ℝ) := lt_of_le_of_lt hN hleft
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hnpos.ne')
  · exact Nat.le_of_lt_succ hnrange

private lemma normalizedDirichletEnergy_bound
    (C : ℕ) (N : ℝ) (b : ℕ → ℂ) (hN : 2 ≤ N)
    (hcoeff : ∀ n ∈ dirichletIndices N,
      ‖b n‖ ≤ (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) :
    dirichletEnergy N (normalizedDirichletCoeff b) ≤
      2 * (1 + Real.log (2 * N)) ^ normalizedDivisorExponent C := by
  classical
  have hNpos : 0 < N := by linarith
  have hNge1 : 1 ≤ N := by linarith
  have hindices := dirichletIndices_subset_floor N (by linarith)
  have henergyTerm (n : ℕ) (hn : n ∈ dirichletIndices N) :
      ‖normalizedDirichletCoeff b n‖ ^ 2 ≤
        ((FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ (2 * C)) / N := by
    have hnBounds : N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N := by
      rw [dirichletIndices, Finset.mem_filter, Finset.mem_range] at hn
      rcases hn with ⟨hnrange, hleft⟩
      have hfloor : (n : ℝ) ≤ Nat.floor (2 * N) := by
        exact_mod_cast (Nat.le_of_lt_succ hnrange)
      exact ⟨hleft, le_trans hfloor (Nat.floor_le (by positivity))⟩
    have hnpos : 0 < (n : ℝ) := lt_trans hNpos hnBounds.1
    have hnorm :
        ‖normalizedDirichletCoeff b n‖ ^ 2 = ‖b n‖ ^ 2 / (n : ℝ) := by
      dsimp [normalizedDirichletCoeff]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (by positivity)]
    have hcoeffSq : ‖b n‖ ^ 2 ≤
        ((FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hcoeff n hn) 2
    have hcoeffPow :
        ((FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) ^ 2 =
          (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ (2 * C) := by
      rw [← pow_mul]
      congr 1
      omega
    have hdivSame := div_le_div_of_nonneg_right
      (hcoeffSq.trans_eq hcoeffPow) (le_of_lt hnpos)
    have hnumNonneg :
        0 ≤ (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ (2 * C) := by
      positivity
    calc
      ‖normalizedDirichletCoeff b n‖ ^ 2 = ‖b n‖ ^ 2 / (n : ℝ) := hnorm
      _ ≤ ((FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^
            (2 * C)) / (n : ℝ) := hdivSame
      _ ≤ ((FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^
            (2 * C)) / N := by
        exact div_le_div_of_nonneg_left hnumNonneg hNpos hnBounds.1.le
  by_cases hC : C = 0
  · subst C
    have henergySmall : dirichletEnergy N (normalizedDirichletCoeff b) ≤ 2 := by
      unfold dirichletEnergy
      calc
        (∑ n ∈ dirichletIndices N, ‖normalizedDirichletCoeff b n‖ ^ 2) ≤
            ∑ n ∈ dirichletIndices N, (1 : ℝ) / N := by
          apply Finset.sum_le_sum
          intro n hn
          have ht := henergyTerm n hn
          simpa [normalizedDivisorExponent] using ht
        _ ≤ ((dirichletIndices N).card : ℝ) / N := by
          apply le_of_eq
          rw [show (∑ n ∈ dirichletIndices N, (1 : ℝ) / N) =
              ((dirichletIndices N).card : ℝ) * ((1 : ℝ) / N) by
                simp [Finset.sum_const, nsmul_eq_mul]]
          ring
        _ ≤ (Nat.floor (2 * N) : ℝ) / N := by
          apply div_le_div_of_nonneg_right ?_ hNpos.le
          have hcard := Finset.card_le_card hindices
          have htarget : (Finset.Icc 1 (Nat.floor (2 * N))).card ≤ Nat.floor (2 * N) := by
            rw [Nat.card_Icc]
            omega
          exact_mod_cast hcard.trans htarget
        _ ≤ 2 := by
          apply (div_le_iff₀ hNpos).2
          exact Nat.floor_le (by positivity)
    simpa [normalizedDivisorExponent] using henergySmall
  · have hCpos : 1 ≤ C := by omega
    have hRpos : 1 ≤ 2 * C := by omega
    have hmoment := FractionalPrimes.Literature.Uniformity.divisorMomentBound
      2 (2 * C) (by norm_num) hRpos (2 * N) (by nlinarith)
    have hsumSubset :
        (∑ n ∈ dirichletIndices N,
          (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ (2 * C)) ≤
          ∑ n ∈ Finset.Icc 1 (Nat.floor (2 * N)),
            (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ (2 * C) :=
      Finset.sum_le_sum_of_subset_of_nonneg hindices (by
        intro n hn hnot
        positivity)
    have henergyLarge :
        dirichletEnergy N (normalizedDirichletCoeff b) ≤
          2 * (1 + Real.log (2 * N)) ^ normalizedDivisorExponent C := by
      unfold dirichletEnergy
      calc
        (∑ n ∈ dirichletIndices N, ‖normalizedDirichletCoeff b n‖ ^ 2) ≤
            ∑ n ∈ dirichletIndices N,
              ((FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^
                (2 * C)) / N := by
          apply Finset.sum_le_sum
          intro n hn
          exact henergyTerm n hn
        _ = (∑ n ∈ dirichletIndices N,
              (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^
                (2 * C)) / N := by rw [Finset.sum_div]
        _ ≤ (∑ n ∈ Finset.Icc 1 (Nat.floor (2 * N)),
              (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^
                (2 * C)) / N := div_le_div_of_nonneg_right hsumSubset hNpos.le
        _ ≤ (2 * N * (1 + Real.log (2 * N)) ^ normalizedDivisorExponent C) / N := by
          apply div_le_div_of_nonneg_right _ hNpos.le
          simpa [normalizedDivisorExponent] using hmoment
        _ = 2 * (1 + Real.log (2 * N)) ^ normalizedDivisorExponent C := by
          field_simp [ne_of_gt hNpos]
    exact henergyLarge

/-- The mean-square branch of `lgv:normalized`: the number of separated
large-value samples is bounded by the exact contribution obtained from
`lgv:sample-square` and the explicit divisor moment estimate. -/
theorem normalizedMeanSquareCountBound
    (C : ℕ) (N T V : ℝ) (b : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ)
    (hN : 2 ≤ N) (hT : 2 ≤ T) (hV : 0 < V)
    (ht : ∀ j, |t j| ≤ T)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|)
    (hcoeff : ∀ n ∈ dirichletIndices N,
      ‖b n‖ ≤ (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C)
    (hlarge : ∀ j,
      V ≤ ‖dirichletPolynomial N (normalizedDirichletCoeff b) (t j)‖) :
    (R : ℝ) ≤
      64 * Real.log (4 * N * T) ^
        (normalizedDivisorExponent C + 1) * (N + T) / V ^ 2 := by
  let E := normalizedDivisorExponent C
  let L := Real.log (4 * N * T)
  have hNpos : 0 < N := by linarith
  have hG :
      dirichletEnergy N (normalizedDirichletCoeff b) ≤ 2 * L ^ E := by
    have hLgap : 1 + Real.log (2 * N) ≤ L := by
      have hlog4 : 1 ≤ Real.log (4 : ℝ) := by
        have h := Real.le_log_one_add_of_nonneg (x := (3 : ℝ)) (by norm_num)
        norm_num at h
        linarith
      have hlog2T : 1 ≤ Real.log (2 * T) := by
        calc
          1 ≤ Real.log 4 := hlog4
          _ ≤ Real.log (2 * T) := Real.log_le_log (by norm_num) (by nlinarith)
      have hlogIdentity : Real.log (4 * N * T) =
          Real.log (2 * N) + Real.log (2 * T) := by
        calc
          Real.log (4 * N * T) = Real.log ((2 * N) * (2 * T)) := by congr 1 <;> ring
          _ = Real.log (2 * N) + Real.log (2 * T) :=
            Real.log_mul (by positivity) (by positivity)
      dsimp [L]
      rw [hlogIdentity]
      linarith
    have hBaseNonneg : 0 ≤ 1 + Real.log (2 * N) := by
      have hlog : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by nlinarith [hN])
      linarith
    have hpow : (1 + Real.log (2 * N)) ^ E ≤ L ^ E :=
      pow_le_pow_left₀ hBaseNonneg hLgap E
    calc
      dirichletEnergy N (normalizedDirichletCoeff b) ≤
          2 * (1 + Real.log (2 * N)) ^ E :=
        normalizedDirichletEnergy_bound C N b hN hcoeff
      _ ≤ 2 * L ^ E := mul_le_mul_of_nonneg_left hpow (by norm_num)
  have hsample := separatedMeanSquare N T R
    (normalizedDirichletCoeff b) t hN hT ht hsep
  have hcountLower :
      (R : ℝ) * V ^ 2 ≤
        ∑ j : Fin R, Complex.normSq
          (dirichletPolynomial N (normalizedDirichletCoeff b) (t j)) := by
    calc
      (R : ℝ) * V ^ 2 = ∑ j : Fin R, V ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j : Fin R,
          Complex.normSq (dirichletPolynomial N (normalizedDirichletCoeff b) (t j)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (le_of_lt hV) (hlarge j) 2
  have hcount := hcountLower.trans hsample
  have hR :
      (R : ℝ) ≤
        32 * (T + N) * L * dirichletEnergy N (normalizedDirichletCoeff b) / V ^ 2 := by
    apply (le_div_iff₀ (by positivity : 0 < V ^ 2)).2
    nlinarith [hcount]
  have hcoeffBound :
      32 * (T + N) * L * dirichletEnergy N (normalizedDirichletCoeff b) ≤
        64 * (T + N) * L ^ (E + 1) := by
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      exact Real.log_nonneg (by nlinarith [hN, hT])
    calc
      32 * (T + N) * L * dirichletEnergy N (normalizedDirichletCoeff b) ≤
          32 * (T + N) * L * (2 * L ^ E) := by
            exact mul_le_mul_of_nonneg_left hG (by positivity)
      _ = 64 * (T + N) * L ^ (E + 1) := by
        rw [pow_succ]
        ring
  have hfinal :
      (R : ℝ) ≤ 64 * (T + N) * L ^ (E + 1) / V ^ 2 := by
    calc
      (R : ℝ) ≤
          32 * (T + N) * L * dirichletEnergy N (normalizedDirichletCoeff b) / V ^ 2 := hR
      _ ≤ 64 * (T + N) * L ^ (E + 1) / V ^ 2 :=
        div_le_div_of_nonneg_right hcoeffBound (sq_nonneg V)
  simpa [E, L, normalizedDivisorExponent, add_comm, mul_comm, mul_left_comm, mul_assoc] using hfinal

end

end FractionalPrimes.Literature.LargeValues

end

#print axioms FractionalPrimes.Literature.LargeValues.normalizedMeanSquareCountBound
