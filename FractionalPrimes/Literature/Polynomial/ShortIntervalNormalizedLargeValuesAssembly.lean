module

public import FractionalPrimes.Literature.Polynomial.ShortIntervalNormalizedMeanSquare
public import FractionalPrimes.Literature.Polynomial.ShortIntervalLevelMeasureAssembly

/-! Conditional assembly of the exact normalized large-value estimate
`lgv:normalized`. The sole unavailable input is the universal finite
`lgv:separated` estimate, kept explicit here until that theorem is checked.

Blueprint: `expanded-blueprint.tex:5624-5665`.
Astra: `blueprint-sources 2/literature-expansion/sections/dirichlet-large-values.tex`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace FractionalPrimes.Literature.LargeValues

noncomputable section

private lemma dirichletIndices_subset_floor_forNormalized (N : ℝ) (hN : 0 ≤ N) :
    dirichletIndices N ⊆ Finset.Icc 1 (Nat.floor (2 * N)) := by
  intro n hn
  rw [dirichletIndices, Finset.mem_filter, Finset.mem_range] at hn
  rcases hn with ⟨hnrange, hleft⟩
  rw [Finset.mem_Icc]
  constructor
  · have hnpos : 0 < (n : ℝ) := lt_of_le_of_lt hN hleft
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hnpos.ne')
  · exact Nat.le_of_lt_succ hnrange

private lemma normalizedEnergyAtSmallLog
    (C : ℕ) (N : ℝ) (b : ℕ → ℂ) (hN : 2 ≤ N)
    (hcoeff : ∀ n ∈ dirichletIndices N,
      ‖b n‖ ≤ (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) :
    dirichletEnergy N (normalizedDirichletCoeff b) ≤
      2 * (1 + Real.log (2 * N)) ^ normalizedDivisorExponent C := by
  classical
  have hNpos : 0 < N := by linarith
  have hindices := dirichletIndices_subset_floor_forNormalized N (by linarith)
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
            (2 * C)) / N :=
        div_le_div_of_nonneg_left hnumNonneg hNpos hnBounds.1.le
  by_cases hC : C = 0
  · subst C
    have hsmall : dirichletEnergy N (normalizedDirichletCoeff b) ≤ 2 := by
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
    simpa [normalizedDivisorExponent] using hsmall
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

/-- Energy estimate required by `lgv:normalized`, with the exact divisor
moment exponent `E = 2^(2C)-1`. -/
theorem normalizedDivisorEnergyBound
    (C : ℕ) (N T : ℝ) (b : ℕ → ℂ) (hN : 2 ≤ N) (hT : 2 ≤ T)
    (hcoeff : ∀ n ∈ dirichletIndices N,
      ‖b n‖ ≤ (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C) :
    dirichletEnergy N (normalizedDirichletCoeff b) ≤
      2 * Real.log (4 * N * T) ^ normalizedDivisorExponent C := by
  let L := Real.log (4 * N * T)
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
  have hlogNonneg : 0 ≤ 1 + Real.log (2 * N) := by
    have h := Real.log_nonneg (by nlinarith [hN] : (1 : ℝ) ≤ 2 * N)
    linarith
  have hpow : (1 + Real.log (2 * N)) ^ normalizedDivisorExponent C ≤
      Real.log (4 * N * T) ^ normalizedDivisorExponent C :=
    pow_le_pow_left₀ hlogNonneg hLgap _
  calc
    dirichletEnergy N (normalizedDirichletCoeff b) ≤
        2 * (1 + Real.log (2 * N)) ^ normalizedDivisorExponent C :=
      normalizedEnergyAtSmallLog C N b hN hcoeff
    _ ≤ 2 * Real.log (4 * N * T) ^ normalizedDivisorExponent C :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)

private lemma shortIntervalLog_ge_one (N T : ℝ) (hN : 2 ≤ N) (hT : 2 ≤ T) :
    1 ≤ Real.log (4 * N * T) := by
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
  have hlog2N : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by nlinarith [hN])
  rw [hlogIdentity]
  linarith

private lemma normalizedDivisorSampleBound
    (C : ℕ) (N T V : ℝ) (b : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ)
    (hN : 2 ≤ N) (hT : 2 ≤ T) (hV : 0 < V)
    (ht : ∀ j, |t j| ≤ T)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|)
    (hcoeff : ∀ n ∈ dirichletIndices N,
      ‖b n‖ ≤ (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C)
    (hlarge : ∀ j,
      V ≤ ‖dirichletPolynomial N (normalizedDirichletCoeff b) (t j)‖)
    (huxley : (R : ℝ) ≤ 2 ^ 24 * Real.log (4 * N * T) *
      (N * dirichletEnergy N (normalizedDirichletCoeff b) / V ^ 2 +
        T * N * (dirichletEnergy N (normalizedDirichletCoeff b)) ^ 3 / V ^ 6)) :
    (R : ℝ) ≤
      2 ^ (3 * normalizedDivisorExponent C + 28) *
        Real.log (4 * N * T) ^ (3 * normalizedDivisorExponent C + 1) *
          (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)) := by
  let E := normalizedDivisorExponent C
  let L := Real.log (4 * N * T)
  let K : ℝ := 2 ^ (3 * E + 28)
  let X := N / V ^ 2
  let Y := T * (1 / V ^ 2)
  let Z := T * (N / V ^ 6)
  have hL : 1 ≤ L := by simpa [L] using shortIntervalLog_ge_one N T hN hT
  have hG : dirichletEnergy N (normalizedDirichletCoeff b) ≤ 2 * L ^ E := by
    simpa [L, E] using normalizedDivisorEnergyBound C N T b hN hT hcoeff
  have hGnonneg : 0 ≤ dirichletEnergy N (normalizedDirichletCoeff b) := by
    unfold dirichletEnergy
    positivity
  have hmean := normalizedMeanSquareCountBound C N T V b R t
    hN hT hV ht hsep hcoeff hlarge
  have hmeanX : (R : ℝ) ≤ 64 * L ^ (E + 1) * (X + Y) := by
    calc
      (R : ℝ) ≤ 64 * L ^ (E + 1) * (N + T) / V ^ 2 := by
        simpa [E, L, normalizedDivisorExponent] using hmean
      _ = 64 * L ^ (E + 1) * (X + Y) := by
        dsimp [X, Y]
        field_simp [ne_of_gt (sq_pos_of_pos hV)]
  have hGcube : (dirichletEnergy N (normalizedDirichletCoeff b)) ^ 3 ≤
      (2 * L ^ E) ^ 3 := pow_le_pow_left₀ hGnonneg hG 3
  have hterm1 :
      N * dirichletEnergy N (normalizedDirichletCoeff b) / V ^ 2 ≤
        2 * L ^ E * X := by
    have hmul : N * dirichletEnergy N (normalizedDirichletCoeff b) ≤
        N * (2 * L ^ E) :=
      mul_le_mul_of_nonneg_left hG (by linarith [hN])
    calc
      N * dirichletEnergy N (normalizedDirichletCoeff b) / V ^ 2 ≤
          N * (2 * L ^ E) / V ^ 2 := div_le_div_of_nonneg_right hmul (sq_nonneg V)
      _ = 2 * L ^ E * X := by dsimp [X]; ring
  have hterm2 :
      T * N * (dirichletEnergy N (normalizedDirichletCoeff b)) ^ 3 / V ^ 6 ≤
        8 * L ^ (3 * E) * Z := by
    have hmul : T * N * (dirichletEnergy N (normalizedDirichletCoeff b)) ^ 3 ≤
        T * N * (2 * L ^ E) ^ 3 :=
      mul_le_mul_of_nonneg_left hGcube (by positivity [hT, hN])
    have hcube : (2 * L ^ E) ^ 3 = 8 * L ^ (3 * E) := by
      calc
        (2 * L ^ E) ^ 3 = 2 ^ 3 * (L ^ E) ^ 3 := by rw [mul_pow]
        _ = 8 * L ^ (E * 3) := by rw [← pow_mul]; norm_num
        _ = 8 * L ^ (3 * E) := by congr 2 <;> omega
    calc
      T * N * (dirichletEnergy N (normalizedDirichletCoeff b)) ^ 3 / V ^ 6 ≤
          T * N * (2 * L ^ E) ^ 3 / V ^ 6 :=
        div_le_div_of_nonneg_right hmul (by positivity)
      _ = 8 * L ^ (3 * E) * Z := by rw [hcube]; dsimp [Z]; ring
  have huxleyUpper :
      2 ^ 24 * L *
          (N * dirichletEnergy N (normalizedDirichletCoeff b) / V ^ 2 +
            T * N * (dirichletEnergy N (normalizedDirichletCoeff b)) ^ 3 / V ^ 6) ≤
        2 ^ 25 * L ^ (E + 1) * X + 2 ^ 27 * L ^ (3 * E + 1) * Z := by
    calc
      _ ≤ 2 ^ 24 * L * (2 * L ^ E * X + 8 * L ^ (3 * E) * Z) :=
        mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by positivity [hL])
      _ = 2 ^ 25 * L ^ (E + 1) * X + 2 ^ 27 * L ^ (3 * E + 1) * Z := by
        rw [pow_succ, pow_succ]
        norm_num
        ring
  have hE0 : 0 ≤ E := Nat.cast_nonneg _
  have hLnonneg : 0 ≤ L := le_trans (by norm_num) hL
  have hExp : E + 1 ≤ 3 * E + 1 := by omega
  have hLpow : L ^ (E + 1) ≤ L ^ (3 * E + 1) :=
    pow_le_pow_right₀ hL hExp
  have hK27 : (2 : ℝ) ^ 27 ≤ K := by
    dsimp [K]
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  have hK25 : (2 : ℝ) ^ 25 ≤ K := by
    have hnum : (2 : ℝ) ^ 25 ≤ (2 : ℝ) ^ 27 := by norm_num
    exact hnum.trans (by simpa [K] using hK27)
  have hK64 : (64 : ℝ) ≤ K := by
    have hnum : (64 : ℝ) ≤ (2 : ℝ) ^ 27 := by norm_num
    exact hnum.trans (by simpa [K] using hK27)
  have hmeanCoeff : 64 * L ^ (E + 1) ≤ K * L ^ (3 * E + 1) := by
    calc
      64 * L ^ (E + 1) ≤ K * L ^ (E + 1) :=
        mul_le_mul_of_nonneg_right hK64 (pow_nonneg hLnonneg _)
      _ ≤ K * L ^ (3 * E + 1) :=
        mul_le_mul_of_nonneg_left hLpow (by positivity [hK27])
  have huxleyCoeff1 : 2 ^ 25 * L ^ (E + 1) ≤ K * L ^ (3 * E + 1) := by
    calc
      2 ^ 25 * L ^ (E + 1) ≤ K * L ^ (E + 1) :=
        mul_le_mul_of_nonneg_right hK25 (pow_nonneg hLnonneg _)
      _ ≤ K * L ^ (3 * E + 1) :=
        mul_le_mul_of_nonneg_left hLpow (by positivity [hK27])
  have huxleyCoeff2 : 2 ^ 27 * L ^ (3 * E + 1) ≤ K * L ^ (3 * E + 1) :=
    mul_le_mul_of_nonneg_right hK27 (pow_nonneg hLnonneg _)
  have hmeanTarget : (R : ℝ) ≤ K * L ^ (3 * E + 1) * (X + Y) := by
    calc
      (R : ℝ) ≤ 64 * L ^ (E + 1) * (X + Y) := hmeanX
      _ ≤ K * L ^ (3 * E + 1) * (X + Y) :=
        mul_le_mul_of_nonneg_right hmeanCoeff (by positivity [hN, hT, hV])
  have huxleyTarget : (R : ℝ) ≤ K * L ^ (3 * E + 1) * (X + Z) := by
    calc
      (R : ℝ) ≤ 2 ^ 24 * L *
          (N * dirichletEnergy N (normalizedDirichletCoeff b) / V ^ 2 +
            T * N * (dirichletEnergy N (normalizedDirichletCoeff b)) ^ 3 / V ^ 6) := huxley
      _ ≤ 2 ^ 25 * L ^ (E + 1) * X + 2 ^ 27 * L ^ (3 * E + 1) * Z := huxleyUpper
      _ ≤ K * L ^ (3 * E + 1) * X + K * L ^ (3 * E + 1) * Z :=
        add_le_add
          (mul_le_mul_of_nonneg_right huxleyCoeff1 (by positivity [hN, hV]))
          (mul_le_mul_of_nonneg_right huxleyCoeff2 (by positivity [hT, hN, hV]))
      _ = K * L ^ (3 * E + 1) * (X + Z) := by ring
  have hfinal : (R : ℝ) ≤ K * L ^ (3 * E + 1) *
      (X + T * min (1 / V ^ 2) (N / V ^ 6)) := by
    by_cases hmin : 1 / V ^ 2 ≤ N / V ^ 6
    · have hminEq : min (1 / V ^ 2) (N / V ^ 6) = 1 / V ^ 2 := min_eq_left hmin
      calc
        (R : ℝ) ≤ K * L ^ (3 * E + 1) * (X + Y) := hmeanTarget
        _ = K * L ^ (3 * E + 1) *
            (X + T * min (1 / V ^ 2) (N / V ^ 6)) := by
          rw [hminEq]
    · have hreverse : N / V ^ 6 ≤ 1 / V ^ 2 := le_of_not_ge hmin
      have hminEq : min (1 / V ^ 2) (N / V ^ 6) = N / V ^ 6 := min_eq_right hreverse
      calc
        (R : ℝ) ≤ K * L ^ (3 * E + 1) * (X + Z) := huxleyTarget
        _ = K * L ^ (3 * E + 1) *
            (X + T * min (1 / V ^ 2) (N / V ^ 6)) := by
          rw [hminEq]
  simpa [K, L, E, X, normalizedDivisorExponent] using hfinal

private lemma normalizedThreshold_sq_rpow (N σ : ℝ) (hN : 0 < N) :
    N / (N ^ (σ - 1 / 2)) ^ 2 = N ^ (2 - 2 * σ) := by
  have hpow : (N ^ (σ - 1 / 2)) ^ 2 =
      N ^ ((σ - 1 / 2) * 2) := by
    exact (Real.rpow_mul_natCast (le_of_lt hN) (σ - 1 / 2) 2).symm
  calc
    N / (N ^ (σ - 1 / 2)) ^ 2 = N ^ (1 : ℝ) / N ^ ((σ - 1 / 2) * 2) := by
      rw [Real.rpow_one, hpow]
    _ = N ^ (1 - (σ - 1 / 2) * 2) := (Real.rpow_sub hN _ _).symm
    _ = N ^ (2 - 2 * σ) := by congr 1 <;> ring

private lemma normalizedThreshold_inv_sq_rpow (N σ : ℝ) (hN : 0 < N) :
    1 / (N ^ (σ - 1 / 2)) ^ 2 = N ^ (1 - 2 * σ) := by
  have hpow : (N ^ (σ - 1 / 2)) ^ 2 =
      N ^ ((σ - 1 / 2) * 2) := by
    exact (Real.rpow_mul_natCast (le_of_lt hN) (σ - 1 / 2) 2).symm
  calc
    1 / (N ^ (σ - 1 / 2)) ^ 2 = N ^ (0 : ℝ) / N ^ ((σ - 1 / 2) * 2) := by
      rw [Real.rpow_zero, hpow]
    _ = N ^ (0 - (σ - 1 / 2) * 2) := (Real.rpow_sub hN _ _).symm
    _ = N ^ (1 - 2 * σ) := by congr 1 <;> ring

private lemma normalizedThreshold_six_rpow (N σ : ℝ) (hN : 0 < N) :
    N / (N ^ (σ - 1 / 2)) ^ 6 = N ^ (4 - 6 * σ) := by
  have hpow : (N ^ (σ - 1 / 2)) ^ 6 =
      N ^ ((σ - 1 / 2) * 6) := by
    exact (Real.rpow_mul_natCast (le_of_lt hN) (σ - 1 / 2) 6).symm
  calc
    N / (N ^ (σ - 1 / 2)) ^ 6 = N ^ (1 : ℝ) / N ^ ((σ - 1 / 2) * 6) := by
      rw [Real.rpow_one, hpow]
    _ = N ^ (1 - (σ - 1 / 2) * 6) := (Real.rpow_sub hN _ _).symm
    _ = N ^ (4 - 6 * σ) := by congr 1 <;> ring

/-- Conditional `lgv:normalized` assembly. Its separated-family premise is
exactly the upcoming `lgv:separated` theorem specialized to the normalized
coefficients. The theorem does not hide that dependency. -/
theorem normalizedDivisorBound_ofSeparated
    (C : ℕ) (N T V : ℝ) (b : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ)
    (hN : 2 ≤ N) (hT : 2 ≤ T) (hV : 0 < V)
    (ht : ∀ j, |t j| ≤ T)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|)
    (hcoeff : ∀ n ∈ dirichletIndices N,
      ‖b n‖ ≤ (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C)
    (hlarge : ∀ j,
      V ≤ ‖dirichletPolynomial N (normalizedDirichletCoeff b) (t j)‖)
    (huxleyBound : ∀ (R' : ℕ) (s : Fin R' → ℝ),
      (∀ j, |s j| ≤ T) →
      (∀ i j, i ≠ j → 1 ≤ |s i - s j|) →
      (∀ j, V ≤ ‖dirichletPolynomial N (normalizedDirichletCoeff b) (s j)‖) →
      (R' : ℝ) ≤ 2 ^ 24 * Real.log (4 * N * T) *
        (N * dirichletEnergy N (normalizedDirichletCoeff b) / V ^ 2 +
          T * N * (dirichletEnergy N (normalizedDirichletCoeff b)) ^ 3 / V ^ 6)) :
    (R : ℝ) ≤
        2 ^ (3 * normalizedDivisorExponent C + 28) *
          Real.log (4 * N * T) ^ (3 * normalizedDivisorExponent C + 1) *
            (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)) ∧
      MeasurableSet (dirichletLevelSet N T V (normalizedDirichletCoeff b)) ∧
      volume.real (dirichletLevelSet N T V (normalizedDirichletCoeff b)) ≤
        2 * (2 ^ (3 * normalizedDivisorExponent C + 28) *
          Real.log (4 * N * T) ^ (3 * normalizedDivisorExponent C + 1) *
            (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6))) := by
  have hcount := normalizedDivisorSampleBound C N T V b R t
    hN hT hV ht hsep hcoeff hlarge (huxleyBound R t ht hsep hlarge)
  have hbound (R' : ℕ) (s : Fin R' → ℝ)
      (hs : ∀ j, s j ∈ dirichletLevelSet N T V (normalizedDirichletCoeff b))
      (hssep : ∀ i j, i ≠ j → 1 ≤ |s i - s j|) :
      (R' : ℝ) ≤
        2 ^ (3 * normalizedDivisorExponent C + 28) *
          Real.log (4 * N * T) ^ (3 * normalizedDivisorExponent C + 1) *
            (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)) := by
    have hst : ∀ j, |s j| ≤ T := by
      intro j
      have hsj := hs j
      change s j ∈ Set.Icc (-T) T ∧
        V ≤ ‖dirichletPolynomial N (normalizedDirichletCoeff b) (s j)‖ at hsj
      exact abs_le.mpr ⟨hsj.1.1, hsj.1.2⟩
    have hslarge : ∀ j,
        V ≤ ‖dirichletPolynomial N (normalizedDirichletCoeff b) (s j)‖ := by
      intro j
      have hsj := hs j
      change s j ∈ Set.Icc (-T) T ∧
        V ≤ ‖dirichletPolynomial N (normalizedDirichletCoeff b) (s j)‖ at hsj
      exact hsj.2
    exact normalizedDivisorSampleBound C N T V b R' s
      hN hT hV hst hssep hcoeff hslarge (huxleyBound R' s hst hssep hslarge)
  have hcover := dirichletLevelSetMeasureBound_of_separated N T V
    (2 ^ (3 * normalizedDivisorExponent C + 28) *
      Real.log (4 * N * T) ^ (3 * normalizedDivisorExponent C + 1) *
        (N / V ^ 2 + T * min (1 / V ^ 2) (N / V ^ 6)))
    (normalizedDirichletCoeff b) hbound
  exact ⟨hcount, dirichletLevelSet_measurable N T V _, hcover⟩

/-- The `V = N^(σ-1/2)` specialization in the blueprint's normalized
divisor-bounded estimate, conditional on the finite separated-family bound. -/
theorem normalizedDivisorBound_rpow_ofSeparated
    (C : ℕ) (N T σ : ℝ) (b : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ)
    (hN : 2 ≤ N) (hT : 2 ≤ T)
    (ht : ∀ j, |t j| ≤ T)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|)
    (hcoeff : ∀ n ∈ dirichletIndices N,
      ‖b n‖ ≤ (FractionalPrimes.Literature.Uniformity.divisorCoefficient 2 n : ℝ) ^ C)
    (hlarge : ∀ j,
      N ^ (σ - 1 / 2) ≤ ‖dirichletPolynomial N (normalizedDirichletCoeff b) (t j)‖)
    (huxleyBound : ∀ (R' : ℕ) (s : Fin R' → ℝ),
      (∀ j, |s j| ≤ T) →
      (∀ i j, i ≠ j → 1 ≤ |s i - s j|) →
      (∀ j, N ^ (σ - 1 / 2) ≤
        ‖dirichletPolynomial N (normalizedDirichletCoeff b) (s j)‖) →
      (R' : ℝ) ≤ 2 ^ 24 * Real.log (4 * N * T) *
        (N * dirichletEnergy N (normalizedDirichletCoeff b) /
            (N ^ (σ - 1 / 2)) ^ 2 +
          T * N * (dirichletEnergy N (normalizedDirichletCoeff b)) ^ 3 /
            (N ^ (σ - 1 / 2)) ^ 6)) :
    (R : ℝ) ≤
        2 ^ (3 * normalizedDivisorExponent C + 28) *
          Real.log (4 * N * T) ^ (3 * normalizedDivisorExponent C + 1) *
            (N ^ (2 - 2 * σ) +
              T * min (N ^ (1 - 2 * σ)) (N ^ (4 - 6 * σ))) ∧
      MeasurableSet (dirichletLevelSet N T (N ^ (σ - 1 / 2))
        (normalizedDirichletCoeff b)) ∧
      volume.real (dirichletLevelSet N T (N ^ (σ - 1 / 2))
        (normalizedDirichletCoeff b)) ≤
        2 * (2 ^ (3 * normalizedDivisorExponent C + 28) *
          Real.log (4 * N * T) ^ (3 * normalizedDivisorExponent C + 1) *
            (N ^ (2 - 2 * σ) +
              T * min (N ^ (1 - 2 * σ)) (N ^ (4 - 6 * σ)))) := by
  have hNpos : 0 < N := by linarith
  have hVpos : 0 < N ^ (σ - 1 / 2) := Real.rpow_pos_of_pos hNpos _
  have hbase := normalizedDivisorBound_ofSeparated C N T
    (N ^ (σ - 1 / 2)) b R t hN hT hVpos ht hsep hcoeff hlarge
    (by
      intro R' s hs hsep' hlarge'
      exact huxleyBound R' s hs hsep' hlarge')
  rcases hbase with ⟨hcount, hmeas, hmeasure⟩
  refine ⟨?_, hmeas, ?_⟩
  · simpa only [normalizedThreshold_sq_rpow N σ hNpos,
      normalizedThreshold_inv_sq_rpow N σ hNpos,
      normalizedThreshold_six_rpow N σ hNpos] using hcount
  · simpa only [normalizedThreshold_sq_rpow N σ hNpos,
      normalizedThreshold_inv_sq_rpow N σ hNpos,
      normalizedThreshold_six_rpow N σ hNpos] using hmeasure

end

end FractionalPrimes.Literature.LargeValues

end

#print axioms FractionalPrimes.Literature.LargeValues.normalizedDivisorBound_ofSeparated
#print axioms FractionalPrimes.Literature.LargeValues.normalizedDivisorBound_rpow_ofSeparated
#print axioms FractionalPrimes.Literature.LargeValues.normalizedDivisorEnergyBound
