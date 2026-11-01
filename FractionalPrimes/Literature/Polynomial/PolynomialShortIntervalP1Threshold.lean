module

public import FractionalPrimes.Literature.Uniformity.ArithmeticGroupingConstants
public import FractionalPrimes.Literature.Uniformity.BinomialPhaseVariation
public import FractionalPrimes.Literature.Uniformity.CramerShortDivisor
public import FractionalPrimes.Literature.Uniformity.LogAbsorption

/-!
# Uniform threshold for the positive-degree conditional integer branch

This realizes the single source cutoff `X_*` in P1 of
`lupo:conditional-integer`.  Finite logarithmic lower bounds are handled by
explicit real-power thresholds; the two logarithmic-power versus `X` bounds
use the checked `lu:elementary-growth` absorption lemma.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- A real logarithm threshold that forces a prescribed positive power of
the logarithm above `C`. -/
noncomputable def logPowerLowerThreshold (r C : ℝ) : ℝ :=
  (C + 1) ^ r⁻¹

/-- Above `logPowerLowerThreshold`, the `r`-th power strictly exceeds `C`. -/
theorem logPowerLowerThreshold_lt {r C L : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hL : logPowerLowerThreshold r C ≤ L) :
    C < L ^ r := by
  have hroot : (logPowerLowerThreshold r C) ^ r = C + 1 := by
    dsimp [logPowerLowerThreshold]
    exact Real.rpow_inv_rpow (by positivity) hr.ne'
  have hpower : (C + 1) ≤ L ^ r := by
    have hthreshold_nonneg : 0 ≤ logPowerLowerThreshold r C := by
      dsimp [logPowerLowerThreshold]
      positivity
    calc
      C + 1 = (logPowerLowerThreshold r C) ^ r := hroot.symm
      _ ≤ L ^ r := Real.rpow_le_rpow hthreshold_nonneg hL hr.le
  linarith

/-- The exact P1 scale conditions from `lupo:conditional-integer` hold
simultaneously for all integer `X ≥ X_*`.  The only varying analytic inputs
are the source PMA and PTW constants; all other constants are the approved
ones from arithmetic grouping, Cramér approximation, and binomial variation. -/
theorem exists_conditionalIntegerP1Threshold
    (d c K D E : ℕ) (A η Cpm Ctw : ℝ)
    (hA : 0 < A) (hη : 0 < η)
    (hDsource : A + (decompositionB : ℝ) + 5 < (D : ℝ))
    (hCpm : 0 < Cpm) (hCtw : 0 < Ctw) :
    ∃ Xstar : ℕ, 3 ≤ Xstar ∧
      ∀ X : ℕ, Xstar ≤ X →
        2 ≤ Real.log (X : ℝ) ∧
        decompositionC ≤
          (Real.log (X : ℝ)) ^ ((D : ℝ) - (decompositionB : ℝ)) ∧
        4 * decompositionC <
          (Real.log (X : ℝ)) ^ ((D : ℝ) - A - (decompositionB : ℝ)) ∧
        Real.exp 26 ≤ (Real.log (X : ℝ)) ^ ((D : ℝ) - 4 / 5) ∧
        4 * cramerApproximationConstant (A + 2) (1 / 16 : ℝ) ≤
          (Real.log (X : ℝ)) ^ (2 : ℕ) ∧
        2 * Cpm < (Real.log (X : ℝ)) ^ (2 : ℕ) ∧
        Ctw < (Real.log (X : ℝ)) ^ (2 : ℕ) ∧
        2 * (K : ℝ) * decompositionC *
            (Real.log (X : ℝ)) ^ (((c * D : ℕ) : ℝ)) <
          (X : ℝ) ^ η ∧
        (Real.log (X : ℝ)) ^ E ≤ (X : ℝ) ∧
        max
            ((d.factorial : ℝ) * (K : ℝ))
            (max
              ((d.factorial : ℝ) *
                (1 + 2 * Real.pi * binomialVariationConstant d) * (K : ℝ))
              (max
                (2 * Real.pi * (d : ℝ) * (K : ℝ))
                ((d.factorial : ℝ) *
                  (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) * (K : ℝ) ^ 2))) ≤
          (Real.log (X : ℝ)) ^ (3 : ℕ) := by
  let Capp : ℝ := cramerApproximationConstant (A + 2) (1 / 16 : ℝ)
  let p : ℝ := ((c * D : ℕ) : ℝ)
  let B : ℝ := binomialVariationConstant d
  let R3 : ℝ :=
    max
      ((d.factorial : ℝ) * (K : ℝ))
      (max
        ((d.factorial : ℝ) * (1 + 2 * Real.pi * B) * (K : ℝ))
        (max
          (2 * Real.pi * (d : ℝ) * (K : ℝ))
          ((d.factorial : ℝ) *
            (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) * (K : ℝ) ^ 2)))
  let t1 := logPowerLowerThreshold
    ((D : ℝ) - (decompositionB : ℝ)) decompositionC
  let t2 := logPowerLowerThreshold
    ((D : ℝ) - A - (decompositionB : ℝ)) (4 * decompositionC)
  let t3 := logPowerLowerThreshold ((D : ℝ) - 4 / 5) (Real.exp 26)
  let t4 := logPowerLowerThreshold 2 (4 * Capp)
  let t5 := logPowerLowerThreshold 2 (2 * Cpm)
  let t6 := logPowerLowerThreshold 2 Ctw
  let t7 := logPowerLowerThreshold 3 R3
  let Ka : ℝ := 1 + 4 * (K : ℝ) * decompositionC
  let t8 := (2 / η) * Real.log (Ka * logAbsorptionM η p)
  let t9 := 2 * Real.log (logAbsorptionM 1 (E : ℝ))
  let L₀ : ℝ := 2 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9
  have hCpos : 0 < decompositionC := by
    unfold decompositionC
    positivity
  have hCapp : 0 ≤ Capp := by
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hbase : 0 < max (Real.log 3)
        ((1 / 16 : ℝ) ^ (-(10 / 9 : ℝ))) :=
      lt_of_lt_of_le hlog3 (le_max_left _ _)
    have hterm : 0 < Real.exp 13 *
        (max (Real.log 3) ((1 / 16 : ℝ) ^ (-(10 / 9 : ℝ)))) ^
          ((A + 2) + 2 / 5) :=
      mul_pos (Real.exp_pos 13) (Real.rpow_pos_of_pos hbase _)
    dsimp [Capp, cramerApproximationConstant]
    exact le_trans hterm.le (le_max_right _ _)
  have hB : 0 ≤ B := by
    exact binomialVariationConstant_nonneg d
  have hR3 : 0 ≤ R3 := by
    dsimp [R3, B]
    positivity
  have hDminusB : 0 < (D : ℝ) - (decompositionB : ℝ) := by
    have hb : 0 ≤ (decompositionB : ℝ) := Nat.cast_nonneg _
    linarith
  have hDminusAB : 0 < (D : ℝ) - A - (decompositionB : ℝ) := by
    linarith [hDsource]
  have hDminus45 : 0 < (D : ℝ) - 4 / 5 := by
    have hb : 0 ≤ (decompositionB : ℝ) := Nat.cast_nonneg _
    linarith [hDsource]
  have hKa : 1 ≤ Ka := by
    dsimp [Ka]
    have hprod : 0 ≤ (K : ℝ) * decompositionC :=
      mul_nonneg (Nat.cast_nonneg K) hCpos.le
    linarith
  have hMa : 1 ≤ logAbsorptionM η p := one_le_logAbsorptionM
  have hME : 1 ≤ logAbsorptionM 1 (E : ℝ) := one_le_logAbsorptionM
  have hargA : 1 ≤ Ka * logAbsorptionM η p := by
    calc
      1 ≤ Ka := hKa
      _ ≤ Ka * logAbsorptionM η p := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hMa (by linarith [hKa]))
  have hlogargA : 0 ≤ Real.log (Ka * logAbsorptionM η p) :=
    Real.log_nonneg hargA
  have ht8 : 0 ≤ t8 := by
    dsimp [t8]
    exact mul_nonneg (by positivity) hlogargA
  have hlogargE : 0 ≤ Real.log (logAbsorptionM 1 (E : ℝ)) :=
    Real.log_nonneg hME
  have ht9 : 0 ≤ t9 := by
    dsimp [t9]
    exact mul_nonneg (by norm_num) hlogargE
  have ht1 : 0 ≤ t1 := by dsimp [t1, logPowerLowerThreshold]; positivity
  have ht2 : 0 ≤ t2 := by dsimp [t2, logPowerLowerThreshold]; positivity
  have ht3 : 0 ≤ t3 := by dsimp [t3, logPowerLowerThreshold]; positivity
  have ht4 : 0 ≤ t4 := by dsimp [t4, logPowerLowerThreshold]; positivity
  have ht5 : 0 ≤ t5 := by dsimp [t5, logPowerLowerThreshold]; positivity
  have ht6 : 0 ≤ t6 := by dsimp [t6, logPowerLowerThreshold]; positivity
  have ht7 : 0 ≤ t7 := by dsimp [t7, logPowerLowerThreshold]; positivity
  have hL₀two : 2 ≤ L₀ := by
    dsimp [L₀]
    linarith [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]
  have hL₀t1 : t1 ≤ L₀ := by
    dsimp [L₀]
    linarith [ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]
  have hL₀t2 : t2 ≤ L₀ := by
    dsimp [L₀]
    linarith [ht1, ht3, ht4, ht5, ht6, ht7, ht8, ht9]
  have hL₀t3 : t3 ≤ L₀ := by
    dsimp [L₀]
    linarith [ht1, ht2, ht4, ht5, ht6, ht7, ht8, ht9]
  have hL₀t4 : t4 ≤ L₀ := by
    dsimp [L₀]
    linarith [ht1, ht2, ht3, ht5, ht6, ht7, ht8, ht9]
  have hL₀t5 : t5 ≤ L₀ := by
    dsimp [L₀]
    linarith [ht1, ht2, ht3, ht4, ht6, ht7, ht8, ht9]
  have hL₀t6 : t6 ≤ L₀ := by
    dsimp [L₀]
    linarith [ht1, ht2, ht3, ht4, ht5, ht7, ht8, ht9]
  have hL₀t7 : t7 ≤ L₀ := by
    dsimp [L₀]
    linarith [ht1, ht2, ht3, ht4, ht5, ht6, ht8, ht9]
  have hL₀t8 : t8 ≤ L₀ := by
    dsimp [L₀]
    linarith [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht9]
  have hL₀t9 : t9 ≤ L₀ := by
    dsimp [L₀]
    linarith [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8]
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp L₀)
  let Xstar : ℕ := max 3 N
  refine ⟨Xstar, ?_, ?_⟩
  · dsimp [Xstar]
    exact le_max_left _ _
  · intro X hXstar
    have hNle : N ≤ X := le_trans (le_max_right _ _) hXstar
    have hExpN : Real.exp L₀ < (N : ℝ) := hN
    have hExpX : Real.exp L₀ < (X : ℝ) :=
      lt_of_lt_of_le hExpN (by exact_mod_cast hNle)
    have hXpos : 0 < (X : ℝ) := lt_trans (Real.exp_pos L₀) hExpX
    have hXone : 1 ≤ (X : ℝ) := by
      have hNat : 1 ≤ X := le_trans (by norm_num) (le_trans (le_max_left _ _) hXstar)
      exact_mod_cast hNat
    have hL : L₀ ≤ Real.log (X : ℝ) :=
      (Real.le_log_iff_exp_le hXpos).2 hExpX.le
    have hLpos : 0 < Real.log (X : ℝ) := by
      have : 2 ≤ Real.log (X : ℝ) := le_trans hL₀two hL
      linarith
    have hLtwo : 2 ≤ Real.log (X : ℝ) := le_trans hL₀two hL
    have h1 : decompositionC ≤
        (Real.log (X : ℝ)) ^ ((D : ℝ) - (decompositionB : ℝ)) := by
      exact (logPowerLowerThreshold_lt hDminusB (le_of_lt hCpos)
        (le_trans hL₀t1 hL)).le
    have h2 : 4 * decompositionC <
        (Real.log (X : ℝ)) ^ ((D : ℝ) - A - (decompositionB : ℝ)) :=
      logPowerLowerThreshold_lt hDminusAB (by positivity)
        (le_trans hL₀t2 hL)
    have h3 : Real.exp 26 ≤
        (Real.log (X : ℝ)) ^ ((D : ℝ) - 4 / 5) := by
      exact (logPowerLowerThreshold_lt hDminus45 (Real.exp_nonneg 26)
        (le_trans hL₀t3 hL)).le
    have h4 : 4 * Capp ≤ (Real.log (X : ℝ)) ^ (2 : ℕ) := by
      have hlt := logPowerLowerThreshold_lt (by norm_num : (0 : ℝ) < 2)
        (by positivity : 0 ≤ 4 * Capp) (le_trans hL₀t4 hL)
      exact_mod_cast hlt.le
    have h5 : 2 * Cpm < (Real.log (X : ℝ)) ^ (2 : ℕ) := by
      have hlt := logPowerLowerThreshold_lt (by norm_num : (0 : ℝ) < 2)
        (by positivity : 0 ≤ 2 * Cpm) (le_trans hL₀t5 hL)
      exact_mod_cast hlt
    have h6 : Ctw < (Real.log (X : ℝ)) ^ (2 : ℕ) := by
      have hlt := logPowerLowerThreshold_lt (by norm_num : (0 : ℝ) < 2)
        (le_of_lt hCtw) (le_trans hL₀t6 hL)
      exact_mod_cast hlt
    have h8large :
        (2 / η) * Real.log (Ka * logAbsorptionM η p) ≤
          Real.log (X : ℝ) := by
      exact le_trans (le_trans (le_of_eq rfl) hL₀t8) hL
    have h8bound := log_absorption_bound hη (by positivity) hKa hXone h8large
    have h8 : 2 * (K : ℝ) * decompositionC *
        (Real.log (X : ℝ)) ^ p < (X : ℝ) ^ η := by
      have hcoef : 2 * (K : ℝ) * decompositionC < Ka := by
        dsimp [Ka]
        nlinarith [mul_nonneg (Nat.cast_nonneg K) (le_of_lt hCpos)]
      have hpowpos : 0 < (Real.log (X : ℝ)) ^ p :=
        Real.rpow_pos_of_pos hLpos p
      calc
        2 * (K : ℝ) * decompositionC *
            (Real.log (X : ℝ)) ^ p <
          Ka * (Real.log (X : ℝ)) ^ p :=
            mul_lt_mul_of_pos_right hcoef hpowpos
        _ ≤ (X : ℝ) ^ η := by simpa [p] using h8bound
    have h9large :
        (2 / 1) * Real.log (1 * logAbsorptionM 1 (E : ℝ)) ≤
          Real.log (X : ℝ) := by
      simpa [t9] using le_trans hL₀t9 hL
    have h9bound := log_absorption_bound (by norm_num : (0 : ℝ) < 1)
      (by positivity : 0 ≤ (E : ℝ)) (by norm_num : (1 : ℝ) ≤ 1)
      hXone h9large
    have h9 : (Real.log (X : ℝ)) ^ E ≤ (X : ℝ) := by
      simpa only [one_mul, Real.rpow_natCast, Real.rpow_one] using h9bound
    have h7 : R3 ≤ (Real.log (X : ℝ)) ^ (3 : ℕ) := by
      have hlt := logPowerLowerThreshold_lt (by norm_num : (0 : ℝ) < 3)
        hR3 (le_trans hL₀t7 hL)
      exact_mod_cast hlt.le
    simpa only [Capp, B, R3, p] using
      ⟨hLtwo, h1, h2, h3, h4, h5, h6, h8, h9, h7⟩

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.logPowerLowerThreshold_lt
#print axioms FractionalPrimes.Literature.Polynomial.exists_conditionalIntegerP1Threshold
