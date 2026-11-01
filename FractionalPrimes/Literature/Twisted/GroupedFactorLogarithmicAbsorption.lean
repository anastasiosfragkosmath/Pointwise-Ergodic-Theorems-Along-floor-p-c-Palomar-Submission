module
public import FractionalPrimes.Literature.Twisted.GroupedSmallFactorOfMobiusGoal
@[expose] public section

noncomputable section
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
namespace FractionalPrimes.Literature.Twisted
/-- The source's numerical absorption, uniform over at most twenty original
factors. This retains the logarithmic mass loss needed by von Mangoldt. -/
theorem groupedFactorLogarithmicCoefficientAbsorption
    {X a : ℝ} (ha : 2 ≤ a)
    (hthreshold : groupedMobiusFactorListAbsorptionThreshold a ≤ Real.log X)
    {k r : ℕ} (hkhi : k ≤ 20) (hr : 1 ≤ r)
    (hrlog : (r : ℝ) ≤ (Real.log X) ^ a) :
    ((2 : ℝ) ^ 10 * (3 : ℝ) ^ (k - 1) *
      (divisorFunction k ⟨r, lt_of_lt_of_le (by decide) hr⟩ : ℝ) *
        (Real.log X) ^ (-21 * a)) * Real.sqrt 2 * (4 * Real.log X) ≤
      (Real.log X) ^ (-20 * a) := by
  let L := Real.log X
  let δ := a - a / 100 - 1
  let K := groupedMobiusFactorListAbsorptionConstant
  have hδ : 0 < δ := by
    dsimp [δ]
    nlinarith [ha]
  have hD : 1 ≤ divisorSubpowerConstant 20 (1 / 100 : ℝ) := by
    rw [divisorSubpowerConstant]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbase : 1 ≤ 1 + (20 : ℝ) / ((1 / 100 : ℝ) * Real.log 2) := by
      have hden : 0 < (1 / 100 : ℝ) * Real.log 2 := by positivity
      have hquot : 0 ≤ (20 : ℝ) / ((1 / 100 : ℝ) * Real.log 2) :=
        div_nonneg (by norm_num) hden.le
      linarith
    exact one_le_pow₀ hbase
  have hK : 1 ≤ K := by
    dsimp [K, groupedMobiusFactorListAbsorptionConstant]
    have hsqrt : 1 ≤ Real.sqrt 2 := by
      rw [Real.one_le_sqrt]
      norm_num
    have hD' := hD
    have hconst : 1 ≤ (2 : ℝ) ^ 12 * (3 : ℝ) ^ 19 := by norm_num
    have hconstsqrt : 1 ≤ (2 : ℝ) ^ 12 * (3 : ℝ) ^ 19 * Real.sqrt 2 := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ ((2 : ℝ) ^ 12 * (3 : ℝ) ^ 19) * Real.sqrt 2 :=
          mul_le_mul hconst hsqrt (by norm_num) (by positivity)
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ ((2 : ℝ) ^ 12 * (3 : ℝ) ^ 19 * Real.sqrt 2) *
          divisorSubpowerConstant 20 (1 / 100 : ℝ) :=
        mul_le_mul hconstsqrt hD (by norm_num) (by positivity)
  have hM : 1 ≤ FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0 :=
    FractionalPrimes.Literature.Uniformity.one_le_logAbsorptionM
  have hKM : 1 ≤ K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0 := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ K * FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0 :=
        mul_le_mul hK hM (by norm_num) (by linarith [hK])
  have hlogKM : 0 ≤ Real.log (K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0) :=
    Real.log_nonneg hKM
  have hExpNonneg : 0 ≤ (2 / δ) * Real.log (K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0) := by
    positivity
  have hthresholdExp : Real.exp ((2 / δ) * Real.log (K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0)) ≤ L := by
    simpa [L, δ, K, groupedMobiusFactorListAbsorptionThreshold,
      groupedMobiusFactorListAbsorptionConstant] using hthreshold
  have hLone : 1 ≤ L := by
    have hExpOne : 1 ≤ Real.exp ((2 / δ) * Real.log (K *
        FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0)) := by
      have h := Real.add_one_le_exp ((2 / δ) * Real.log (K *
        FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0))
      linarith
    exact hExpOne.trans hthresholdExp
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  have hlarge : (2 / δ) * Real.log (K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0) ≤
        Real.log L := by
    rw [← Real.log_exp ((2 / δ) * Real.log (K *
      FractionalPrimes.Literature.Uniformity.logAbsorptionM δ 0))]
    exact Real.log_le_log (Real.exp_pos _) hthresholdExp
  have hKpow : K ≤ L ^ δ := by
    have hAbsorb := FractionalPrimes.Literature.Uniformity.log_absorption_bound
      (a := δ) (b := 0) (K := K) (X := L)
      hδ (by norm_num) hK hLone hlarge
    simpa using hAbsorb
  have hKnegative : K * L ^ (-δ) ≤ 1 := by
    have hpowpos : 0 < L ^ δ := Real.rpow_pos_of_pos hLpos δ
    calc
      K * L ^ (-δ) = K / L ^ δ := by
        rw [Real.rpow_neg hLpos.le]
        simp [div_eq_mul_inv]
      _ ≤ 1 := (div_le_one hpowpos).2 hKpow
  have hlenexp : k - 1 ≤ 19 := by omega
  have hthree : (3 : ℝ) ^ (k - 1) ≤ (3 : ℝ) ^ 19 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hlenexp
  have hdivNat : divisorFunction k ⟨r, lt_of_lt_of_le
      (by decide) hr⟩ ≤ divisorFunction 20 ⟨r, lt_of_lt_of_le
        (by decide) hr⟩ := by
    rw [← divisorCoefficient_eq_divisorFunction k r
          (lt_of_lt_of_le (by decide) hr),
        ← divisorCoefficient_eq_divisorFunction 20 r
          (lt_of_lt_of_le (by decide) hr)]
    exact divisorCoefficient_mono
      (lt_of_lt_of_le (by decide) hr) hkhi
  have hdivNatR : (divisorFunction k ⟨r,
      lt_of_lt_of_le (by decide) hr⟩ : ℝ) ≤
        divisorFunction 20 ⟨r, lt_of_lt_of_le (by decide) hr⟩ := by
    exact_mod_cast hdivNat
  have hdiv20 : (divisorFunction 20 ⟨r,
      lt_of_lt_of_le (by decide) hr⟩ : ℝ) ≤
        (divisorFunction 2 ⟨r,
          lt_of_lt_of_le (by decide) hr⟩ : ℝ) ^ 20 := by
    have hNat := divisorCoefficient_twenty_le_two_pow r
      (lt_of_lt_of_le (by decide) hr)
    rw [divisorCoefficient_eq_divisorFunction 20 r
          (lt_of_lt_of_le (by decide) hr),
        divisorCoefficient_eq_divisorFunction 2 r
          (lt_of_lt_of_le (by decide) hr)] at hNat
    exact_mod_cast hNat
  have hdivSub := divisorSubpowerExplicit
    (C := 20) (by norm_num) (ε := 1 / 100) (by norm_num)
      (⟨r, lt_of_lt_of_le (by decide) hr⟩ : PositiveInteger)
  have hdivBound : (divisorFunction k ⟨r,
      lt_of_lt_of_le (by decide) hr⟩ : ℝ) ≤
        divisorSubpowerConstant 20 (1 / 100 : ℝ) *
          (r : ℝ) ^ (1 / 100 : ℝ) := by
    exact hdivNatR.trans (hdiv20.trans hdivSub)
  have hrpow : (r : ℝ) ^ (1 / 100 : ℝ) ≤ L ^ (a / 100) := by
    calc
      (r : ℝ) ^ (1 / 100 : ℝ) ≤ (L ^ a) ^ (1 / 100 : ℝ) :=
        Real.rpow_le_rpow (by exact_mod_cast (Nat.zero_le r)) hrlog
          (by norm_num)
      _ = L ^ (a / 100) := by
        rw [← Real.rpow_mul hLpos.le a (1 / 100 : ℝ)]
        congr 1
        ring
  have hdivBoundL : (divisorFunction k ⟨r,
      lt_of_lt_of_le (by decide) hr⟩ : ℝ) ≤
        divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100) := by
    exact hdivBound.trans (mul_le_mul_of_nonneg_left hrpow
      (by positivity))
  have hcoeffBase :
      (2 : ℝ) ^ 10 * (3 : ℝ) ^ (k - 1) *
          (divisorFunction k ⟨r,
            lt_of_lt_of_le (by decide) hr⟩ : ℝ) ≤
        (2 : ℝ) ^ 10 * (3 : ℝ) ^ 19 *
          divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100) := by
    have hA : (2 : ℝ) ^ 10 * (3 : ℝ) ^ (k - 1) ≤
        (2 : ℝ) ^ 10 * (3 : ℝ) ^ 19 :=
      mul_le_mul_of_nonneg_left hthree (by positivity)
    calc
      _ ≤ ((2 : ℝ) ^ 10 * (3 : ℝ) ^ (k - 1)) *
          (divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100)) :=
        mul_le_mul_of_nonneg_left hdivBoundL (by positivity)
      _ ≤ (2 : ℝ) ^ 10 * (3 : ℝ) ^ 19 *
          (divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100)) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ = (2 : ℝ) ^ 10 * (3 : ℝ) ^ 19 *
          divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100) := by ring
  have hpowjoin : L ^ (a / 100) * L ^ (-21 * a) * L =
      L ^ (-20 * a) * L ^ (-δ) := by
    calc
      L ^ (a / 100) * L ^ (-21 * a) * L =
          L ^ ((a / 100) + (-21 * a) + 1) := by
            calc
              _ = L ^ ((a / 100) + (-21 * a)) * L := by
                rw [← Real.rpow_add hLpos]
              _ = L ^ ((a / 100) + (-21 * a)) * L ^ (1 : ℝ) := by
                congr 1
                exact (Real.rpow_one L).symm
              _ = _ := by rw [← Real.rpow_add hLpos]
      _ = L ^ (-20 * a + -δ) := by
            congr 1
            dsimp [δ]
            ring
      _ = L ^ (-20 * a) * L ^ (-δ) := by
            rw [← Real.rpow_add hLpos]
  have hcoeffAbsorb :
      ((2 : ℝ) ^ 10 * (3 : ℝ) ^ (k - 1) *
          (divisorFunction k ⟨r,
            lt_of_lt_of_le (by decide) hr⟩ : ℝ) * L ^ (-21 * a)) *
          Real.sqrt 2 * (4 * L) ≤ L ^ (-20 * a) := by
    calc
      _ ≤ ((2 : ℝ) ^ 10 * (3 : ℝ) ^ 19 *
          divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100)) *
            L ^ (-21 * a) * Real.sqrt 2 * (4 * L) := by
          calc
            _ = ((2 : ℝ) ^ 10 * (3 : ℝ) ^ (k - 1) *
                (divisorFunction k ⟨r,
                  lt_of_lt_of_le (by decide) hr⟩ : ℝ)) *
                (L ^ (-21 * a) * Real.sqrt 2 * (4 * L)) := by ring
            _ ≤ ((2 : ℝ) ^ 10 * (3 : ℝ) ^ 19 *
                divisorSubpowerConstant 20 (1 / 100 : ℝ) * L ^ (a / 100)) *
                (L ^ (-21 * a) * Real.sqrt 2 * (4 * L)) :=
              mul_le_mul_of_nonneg_right hcoeffBase (by positivity)
            _ = _ := by ring
      _ = K * L ^ (-20 * a) * L ^ (-δ) := by
          calc
            _ = ((2 : ℝ) ^ 12 * (3 : ℝ) ^ 19 * Real.sqrt 2 *
                divisorSubpowerConstant 20 (1 / 100 : ℝ)) *
                  (L ^ (a / 100) * L ^ (-21 * a) * L) := by ring
            _ = K * (L ^ (-20 * a) * L ^ (-δ)) := by
              rw [hpowjoin]
              rfl
            _ = _ := by ring
      _ ≤ L ^ (-20 * a) := by
          calc
            K * L ^ (-20 * a) * L ^ (-δ) =
                L ^ (-20 * a) * (K * L ^ (-δ)) := by ring
            _ ≤ L ^ (-20 * a) * 1 :=
              mul_le_mul_of_nonneg_left hKnegative
                (Real.rpow_nonneg hLpos.le _)
            _ = L ^ (-20 * a) := by ring
  exact hcoeffAbsorb

#print axioms groupedFactorLogarithmicCoefficientAbsorption
end FractionalPrimes.Literature.Twisted
