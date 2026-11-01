module

public import FractionalPrimes.ProgressionPrefixAllScales
public import FractionalPrimes.Literature.Harmonic.ContinuousModel
public import FractionalPrimes.Literature.Harmonic.EndpointBounds
public import FractionalPrimes.Literature.Harmonic.DyadicMaximalComparison
public import FractionalPrimes.Literature.Harmonic.ContinuousModelVariation
public import FractionalPrimes.FourierLpBridge
public import FractionalPrimes.InterpolationKernelGain
public import FractionalPrimes.VariationAbsoluteSum

set_option maxHeartbeats 600000

/-!
# The low-level Fourier comparison for the dyadic unweighted averages

This file begins the spectral-error half of `ha:dyadic`. It keeps the
progression estimate at the same representative in `[-1/2,1/2)`, including
the left endpoint, and records the conjugation bridge from its positive phase
to the paper's negative-phase multiplier.
-/

@[expose] public section

open FractionalPrimes
open MeasureTheory
open scoped ComplexConjugate
open scoped ENNReal
open scoped NNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

namespace FractionalPrimes.Literature.Harmonic

noncomputable section

/-- The positive-phase multiplier paired with `bN` by complex conjugation. -/
def positiveFloorPowerMultiplier (c ξ : ℝ) (N : Scale) : ℂ :=
  (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
    unitFrequencyPhase (ξ * (floorPower c n : ℝ))

/-- Conjugating the positive-phase finite multiplier gives exactly `bN`. -/
private theorem conj_positiveFloorPowerMultiplier (c ξ : ℝ) (N : Scale) :
    star (positiveFloorPowerMultiplier c ξ N) = bN c ξ N := by
  simp [positiveFloorPowerMultiplier, bN, map_mul, map_sum,
    ← unitFrequencyPhase_neg_eq_conj]

/-- The continuous negative-phase symbol is the conjugate of the normalized
positive-phase integral, including every positive scale. -/
theorem continuousModelV_eq_star_continuousFractionalModel
    {c N ξ : ℝ} (hN : 0 < N) :
    continuousModelV c N ξ = star (continuousFractionalModel c N ξ) := by
  rw [continuousFractionalModel_eq_unitIntegral hN]
  change (∫ u in (0 : ℝ)..1,
      unitFrequencyPhase (-ξ * N ^ c * u ^ c)) =
    star (∫ u in (0 : ℝ)..1,
      unitFrequencyPhase ((ξ * N ^ c) * u ^ c))
  have hphase (u : ℝ) :
      unitFrequencyPhase (-ξ * N ^ c * u ^ c) =
        starRingEnd ℂ (unitFrequencyPhase ((ξ * N ^ c) * u ^ c)) := by
    calc
      unitFrequencyPhase (-ξ * N ^ c * u ^ c) =
          unitFrequencyPhase (-((ξ * N ^ c) * u ^ c)) := by
        congr 1 <;> ring
      _ = starRingEnd ℂ (unitFrequencyPhase ((ξ * N ^ c) * u ^ c)) :=
        unitFrequencyPhase_neg_eq_conj _
  have hint :
      (∫ u in (0 : ℝ)..1, unitFrequencyPhase (-ξ * N ^ c * u ^ c)) =
        ∫ u in (0 : ℝ)..1,
          starRingEnd ℂ (unitFrequencyPhase ((ξ * N ^ c) * u ^ c)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact hphase u
  rw [hint, intervalIntegral.intervalIntegral_conj]
  simp [Complex.star_def]

/-- Reindex the progression's `i=0,...,N-1` prefix to the exact `[1,N]`
finite multiplier used by `bN`. -/
private theorem positiveFloorPowerMultiplier_eq_IcoSum
    (c ξ : ℝ) (N : Scale) :
    positiveFloorPowerMultiplier c ξ N =
      (N.1 : ℂ)⁻¹ * ∑ i ∈ Finset.Ico 0 N.1,
        unitFrequencyPhase
          (ξ * ((Int.floor (((Nat.succ i : ℕ) : ℝ) ^ c) : ℤ) : ℝ)) := by
  let f : ℤ → ℂ := fun z =>
    unitFrequencyPhase (ξ * (Int.floor ((z : ℝ) ^ c) : ℝ))
  have hsumIcc :
      (∑ n ∈ Finset.Icc 1 N.1,
        unitFrequencyPhase (ξ * (floorPower c n : ℝ))) =
      ∑ z ∈ FractionalPrimes.realIntegerInterval 0 (N.1 : ℝ), f z := by
    calc
      (∑ n ∈ Finset.Icc 1 N.1,
          unitFrequencyPhase (ξ * (floorPower c n : ℝ))) =
        ∑ n ∈ Finset.Icc 1 N.1, f (n : ℤ) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [f, floorPower]
      _ = ∑ z ∈ FractionalPrimes.realIntegerInterval 0 (N.1 : ℝ), f z :=
        (FractionalPrimes.sum_realIntegerInterval_zero_eq_nat_Icc N.1 f).symm
  have hsumIco :
      (∑ z ∈ FractionalPrimes.realIntegerInterval 0 (N.1 : ℝ), f z) =
        ∑ i ∈ Finset.Ico 0 N.1,
          unitFrequencyPhase
            (ξ * ((Int.floor (((Nat.succ i : ℕ) : ℝ) ^ c) : ℤ) : ℝ)) := by
    have h := FractionalPrimes.progression_floorPhase_sum_reindex
      (N := (N.1 : ℝ)) (d := 1) (ξ := ξ) (c := c) (by positivity)
    simpa [f, one_mul] using h
  simp only [positiveFloorPowerMultiplier]
  rw [hsumIcc, hsumIco]

/-- The all-scale progression estimate, specialized at `d=1`, in the exact
positive-phase multiplier normalization corresponding to `bN`. -/
theorem positiveFloorPowerMultiplier_close_continuousFractionalModel
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : Scale, 3 ≤ (N.1 : ℝ) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        ‖positiveFloorPowerMultiplier c ξ N -
            continuousFractionalModel c (N.1 : ℝ) ξ‖ ≤
          C * (N.1 : ℝ) ^ (-δ) := by
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let δ : ℝ := η / 4
  dsimp only [j, η, δ]
  obtain ⟨C, hC, hprog⟩ :=
    exists_progression_floorPrefix_exactAverage_all_scales hc hcNon
  refine ⟨C, hC, ?_⟩
  intro N hN ξ hξlo hξhi
  have h := hprog (N.1 : ℝ) hN 1 (by norm_num) (by
    have hNpos : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
    have hN1 : 1 ≤ (N.1 : ℝ) := by linarith
    have hlognon : 0 ≤ (Real.log (N.1 : ℝ)) ^ (3 / 10 : ℝ) := by
      exact Real.rpow_nonneg (Real.log_nonneg hN1) _
    have hexp : 1 ≤ Real.exp ((Real.log (N.1 : ℝ)) ^ (3 / 10 : ℝ)) :=
      (Real.one_le_exp_iff).2 hlognon
    exact_mod_cast hexp) ξ hξlo hξhi
  have hL : Nat.floor ((N.1 : ℝ) / (1 : ℝ)) = N.1 := by
    simp
  have hprefix :
      ((↑(Nat.floor ((N.1 : ℝ) / (1 : ℝ))) : ℝ)⁻¹ : ℝ) •
          (∑ i ∈ Finset.Ico 0 (Nat.floor ((N.1 : ℝ) / (1 : ℝ))),
            unitFrequencyPhase
              (ξ * ((Int.floor (((1 : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) =
        positiveFloorPowerMultiplier c ξ N := by
    rw [hL, positiveFloorPowerMultiplier_eq_IcoSum]
    simp only [one_mul]
    simp [smul_eq_mul, Complex.ofReal_inv]
  have hnorm :
      ‖((↑(Nat.floor ((N.1 : ℝ) / (1 : ℝ))) : ℝ)⁻¹ : ℝ) •
          (∑ i ∈ Finset.Ico 0 (Nat.floor ((N.1 : ℝ) / (1 : ℝ))),
            unitFrequencyPhase
              (ξ * ((Int.floor (((1 : ℝ) * ((Nat.succ i : ℕ) : ℝ)) ^ c) : ℤ) : ℝ))) -
        continuousFractionalModel c (N.1 : ℝ) ξ‖ ≤ C * (N.1 : ℝ) ^ (-(
          ((1 / 100 : ℝ) /
            (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
              (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4)) := by
    simpa [hL] using h.2
  rw [hprefix] at hnorm
  exact hnorm

/-- At the same half-open frequency representative, conjugation transports the
`d=1` progression estimate to the multiplier `bN` and the negative-phase
continuous model. -/
theorem bN_close_continuousModelV
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : Scale, 3 ≤ (N.1 : ℝ) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        ‖bN c ξ N - continuousModelV c (N.1 : ℝ) ξ‖ ≤
          C * (N.1 : ℝ) ^ (-δ) := by
  dsimp only
  obtain ⟨C, hC, hclose⟩ :=
    positiveFloorPowerMultiplier_close_continuousFractionalModel hc hcNon
  refine ⟨C, hC, ?_⟩
  intro N hN ξ hξlo hξhi
  have hclose := hclose N hN ξ hξlo hξhi
  have hconj :
      star (positiveFloorPowerMultiplier c ξ N -
        continuousFractionalModel c (N.1 : ℝ) ξ) =
        bN c ξ N - continuousModelV c (N.1 : ℝ) ξ := by
    rw [star_sub, conj_positiveFloorPowerMultiplier,
      continuousModelV_eq_star_continuousFractionalModel]
    exact_mod_cast N.2
  calc
    ‖bN c ξ N - continuousModelV c (N.1 : ℝ) ξ‖ =
        ‖star (positiveFloorPowerMultiplier c ξ N -
          continuousFractionalModel c (N.1 : ℝ) ξ)‖ := by rw [hconj]
    _ = ‖positiveFloorPowerMultiplier c ξ N -
        continuousFractionalModel c (N.1 : ℝ) ξ‖ := norm_star _
    _ ≤ _ := hclose

private theorem continuousModelV_tail_bound {c N ξ : ℝ}
    (hc : 1 < c) (hN : 0 < N) (hξ : 1 / 10 ≤ |ξ|)
    (hξupper : |ξ| ≤ 1 / 2) :
    ‖continuousModelV c N ξ‖ ≤ 10 * continuousModelK c / N := by
  have hcpos : 0 < c := by linarith
  have hKnonneg : 0 ≤ continuousModelK c := by
    unfold continuousModelK
    positivity
  have hξpos : 0 < |ξ| := by linarith
  have hξle : |ξ| ≤ 1 := hξupper.trans (by norm_num)
  have hpowξ : |ξ| ^ (-c⁻¹) ≤ |ξ| ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hξpos hξle (by
      have hcinv : c⁻¹ < 1 := (inv_lt_one₀ hcpos).2 hc
      linarith)
  have hξinv : |ξ| ^ (-1 : ℝ) ≤ 10 := by
    rw [Real.rpow_neg_one]
    rw [← one_div]
    apply (div_le_iff₀ hξpos).2
    norm_num at hξ ⊢
    linarith
  have hNpow : (N ^ c) ^ (-c⁻¹) = N ^ (-1 : ℝ) := by
    rw [← Real.rpow_mul hN.le c (-c⁻¹)]
    congr 1
    field_simp
  have hprod : (|ξ| * N ^ c) ^ (-c⁻¹) =
      |ξ| ^ (-c⁻¹) * (N ^ c) ^ (-c⁻¹) :=
    Real.mul_rpow (abs_nonneg ξ) (Real.rpow_nonneg hN.le c)
  have hmodel := continuousModelV_norm_le_min (ξ := ξ) hc hN
  have hmodel' : ‖continuousModelV c N ξ‖ ≤
      continuousModelK c * ((|ξ| * N ^ c) ^ (-c⁻¹)) := by
    have hξne : ξ ≠ 0 := by
      intro hz
      subst ξ
      norm_num at hξpos
    rw [continuousModelMin, if_neg hξne] at hmodel
    exact hmodel.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hKnonneg)
  calc
    ‖continuousModelV c N ξ‖ ≤
        continuousModelK c * ((|ξ| * N ^ c) ^ (-c⁻¹)) := hmodel'
    _ = continuousModelK c *
        (|ξ| ^ (-c⁻¹) * (N ^ c) ^ (-c⁻¹)) := by rw [hprod]
    _ ≤ continuousModelK c * (10 * N ^ (-1 : ℝ)) := by
      rw [hNpow]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hpowξ.trans hξinv)
          (Real.rpow_nonneg hN.le (-1 : ℝ)))
        hKnonneg
    _ = 10 * continuousModelK c / N := by
      rw [Real.rpow_neg_one]
      ring

/-- Inserting the fixed cutoff costs only the high-frequency `O_c(N⁻¹)`
tail. The frequency remains in the same half-open representative interval as
the progression estimate. -/
theorem bN_close_continuousModelSymbolLift
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : Scale, 3 ≤ (N.1 : ℝ) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        ‖bN c ξ N - continuousModelSymbolLift c (N.1 : ℝ) ξ‖ ≤
          C * (N.1 : ℝ) ^ (-δ) := by
  dsimp only
  obtain ⟨C, hC, hclose⟩ := bN_close_continuousModelV hc hcNon
  have hK : 0 ≤ continuousModelK c := by
    unfold continuousModelK
    positivity
  refine ⟨C + 10 * continuousModelK c, by positivity, ?_⟩
  intro N hN ξ hξlo hξhi
  have hNpos : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
  have hNge : 1 ≤ (N.1 : ℝ) := by linarith
  have hδ := progressionParameters_delta_bounds hc
  have hδlt :
      ((1 / 100 : ℝ) /
        (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
          (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4 < 1 := by
    simpa using hδ.2
  have hpower : (N.1 : ℝ) ^ (-1 : ℝ) ≤
      (N.1 : ℝ) ^ (-((1 / 100 : ℝ) /
        (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
          (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) / 4)) :=
    Real.rpow_le_rpow_of_exponent_le hNge (by linarith)
  have hcutErr :
      ‖((1 : ℂ) - (continuousModelEta ξ : ℂ)) *
          continuousModelV c (N.1 : ℝ) ξ‖ ≤
        10 * continuousModelK c / (N.1 : ℝ) := by
    by_cases hsmall : |ξ| ≤ 1 / 10
    · rw [continuousModelEta_eq_one_of_abs_le_tenth ξ hsmall]
      simp
      positivity
    · have hξ : 1 / 10 ≤ |ξ| := le_of_not_ge hsmall
      have hξupper : |ξ| ≤ 1 / 2 :=
        (abs_le).2 ⟨by linarith, le_of_lt hξhi⟩
      have hV := continuousModelV_tail_bound hc hNpos hξ hξupper
      have hηnonneg : 0 ≤ continuousModelEta ξ := continuousModelEta_nonneg ξ
      have hηle : continuousModelEta ξ ≤ 1 := continuousModelEta_le_one ξ
      have hcutAbs : |1 - continuousModelEta ξ| ≤ 1 := by
        rw [abs_of_nonneg (by linarith : 0 ≤ 1 - continuousModelEta ξ)]
        linarith
      have hcutComplex :
          (1 : ℂ) - (continuousModelEta ξ : ℂ) =
            ((1 - continuousModelEta ξ : ℝ) : ℂ) := by
        push_cast
        rfl
      calc
        ‖((1 : ℂ) - (continuousModelEta ξ : ℂ)) *
            continuousModelV c (N.1 : ℝ) ξ‖ =
          |1 - continuousModelEta ξ| *
            ‖continuousModelV c (N.1 : ℝ) ξ‖ := by
              rw [hcutComplex, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 1 * (10 * continuousModelK c / (N.1 : ℝ)) :=
          mul_le_mul hcutAbs hV (norm_nonneg _) (by positivity)
        _ = 10 * continuousModelK c / (N.1 : ℝ) := by ring
  have hcloseN := hclose N hN ξ hξlo hξhi
  have hmodelEq :
      continuousModelSymbolLift c (N.1 : ℝ) ξ =
        (continuousModelEta ξ : ℂ) * continuousModelV c (N.1 : ℝ) ξ := rfl
  have hmain :
      ‖bN c ξ N - continuousModelSymbolLift c (N.1 : ℝ) ξ‖ ≤
        C * (N.1 : ℝ) ^ (-((1 / 100 : ℝ) /
          (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) / 4)) +
          10 * continuousModelK c / (N.1 : ℝ) := by
    calc
      ‖bN c ξ N - continuousModelSymbolLift c (N.1 : ℝ) ξ‖ =
          ‖(bN c ξ N - continuousModelV c (N.1 : ℝ) ξ) +
            ((1 : ℂ) - (continuousModelEta ξ : ℂ)) *
              continuousModelV c (N.1 : ℝ) ξ‖ := by
            rw [hmodelEq]
            congr 1
            ring
      _ ≤ ‖bN c ξ N - continuousModelV c (N.1 : ℝ) ξ‖ +
            ‖((1 : ℂ) - (continuousModelEta ξ : ℂ)) *
              continuousModelV c (N.1 : ℝ) ξ‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hcloseN hcutErr
  have htail : 10 * continuousModelK c / (N.1 : ℝ) ≤
      10 * continuousModelK c *
        (N.1 : ℝ) ^ (-((1 / 100 : ℝ) /
          (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) / 4)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_left hpower (mul_nonneg (by norm_num) hK)
  calc
    ‖bN c ξ N - continuousModelSymbolLift c (N.1 : ℝ) ξ‖ ≤
        C * (N.1 : ℝ) ^ (-((1 / 100 : ℝ) /
          (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) / 4)) +
          10 * continuousModelK c / (N.1 : ℝ) := hmain
    _ ≤ (C + 10 * continuousModelK c) *
        (N.1 : ℝ) ^ (-((1 / 100 : ℝ) /
          (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) / 4)) := by
      calc
        _ = 10 * continuousModelK c / (N.1 : ℝ) +
              C * (N.1 : ℝ) ^ (-((1 / 100 : ℝ) /
                (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
                  (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) / 4)) := by ring
        _ ≤ 10 * continuousModelK c *
              (N.1 : ℝ) ^ (-((1 / 100 : ℝ) /
                (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
                  (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) / 4)) +
              C * (N.1 : ℝ) ^ (-((1 / 100 : ℝ) /
                (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
                  (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ)) / 4)) :=
          by nlinarith [htail]
        _ = _ := by ring

/-- Evaluate the period-one kernel symbol at the same centered representative
used by the nonperiodic fractional-power model. Negative representatives are
shifted by one only for the lift evaluation; periodicity returns the original
frequency for the kernel transform. -/
theorem integerKernelFourierSymbol_coe_centered
    (K : IntegerL1Kernel) {ξ : ℝ}
    (hξ : ξ ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2)) :
    integerKernelFourierSymbol K (ξ : AddCircle (1 : ℝ)) =
      integerKernelFourierTransform K ξ := by
  by_cases hξ0 : 0 ≤ ξ
  · exact integerKernelFourierSymbol_coe_Ico K ξ ⟨hξ0, by linarith [hξ.2]⟩
  · have hshift : ξ + 1 ∈ Set.Ico 0 1 := by
      constructor <;> linarith [hξ.1, hξ.2]
    have hcoe : ((ξ + 1 : ℝ) : AddCircle (1 : ℝ)) = (ξ : AddCircle (1 : ℝ)) :=
      AddCircle.coe_add_period (1 : ℝ) ξ
    rw [← hcoe, integerKernelFourierSymbol_coe_Ico K (ξ + 1) hshift,
      integerKernelFourierTransform_add_one]

/-- The exact discrete Fourier symbol of the finite average is uniformly
within the progression saving of the continuous torus model on all circle
frequencies. -/
theorem floorPowerKernelFourierSymbol_close_continuousModel
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : Scale, 3 ≤ (N.1 : ℝ) →
      ∀ x : AddCircle (1 : ℝ),
        ‖integerKernelFourierSymbol (floorPowerKernel c N) x -
            continuousModelTorusSymbol c (N.1 : ℝ) x‖ ≤
          C * (N.1 : ℝ) ^ (-δ) := by
  dsimp only
  obtain ⟨C, hC, hclose⟩ := bN_close_continuousModelSymbolLift hc hcNon
  refine ⟨C, hC, ?_⟩
  intro N hN x
  let y : Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
    AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) x
  have hy : (y : AddCircle (1 : ℝ)) = x := AddCircle.coe_equivIco
  have hycenter : (y : ℝ) ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2) := by
    simpa only [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num] using y.property
  have hsymbol : integerKernelFourierSymbol (floorPowerKernel c N) x =
      bN c (y : ℝ) N := by
    rw [← hy, integerKernelFourierSymbol_coe_centered _ hycenter,
      floorPowerKernelFourier_eq_bN]
  have hmodel : continuousModelTorusSymbol c (N.1 : ℝ) x =
      continuousModelSymbolLift c (N.1 : ℝ) (y : ℝ) := by
    rw [← hy]
    simpa [continuousModelSymbolLift] using
      continuousModelTorusSymbol_apply_coe c (N.1 : ℝ) hycenter
  rw [hsymbol, hmodel]
  exact hclose N hN (y : ℝ) hycenter.1 hycenter.2

/-- Essential-supremum form of the all-frequency symbol comparison, ready for
the `L²` Fourier multiplier estimate. -/
theorem eLpNormEssSup_floorPowerKernelFourierSymbol_sub_continuousModel_le
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c)
    (N : Scale) (hN : 3 ≤ (N.1 : ℝ)) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNormEssSup
          (fun x : AddCircle (1 : ℝ) =>
            integerKernelFourierSymbol (floorPowerKernel c N) x -
              continuousModelTorusSymbol c (N.1 : ℝ) x)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) ≤
        ENNReal.ofReal (C * (N.1 : ℝ) ^ (-δ)) := by
  dsimp only
  obtain ⟨C, hC, hbound⟩ :=
    floorPowerKernelFourierSymbol_close_continuousModel hc hcNon
  have hNbound := hbound N hN
  refine ⟨C, hC, ?_⟩
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards with x
  exact hNbound x

/-- The endpoint kernel's coefficient sequence is the reflected Fourier
coefficient sequence of the continuous torus symbol. The reflection matches
the negative-frequency convention in `integerKernelFourierTransform`. -/
theorem continuousModelEndpointKernel_coeff_eq_fourierCoeff
    {c N : ℝ} (hc : 1 < c) (m : ℤ) :
    (continuousModelEndpointKernel c N hc).coeff m =
      fourierCoeff (continuousModelTorusSymbol c N) (-m) := by
  rw [continuousModelEndpointKernel_coeff]
  change continuousModelKernelCoefficient c N m = _
  exact continuousModelKernelCoefficient_eq_fourierCoefficient hc m

/-- Absolute summability of the endpoint kernel allows reconstruction of its
continuous torus symbol by its Fourier series. -/
theorem continuousModelEndpointKernelFourierTransform_eq
    {c N : ℝ} (hc : 1 < c) (ξ : ℝ) :
    integerKernelFourierTransform (continuousModelEndpointKernel c N hc) ξ =
      continuousModelTorusSymbol c N (ξ : AddCircle (1 : ℝ)) := by
  let K := continuousModelEndpointKernel c N hc
  let F : ContinuousMap (AddCircle (1 : ℝ)) ℂ :=
    ⟨continuousModelTorusSymbol c N,
      continuousModelTorusSymbol_continuous c N hc⟩
  have hcoeff (m : ℤ) : K.coeff m = fourierCoeff F (-m) := by
    simpa [F] using continuousModelEndpointKernel_coeff_eq_fourierCoeff hc m
  have hcoeffSummable : Summable (fourierCoeff F) := by
    apply Summable.of_norm
    have hnorm : Summable (fun m : ℤ => ‖fourierCoeff F (-m)‖) := by
      exact K.summable_norm.congr fun m => by rw [← hcoeff m]
    exact (Equiv.neg ℤ).summable_iff.mp hnorm
  have hseries : (∑' n : ℤ, fourierCoeff F n *
      (_root_.fourier (T := (1 : ℝ)) n (ξ : AddCircle (1 : ℝ)))) =
      F (ξ : AddCircle (1 : ℝ)) := by
    have hpoint :=
      (has_pointwise_sum_fourier_series_of_summable hcoeffSummable
        (ξ : AddCircle (1 : ℝ))).tsum_eq
    simpa only [smul_eq_mul] using hpoint
  have htransform : integerKernelFourierTransform K ξ =
      ∑' n : ℤ, fourierCoeff F n *
        (_root_.fourier (T := (1 : ℝ)) n (ξ : AddCircle (1 : ℝ))) := by
    unfold integerKernelFourierTransform
    rw [show (fun m : ℤ => K.coeff m * unitFrequencyPhase (-ξ * (m : ℝ))) =
      (fun n : ℤ => fourierCoeff F n *
        (_root_.fourier (T := (1 : ℝ)) n (ξ : AddCircle (1 : ℝ)))) ∘
          (Equiv.neg ℤ) by
        funext m
        simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg]
        rw [hcoeff]
        rw [show -ξ * (m : ℝ) = ((-m : ℤ) : ℝ) * ξ by
          push_cast
          ring,
          unitFrequencyPhase_int_mul_eq_addCircleFourier (-m) ξ]]
    exact (Equiv.neg ℤ).tsum_eq
      (fun n : ℤ => fourierCoeff F n *
        (_root_.fourier (T := (1 : ℝ)) n (ξ : AddCircle (1 : ℝ))))
  rw [htransform, hseries]
  rfl

/-- The exact error kernel between the finite average and its continuous
endpoint model. -/
noncomputable def floorPowerEndpointErrorKernel
    (c : ℝ) (N : Scale) (hc : 1 < c) : IntegerL1Kernel where
  coeff m := (floorPowerKernel c N).coeff m -
    (continuousModelEndpointKernel c (N.1 : ℝ) hc).coeff m
  summable_norm := by
    have hmajor : Summable (fun m : ℤ =>
        ‖(floorPowerKernel c N).coeff m‖ +
          ‖(continuousModelEndpointKernel c (N.1 : ℝ) hc).coeff m‖) :=
      (floorPowerKernel c N).summable_norm.add
        (continuousModelEndpointKernel c (N.1 : ℝ) hc).summable_norm
    have hnorm : Summable (fun m : ℤ =>
        ‖(floorPowerKernel c N).coeff m -
          (continuousModelEndpointKernel c (N.1 : ℝ) hc).coeff m‖) :=
      hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _)
    exact hnorm

/-- The finite kernel of the unweighted average has total mass one. This is
the exact `ℓ¹` endpoint needed in interpolation, with multiplicities retained
when several indices have the same floor time. -/
theorem floorPowerKernel_norm_tsum_le_one (c : ℝ) (N : Scale) :
    ∑' m : ℤ, ‖(floorPowerKernel c N).coeff m‖ ≤ 1 := by
  classical
  let I := Finset.Icc 1 N.1
  let S := I.image (floorPower c)
  have hzero (m : ℤ) (hm : m ∉ S) : (floorPowerKernel c N).coeff m = 0 := by
    have hne : ∀ n ∈ I, floorPower c n ≠ m := by
      intro n hn heq
      apply hm
      exact Finset.mem_image.mpr ⟨n, hn, heq⟩
    unfold floorPowerKernel
    change (N.1 : ℂ)⁻¹ *
      (∑ n ∈ I, if floorPower c n = m then (1 : ℂ) else 0) = 0
    have hsum :
        (∑ n ∈ I, if floorPower c n = m then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [hne n hn]
    rw [hsum]
    simp
  have hcoef (m : ℤ) :
      ‖(floorPowerKernel c N).coeff m‖ ≤
        (N.1 : ℝ)⁻¹ * ∑ n ∈ I,
          if floorPower c n = m then (1 : ℝ) else 0 := by
    unfold floorPowerKernel
    rw [norm_mul]
    have hInv : ‖(N.1 : ℂ)⁻¹‖ = (N.1 : ℝ)⁻¹ := by simp [norm_inv]
    rw [hInv]
    calc
      (N.1 : ℝ)⁻¹ *
          ‖∑ n ∈ I, if floorPower c n = m then (1 : ℂ) else 0‖ ≤
        (N.1 : ℝ)⁻¹ *
          ∑ n ∈ I, ‖if floorPower c n = m then (1 : ℂ) else 0‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = (N.1 : ℝ)⁻¹ *
          ∑ n ∈ I, if floorPower c n = m then (1 : ℝ) else 0 := by
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        by_cases h : floorPower c n = m <;> simp [h]
  have hcount :
      (∑ m ∈ S, ∑ n ∈ I,
        if floorPower c n = m then (1 : ℝ) else 0) =
        ∑ n ∈ I, (1 : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    have hmem : floorPower c n ∈ S := by
      exact Finset.mem_image.mpr ⟨n, by simpa [I] using hn, rfl⟩
    rw [Finset.sum_eq_single (floorPower c n)]
    · simp
    · intro m hm hmn
      have hne : floorPower c n ≠ m := by
        intro heq
        exact hmn heq.symm
      simp [hne]
    · intro hnot
      exact (hnot hmem).elim
  rw [tsum_eq_sum (s := S) (fun m hm => by simp [hzero m hm])]
  calc
    (∑ m ∈ S, ‖(floorPowerKernel c N).coeff m‖) ≤
        ∑ m ∈ S, (N.1 : ℝ)⁻¹ *
          ∑ n ∈ I, if floorPower c n = m then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro m hm
      exact hcoef m
    _ = (N.1 : ℝ)⁻¹ * ∑ m ∈ S, ∑ n ∈ I,
          if floorPower c n = m then (1 : ℝ) else 0 := by
      rw [Finset.mul_sum]
    _ = (N.1 : ℝ)⁻¹ * ∑ n ∈ I, (1 : ℝ) := by rw [hcount]
    _ = 1 := by
      have hNreal : (N.1 : ℝ) ≠ 0 := by exact_mod_cast N.2.ne'
      simp [I, Nat.card_Icc, hNreal]

/-- The error kernel has the source endpoint mass bound `1+Sψ`, uniformly in
the scale. -/
theorem floorPowerEndpointErrorKernel_norm_tsum_le
    (c : ℝ) (N : Scale) (hc : 1 < c) :
    ∑' m : ℤ, ‖(floorPowerEndpointErrorKernel c N hc).coeff m‖ ≤
      1 + schwartzExtensionS continuousModelPsiSchwartz := by
  let K₁ := floorPowerKernel c N
  let K₂ := continuousModelEndpointKernel c (N.1 : ℝ) hc
  let K := floorPowerEndpointErrorKernel c N hc
  have hmajor : Summable (fun m : ℤ => ‖K₁.coeff m‖ + ‖K₂.coeff m‖) :=
    K₁.summable_norm.add K₂.summable_norm
  calc
    ∑' m : ℤ, ‖K.coeff m‖ ≤ ∑' m : ℤ, (‖K₁.coeff m‖ + ‖K₂.coeff m‖) :=
      K.summable_norm.tsum_le_tsum (fun m => by
        simp [K, K₁, K₂]
        exact norm_sub_le _ _) hmajor
    _ = (∑' m : ℤ, ‖K₁.coeff m‖) +
          (∑' m : ℤ, ‖K₂.coeff m‖) :=
      K₁.summable_norm.tsum_add K₂.summable_norm
    _ ≤ 1 + schwartzExtensionS continuousModelPsiSchwartz :=
      add_le_add (floorPowerKernel_norm_tsum_le_one c N)
        (continuousModelEndpointKernel_norm_sum_le c (N.1 : ℝ) hc)

/-- The Fourier symbol of the error kernel is exactly the difference of the
two source symbols on every torus frequency. -/
theorem floorPowerEndpointErrorKernelFourierSymbol_eq
    {c : ℝ} (hc : 1 < c) (N : Scale) (x : AddCircle (1 : ℝ)) :
    integerKernelFourierSymbol (floorPowerEndpointErrorKernel c N hc) x =
      integerKernelFourierSymbol (floorPowerKernel c N) x -
        continuousModelTorusSymbol c (N.1 : ℝ) x := by
  let y : Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
    AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) x
  have hy : (y : AddCircle (1 : ℝ)) = x := AddCircle.coe_equivIco
  have hycenter : (y : ℝ) ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2) := by
    simpa only [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num] using y.property
  rw [← hy, integerKernelFourierSymbol_coe_centered
    (floorPowerEndpointErrorKernel c N hc) hycenter,
    integerKernelFourierSymbol_coe_centered (floorPowerKernel c N) hycenter]
  have herror : integerKernelFourierTransform
      (floorPowerEndpointErrorKernel c N hc) (y : ℝ) =
      integerKernelFourierTransform (floorPowerKernel c N) (y : ℝ) -
        integerKernelFourierTransform
          (continuousModelEndpointKernel c (N.1 : ℝ) hc) (y : ℝ) := by
    change (∑' m : ℤ,
        ((floorPowerKernel c N).coeff m -
          (continuousModelEndpointKernel c (N.1 : ℝ) hc).coeff m) *
          unitFrequencyPhase (-(y : ℝ) * (m : ℝ))) = _
    rw [show (fun m : ℤ =>
        ((floorPowerKernel c N).coeff m -
          (continuousModelEndpointKernel c (N.1 : ℝ) hc).coeff m) *
          unitFrequencyPhase (-(y : ℝ) * (m : ℝ))) =
        (fun m : ℤ => (floorPowerKernel c N).coeff m *
          unitFrequencyPhase (-(y : ℝ) * (m : ℝ))) -
        (fun m : ℤ => (continuousModelEndpointKernel c (N.1 : ℝ) hc).coeff m *
          unitFrequencyPhase (-(y : ℝ) * (m : ℝ))) by
          funext m
          simp only [Pi.sub_apply]
          ring]
    exact (summable_integerKernelFourier_terms (floorPowerKernel c N) (y : ℝ)).tsum_sub
      (summable_integerKernelFourier_terms
        (continuousModelEndpointKernel c (N.1 : ℝ) hc) (y : ℝ))
  rw [herror, continuousModelEndpointKernelFourierTransform_eq hc]

/-- The Fourier symbol of the error kernel inherits the exact uniform
progression saving on the torus. -/
theorem eLpNormEssSup_floorPowerEndpointErrorKernel_le
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c)
    (N : Scale) (hN : 3 ≤ (N.1 : ℝ)) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNormEssSup
          (integerKernelFourierSymbol (floorPowerEndpointErrorKernel c N hc))
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) ≤
        ENNReal.ofReal (C * (N.1 : ℝ) ^ (-δ)) := by
  dsimp only
  obtain ⟨C, hC, hclose⟩ :=
    floorPowerKernelFourierSymbol_close_continuousModel hc hcNon
  refine ⟨C, hC, ?_⟩
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards with x
  rw [floorPowerEndpointErrorKernelFourierSymbol_eq hc]
  exact hclose N hN x

/-- The error summands' pointwise magnitudes, viewed as a real-valued `Lᵖ`
family. This package lets the absolute error sum be estimated by Minkowski. -/
noncomputable def harmonicMagnitudeLp {p : ℝ≥0∞}
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    Lp ℝ p (Measure.count : Measure ℤ) :=
  (MemLp.norm f.2).toLp (fun x : ℤ => ‖(f : ℤ → ℂ) x‖)

theorem harmonicMagnitudeLp_apply {p : ℝ≥0∞}
    (f : Lp ℂ p (Measure.count : Measure ℤ)) (x : ℤ) :
    harmonicMagnitudeLp f x = ‖(f : ℤ → ℂ) x‖ := by
  have h := MemLp.coeFn_toLp (MemLp.norm f.2)
  have hforall := (ae_count_int_iff_forall.mp h) x
  simpa [harmonicMagnitudeLp] using hforall

theorem harmonicMagnitudeLp_norm {p : ℝ≥0∞}
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    ‖harmonicMagnitudeLp f‖ = ‖f‖ := by
  change ‖((MemLp.norm f.2).toLp
      (fun x : ℤ => ‖(f : ℤ → ℂ) x‖))‖ = ‖f‖
  calc
    ‖harmonicMagnitudeLp f‖ =
        ENNReal.toReal (eLpNorm (fun x : ℤ => ‖(f : ℤ → ℂ) x‖)
          p (Measure.count : Measure ℤ)) := by
      exact Lp.norm_toLp (fun x : ℤ => ‖(f : ℤ → ℂ) x‖)
        (MemLp.norm f.2)
    _ = ENNReal.toReal (eLpNorm (f : ℤ → ℂ) p
          (Measure.count : Measure ℤ)) := by
      rw [eLpNorm_norm (f : ℤ → ℂ) (Lp.aestronglyMeasurable f)]
    _ = ‖f‖ := by rw [Lp.norm_def]

/-- Countable Minkowski for the pointwise sum of magnitudes of `Lᵖ` outputs.
All functions are on counting `ℤ`, so the displayed pointwise sum is a
measurable representative. -/
theorem eLpNorm_tsum_ofReal_norm_le_tsum
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type*} [Countable ι]
    (f : ι → Lp ℂ p (Measure.count : Measure ℤ))
    (hs : Summable (fun i => ‖f i‖)) :
    eLpNorm (fun x : ℤ => ∑' i, ENNReal.ofReal ‖f i x‖)
        p (Measure.count : Measure ℤ) ≤ ∑' i, ENNReal.ofReal ‖f i‖ := by
  let g : ι → Lp ℝ p (Measure.count : Measure ℤ) := fun i => harmonicMagnitudeLp (f i)
  let G : Lp ℝ p (Measure.count : Measure ℤ) := ∑' i, g i
  have hnorm (i : ι) : ‖g i‖ = ‖f i‖ := harmonicMagnitudeLp_norm (f i)
  have hgs : Summable (fun i => ‖g i‖) := by
    simpa only [hnorm] using hs
  have hsumEnorm : (∑' i, ‖g i‖ₑ) = ENNReal.ofReal (∑' i, ‖g i‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun i => norm_nonneg _) hgs]
    simp [ofReal_norm]
  have hfinite : (∑' i, ‖g i‖ₑ) ≠ ∞ := by
    rw [hsumEnorm]
    exact ENNReal.ofReal_ne_top
  have hpoint := Lp.hasSum_coeFn_tsum (p := p) hfinite
  let S : ℤ → ℝ≥0∞ := fun x => ∑' i, ENNReal.ofReal ‖f i x‖
  have hSmeas : AEStronglyMeasurable S (Measure.count : Measure ℤ) :=
    (measurable_of_countable S).aestronglyMeasurable
  have hGmeas : AEStronglyMeasurable (G : ℤ → ℝ) (Measure.count : Measure ℤ) :=
    Lp.aestronglyMeasurable G
  have hnormEq : ∀ᵐ x ∂(Measure.count : Measure ℤ),
      ‖S x‖ₑ = ‖(G : ℤ → ℝ) x‖ₑ := by
    filter_upwards [hpoint] with x hx
    have hx' : HasSum (fun i => ‖(f i : ℤ → ℂ) x‖) ((G : ℤ → ℝ) x) := by
      simpa [g, harmonicMagnitudeLp_apply] using hx
    have hvalue : (∑' i, ‖(f i : ℤ → ℂ) x‖) = (G : ℤ → ℝ) x :=
      hx'.tsum_eq
    have hsumS : S x = ENNReal.ofReal ((G : ℤ → ℝ) x) := by
      calc
        S x = ENNReal.ofReal (∑' i, ‖(f i : ℤ → ℂ) x‖) := by
          symm
          exact ENNReal.ofReal_tsum_of_nonneg (fun i => norm_nonneg _)
            hx'.summable
        _ = _ := by rw [hvalue]
    have hGnonneg : 0 ≤ (G : ℤ → ℝ) x := by
      rw [← hvalue]
      exact tsum_nonneg (fun i => norm_nonneg _)
    rw [hsumS]
    calc
      ENNReal.ofReal ((G : ℤ → ℝ) x) =
          ENNReal.ofReal ‖(G : ℤ → ℝ) x‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hGnonneg]
      _ = ‖(G : ℤ → ℝ) x‖ₑ := ofReal_norm _
  have hmono := eLpNorm_mono_enorm_ae (p := p) hSmeas
    (hnormEq.mono fun _ hx => hx.le)
  have hGnorm : eLpNorm (G : ℤ → ℝ) p (Measure.count : Measure ℤ) =
      ‖G‖ₑ := by rw [Lp.enorm_def]
  have hGbound : ‖G‖ ≤ ∑' i, ‖g i‖ := norm_tsum_le_tsum_norm hgs
  change eLpNorm S p (Measure.count : Measure ℤ) ≤
    ∑' i, ENNReal.ofReal ‖f i‖
  calc
    eLpNorm S p (Measure.count : Measure ℤ) ≤
        eLpNorm (G : ℤ → ℝ) p (Measure.count : Measure ℤ) := hmono
    _ = ‖G‖ₑ := hGnorm
    _ = ENNReal.ofReal ‖G‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (∑' i, ‖g i‖) :=
      ENNReal.ofReal_le_ofReal hGbound
    _ = ∑' i, ENNReal.ofReal ‖g i‖ :=
      ENNReal.ofReal_tsum_of_nonneg (fun i => norm_nonneg _) hgs
    _ = ∑' i, ENNReal.ofReal ‖f i‖ := by
      apply tsum_congr
      intro i
      rw [hnorm i]

/-- The source spectral comparison gives the exact `L²` multiplier bound for
the finite-minus-continuous endpoint error kernel. -/
theorem floorPowerEndpointErrorKernel_l2_bound
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c)
    (N : Scale) (hN : 3 ≤ (N.1 : ℝ)) :
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm
        (integerKernelConvolution
          (floorPowerEndpointErrorKernel c N hc) (f : ℤ → ℂ))
        2 Measure.count ≤
      ENNReal.ofReal (C * (N.1 : ℝ) ^ (-δ)) *
        eLpNorm (f : ℤ → ℂ) 2 Measure.count := by
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let δ : ℝ := η / 4
  dsimp only [j, η, δ]
  obtain ⟨C, hC, hSymbol⟩ :=
    eLpNormEssSup_floorPowerEndpointErrorKernel_le hc hcNon N hN
  refine ⟨C, hC, ?_⟩
  intro f
  calc
    eLpNorm
        (integerKernelConvolution
          (floorPowerEndpointErrorKernel c N hc) (f : ℤ → ℂ))
        2 Measure.count ≤
      eLpNormEssSup
          (integerKernelFourierSymbol
            (floorPowerEndpointErrorKernel c N hc))
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
        eLpNorm (f : ℤ → ℂ) 2 Measure.count :=
      eLpNorm_integerKernelConvolution_two_le_fourierSymbol
        (hT := ⟨by norm_num⟩) _ f
    _ ≤ ENNReal.ofReal (C * (N.1 : ℝ) ^ (-δ)) *
          eLpNorm (f : ℤ → ℂ) 2 Measure.count :=
      mul_le_mul_of_nonneg_right hSymbol (by positivity)

/-- Interpolating the spectral bound with the source `1+Sψ` endpoint gives
the exact positive power saving `δ βₚ` for every `1<p<∞`. -/
theorem floorPowerEndpointErrorKernel_lp_operator_decay
    {c p : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) (hp : 1 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨(ENNReal.one_le_ofReal).2 (by linarith)⟩
    let j : ℕ := Nat.ceil c + 2
    let η : ℝ := (1 / 100 : ℝ) /
      (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
    let δ : ℝ := η / 4
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : Scale, 3 ≤ (N.1 : ℝ) →
      ∀ f : Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ),
        ‖integerKernelLpConvolutionCLM
          (p := ENNReal.ofReal p)
          (floorPowerEndpointErrorKernel c N hc) f‖ ≤
        A * (N.1 : ℝ) ^ (-δ * interpolationBeta p) * ‖f‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨(ENNReal.one_le_ofReal).2 (by linarith)⟩
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let δ : ℝ := η / 4
  dsimp only [j, η, δ]
  obtain ⟨C, hC, hSymbol⟩ :=
    floorPowerKernelFourierSymbol_close_continuousModel hc hcNon
  let B : ℝ := 1 + schwartzExtensionS continuousModelPsiSchwartz
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    have hS := schwartzExtensionS_nonneg continuousModelPsiSchwartz
    linarith
  have hBpos : 0 < B := by
    dsimp [B]
    have hS := schwartzExtensionS_nonneg continuousModelPsiSchwartz
    linarith
  have hbeta : 0 < interpolationBeta p := by
    rcases lt_trichotomy p 2 with hp2 | hp2 | hp2
    · rw [interpolationBeta_eq_lower hp hp2]
      have hp0 : 0 < p := by linarith
      have hfraclt : 2 / p < 2 := by
        apply (div_lt_iff₀ hp0).2
        nlinarith
      linarith
    · subst p
      norm_num [interpolationBeta]
    · rw [interpolationBeta_eq_upper hp2]
      positivity
  refine ⟨interpolationConstant p * B ^ (1 - interpolationBeta p) *
      (C + 1) ^ interpolationBeta p, ?_, ?_⟩
  · have hconst : 0 ≤ interpolationConstant p := by
      rcases lt_trichotomy p 2 with hpLower | hpTwo | hpUpper
      · simp [interpolationConstant, hpLower]
        unfold interpolationLowerConstant
        have hp0 : 0 < p := by linarith
        have hpden : 0 < p - 1 := by linarith
        have hden : 0 < 2 - p := by linarith
        positivity
      · simp [interpolationConstant, hpTwo]
      · have hq1 : 1 < p / (p - 1) :=
          (interpolation_dual_exponent_identities hpUpper).1
        have hq2 : p / (p - 1) < 2 :=
          (interpolation_dual_exponent_identities hpUpper).2.1
        have hqden : 0 < p / (p - 1) - 1 := by linarith
        have hqtop : 0 < 2 - p / (p - 1) := by linarith
        simp [interpolationConstant, not_lt_of_gt hpUpper, ne_of_gt hpUpper]
        unfold interpolationLowerConstant
        positivity
    have hCplus : 0 ≤ C + 1 := by linarith
    exact mul_nonneg (mul_nonneg hconst
      (Real.rpow_nonneg hBnonneg _)) (Real.rpow_nonneg hCplus _)
  · intro N hN f
    have hNpos : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
    have hNpow : 0 < (N.1 : ℝ) ^ (-δ) :=
      Real.rpow_pos_of_pos hNpos _
    have hCplus : 0 < C + 1 := by linarith
    let ε : ℝ := (C + 1) * (N.1 : ℝ) ^ (-δ)
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hCoefficient : C * (N.1 : ℝ) ^ (-δ) ≤ ε := by
      dsimp [ε]
      nlinarith [hC, hNpow]
    let K := floorPowerEndpointErrorKernel c N hc
    have hmass : ∑' m : ℤ, ‖K.coeff m‖ ≤ B := by
      dsimp [K, B]
      exact floorPowerEndpointErrorKernel_norm_tsum_le c N hc
    have hSpectral :
        eLpNormEssSup (integerKernelFourierSymbol K)
          (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) ≤
        ENNReal.ofReal (C * (N.1 : ℝ) ^ (-δ)) := by
      apply eLpNormEssSup_le_of_ae_bound
      filter_upwards with x
      rw [floorPowerEndpointErrorKernelFourierSymbol_eq hc]
      exact hSymbol N hN x
    have hL2 : ∀ g : Lp ℂ 2 (Measure.count : Measure ℤ),
        eLpNorm (integerKernelConvolution K (g : ℤ → ℂ)) 2 Measure.count ≤
          ENNReal.ofReal ε * eLpNorm (g : ℤ → ℂ) 2 Measure.count := by
      intro g
      calc
        eLpNorm (integerKernelConvolution K (g : ℤ → ℂ)) 2 Measure.count ≤
            eLpNormEssSup (integerKernelFourierSymbol K)
              (@AddCircle.haarAddCircle (1 : ℝ) ⟨by norm_num⟩) *
              eLpNorm (g : ℤ → ℂ) 2 Measure.count :=
          eLpNorm_integerKernelConvolution_two_le_fourierSymbol
            (hT := ⟨by norm_num⟩) K g
        _ ≤ ENNReal.ofReal (C * (N.1 : ℝ) ^ (-δ)) *
              eLpNorm (g : ℤ → ℂ) 2 Measure.count :=
          mul_le_mul_of_nonneg_right hSpectral (by positivity)
        _ ≤ ENNReal.ofReal ε * eLpNorm (g : ℤ → ℂ) 2 Measure.count :=
          mul_le_mul_of_nonneg_right
            (ENNReal.ofReal_le_ofReal hCoefficient) (by positivity)
    have hgain := interpolateKernelGain hp K hmass hBpos hε hL2
    have hgain' : ∀ g : Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ),
        ‖integerKernelLpConvolutionCLM
            (p := ENNReal.ofReal p) K g‖ ≤
          interpolationConstant p * B ^ (1 - interpolationBeta p) *
            ε ^ interpolationBeta p * ‖g‖ := by
      intro g
      exact hgain g
    have hpow : ε ^ interpolationBeta p =
        (C + 1) ^ interpolationBeta p *
          (N.1 : ℝ) ^ ((-δ) * interpolationBeta p) := by
      dsimp [ε]
      rw [Real.mul_rpow hCplus.le hNpow.le,
        ← Real.rpow_mul (le_of_lt hNpos)]
    calc
      ‖integerKernelLpConvolutionCLM
          (p := ENNReal.ofReal p) K f‖ ≤
        interpolationConstant p * B ^ (1 - interpolationBeta p) *
          ε ^ interpolationBeta p * ‖f‖ := hgain' f
      _ = (interpolationConstant p * B ^ (1 - interpolationBeta p) *
          (C + 1) ^ interpolationBeta p) *
          (N.1 : ℝ) ^ ((-δ) * interpolationBeta p) * ‖f‖ := by
            rw [hpow]
            ring

/-- The discrete and continuous dyadic operators differ by convolution with
the exact endpoint error kernel. -/
theorem floorPowerEndpointErrorKernelLpConvolution_eq_sub
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (c : ℝ) (N : Scale) (hc : 1 < c) :
    integerKernelLpConvolutionCLM (p := p)
        (floorPowerEndpointErrorKernel c N hc) =
      integerKernelLpConvolutionCLM (p := p) (floorPowerKernel c N) -
        integerKernelLpConvolutionCLM (p := p)
          (continuousModelEndpointKernel c (N.1 : ℝ) hc) := by
  let Kd := floorPowerKernel c N
  let Kc := continuousModelEndpointKernel c (N.1 : ℝ) hc
  let Ke := floorPowerEndpointErrorKernel c N hc
  calc
    integerKernelLpConvolutionCLM (p := p) Ke =
        ∑' m : ℤ, (integerKernelLpTermCLM (p := p) Kd m -
            integerKernelLpTermCLM (p := p) Kc m) := by
      change (∑' m : ℤ, integerKernelLpTermCLM (p := p) Ke m) = _
      apply tsum_congr
      intro m
      simp only [integerKernelLpTermCLM, Ke, Kd, Kc,
        floorPowerEndpointErrorKernel]
      exact sub_smul (Kd.coeff m) (Kc.coeff m)
        ((Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := p)
          (μ := Measure.count) (μb := Measure.count) ℂ
          (MeasurableEquiv.addLeft (-m))
          (measurePreserving_add_left Measure.count (-m))).toContinuousLinearMap)
    _ = integerKernelLpConvolutionCLM (p := p) Kd -
          integerKernelLpConvolutionCLM (p := p) Kc := by
      rw [integerKernelLpConvolutionCLM, integerKernelLpConvolutionCLM]
      exact (integerKernelLpTermCLM_summable (p := p) Kd).tsum_sub
        (integerKernelLpTermCLM_summable (p := p) Kc)

/-- The counting-`Lp` error output at each positive scale. The index `s` is
exactly the blueprint's `k=s-1` convention, so its endpoint is `2^k`. -/
noncomputable def floorPowerEndpointErrorDyadicOperator {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (c : ℝ) (hc : 1 < c) (s : Scale) :
    Lp ℂ p (Measure.count : Measure ℤ) →L[ℂ]
      Lp ℂ p (Measure.count : Measure ℤ) :=
  integerKernelLpConvolutionCLM (p := p)
    (floorPowerEndpointErrorKernel c
      (unweightedDyadicScale (s.1 - 1)) hc)

/-- Pointwise, the paper's integer dyadic average is the continuous endpoint
operator plus the checked error-kernel output. -/
theorem unweightedDyadicFamily_eq_continuousModel_add_error
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (c : ℝ) (hc : 1 < c)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) (s : Scale) (x : ℤ) :
    unweightedDyadicFamily c (f : ℤ → ℂ) s x =
      continuousModelDyadicFamily c hc f s x +
        (floorPowerEndpointErrorDyadicOperator c hc s f : ℤ → ℂ) x := by
  let N := unweightedDyadicScale (s.1 - 1)
  let Kd := floorPowerKernel c N
  let Kc := continuousModelEndpointKernel c (N.1 : ℝ) hc
  have hparameter : (N.1 : ℝ) = continuousModelDyadicParameter s := by
    dsimp [N, unweightedDyadicScale, continuousModelDyadicParameter]
    norm_cast
  have hdiscrete : unweightedDyadicFamily c (f : ℤ → ℂ) s x =
      (integerKernelLpConvolutionCLM (p := p) Kd f : ℤ → ℂ) x := by
    rw [unweightedDyadicFamily, unweightedAverage_integerShift_eq_integerKernelConvolution]
    rw [← integerKernelLpConvolution_apply_eq_integerKernelConvolution
      Kd f x, ← integerKernelLpConvolutionCLM_apply Kd f]
  have hcontinuous : continuousModelDyadicFamily c hc f s x =
      (integerKernelLpConvolutionCLM (p := p) Kc f : ℤ → ℂ) x := by
    dsimp [continuousModelDyadicFamily, continuousModelDyadicEndpointOperator,
      continuousModelEndpointOperator]
    rw [← hparameter]
  have hoperator := floorPowerEndpointErrorKernelLpConvolution_eq_sub
    (p := p) c N hc
  have herror :
      (floorPowerEndpointErrorDyadicOperator c hc s f : ℤ → ℂ) x =
        (integerKernelLpConvolutionCLM (p := p) Kd f : ℤ → ℂ) x -
          (integerKernelLpConvolutionCLM (p := p) Kc f : ℤ → ℂ) x := by
    have h := congrArg (fun T :
        Lp ℂ p (Measure.count : Measure ℤ) →L[ℂ]
          Lp ℂ p (Measure.count : Measure ℤ) => (T f : ℤ → ℂ) x) hoperator
    rw [ContinuousLinearMap.sub_apply] at h
    have hsub :
        ((integerKernelLpConvolutionCLM (p := p) Kd f -
          integerKernelLpConvolutionCLM (p := p) Kc f :
            Lp ℂ p (Measure.count : Measure ℤ)) : ℤ → ℂ) x =
          (integerKernelLpConvolutionCLM (p := p) Kd f : ℤ → ℂ) x -
            (integerKernelLpConvolutionCLM (p := p) Kc f : ℤ → ℂ) x :=
      ae_count_int_iff_forall.mp (Lp.coeFn_sub _ _) x
    rw [hsub] at h
    change (integerKernelLpConvolutionCLM (p := p)
        (floorPowerEndpointErrorKernel c N hc) f : ℤ → ℂ) x =
      (integerKernelLpConvolutionCLM (p := p) Kd f : ℤ → ℂ) x -
        (integerKernelLpConvolutionCLM (p := p) Kc f : ℤ → ℂ) x at h
    simpa [floorPowerEndpointErrorDyadicOperator, N, Kd, Kc] using h
  rw [hdiscrete, hcontinuous, herror]
  ring

private def dyadicScaleNatEquiv : ℕ ≃ Scale where
  toFun k := ⟨k + 1, by omega⟩
  invFun s := s.1 - 1
  left_inv k := by simp
  right_inv s := by
    apply Subtype.ext
    dsimp
    omega

private theorem summable_dyadicGeometric_scale {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun s : Scale => q ^ (s.1 - 1)) := by
  have hnat : Summable (fun k : ℕ => q ^ k) :=
    summable_geometric_of_lt_one hq0 hq1
  let g : Scale → ℝ := fun s => q ^ (s.1 - 1)
  have hcomp : Summable (g ∘ dyadicScaleNatEquiv) := by
    have hfun : (fun k : ℕ => q ^ k) = g ∘ dyadicScaleNatEquiv := by
      funext k
      simp [g, dyadicScaleNatEquiv]
    rw [← hfun]
    exact hnat
  simpa only [g] using dyadicScaleNatEquiv.summable_iff.mp hcomp

private theorem dyadicRpowNatPower (a : ℝ) (k : ℕ) :
    ((2 : ℝ) ^ k) ^ a = ((2 : ℝ) ^ a) ^ k := by
  calc
    ((2 : ℝ) ^ k) ^ a = (2 : ℝ) ^ ((k : ℝ) * a) := by
      rw [← Real.rpow_natCast (2 : ℝ) k,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    _ = ((2 : ℝ) ^ a) ^ k := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ a) k,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      congr 1
      ring

/-- All dyadic error outputs have one geometric majorant. The two initial
scales use the full Young bound; every later scale uses the spectral saving. -/
theorem floorPowerEndpointErrorDyadic_geometric_majorant
    {c p : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) (hp : 1 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨(ENNReal.one_le_ofReal).2 (by linarith)⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ∀ f : Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ),
      ∀ s : Scale,
        ‖floorPowerEndpointErrorDyadicOperator c hc s f‖ ≤
          D * q ^ (s.1 - 1) * ‖f‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨(ENNReal.one_le_ofReal).2 (by linarith)⟩
  let j : ℕ := Nat.ceil c + 2
  let η : ℝ := (1 / 100 : ℝ) /
    (100 * (j : ℝ) * (2 : ℝ) ^ (j : ℝ))
  let δ : ℝ := η / 4
  obtain ⟨A, hA, hdecay⟩ :=
    floorPowerEndpointErrorKernel_lp_operator_decay hc hcNon hp
  have hδpos : 0 < δ := by
    simpa [j, η, δ] using (progressionParameters_delta_bounds hc).1
  have hβpos : 0 < interpolationBeta p := by
    rcases lt_trichotomy p 2 with hp2 | hp2 | hp2
    · rw [interpolationBeta_eq_lower hp hp2]
      have hp0 : 0 < p := by linarith
      have hlt : 2 / p < 2 := by
        apply (div_lt_iff₀ hp0).2
        nlinarith
      linarith
    · subst p
      norm_num [interpolationBeta]
    · rw [interpolationBeta_eq_upper hp2]
      positivity
  let α : ℝ := δ * interpolationBeta p
  have hαpos : 0 < α := mul_pos hδpos hβpos
  let q : ℝ := (2 : ℝ) ^ (-α)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqone : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let B : ℝ := 1 + schwartzExtensionS continuousModelPsiSchwartz
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    have hS := schwartzExtensionS_nonneg continuousModelPsiSchwartz
    linarith
  have hBpos : 0 < B := by
    dsimp [B]
    have hS := schwartzExtensionS_nonneg continuousModelPsiSchwartz
    linarith
  let D : ℝ := A + B * (2 : ℝ) ^ α
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨D, hDnonneg, q, hqpos.le, hqone, ?_⟩
  intro f s
  let k : ℕ := s.1 - 1
  have hsval : s.1 = k + 1 := by dsimp [k]; omega
  let N : Scale := unweightedDyadicScale k
  have hNcast : (N.1 : ℝ) = (2 : ℝ) ^ k := by
    simp [N, unweightedDyadicScale]
  have herrorBound :
      ‖floorPowerEndpointErrorDyadicOperator c hc s f‖ ≤
        D * q ^ (s.1 - 1) * ‖f‖ := by
    rw [show s.1 - 1 = k by dsimp [k]]
    by_cases hk : 2 ≤ k
    · have hNat : 3 ≤ 2 ^ k := by
        have hpow : 2 ^ 2 ≤ 2 ^ k :=
          Nat.pow_le_pow_right (by decide : 0 < 2) hk
        norm_num at hpow
        omega
      have hN : 3 ≤ (N.1 : ℝ) := by
        rw [hNcast]
        exact_mod_cast hNat
      have h := hdecay N hN f
      have hpower : (N.1 : ℝ) ^ ((-δ) * interpolationBeta p) = q ^ k := by
        rw [hNcast]
        have hexp : (-δ) * interpolationBeta p = -α := by
          dsimp [α]
          ring
        rw [hexp, dyadicRpowNatPower]
      have hsource :
          ‖integerKernelLpConvolutionCLM
            (p := ENNReal.ofReal p)
            (floorPowerEndpointErrorKernel c N hc) f‖ ≤
          A * q ^ k * ‖f‖ := by
        rw [← hpower]
        exact h
      change ‖integerKernelLpConvolutionCLM
        (p := ENNReal.ofReal p)
        (floorPowerEndpointErrorKernel c
          (unweightedDyadicScale (s.1 - 1)) hc) f‖ ≤ _
      rw [show s.1 - 1 = k by dsimp [k]]
      calc
        ‖integerKernelLpConvolutionCLM
            (p := ENNReal.ofReal p)
            (floorPowerEndpointErrorKernel c N hc) f‖ ≤
          A * q ^ k * ‖f‖ := hsource
        _ ≤ D * q ^ k * ‖f‖ := by
          have hAD : A ≤ D := by
            have hBpow : 0 ≤ B * (2 : ℝ) ^ α :=
              mul_nonneg hBnonneg (Real.rpow_nonneg (by norm_num) _)
            dsimp [D]
            linarith
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hAD (pow_nonneg hqpos.le _))
            (norm_nonneg _)
    · have hklt : k < 2 := by omega
      have hmass :
          ∑' m : ℤ,
            ‖(floorPowerEndpointErrorKernel c N hc).coeff m‖ ≤ B := by
        dsimp [B]
        exact floorPowerEndpointErrorKernel_norm_tsum_le c N hc
      have hYoung :
          ‖integerKernelLpConvolutionCLM
              (p := ENNReal.ofReal p)
              (floorPowerEndpointErrorKernel c N hc) f‖ ≤ B * ‖f‖ := by
        calc
          ‖integerKernelLpConvolutionCLM
              (p := ENNReal.ofReal p)
              (floorPowerEndpointErrorKernel c N hc) f‖ ≤
            (∑' m : ℤ,
              ‖(floorPowerEndpointErrorKernel c N hc).coeff m‖) * ‖f‖ :=
              integerKernelLpConvolutionCLM_norm_le _ f
          _ ≤ B * ‖f‖ :=
            mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
      have hsmallCoefficient : B ≤ D * q ^ k := by
        change B ≤ D * q ^ (s.1 - 1)
        rw [show s.1 - 1 = k by dsimp [k]]
        have hkcases : k = 0 ∨ k = 1 := by omega
        rcases hkcases with hk0 | hk1
        · rw [hk0]
          have hpow : 1 ≤ (2 : ℝ) ^ α := Real.one_le_rpow (by norm_num) hαpos.le
          have hbase : B ≤ A + B * (2 : ℝ) ^ α := by
            nlinarith [hA, hBnonneg, hpow]
          simpa [D] using hbase
        · rw [hk1]
          have hcancel : (2 : ℝ) ^ α * q = 1 := by
            dsimp [q]
            rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
            simp
          have hcoef : B ≤ D * q := by
            dsimp [D]
            nlinarith [hA, hBnonneg, mul_nonneg hA hqpos.le, hcancel]
          simpa using hcoef
      change ‖integerKernelLpConvolutionCLM
        (p := ENNReal.ofReal p)
        (floorPowerEndpointErrorKernel c
          (unweightedDyadicScale (s.1 - 1)) hc) f‖ ≤ _
      rw [show s.1 - 1 = k by dsimp [k]]
      exact hYoung.trans (mul_le_mul_of_nonneg_right
        hsmallCoefficient (norm_nonneg _))
  exact herrorBound

/-- The absolute error sum has finite `ℓᵖ` norm with the source dyadic
geometric series constant. This is the summability input for the variation
perturbation inequality. -/
theorem floorPowerEndpointErrorDyadic_sum_eLpNorm_le
    {c p : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) (hp : 1 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨(ENNReal.one_le_ofReal).2 (by linarith)⟩
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ f : Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ),
      eLpNorm
        (fun x : ℤ => ∑' s : Scale,
          ENNReal.ofReal ‖(floorPowerEndpointErrorDyadicOperator c hc s f :
            ℤ → ℂ) x‖)
        (ENNReal.ofReal p) (Measure.count : Measure ℤ) ≤
      ENNReal.ofReal E * eLpNorm (f : ℤ → ℂ)
        (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨(ENNReal.one_le_ofReal).2 (by linarith)⟩
  obtain ⟨D, hD, q, hq0, hq1, hmajor⟩ :=
    floorPowerEndpointErrorDyadic_geometric_majorant hc hcNon hp
  have hqsum : Summable (fun s : Scale => q ^ (s.1 - 1)) :=
    summable_dyadicGeometric_scale hq0 hq1
  let E : ℝ := D * (∑' s : Scale, q ^ (s.1 - 1))
  have hEnonneg : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg hD (tsum_nonneg fun s => pow_nonneg hq0 _)
  refine ⟨E, hEnonneg, ?_⟩
  intro f
  let e : Scale → Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
    fun s => floorPowerEndpointErrorDyadicOperator c hc s f
  have hmajorSummable :
      Summable (fun s : Scale => D * q ^ (s.1 - 1) * ‖f‖) := by
    have h := hqsum.mul_left (D * ‖f‖)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have heSummable : Summable (fun s : Scale => ‖e s‖) :=
    Summable.of_nonneg_of_le (fun s => norm_nonneg (e s))
      (fun s => by simpa [e] using hmajor f s) hmajorSummable
  have hrealTsum : (∑' s : Scale, ‖e s‖) ≤ E * ‖f‖ := by
    calc
      (∑' s : Scale, ‖e s‖) ≤
          ∑' s : Scale, D * q ^ (s.1 - 1) * ‖f‖ :=
        heSummable.tsum_le_tsum (fun s => by simpa [e] using hmajor f s)
          hmajorSummable
      _ = (D * ‖f‖) * (∑' s : Scale, q ^ (s.1 - 1)) := by
        calc
          _ = ∑' s : Scale, (D * ‖f‖) * q ^ (s.1 - 1) := by
            apply tsum_congr
            intro s
            ring
          _ = _ := hqsum.tsum_mul_left _
      _ = E * ‖f‖ := by dsimp [E]; ring
  have hENNsum :
      (∑' s : Scale, ENNReal.ofReal ‖e s‖) =
        ENNReal.ofReal (∑' s : Scale, ‖e s‖) := by
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun s => norm_nonneg (e s)) heSummable).symm
  have hinput : eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p)
      (Measure.count : Measure ℤ) = ENNReal.ofReal ‖f‖ := by
    calc
      eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p)
          (Measure.count : Measure ℤ) = ‖f‖ₑ := by rw [Lp.enorm_def]
      _ = ENNReal.ofReal ‖f‖ := (ofReal_norm _).symm
  calc
    eLpNorm
        (fun x : ℤ => ∑' s : Scale,
          ENNReal.ofReal ‖(floorPowerEndpointErrorDyadicOperator c hc s f :
            ℤ → ℂ) x‖)
        (ENNReal.ofReal p) (Measure.count : Measure ℤ) ≤
      ∑' s : Scale, ENNReal.ofReal ‖e s‖ := by
        simpa [e, harmonicMagnitudeLp_apply] using
          (eLpNorm_tsum_ofReal_norm_le_tsum e heSummable)
    _ = ENNReal.ofReal (∑' s : Scale, ‖e s‖) := hENNsum
    _ ≤ ENNReal.ofReal (E * ‖f‖) := ENNReal.ofReal_le_ofReal hrealTsum
    _ = ENNReal.ofReal E *
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p)
          (Measure.count : Measure ℤ) := by
            rw [ENNReal.ofReal_mul hEnonneg, ← hinput]

/-- Conditional `ha:dyadic` variation estimate. Its only analytic input is
the exact continuous-model variation hypothesis `hjsw`; the discrete error
term is controlled by the checked spectral, interpolation, and dyadic
geometric estimates above. -/
theorem unweightedDyadicVariation_eLpNorm_le_of_jsw
    {p r : ℝ} (hp : 1 < p) (hr : 2 < r)
    (cval : ℝ) (hc : 1 < cval) (hcNon : NonIntegral cval)
    (Cjsw : ℝ≥0)
    (hjsw : ∀ g : ℤ →₀ ℂ,
      eLpNorm
        (fun y : ℝ =>
          FractionalPrimes.Literature.Variation.orderedRVariation r
            (fun k : ℤ =>
              continuousModelAllDyadicConvolutionFamily cval hc g k y))
        (ENNReal.ofReal p) (volume : Measure ℝ) ≤
      (Cjsw : ℝ≥0∞) * eLpNorm
        (continuousModelSchwartzExtension g : ℝ → ℂ)
        (ENNReal.ofReal p) (volume : Measure ℝ)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨(ENNReal.one_le_ofReal).2 (by linarith)⟩
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ f : Lp ℂ (ENNReal.ofReal p) (Measure.count : Measure ℤ),
      eLpNorm
        (rVariationFun r
          (unweightedDyadicFamily cval (f : ℤ → ℂ)))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ) ≤
      (ENNReal.ofReal
          (schwartzExtensionL continuousModelReproducingSchwartz ^ (1 - p⁻¹) *
            schwartzExtensionS continuousModelReproducingSchwartz ^ p⁻¹) *
        (Cjsw : ℝ≥0∞) *
        ENNReal.ofReal
          (schwartzExtensionS continuousModelPsiSchwartz ^ (1 - p⁻¹) *
            schwartzExtensionL continuousModelPsiSchwartz ^ p⁻¹) +
        2 * ENNReal.ofReal E) *
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p)
          (Measure.count : Measure ℤ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨(ENNReal.one_le_ofReal).2 (by linarith)⟩
  obtain ⟨E, hEnonneg, hErrorAll⟩ :=
    floorPowerEndpointErrorDyadic_sum_eLpNorm_le hc hcNon hp
  refine ⟨E, hEnonneg, ?_⟩
  intro f
  have hError := hErrorAll f
  have hModel :=
    continuousModelDyadicVariation_eLpNorm_le_of_jsw
      hp hr cval hc Cjsw hjsw f
  have hModelBound :
      eLpNorm
        (rVariationFun r (continuousModelDyadicFamily cval hc f))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ) ≤
      ENNReal.ofReal
          (schwartzExtensionL continuousModelReproducingSchwartz ^ (1 - p⁻¹) *
            schwartzExtensionS continuousModelReproducingSchwartz ^ p⁻¹) *
        (Cjsw : ℝ≥0∞) *
        ENNReal.ofReal
          (schwartzExtensionS continuousModelPsiSchwartz ^ (1 - p⁻¹) *
            schwartzExtensionL continuousModelPsiSchwartz ^ p⁻¹) *
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p)
          (Measure.count : Measure ℤ) := hModel
  let FQ : Scale → ℤ → ℂ :=
    unweightedDyadicFamily cval (f : ℤ → ℂ)
  let FP : Scale → ℤ → ℂ := continuousModelDyadicFamily cval hc f
  let FE : Scale → ℤ → ℂ := fun s =>
    (floorPowerEndpointErrorDyadicOperator cval hc s f : ℤ → ℂ)
  let G : ℤ → ℝ≥0∞ := fun x =>
    ∑' s : Scale, ENNReal.ofReal ‖FE s x‖
  have hr1 : 1 ≤ r := by linarith
  have hpoint (x : ℤ) :
      rVariationFun r FQ x ≤ rVariationFun r FP x + (G x + G x) := by
    have hvar := rVariation_le_of_pointwise_error r hr1
      (fun s => FQ s x) (fun s => FP s x) (fun s => FE s x) (by
        intro s
        simpa [FQ, FP, FE] using
          unweightedDyadicFamily_eq_continuousModel_add_error
            cval hc f s x)
    rw [rVariationFun_apply, rVariationFun_apply]
    calc
      rVariation r (fun s => FQ s x) ≤
          rVariation r (fun s => FP s x) +
            2 * ∑' s : Scale, ENNReal.ofReal ‖FE s x‖ := hvar
      _ = rVariationFun r FP x + (G x + G x) := by
        rw [rVariationFun_apply]
        simp [G, two_mul, add_assoc]
  have hQmeas : ∀ s : Scale, AEMeasurable (FQ s) Measure.count := by
    intro s
    exact (measurable_of_countable (FQ s)).aemeasurable
  have hPmeas : ∀ s : Scale, AEMeasurable (FP s) Measure.count := by
    intro s
    exact (measurable_of_countable (FP s)).aemeasurable
  have hLongQ : AEStronglyMeasurable (rVariationFun r FQ) Measure.count :=
    (aemeasurable_rVariationFun Measure.count r FQ hQmeas).aestronglyMeasurable
  have hLongP : AEStronglyMeasurable (rVariationFun r FP) Measure.count :=
    (aemeasurable_rVariationFun Measure.count r FP hPmeas).aestronglyMeasurable
  have hmajor :
      eLpNorm (rVariationFun r FQ) (ENNReal.ofReal p) Measure.count ≤
        eLpNorm (fun x => rVariationFun r FP x + (G x + G x))
          (ENNReal.ofReal p) Measure.count := by
    apply eLpNorm_mono_enorm_ae hLongQ
    filter_upwards with x
    simpa only [enorm_eq_self] using hpoint x
  have hsum1 := eLpNorm_add_le (p := ENNReal.ofReal p)
    (μ := Measure.count) (Fact.out : 1 ≤ ENNReal.ofReal p)
    (f := rVariationFun r FP) (g := fun x => G x + G x)
  have hsum2 := eLpNorm_add_le (p := ENNReal.ofReal p)
    (μ := Measure.count) (Fact.out : 1 ≤ ENNReal.ofReal p)
    (f := G) (g := G)
  let A : ℝ≥0∞ :=
    ENNReal.ofReal
        (schwartzExtensionL continuousModelReproducingSchwartz ^ (1 - p⁻¹) *
          schwartzExtensionS continuousModelReproducingSchwartz ^ p⁻¹) *
      (Cjsw : ℝ≥0∞) *
      ENNReal.ofReal
        (schwartzExtensionS continuousModelPsiSchwartz ^ (1 - p⁻¹) *
          schwartzExtensionL continuousModelPsiSchwartz ^ p⁻¹)
  let nf : ℝ≥0∞ :=
    eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count
  change eLpNorm (rVariationFun r FQ) (ENNReal.ofReal p) Measure.count ≤
    (A + 2 * ENNReal.ofReal E) * nf
  calc
    eLpNorm (rVariationFun r FQ) (ENNReal.ofReal p) Measure.count ≤
        eLpNorm (fun x => rVariationFun r FP x + (G x + G x))
          (ENNReal.ofReal p) Measure.count := hmajor
    _ ≤ eLpNorm (rVariationFun r FP) (ENNReal.ofReal p) Measure.count +
        eLpNorm (fun x => G x + G x) (ENNReal.ofReal p) Measure.count := hsum1
    _ ≤ eLpNorm (rVariationFun r FP) (ENNReal.ofReal p) Measure.count +
        (eLpNorm G (ENNReal.ofReal p) Measure.count +
          eLpNorm G (ENNReal.ofReal p) Measure.count) :=
      add_le_add le_rfl hsum2
    _ ≤ A * nf + (ENNReal.ofReal E * nf + ENNReal.ofReal E * nf) := by
      exact add_le_add hModelBound (add_le_add hError hError)
    _ = (A + 2 * ENNReal.ofReal E) * nf := by
      simp [two_mul, add_mul, mul_add, add_assoc]

end

end FractionalPrimes.Literature.Harmonic

end
