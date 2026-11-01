module

public import FractionalPrimes.Literature.Polynomial.PolynomialIntegerToRealLargeTransfer
public import FractionalPrimes.CramerDensityAtScale

/-!
# Bounded-centre branch of the integer-to-real transfer

This module formalizes the small-`X` estimate in approved blueprint
`lc:integer-to-real` and Astra `literature-expansion/sections/centres.tex`.
The integer-centred cancellation hypothesis is not needed in this bounded
range: absolute coefficient bounds and the exact real interval cardinality
suffice.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Centres

open _root_.Polynomial

noncomputable section

/-- The exact bounded-centre constant `C₀` from blueprint
`lc:integer-to-real`. -/
def integerToRealSmallXConstant (A ε : ℝ) : ℝ :=
  2 * (Real.log (integerToRealThreshold ε)) ^ A *
    (1 + Real.log (2 * integerToRealThreshold ε) +
      Real.exp 13 * (Real.log (integerToRealThreshold ε)) ^ (2 / 5 : ℝ))

private theorem smallTransfer_cramer_weight_abs_le_density (X : ℝ) (n : ℤ) :
    |FractionalPrimes.paperCramerWeight
        (FractionalPrimes.paperShortBlockCutoff X) n| ≤
      FractionalPrimes.paperCramerDensity
        (FractionalPrimes.paperShortBlockCutoff X) := by
  have hR : 0 ≤ FractionalPrimes.paperCramerDensity
      (FractionalPrimes.paperShortBlockCutoff X) := by
    unfold FractionalPrimes.paperCramerDensity
    positivity
  unfold FractionalPrimes.paperCramerWeight
  split_ifs <;> simp [abs_of_nonneg hR, hR]

private theorem norm_sum_phase_le_card
    (S : Finset ℤ) (a : ℤ → ℂ) (P : Polynomial ℝ) (B : ℝ)
    (hterm : ∀ n ∈ S,
      ‖a n * FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ ≤ B) :
    ‖∑ n ∈ S,
      a n * FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
        (S.card : ℝ) * B := by
  calc
    _ ≤ ∑ n ∈ S,
        ‖a n * FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, B := by
      apply Finset.sum_le_sum
      intro n hn
      exact hterm n hn
    _ = (S.card : ℝ) * B := by simp [nsmul_eq_mul]

/-- The exact small-`X` branch of `lc:integer-to-real`, simultaneously for
the Möbius and von-Mangoldt-minus-Cramér sums and uniformly over the real
polynomial phase. -/
theorem integerToRealSmallXTransfer
    (k : ℕ) (A ε : ℝ) (hA : 0 < A)
    (hε : 0 < ε) (hεtop : ε < 3 / 16) :
    ∀ X H : ℝ,
      3 ≤ X → X < integerToRealThreshold ε →
      X ^ (5 / 8 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ P : Polynomial ℝ, P.natDegree ≤ k →
        ‖∑ n ∈ FractionalPrimes.realIntegerInterval X H,
            (FractionalPrimes.paperMu n : ℂ) *
              FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ +
          ‖FractionalPrimes.Literature.Centres.realCenterLambdaModelPhaseSum
              P X H‖ ≤
          integerToRealSmallXConstant A ε * H * (Real.log X) ^ (-A : ℝ) := by
  intro X H hX hXlt hHlower hHupper P hP
  let X₀ : ℝ := integerToRealThreshold ε
  let logBound : ℝ :=
    Real.log (2 * X₀) + Real.exp 13 * (Real.log X₀) ^ (2 / 5 : ℝ)
  let totalBound : ℝ := 1 + logBound
  have hXpos : 0 < X := by linarith
  have hXgt1 : 1 < X := by linarith
  have hXone : 1 ≤ X := le_of_lt hXgt1
  have hX₀gt1 : 1 < X₀ := by
    dsimp [X₀, integerToRealThreshold]
    exact Real.one_lt_rpow (by norm_num) (by positivity)
  have hX₀pos : 0 < X₀ := by linarith
  have hlogXpos : 0 < Real.log X := Real.log_pos hXgt1
  have hlogX₀pos : 0 < Real.log X₀ := Real.log_pos hX₀gt1
  have hXleX₀ : X ≤ X₀ := le_of_lt hXlt
  have hlogXle : Real.log X ≤ Real.log X₀ :=
    Real.log_le_log hXpos hXleX₀
  have hHexp : 0 < 5 / 8 + ε := by linarith
  have hHge1 : 1 ≤ H := by
    have hpow : 1 ≤ X ^ (5 / 8 + ε) := Real.one_le_rpow hXone hHexp.le
    linarith [hHlower]
  have hHleX : H ≤ X := by
    have hexp : 1 - ε ≤ 1 := by linarith
    have hpow : X ^ (1 - ε) ≤ X ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hXone hexp
    rw [Real.rpow_one] at hpow
    exact hHupper.trans hpow
  have hcutoff := FractionalPrimes.paperCramerDensity_at_cutoff_scale hX
  have hlogBound_nonneg : 0 ≤ logBound := by
    have hlog2X₀ : 0 < Real.log (2 * X₀) :=
      Real.log_pos (by nlinarith [hX₀gt1])
    have hlogX₀pow : 0 ≤ (Real.log X₀) ^ (2 / 5 : ℝ) :=
      Real.rpow_nonneg hlogX₀pos.le _
    dsimp [logBound]
    exact add_nonneg hlog2X₀.le
      (mul_nonneg (le_of_lt (Real.exp_pos 13)) hlogX₀pow)
  have htotalBound_nonneg : 0 ≤ totalBound := by
    dsimp [totalBound]
    positivity
  have hcoeff : ∀ n ∈ FractionalPrimes.realIntegerInterval X H,
      |FractionalPrimes.paperLambda n -
          FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff X) n| ≤ logBound := by
    intro n hn
    have hninterval :=
      (FractionalPrimes.mem_realIntegerInterval_iff X H n).mp hn
    have hnrealge1 : (1 : ℝ) ≤ (n : ℝ) := by linarith [hninterval.1]
    have hnge1 : (1 : ℤ) ≤ n := by exact_mod_cast hnrealge1
    have hnrealupper : (n : ℝ) ≤ 2 * X₀ := by
      dsimp [X₀]
      calc
        (n : ℝ) ≤ X + H := hninterval.2
        _ ≤ 2 * X := by linarith [hHleX]
        _ ≤ 2 * integerToRealThreshold ε := by nlinarith [hXleX₀]
    have hLambda := FractionalPrimes.paperLambda_bounds hnge1
    have hLambdaUpper :
        FractionalPrimes.paperLambda n ≤ Real.log (2 * X₀) := by
      calc
        FractionalPrimes.paperLambda n ≤ Real.log (n : ℝ) := hLambda.2
        _ ≤ Real.log (2 * X₀) :=
          Real.log_le_log (by linarith [hnrealge1]) hnrealupper
    have hcramerAbs :
        |FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff X) n| ≤
          Real.exp 13 * (Real.log X₀) ^ (2 / 5 : ℝ) := by
      calc
        |FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff X) n| ≤
            FractionalPrimes.paperCramerDensity
              (FractionalPrimes.paperShortBlockCutoff X) := by
          exact smallTransfer_cramer_weight_abs_le_density X n
        _ ≤ Real.exp 13 * (Real.log X) ^ (2 / 5 : ℝ) := hcutoff
        _ ≤ Real.exp 13 * (Real.log X₀) ^ (2 / 5 : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hlogXpos.le hlogXle (by norm_num))
            (le_of_lt (Real.exp_pos 13))
    calc
      |FractionalPrimes.paperLambda n -
          FractionalPrimes.paperCramerWeight
            (FractionalPrimes.paperShortBlockCutoff X) n| ≤
          |FractionalPrimes.paperLambda n| +
            |FractionalPrimes.paperCramerWeight
              (FractionalPrimes.paperShortBlockCutoff X) n| :=
        (by
          simpa [abs_of_nonneg hLambda.1] using
            (abs_sub_le (FractionalPrimes.paperLambda n) (0 : ℝ)
              (FractionalPrimes.paperCramerWeight
                (FractionalPrimes.paperShortBlockCutoff X) n)))
      _ ≤ Real.log (2 * X₀) +
          Real.exp 13 * (Real.log X₀) ^ (2 / 5 : ℝ) := by
        rw [abs_of_nonneg hLambda.1]
        exact add_le_add hLambdaUpper hcramerAbs
      _ = logBound := by rfl
  have hmu : ∀ n ∈ FractionalPrimes.realIntegerInterval X H,
      ‖(FractionalPrimes.paperMu n : ℂ) *
          FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ ≤ 1 := by
    intro n hn
    have hninterval :=
      (FractionalPrimes.mem_realIntegerInterval_iff X H n).mp hn
    have hnrealge1 : (1 : ℝ) ≤ (n : ℝ) := by linarith [hninterval.1]
    have hnge1 : (1 : ℤ) ≤ n := by exact_mod_cast hnrealge1
    rw [norm_mul, Complex.norm_intCast,
      FractionalPrimes.norm_unitFrequencyPhase, mul_one]
    exact_mod_cast (FractionalPrimes.paperMu_abs_le_one hnge1)
  have hmuNorm := norm_sum_phase_le_card
    (FractionalPrimes.realIntegerInterval X H)
    (fun n => (FractionalPrimes.paperMu n : ℂ)) P 1 hmu
  have hlambdaNorm := norm_sum_phase_le_card
    (FractionalPrimes.realIntegerInterval X H)
    (fun n => ((FractionalPrimes.paperLambda n -
      FractionalPrimes.paperCramerWeight
        (FractionalPrimes.paperShortBlockCutoff X) n : ℝ) : ℂ))
    P logBound (by
      intro n hn
      rw [norm_mul, Complex.norm_real,
        FractionalPrimes.norm_unitFrequencyPhase, mul_one]
      exact hcoeff n hn)
  have hcard := FractionalPrimes.realIntegerInterval_card_le X H hHge1
  have hraw :
      ‖∑ n ∈ FractionalPrimes.realIntegerInterval X H,
          (FractionalPrimes.paperMu n : ℂ) *
            FractionalPrimes.unitFrequencyPhase (P.eval (n : ℝ))‖ +
        ‖FractionalPrimes.Literature.Centres.realCenterLambdaModelPhaseSum
            P X H‖ ≤
        (FractionalPrimes.realIntegerInterval X H).card * totalBound := by
    unfold FractionalPrimes.Literature.Centres.realCenterLambdaModelPhaseSum
    calc
      _ ≤ (FractionalPrimes.realIntegerInterval X H).card * 1 +
            (FractionalPrimes.realIntegerInterval X H).card * logBound :=
        add_le_add hmuNorm hlambdaNorm
      _ = _ := by dsimp [totalBound]; ring
  have hcardScaled :
      (FractionalPrimes.realIntegerInterval X H).card * totalBound ≤
        2 * H * totalBound := by
    calc
      (FractionalPrimes.realIntegerInterval X H).card * totalBound ≤
          (H + 1) * totalBound :=
        mul_le_mul_of_nonneg_right hcard htotalBound_nonneg
      _ ≤ 2 * H * totalBound :=
        mul_le_mul_of_nonneg_right (by linarith [hHge1]) htotalBound_nonneg
  have hlogScale :
      1 ≤ (Real.log X₀) ^ A * (Real.log X) ^ (-A : ℝ) := by
    have hpower : (Real.log X) ^ A ≤ (Real.log X₀) ^ A :=
      Real.rpow_le_rpow hlogXpos.le hlogXle hA.le
    have hneg : 0 ≤ (Real.log X) ^ (-A : ℝ) :=
      Real.rpow_nonneg hlogXpos.le _
    have hcancel :
        (Real.log X) ^ A * (Real.log X) ^ (-A : ℝ) = 1 := by
      rw [← Real.rpow_add hlogXpos]
      rw [show A + -A = 0 by ring, Real.rpow_zero]
    calc
      1 = (Real.log X) ^ A * (Real.log X) ^ (-A : ℝ) := hcancel.symm
      _ ≤ (Real.log X₀) ^ A * (Real.log X) ^ (-A : ℝ) :=
        mul_le_mul_of_nonneg_right hpower hneg
  have hrawFactorNonneg : 0 ≤ 2 * H * totalBound := by positivity
  calc
    _ ≤ 2 * H * totalBound := hraw.trans hcardScaled
    _ ≤ integerToRealSmallXConstant A ε * H * (Real.log X) ^ (-A : ℝ) := by
      calc
        2 * H * totalBound = 2 * H * totalBound * 1 := by ring
        _ ≤ 2 * H * totalBound *
              ((Real.log X₀) ^ A * (Real.log X) ^ (-A : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogScale hrawFactorNonneg
        _ = integerToRealSmallXConstant A ε * H *
              (Real.log X) ^ (-A : ℝ) := by
          dsimp [integerToRealSmallXConstant, totalBound, logBound, X₀]
          ring

#print axioms integerToRealSmallXTransfer

end

end FractionalPrimes.Literature.Centres

end
