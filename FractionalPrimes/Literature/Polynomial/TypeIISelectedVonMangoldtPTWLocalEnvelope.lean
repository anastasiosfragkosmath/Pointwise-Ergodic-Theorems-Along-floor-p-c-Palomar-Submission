module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWLongPrefixTransfer
public import FractionalPrimes.Literature.Polynomial.SelectedPTWLocalPrefixWindowFacts
public import FractionalPrimes.Literature.Polynomial.SelectedPTWShortPrefix
public import FractionalPrimes.Literature.Polynomial.ResiduePrefixShortLong
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalLargeXSelectionAssembly
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalAllXPTWSelection
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWFullFrequencyIntegral
public import FractionalPrimes.Literature.Polynomial.SelectedPTWResidueReduction
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTransferAssembly
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTaggedLiveAggregateContinuous
public import FractionalPrimes.Literature.Twisted.PrefixTwistRange
public import Mathlib.Tactic
@[expose] public section

/-! The local-prefix form of the selected von Mangoldt PTW bound, followed by
the exact short/long split for the canonical raw-component envelope. The
outer length controls the source frequency lower bound; the individual
long-branch prefix length controls its own Mellin data. -/

section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- The common eventual threshold for the selected von Mangoldt envelope.
It includes the existing OAISource/source-window threshold and the extra
42-logarithm-power absorption for every local prefix in the long branch. -/
noncomputable def selectedVonMangoldtPTWLocalEnvelopeThreshold
    (a eta : ℝ) (haMUF : 2 ≤ a) : ℝ :=
  max (selectedMobiusPTWFinalSourceOAISourceThreshold a eta haMUF)
    (selectedMobiusPTWLocalPrefixWindowThreshold a eta)

private theorem selectedVonMangoldtPTW_componentK_le_prefixMassScale_local
    {X : ℝ} (hX : (2 : ℝ) ^ 120 ≤ X)
    (hlog : 2 ≤ Real.log X) :
    selectedComponentK X ≤ prefixTwistMassScale *
      (Real.log X) ^ (selectedMobiusPTWComponentExponent : ℝ) := by
  have hXpos : 0 < X := by positivity
  have hlogXnonneg : 0 ≤ Real.log X := by linarith
  have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogZ : Real.log ((2 : ℝ) ^ 22 * X) =
      22 * Real.log 2 + Real.log X := by
    rw [Real.log_mul (by positivity) hXpos.ne', Real.log_pow]
    push_cast
    ring
  have hZbound : 1 + Real.log ((2 : ℝ) ^ 22 * X) ≤
      (2 + 22 * Real.log 2) * Real.log X := by
    rw [hlogZ]
    nlinarith
  have hZnonneg : 0 ≤ 1 + Real.log ((2 : ℝ) ^ 22 * X) := by
    rw [hlogZ]
    positivity
  have hpow := pow_le_pow_left₀ hZnonneg hZbound prefixTwistBeta
  have hbeta : (prefixTwistBeta : ℝ) =
      (selectedMobiusPTWComponentExponent : ℝ) := by
    rfl
  calc
    selectedComponentK X = (2 : ℝ) ^ 90 *
        (1 + Real.log ((2 : ℝ) ^ 22 * X)) ^ prefixTwistBeta := by
      simp [selectedComponentK, prefixTwistBeta]
    _ ≤ (2 : ℝ) ^ 90 *
        ((2 + 22 * Real.log 2) * Real.log X) ^ prefixTwistBeta :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = prefixTwistMassScale *
        (Real.log X) ^ (prefixTwistBeta : ℝ) := by
      rw [mul_pow]
      simp [prefixTwistMassScale, Real.rpow_natCast]
      ring
    _ = prefixTwistMassScale *
        (Real.log X) ^ (selectedMobiusPTWComponentExponent : ℝ) := by
      rw [hbeta]

private theorem selectedVonMangoldtPTW_sourceIntegralConstant_nonneg_local :
    0 ≤ selectedPTWSourceIntegralConstant := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have heps : 0 < (1 / 1000 : ℝ) := by norm_num
  have hden : 0 < (1 / 1000 : ℝ) * Real.log 2 := mul_pos heps hlog2
  have hdiv (C : ℕ) : 0 ≤ divisorSubpowerConstant C (1 / 1000 : ℝ) := by
    have hbase : 0 ≤ 1 + (C : ℝ) /
        ((1 / 1000 : ℝ) * Real.log 2) := by positivity
    unfold divisorSubpowerConstant divisorSubpowerCutoff
    exact pow_nonneg hbase _
  have hdecomp : 0 ≤ decompositionC := by
    unfold decompositionC
    positivity
  have hblocks : 0 ≤
      (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) :=
    Nat.cast_nonneg _
  have hJ : 0 ≤ J 20 := by unfold J K; positivity
  have hfirst : 0 ≤ (2 : ℝ) ^ (37 + selectedMobiusPTWLogExponent) := by
    positivity
  have hsecond : 0 ≤ J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1)) :=
    mul_nonneg hJ (by positivity)
  have hthird : 0 ≤ (2 * decompositionC) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (by norm_num) hdecomp) _
  have hfourth : 0 ≤
      (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 := by
    positivity
  have hAB : 0 ≤ (2 : ℝ) ^ (37 + selectedMobiusPTWLogExponent) *
      (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) :=
    mul_nonneg hfirst hsecond
  have hABC : 0 ≤
      ((2 : ℝ) ^ (37 + selectedMobiusPTWLogExponent) *
        (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
        (2 * decompositionC) ^ (3 / 2 : ℝ)) :=
    mul_nonneg hAB hthird
  have hABCD : 0 ≤
      (((2 : ℝ) ^ (37 + selectedMobiusPTWLogExponent) *
        (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
        (2 * decompositionC) ^ (3 / 2 : ℝ)) *
        (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3) :=
    mul_nonneg hABC hfourth
  have hABCDE : 0 ≤
      (((2 : ℝ) ^ (37 + selectedMobiusPTWLogExponent) *
        (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
        (2 * decompositionC) ^ (3 / 2 : ℝ)) *
        (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3) *
        divisorSubpowerConstant 60 (1 / 1000 : ℝ) :=
    mul_nonneg hABCD (hdiv 60)
  unfold selectedPTWSourceIntegralConstant
  exact mul_nonneg hABCDE (hdiv 3)

set_option maxHeartbeats 8000000 in
/-- The source long-prefix estimate with a macro interval `H` and an actual
prefix `m` in its long branch. The source twist lower bound remains normalized
by `H`; the full-frequency data and recovered mean are for the actual `m`. -/
theorem selectedVonMangoldtPTW_localPrefixSum_norm_le_of_OAISource
    {X H m q b : ℕ} {a eta T : ℝ}
    (D : SelectedVonMangoldtPTWTaggedOuterDecomposition (X : ℝ))
    (ν : VonMangoldtDyadicLabel (X : ℝ))
    (hν : ν ∈ vonMangoldtDyadicLabels (X : ℝ)
      (dyadicMobiusCutoff (X : ℝ)))
    (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (heta0 : 0 < eta) (heta : eta < 3 / 16)
    (hX : selectedVonMangoldtPTWLocalEnvelopeThreshold a eta
      (show 2 ≤ a from by
        have h2nat : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
        have h2 : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast h2nat
        exact h2.trans ha) ≤ (X : ℝ))
    (hHlower : (X : ℝ) ^ (5 / 8 + eta) ≤ (H : ℝ))
    (hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - eta))
    (hTlower : ((X : ℝ) / (H : ℝ)) *
      (Real.log (X : ℝ)) ^ (50 * a) ≤ |T|)
    (hTupper : |T| ≤ (X : ℝ) ^ a)
    (hq : 0 < q)
    (hqlog : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ a)
    (hcutoff : (H : ℝ) * (Real.log (X : ℝ)) ^ (-2 * a) ≤ (m : ℝ))
    (hmH : m ≤ H)
    (hThird :
      largeTypeIIDyadicComponentData (dyadicMobiusCutoff (X : ℝ))
        (dyadicBinomialCoefficient ν.1) (decompositionDelta (X : ℝ))
        (selectedVonMangoldtPTWRawDyadicComponent ν)
        (vonMangoldtLabelFactors ν)
        (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents ∧
      ∀ j, (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents j <
        (3 / 8 : ℝ)) :
    ‖residuePrefixSum X m q b
        (selectedVonMangoldtPTWLongPrefixWeight ν T)‖ ≤
      (m : ℝ) * selectedMobiusPTWLongPrefixConstant a
        polynomialKernelM1 prefixTwistMassScale selectedPTWSourceIntegralConstant *
          (Real.log (X : ℝ)) ^ (-a) := by
  classical
  have h2nat : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
  have h2 : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast h2nat
  have haMUF : 2 ≤ a := h2.trans ha
  have hXbase : selectedMobiusPTWFinalSourceOAISourceThreshold a eta haMUF ≤
      (X : ℝ) := by
    exact (le_max_left _ _).trans hX
  have hXlocal : selectedMobiusPTWLocalPrefixWindowThreshold a eta ≤
      (X : ℝ) := by
    exact (le_max_right _ _).trans hX
  have hXfinal : selectedMobiusPTWFinalSourceThreshold a eta ≤ (X : ℝ) := by
    unfold selectedMobiusPTWFinalSourceOAISourceThreshold at hXbase
    exact (le_max_left _ _).trans hXbase
  have hTail : max (Real.exp (selectedMobiusPTWCellLogThreshold a (eta / 4)))
      (selectedMobiusPTWUncappedSavingThreshold a (eta / 4)) ≤ (X : ℝ) :=
    (le_max_right _ _).trans hXfinal
  have hXlog : Real.exp (selectedMobiusPTWCellLogThreshold a (eta / 4)) ≤
      (X : ℝ) := (le_max_left _ _).trans hTail
  have hXsave : selectedMobiusPTWUncappedSavingThreshold a (eta / 4) ≤
      (X : ℝ) := (le_max_right _ _).trans hTail
  have hXMUF : selectedMobiusPTWFirstFactorMUFThreshold
      FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
      a haMUF ≤ (X : ℝ) := by
    unfold selectedMobiusPTWFinalSourceOAISourceThreshold at hXbase
    exact (le_max_right _ _).trans hXbase
  have hXlarge : (2 : ℝ) ^ 120 ≤ (X : ℝ) := by
    have hbase : (2 : ℝ) ^ 120 ≤
        selectedMobiusPTWFirstFactorMUFThreshold
          FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
          a haMUF := by
      unfold selectedMobiusPTWFirstFactorMUFThreshold
      exact le_max_left _ _
    exact hbase.trans hXMUF
  have hXgrowth : selectedMobiusPTWTransferGrowthThreshold a eta ≤ (X : ℝ) := by
    have hSource : selectedMobiusPTWSourceWindowThreshold a eta ≤ (X : ℝ) :=
      (le_max_left _ _).trans hXlocal
    exact (le_max_left _ _).trans hSource
  have hgrowth := selectedMobiusPTWTransferGrowth_of_threshold ha heta0 hXgrowth
  have hlog2 : 2 ≤ Real.log (X : ℝ) := hgrowth.1
  have hXpos : 0 < (X : ℝ) := by linarith [hXlarge]
  have hXone : 1 ≤ (X : ℝ) := by linarith [hXlarge]
  have hHpos : 0 < (H : ℝ) := by
    have hpow : 0 < (X : ℝ) ^ (5 / 8 + eta) :=
      Real.rpow_pos_of_pos hXpos _
    exact lt_of_lt_of_le hpow hHlower
  have hHleX : (H : ℝ) ≤ (X : ℝ) := by
    have hexp : (1 - eta : ℝ) ≤ 1 := by linarith
    have hpow : (X : ℝ) ^ (1 - eta) ≤ (X : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hXone hexp
    simpa only [Real.rpow_one] using hHupper.trans hpow
  have hmHreal : (m : ℝ) ≤ (H : ℝ) := by exact_mod_cast hmH
  have hmpos : 0 < (m : ℝ) := by
    have hlogpos : 0 < Real.log (X : ℝ) := by linarith [hlog2]
    have hcutoffPos : 0 < (H : ℝ) * (Real.log (X : ℝ)) ^ (-2 * a) :=
      mul_pos hHpos (Real.rpow_pos_of_pos hlogpos _)
    exact lt_of_lt_of_le hcutoffPos hcutoff
  have hmleX : (m : ℝ) ≤ (X : ℝ) := hmHreal.trans hHleX
  obtain ⟨d, Q, r, hd, hQ, hdQ, hdb, _hdle, _hcop, hrchar⟩ :=
    selectedPTWResidueReduction q b hq
  let residue : ℤ := (b : ℤ)
  let fd := selectedVonMangoldtPTWFullFrequencyResidueData
    hXlarge hν (m : ℝ) hmpos hmleX q residue T
  have hfdX : fd.X = (X : ℝ) := by rfl
  have hfdH : fd.H = (m : ℝ) := by rfl
  have hK : fd.K ≤ prefixTwistMassScale *
      (Real.log fd.X) ^ (selectedMobiusPTWComponentExponent : ℝ) := by
    change selectedComponentK (X : ℝ) ≤ prefixTwistMassScale *
      (Real.log (X : ℝ)) ^ (selectedMobiusPTWComponentExponent : ℝ)
    exact selectedVonMangoldtPTW_componentK_le_prefixMassScale_local
      hXlarge hlog2
  have hh0 : fd.h0 = selectedComponentH0 fd.X := by rfl
  have hK₀ : 0 ≤ prefixTwistMassScale := by
    unfold prefixTwistMassScale
    positivity
  have hC₁ : 0 ≤ selectedPTWSourceIntegralConstant :=
    selectedVonMangoldtPTW_sourceIntegralConstant_nonneg_local
  have hlogpos : 0 < Real.log (X : ℝ) := by linarith [hlog2]
  have hlogPow : (Real.log (X : ℝ)) ^ (-2 * a) ≤ 1 := by
    have hExp : (-2 * a : ℝ) = -(2 * a) := by ring
    rw [hExp, Real.rpow_neg hlogpos.le]
    have hlarge : 1 ≤ (Real.log (X : ℝ)) ^ (2 * a) :=
      Real.one_le_rpow (by linarith [hlog2]) (by positivity)
    exact inv_le_one_of_one_le₀ hlarge
  have hprefix : (H : ℝ) * (Real.log fd.X) ^ (-2 * a) ≤ fd.H := by
    rw [hfdX, hfdH]
    exact hcutoff
  have hIntegral : ∀ U ∈ Set.Icc (fd.X / fd.H)
      ((fd.X / fd.H) * selectedMobiusPTWTransferW fd.X a ^ 4),
      (∫ t in Set.Icc (-U) U,
        ‖fullFrequencyMellinPolynomial fd t‖ ∂volume) ≤
        selectedPTWSourceIntegralConstant * Real.sqrt fd.X *
          (Real.log fd.X) ^ selectedMobiusPTWSourceIntegralExponent a := by
    intro U hU
    have hUlocal : U ∈ Set.Icc ((X : ℝ) / (m : ℝ))
        (((X : ℝ) / (m : ℝ)) *
          selectedMobiusPTWTransferW (X : ℝ) a ^ 4) := by
      simpa [hfdX, hfdH] using hU
    obtain ⟨_hmpos', _hmleX', hU0, hUsource, hfreq⟩ :=
      selectedMobiusPTWLocalPrefixWindowFacts
        ha heta0 heta hXlocal hHlower hHupper hcutoff hmHreal
        hTlower hTupper hUlocal
    have hUsource' : U ≤ (X : ℝ) ^ (3 / 8 - 2 * (eta / 4)) := by
      have heps : eta / 2 = 2 * (eta / 4) := by ring
      simpa [heps] using hUsource
    obtain ⟨_W, _hWdata, _hiI, _hiAlpha, _hScaleLo,
      _hScaleHi, _hTagged, _hrawIntegral, hbound⟩ :=
      selectedVonMangoldtPTW_fullFrequencyIccIntegral_le_from_OAISource
        (X := (X : ℝ)) (U := U) (a := a) (eps := eta / 4) (T := T)
        (H := (m : ℝ)) (d := d) (Q := Q) (q := q)
        D ν hν haMUF hXMUF (by positivity) (by nlinarith [heta])
        hXlog hU0 hUsource' hmpos hmleX hd hQ hdQ hqlog r hrchar
        hfreq hXsave hThird
    have hresidue : (d : ℤ) * (r : ℤ) = (b : ℤ) := by
      exact_mod_cast hdb
    simpa [fd, residue, hresidue,
      selectedVonMangoldtPTWFullFrequencyResidueData,
      fullFrequencyMellinData, hfdX] using hbound
  have hmean := selectedMobiusPTWAbsoluteTransfer_of_uniformSourceIntegral
    fd (a := a) (eta := eta) (H := (H : ℝ))
    (K₀ := prefixTwistMassScale) (C₁ := selectedPTWSourceIntegralConstant)
    ha heta0 hXgrowth hHlower hprefix hh0 hK hK₀ hC₁ hIntegral
  have hcoeff : ∀ n : ℕ, fd.a n =
      selectedVonMangoldtPTWLongPrefixWeight ν T (n : ℤ) *
        (if Int.ModEq (q : ℤ) (n : ℤ) (b : ℤ) then 1 else 0) := by
    intro n
    change selectedVonMangoldtPTWResiduePrefixCoefficient ν q residue T n = _
    simp only [selectedVonMangoldtPTWResiduePrefixCoefficient,
      selectedVonMangoldtPTWResiduePrefixWeight,
      selectedVonMangoldtPTWLongPrefixWeight, residue, Int.cast_natCast]
    ring
  have hprefixNorm := residuePrefixSum_norm_le_of_fullFrequencyMean
    fd X m q b (selectedVonMangoldtPTWLongPrefixWeight ν T)
    (by exact_mod_cast hmpos) (by exact hfdX) (by exact hfdH) hcoeff hmean
  calc
    ‖residuePrefixSum X m q b
        (selectedVonMangoldtPTWLongPrefixWeight ν T)‖ ≤
      (m : ℝ) *
        (selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
          prefixTwistMassScale selectedPTWSourceIntegralConstant *
          (Real.log (X : ℝ)) ^ (-a)) := hprefixNorm
    _ = (m : ℝ) * selectedMobiusPTWLongPrefixConstant a
          polynomialKernelM1 prefixTwistMassScale
          selectedPTWSourceIntegralConstant *
          (Real.log (X : ℝ)) ^ (-a) := by ring

set_option maxHeartbeats 8000000 in
/-- Exact canonical raw-component type-II envelope from the selected λ
source integral, its actual long-prefix transfer, and the approved
short/long residue-prefix split. The canonical tag-II alignment supplies
the same outer tagged data used by the source theorem. -/
theorem selectedVonMangoldtPTWCanonicalTagIIEnvelopeBound_of_OAISource
    {X : ℕ} {a eta : ℝ}
    (C : SelectedVonMangoldtPTWCanonicalTaggedDecomposition (X : ℝ))
    (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (heta0 : 0 < eta) (heta : eta < 3 / 16)
    (hX : selectedVonMangoldtPTWLocalEnvelopeThreshold a eta
      (show 2 ≤ a from by
        have h2nat : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
        have h2 : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast h2nat
        exact h2.trans ha) ≤ (X : ℝ)) :
    selectedVonMangoldtCanonicalTagIIEnvelopeBound X a eta
      (selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
        prefixTwistMassScale selectedPTWSourceIntegralConstant) C := by
  classical
  have h2nat : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
  have h2 : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast h2nat
  have haMUF : 2 ≤ a := h2.trans ha
  have hXlocal : selectedMobiusPTWLocalPrefixWindowThreshold a eta ≤
      (X : ℝ) := (le_max_right _ _).trans hX
  have hXbase : selectedMobiusPTWFinalSourceOAISourceThreshold a eta haMUF ≤
      (X : ℝ) := (le_max_left _ _).trans hX
  have hgrowth : selectedMobiusPTWTransferGrowthThreshold a eta ≤ (X : ℝ) := by
    have hfinal : selectedMobiusPTWFinalSourceThreshold a eta ≤ (X : ℝ) := by
      unfold selectedMobiusPTWFinalSourceOAISourceThreshold at hXbase
      exact (le_max_left _ _).trans hXbase
    have hwindow : selectedMobiusPTWSourceWindowThreshold a eta ≤ (X : ℝ) :=
      (le_max_left _ _).trans hfinal
    exact (le_max_left _ _).trans hwindow
  have hgrowthFacts := selectedMobiusPTWTransferGrowth_of_threshold ha heta0 hgrowth
  have hlog2 : 2 ≤ Real.log (X : ℝ) := hgrowthFacts.1
  have hXpos : 0 < (X : ℝ) := by linarith [hgrowthFacts.2.1]
  have hXone : 1 ≤ (X : ℝ) := by linarith [hgrowthFacts.2.1]
  have hlogone : 1 ≤ Real.log (X : ℝ) := by linarith
  have hQ : 1 ≤ (Real.log (X : ℝ)) ^ a :=
    Real.one_le_rpow hlogone (by
      have h2a : 2 ≤ a := haMUF
      linarith)
  have hBeta : (prefixTwistBeta : ℝ) < a := by
    have hBetaNat : selectedMobiusPTWComponentExponent + 2 ≤
        selectedMobiusPTWThreshold :=
      le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hBetaReal : (selectedMobiusPTWComponentExponent : ℝ) + 2 ≤ a := by
      have hBetaThreshold :
          (selectedMobiusPTWComponentExponent : ℝ) + 2 ≤
            (selectedMobiusPTWThreshold : ℝ) := by exact_mod_cast hBetaNat
      linarith [hBetaThreshold.trans ha]
    have hBetaEq : (prefixTwistBeta : ℝ) =
        (selectedMobiusPTWComponentExponent : ℝ) := rfl
    rw [hBetaEq]
    linarith
  have hXprefix : prefixTwistRangeThreshold a eta ≤ (X : ℝ) := by
    have hsource : selectedMobiusPTWSourceWindowThreshold a eta ≤ (X : ℝ) :=
      (le_max_left _ _).trans hXlocal
    have hgrowth' : selectedMobiusPTWTransferGrowthThreshold a eta ≤ (X : ℝ) :=
      (le_max_left _ _).trans hsource
    exact (le_max_left _ _).trans hgrowth'
  have hLongC : 1 ≤ selectedMobiusPTWLongPrefixConstant a
      polynomialKernelM1 prefixTwistMassScale selectedPTWSourceIntegralConstant :=
    le_max_left _ _
  intro i hi htag H hHlower hHupper T hTlower hTupper
  have hThird0 := C.designationTagIIAlignment i hi htag
  have hThird :
      largeTypeIIDyadicComponentData (dyadicMobiusCutoff (X : ℝ))
        (dyadicBinomialCoefficient (C.label i).1)
        (decompositionDelta (X : ℝ))
        (selectedVonMangoldtPTWRawDyadicComponent (C.label i))
        (vonMangoldtLabelFactors (C.label i))
        (selectedVonMangoldtPTWTaggedComponentOfOuter C.outer (C.label i)
          (C.label_mem i hi)).exponents ∧
      ∀ j, (selectedVonMangoldtPTWTaggedComponentOfOuter C.outer
        (C.label i) (C.label_mem i hi)).exponents j < (3 / 8 : ℝ) := by
    simpa [selectedVonMangoldtPTWTaggedComponentOfOuter] using hThird0
  have hHpos : 0 < (H : ℝ) := by
    have hpow : 0 < (X : ℝ) ^ ((5 / 8 : ℝ) + eta) :=
      Real.rpow_pos_of_pos hXpos _
    exact lt_of_lt_of_le hpow hHlower
  have hHleXreal : (H : ℝ) ≤ (X : ℝ) := by
    have hexp : (1 - eta : ℝ) ≤ 1 := by linarith
    have hpow : (X : ℝ) ^ (1 - eta) ≤ (X : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hXone hexp
    simpa only [Real.rpow_one] using hHupper.trans hpow
  have hHX : H ≤ X := by exact_mod_cast hHleXreal
  let w : ℤ → ℂ := selectedVonMangoldtPTWLongPrefixWeight (C.label i) T
  have hEnvelope : residuePrefixEnvelope X H w ((Real.log (X : ℝ)) ^ a) ≤
      selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
        prefixTwistMassScale selectedPTWSourceIntegralConstant *
          ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) := by
    have hB : 0 ≤ (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by
      exact mul_nonneg (Nat.cast_nonneg H)
        (Real.rpow_nonneg
          (by linarith [hlog2] : 0 ≤ Real.log (X : ℝ)) _)
    apply residuePrefixEnvelope_le_of_short_long X H w hQ hB hLongC
    · intro q b m hq hqlog hb hm hsmall
      have hshort := vonMangoldtSelectedPTWShortPrefix
        hBeta heta0 hXprefix hHlower hHX hsmall (C.label i)
        (C.label_mem i hi) T q b
      have hshortW : ‖residuePrefixSum X m q b
          (selectedVonMangoldtPTWLongPrefixWeight (C.label i) T)‖ ≤
            (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by
        change ‖residuePrefixSum X m q b
          (fun n : ℤ =>
            complexPositiveIntegerZeroExtension
                (selectedVonMangoldtPTWRawDyadicComponent (C.label i)) n *
              archimedeanTwist T (n : ℝ))‖ ≤
          (H : ℝ) * (Real.log (X : ℝ)) ^ (-a)
        exact hshort
      simpa [w] using hshortW
    · intro q b m hq hqlog hb hm hlong
      have hlongLocal := selectedVonMangoldtPTW_localPrefixSum_norm_le_of_OAISource
        (X := X) (H := H) (m := m) (q := q) (b := b)
        C.outer (C.label i) (C.label_mem i hi) ha heta0 heta hX
        hHlower hHupper hTlower hTupper (by omega) hqlog hlong hm
        hThird
      have hlongFactor : 0 ≤
          selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
            prefixTwistMassScale selectedPTWSourceIntegralConstant *
            (Real.log (X : ℝ)) ^ (-a) := by
        exact mul_nonneg (by linarith [hLongC])
          (Real.rpow_nonneg
            (by linarith [hlog2] : 0 ≤ Real.log (X : ℝ)) _)
      have hmcast : (m : ℝ) ≤ (H : ℝ) := by exact_mod_cast hm
      calc
        ‖residuePrefixSum X m q b w‖ ≤
            (m : ℝ) * selectedMobiusPTWLongPrefixConstant a
              polynomialKernelM1 prefixTwistMassScale
              selectedPTWSourceIntegralConstant *
                (Real.log (X : ℝ)) ^ (-a) := by
                  simpa [w] using hlongLocal
        _ = (m : ℝ) *
            (selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
              prefixTwistMassScale selectedPTWSourceIntegralConstant *
              (Real.log (X : ℝ)) ^ (-a)) := by ring
        _ ≤ (H : ℝ) *
            (selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
              prefixTwistMassScale selectedPTWSourceIntegralConstant *
              (Real.log (X : ℝ)) ^ (-a)) :=
          mul_le_mul_of_nonneg_right hmcast hlongFactor
        _ = selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
            prefixTwistMassScale selectedPTWSourceIntegralConstant *
              ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) := by ring
  have hEnvelopeFinal : residuePrefixEnvelope X H w ((Real.log (X : ℝ)) ^ a) ≤
        selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
          prefixTwistMassScale selectedPTWSourceIntegralConstant *
            (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by
    calc
      _ ≤ selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
            prefixTwistMassScale selectedPTWSourceIntegralConstant *
              ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) := hEnvelope
      _ = selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
            prefixTwistMassScale selectedPTWSourceIntegralConstant *
              (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by ring
  change residuePrefixEnvelope X H
      (fun n : ℤ =>
        complexPositiveIntegerZeroExtension
            (selectedVonMangoldtPTWRawDyadicComponent (C.label i)) n *
          archimedeanTwist T (n : ℝ))
      ((Real.log (X : ℝ)) ^ a) ≤
    selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
      prefixTwistMassScale selectedPTWSourceIntegralConstant *
        (H : ℝ) * (Real.log (X : ℝ)) ^ (-a)
  exact hEnvelopeFinal

/-- The exact eventual canonical tag-II raw-component envelope needed by
`PolynomialShortIntervalAllXPTWSelection`. -/
theorem selectedVonMangoldtPTWEventualTagIIEnvelopeBound_of_OAISource
    {X₀ a eta : ℝ}
    (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (heta0 : 0 < eta) (heta : eta < 3 / 16)
    (hX₀ : selectedVonMangoldtPTWLocalEnvelopeThreshold a eta
      (show 2 ≤ a from by
        have h2nat : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
        have h2 : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast h2nat
        exact h2.trans ha) ≤ X₀) :
    selectedVonMangoldtPTWEventualTagIIEnvelopeBound X₀ a eta
      (selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
        prefixTwistMassScale selectedPTWSourceIntegralConstant) := by
  intro X hXlarge hX₀X
  exact selectedVonMangoldtPTWCanonicalTagIIEnvelopeBound_of_OAISource
    (selectedVonMangoldtPTWCanonicalForNat X hXlarge) ha heta0 heta
    (hX₀.trans hX₀X)

#print axioms selectedVonMangoldtPTW_localPrefixSum_norm_le_of_OAISource
#print axioms selectedVonMangoldtPTWCanonicalTagIIEnvelopeBound_of_OAISource
#print axioms selectedVonMangoldtPTWEventualTagIIEnvelopeBound_of_OAISource

end FractionalPrimes.Literature.DirichletMean

end
