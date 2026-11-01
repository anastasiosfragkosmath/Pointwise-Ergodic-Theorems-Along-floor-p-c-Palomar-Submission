module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedVonMangoldtPTWFullFrequencyIntegral
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFinalThreshold
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTaggedLiveAggregateContinuous
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTransferAssembly
public import FractionalPrimes.Literature.Polynomial.ResiduePrefixMellinMean
public import FractionalPrimes.Literature.Polynomial.SelectedPTWResidueReduction
public import FractionalPrimes.Literature.Twisted.PrefixTwistRange
public import Mathlib.Tactic
@[expose] public section

/-! The selected von Mangoldt full-frequency estimate transfers to the actual
integer residue prefix by the shared absolute-transfer theorem and the exact
mean-recovery identity. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- The actual selected von Mangoldt coefficient used in the integer prefix,
including its exact Archimedean twist. The residue indicator is kept in the
prefix sum itself. -/
def selectedVonMangoldtPTWLongPrefixWeight
    {X : ℝ} (ν : VonMangoldtDyadicLabel X) (T : ℝ) (n : ℤ) : ℂ :=
  complexPositiveIntegerZeroExtension
      (selectedVonMangoldtPTWRawDyadicComponent ν) n *
    archimedeanTwist T (n : ℝ)

private theorem selectedVonMangoldtPTW_componentK_le_prefixMassScale
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

set_option maxHeartbeats 8000000 in
/-- The exact selected von Mangoldt long-prefix bound. It uses the source
short-interval/full-frequency theorem on the entire absolute-transfer window,
then recovers the unnormalized integer prefix with the shared residue-prefix
mean identity. The residue reduction is the exact gcd/quotient factorization
for the given natural residue `b`. -/
theorem selectedVonMangoldtPTW_residuePrefixSum_norm_le_of_OAISource
    {X eta a T : ℝ} {N H q b : ℕ}
    (hXnat : (N : ℝ) = X)
    (D : SelectedVonMangoldtPTWTaggedOuterDecomposition X)
    (ν : VonMangoldtDyadicLabel X)
    (hν : ν ∈ vonMangoldtDyadicLabels X (dyadicMobiusCutoff X))
    (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (heta0 : 0 < eta) (heta : eta < 3 / 16)
    (hX : selectedMobiusPTWFinalSourceOAISourceThreshold a eta
      (show 2 ≤ a from by
        have h2nat : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
        have h2 : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast h2nat
        exact h2.trans ha) ≤ X)
    (hHlower : X ^ (5 / 8 + eta) ≤ (H : ℝ))
    (hHupper : (H : ℝ) ≤ X ^ (1 - eta))
    (hTlower : (X / (H : ℝ)) * (Real.log X) ^ (50 * a) ≤ |T|)
    (hTupper : |T| ≤ X ^ a)
    (hq : 0 < q)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ a)
    (hThird :
      largeTypeIIDyadicComponentData (dyadicMobiusCutoff X)
        (dyadicBinomialCoefficient ν.1) (decompositionDelta X)
        (selectedVonMangoldtPTWRawDyadicComponent ν)
        (vonMangoldtLabelFactors ν)
        (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents ∧
      ∀ j, (selectedVonMangoldtPTWTaggedComponentOfOuter D ν hν).exponents j <
        (3 / 8 : ℝ)) :
    ‖residuePrefixSum N H q b
        (selectedVonMangoldtPTWLongPrefixWeight ν T)‖ ≤
      (H : ℝ) * selectedMobiusPTWLongPrefixConstant a
        polynomialKernelM1 prefixTwistMassScale selectedPTWSourceIntegralConstant *
          (Real.log X) ^ (-a) := by
  classical
  have h2nat : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
  have haMUF : 2 ≤ a := by
    have h2 : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast h2nat
    exact h2.trans ha
  obtain ⟨m, Q, r, hm, hQ, hmQ, hmb, _hmle, _hcop, hrchar⟩ :=
    selectedPTWResidueReduction q b hq
  have hXgrowth : selectedMobiusPTWTransferGrowthThreshold a eta ≤ X := by
    have hfinal : selectedMobiusPTWFinalSourceThreshold a eta ≤ X := by
      have hcombined := (le_max_left
        (selectedMobiusPTWFinalSourceThreshold a eta)
        (selectedMobiusPTWFirstFactorMUFThreshold
          FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
          a haMUF)).trans hX
      exact hcombined
    have hwindow : selectedMobiusPTWSourceWindowThreshold a eta ≤ X :=
      (le_max_left _ _).trans hfinal
    exact (le_max_left _ _).trans hwindow
  have hgrowth := selectedMobiusPTWTransferGrowth_of_threshold ha heta0 hXgrowth
  have hXpos : 0 < X := by linarith [hgrowth.2.1]
  have hXone : 1 ≤ X := by linarith
  have hHpos : 0 < (H : ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hHlower
  have hHleX : (H : ℝ) ≤ X := by
    apply le_trans hHupper
    calc
      X ^ (1 - eta) ≤ X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone (by linarith : (1 - eta : ℝ) ≤ 1)
      _ = X := by rw [Real.rpow_one]
  have hfacts := selectedMobiusPTWFinalSourceOAISourceThreshold_facts
    ha heta0 heta haMUF hX hHpos hHlower hHupper hTlower hTupper
    (U := X / (H : ℝ)) (by
      constructor
      · rfl
      · have hW1 : 1 ≤ selectedMobiusPTWTransferW X a := by
          have hlog1 : 1 ≤ Real.log X := by linarith [hgrowth.1]
          have hexp : 0 ≤ 10 * a := by linarith [haMUF]
          have hpow := Real.one_le_rpow hlog1 hexp
          simpa [selectedMobiusPTWTransferW] using hpow
        have hW4 : 1 ≤ selectedMobiusPTWTransferW X a ^ 4 := one_le_pow₀ hW1
        have hratio : 0 ≤ X / (H : ℝ) := div_nonneg hXpos.le hHpos.le
        calc
          X / (H : ℝ) = (X / (H : ℝ)) * 1 := by ring
          _ ≤ (X / (H : ℝ)) * selectedMobiusPTWTransferW X a ^ 4 :=
            mul_le_mul_of_nonneg_left hW4 hratio)
  rcases hfacts with ⟨hMUFthreshold,
    ⟨_hXlarge, hXcell, hXsave, heps0, heps, hU0, hUsource, hfreq⟩⟩
  have hXlarge : (2 : ℝ) ^ 120 ≤ X := by
    have hbase : (2 : ℝ) ^ 120 ≤
        selectedMobiusPTWFirstFactorMUFThreshold
          FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
          a haMUF := by
      unfold selectedMobiusPTWFirstFactorMUFThreshold
      exact le_max_left _ _
    exact hbase.trans hMUFthreshold
  let residue : ℤ := (b : ℤ)
  let fd := selectedVonMangoldtPTWFullFrequencyResidueData
    hXlarge hν (H : ℝ) hHpos hHleX q residue T
  have hfdX : fd.X = X := by rfl
  have hfdH : fd.H = (H : ℝ) := by rfl
  have hK : fd.K ≤ prefixTwistMassScale *
      (Real.log fd.X) ^ (selectedMobiusPTWComponentExponent : ℝ) := by
    change selectedComponentK X ≤ prefixTwistMassScale *
      (Real.log X) ^ (selectedMobiusPTWComponentExponent : ℝ)
    exact selectedVonMangoldtPTW_componentK_le_prefixMassScale hXlarge hgrowth.1
  have hh0 : fd.h0 = selectedComponentH0 fd.X := by rfl
  have hK₀ : 0 ≤ prefixTwistMassScale := by
    unfold prefixTwistMassScale
    positivity
  have hC₁ : 0 ≤ selectedPTWSourceIntegralConstant := by
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
    have hfirst : 0 ≤ (2 : ℝ) ^ (37 + selectedMobiusPTWLogExponent) := by positivity
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
  have hlogpos : 0 < Real.log X := by linarith [hgrowth.1]
  have hlogPow : (Real.log X) ^ (-2 * a) ≤ 1 := by
    have hExp : (-2 * a : ℝ) = -(2 * a) := by ring
    rw [hExp, Real.rpow_neg hlogpos.le]
    have hlarge : 1 ≤ (Real.log X) ^ (2 * a) :=
      Real.one_le_rpow (by linarith [hgrowth.1]) (by positivity)
    exact inv_le_one_of_one_le₀ hlarge
  have hprefix : (H : ℝ) * (Real.log fd.X) ^ (-2 * a) ≤ fd.H := by
    rw [hfdX, hfdH]
    calc
      (H : ℝ) * (Real.log X) ^ (-2 * a) ≤ (H : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlogPow (by positivity)
      _ = (H : ℝ) := by ring
  have hIntegral : ∀ U ∈ Set.Icc (fd.X / fd.H)
      ((fd.X / fd.H) * selectedMobiusPTWTransferW fd.X a ^ 4),
      (∫ t in Set.Icc (-U) U,
        ‖fullFrequencyMellinPolynomial fd t‖ ∂volume) ≤
        selectedPTWSourceIntegralConstant * Real.sqrt fd.X *
          (Real.log fd.X) ^ selectedMobiusPTWSourceIntegralExponent a := by
    intro U hU
    have hU' : U ∈ Set.Icc (X / (H : ℝ))
        ((X / (H : ℝ)) * selectedMobiusPTWTransferW X a ^ 4) := by
      simpa [hfdX, hfdH] using hU
    have hfactsU := selectedMobiusPTWFinalSourceOAISourceThreshold_facts
      ha heta0 heta haMUF hX hHpos hHlower hHupper hTlower hTupper hU'
    rcases hfactsU with ⟨_hMUFthresholdU,
      ⟨_hXlargeU, _hXcellU, _hXsaveU, _heps0U, _hepsU,
        hU0U, hUsourceU, hfreqU⟩⟩
    obtain ⟨_W, _hWdata, _hiI, _hiAlpha, _hScaleLo, _hScaleHi,
      _hTagged, _hrawIntegral, hbound⟩ :=
      selectedVonMangoldtPTW_fullFrequencyIccIntegral_le_from_OAISource
        D ν hν haMUF hMUFthreshold heps0 heps hXcell hU0U hUsourceU
        hHpos hHleX hm hQ hmQ hqlog (r : ℤ) hrchar hfreqU hXsave hThird
    have hresidue : (m : ℤ) * (r : ℤ) = (b : ℤ) := by exact_mod_cast hmb
    simpa [fd, residue, hresidue, selectedVonMangoldtPTWFullFrequencyResidueData,
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
    fd N H q b (selectedVonMangoldtPTWLongPrefixWeight ν T)
    (by exact_mod_cast hHpos)
    (by rw [hfdX]; exact hXnat.symm) (by exact hfdH) hcoeff hmean
  calc
    ‖residuePrefixSum N H q b
        (selectedVonMangoldtPTWLongPrefixWeight ν T)‖ ≤
      (H : ℝ) *
        (selectedMobiusPTWLongPrefixConstant a polynomialKernelM1
          prefixTwistMassScale selectedPTWSourceIntegralConstant *
          (Real.log X) ^ (-a)) := hprefixNorm
    _ = (H : ℝ) * selectedMobiusPTWLongPrefixConstant a
          polynomialKernelM1 prefixTwistMassScale
          selectedPTWSourceIntegralConstant * (Real.log X) ^ (-a) := by ring

#print axioms selectedVonMangoldtPTW_componentK_le_prefixMassScale
#print axioms selectedVonMangoldtPTW_residuePrefixSum_norm_le_of_OAISource

end FractionalPrimes.Literature.DirichletMean

end
