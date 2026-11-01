module
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalAllXPTWSelection
public import FractionalPrimes.Literature.Polynomial.SelectedPTWShortPrefix
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWFullFrequencyIntegral
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTransferAssembly
public import FractionalPrimes.Literature.Polynomial.SelectedPTWLocalPrefixWindowFacts
public import FractionalPrimes.Literature.Polynomial.SelectedPTWResidueReduction
public import FractionalPrimes.Literature.Polynomial.ResiduePrefixMellinMean
public import FractionalPrimes.Literature.Polynomial.ResiduePrefixShortLong
public import FractionalPrimes.Literature.Polynomial.SelectedPTWSourceRangeFacts
public import Mathlib.Tactic
@[expose] public section

/-! Derive the eventual canonical Möbius type-II envelope required by the
all-X PTW selector. The source prefix split is at `H (log X)^(-2a)`. For
long prefixes, the Fourier window is rescaled to the local prefix length,
while the source frequency lower bound remains at the macro scale `H`. -/

noncomputable section

open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
open scoped BigOperators

namespace FractionalPrimes.Literature.DirichletMean

/-- The exact source threshold for the eventual canonical μ tag-II
envelope. It combines the short-prefix range, the source full-frequency
integral threshold, and the macro-to-local frequency-window threshold. -/
noncomputable def selectedMobiusPTWEventualCanonicalEnvelopeThreshold
    (a eta : ℝ) (ha2 : 2 ≤ a) : ℝ :=
  max (prefixTwistRangeThreshold a eta)
    (max (selectedMobiusPTWFinalSourceOAISourceThreshold a eta ha2)
      (selectedMobiusPTWLocalPrefixWindowThreshold a eta))

/-- The unchanged long-prefix constant from the checked source transfer. -/
noncomputable def selectedMobiusPTWEventualCanonicalEnvelopeConstant
    (a : ℝ) : ℝ :=
  selectedMobiusPTWLongPrefixConstant a
    FractionalPrimes.polynomialKernelM1 prefixTwistMassScale
    selectedPTWSourceIntegralConstant

private theorem selectedMobiusPTWSourceIntegralConstant_nonneg_local :
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
  have hJ : 0 ≤ J 20 := by
    unfold J K
    positivity
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
  have hABC : 0 ≤ ((2 : ℝ) ^ (37 + selectedMobiusPTWLogExponent) *
      (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
      (2 * decompositionC) ^ (3 / 2 : ℝ)) :=
    mul_nonneg hAB hthird
  have hABCD : 0 ≤ (((2 : ℝ) ^ (37 + selectedMobiusPTWLogExponent) *
      (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
      (2 * decompositionC) ^ (3 / 2 : ℝ)) *
      (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3) :=
    mul_nonneg hABC hfourth
  have hABCDE : 0 ≤ (((2 : ℝ) ^ (37 + selectedMobiusPTWLogExponent) *
      (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
      (2 * decompositionC) ^ (3 / 2 : ℝ)) *
      (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3) *
      divisorSubpowerConstant 60 (1 / 1000 : ℝ) :=
    mul_nonneg hABCD (hdiv 60)
  unfold selectedPTWSourceIntegralConstant
  exact mul_nonneg hABCDE (hdiv 3)

private theorem selectedMobiusPTW_componentK_log_majorant_local
    {X : ℝ} (hX : (2 : ℝ) ^ 120 ≤ X)
    (hlog : 2 ≤ Real.log X) :
    selectedComponentK X ≤
      prefixTwistMassScale * (Real.log X) ^ (prefixTwistBeta : ℝ) := by
  have hXpos : 0 < X := by positivity
  have hlog0 : 0 ≤ Real.log X := by linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogZ : Real.log ((2 : ℝ) ^ 22 * X) =
      22 * Real.log 2 + Real.log X := by
    rw [Real.log_mul (by positivity) hXpos.ne', Real.log_pow]
    push_cast
    ring
  have hZbound :
      1 + Real.log ((2 : ℝ) ^ 22 * X) ≤
        (2 + 22 * Real.log 2) * Real.log X := by
    rw [hlogZ]
    nlinarith
  have hZ0 : 0 ≤ 1 + Real.log ((2 : ℝ) ^ 22 * X) := by
    rw [hlogZ]
    positivity
  have hpow := pow_le_pow_left₀ hZ0 hZbound prefixTwistBeta
  calc
    selectedComponentK X =
        (2 : ℝ) ^ 90 *
          (1 + Real.log ((2 : ℝ) ^ 22 * X)) ^ prefixTwistBeta := rfl
    _ ≤ (2 : ℝ) ^ 90 *
          ((2 + 22 * Real.log 2) * Real.log X) ^ prefixTwistBeta :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = prefixTwistMassScale * (Real.log X) ^ (prefixTwistBeta : ℝ) := by
      rw [mul_pow]
      simp [prefixTwistMassScale, Real.rpow_natCast]
      ring

private theorem selectedMobiusPTW_log42_absorption
    {X a eta : ℝ} (ha : 0 < a) (heta : 0 < eta)
    (hX : selectedMobiusPTWLocalPrefixWindowThreshold a eta ≤ X)
    (hXone : 1 ≤ X) :
    (Real.log X) ^ (42 * a) ≤ X ^ (eta / 2) := by
  have hthreshold : Real.exp ((2 / (eta / 2)) *
      Real.log (logAbsorptionM (eta / 2) (42 * a))) ≤ X := by
    exact (le_max_right _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hlargeExp : Real.exp ((2 / (eta / 2)) *
      Real.log (logAbsorptionM (eta / 2) (42 * a))) ≤
        Real.exp (Real.log X) := by
    simpa only [Real.exp_log hXpos] using hthreshold
  have hlarge : (2 / (eta / 2)) *
      Real.log (logAbsorptionM (eta / 2) (42 * a)) ≤ Real.log X :=
    Real.exp_le_exp.mp hlargeExp
  have hbound := log_absorption_bound
    (a := eta / 2) (b := 42 * a) (K := 1) (X := X)
    (by positivity) (by positivity) (by norm_num) hXone
    (by simpa only [one_mul] using hlarge)
  simpa only [one_mul] using hbound

theorem selectedMobiusPTWEventualCanonicalTagIIEnvelopeBound_from_OAISource
    {a eta : ℝ}
    (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (heta0 : 0 < eta) (heta : eta < 3 / 16) :
    selectedMobiusPTWEventualTagIIEnvelopeBound
      (selectedMobiusPTWEventualCanonicalEnvelopeThreshold a eta
        (by
          have hsource := selectedPTWSourceThreshold_facts ha
          exact hsource.2.1))
      a eta (selectedMobiusPTWEventualCanonicalEnvelopeConstant a) := by
  have hsourceA := selectedPTWSourceThreshold_facts ha
  have ha2 : 2 ≤ a := hsourceA.2.1
  have hbeta : (prefixTwistBeta : ℝ) < a := hsourceA.2.2
  have hconst : 1 ≤ selectedMobiusPTWEventualCanonicalEnvelopeConstant a := by
    dsimp [selectedMobiusPTWEventualCanonicalEnvelopeConstant,
      selectedMobiusPTWLongPrefixConstant]
    exact le_max_left _ _
  intro X hXlarge hXthreshold
  let C := selectedMobiusPTWCanonicalForNat X hXlarge
  have hXprefix : prefixTwistRangeThreshold a eta ≤ (X : ℝ) :=
    (le_max_left _ _).trans hXthreshold
  have htail : max (selectedMobiusPTWFinalSourceOAISourceThreshold a eta ha2)
      (selectedMobiusPTWLocalPrefixWindowThreshold a eta) ≤ (X : ℝ) :=
    (le_max_right _ _).trans hXthreshold
  have hXsource : selectedMobiusPTWFinalSourceOAISourceThreshold a eta ha2 ≤
      (X : ℝ) := (le_max_left _ _).trans htail
  have hXlocal : selectedMobiusPTWLocalPrefixWindowThreshold a eta ≤
      (X : ℝ) := (le_max_right _ _).trans htail
  have hXMUF : selectedMobiusPTWFirstFactorMUFThreshold
      FractionalPrimes.Literature.Reciprocal.mobiusUniformity_of_OAISource
      a ha2 ≤ (X : ℝ) := by
    unfold selectedMobiusPTWFinalSourceOAISourceThreshold at hXsource
    exact (le_max_right _ _).trans hXsource
  have hXfinal : selectedMobiusPTWFinalSourceThreshold a eta ≤ (X : ℝ) := by
    unfold selectedMobiusPTWFinalSourceOAISourceThreshold at hXsource
    exact (le_max_left _ _).trans hXsource
  have hXwindow : selectedMobiusPTWSourceWindowThreshold a eta ≤ (X : ℝ) :=
    (le_max_left _ _).trans hXfinal
  have hXgrowth : selectedMobiusPTWTransferGrowthThreshold a eta ≤ (X : ℝ) :=
    (le_max_left _ _).trans hXwindow
  have hXtail : max (Real.exp (selectedMobiusPTWCellLogThreshold a (eta / 4)))
      (selectedMobiusPTWUncappedSavingThreshold a (eta / 4)) ≤ (X : ℝ) :=
    (le_max_right _ _).trans hXfinal
  have hXcell : Real.exp (selectedMobiusPTWCellLogThreshold a (eta / 4)) ≤
      (X : ℝ) := (le_max_left _ _).trans hXtail
  have hXsave : selectedMobiusPTWUncappedSavingThreshold a (eta / 4) ≤
      (X : ℝ) := (le_max_right _ _).trans hXtail
  have hXnat : 3 ≤ X := by
    have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact_mod_cast h3.trans hXlarge
  have hXone : 1 ≤ (X : ℝ) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ 120 := by norm_num
    exact h1.trans hXlarge
  have hXpos : 0 < (X : ℝ) := by linarith
  have hlog : 1 ≤ Real.log (X : ℝ) := log_nat_three_ge_one hXnat
  have hlog2 : 2 ≤ Real.log (X : ℝ) :=
    (selectedMobiusPTWTransferGrowth_of_threshold ha heta0 hXgrowth).1
  have ha0 : 0 ≤ a := by linarith [ha2]
  have hQ : 1 ≤ (Real.log (X : ℝ)) ^ a := Real.one_le_rpow hlog ha0
  have hlog42 := selectedMobiusPTW_log42_absorption
    (X := (X : ℝ)) (a := a) (eta := eta) (by linarith [ha2]) heta0
    hXlocal hXone
  have hexp2 : 2 * a ≤ 42 * a := by nlinarith [ha2]
  have hlog2a : (Real.log (X : ℝ)) ^ (2 * a) ≤
      (X : ℝ) ^ (eta / 2) :=
    (Real.rpow_le_rpow_of_exponent_le hlog hexp2).trans hlog42
  have hbound : selectedMobiusCanonicalTagIIEnvelopeBound X a eta
      (selectedMobiusPTWEventualCanonicalEnvelopeConstant a) C := by
    intro i hi htag H hHlower hHupper T hTlower hTupper
    have hB : 0 ≤ (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) :=
      mul_nonneg (Nat.cast_nonneg H) (Real.rpow_nonneg (by linarith) _)
    let ν := C.label i
    have hν : ν ∈ mobiusDyadicLabels (X : ℝ)
        (dyadicMobiusCutoff (X : ℝ)) := C.label_mem i hi
    have hthird := C.designationTagIIAlignment i hi htag
    have hHposR : 0 < (H : ℝ) := by
      have hpower : 0 < (X : ℝ) ^ ((5 / 8 : ℝ) + eta) :=
        Real.rpow_pos_of_pos hXpos _
      exact lt_of_lt_of_le hpower hHlower
    have hHX : H ≤ X := shortLength_le_X_of_upper hXnat heta0 hHupper
    have hHpos : 0 < H := by exact_mod_cast hHposR
    let w : ℤ → ℂ := fun n =>
      complexPositiveIntegerZeroExtension
          (selectedMobiusPTWRawDyadicComponent ν) n *
        archimedeanTwist T (n : ℝ)
    let cutoff : ℝ := (H : ℝ) * (Real.log (X : ℝ)) ^ (-2 * a)
    have hcutoffPos : 0 < cutoff := by
      dsimp [cutoff]
      exact mul_pos hHposR (Real.rpow_pos_of_pos (by linarith) _)
    have hshort : ∀ q b m : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log (X : ℝ)) ^ a →
        b < q → m ≤ H → (m : ℝ) ≤ cutoff →
          ‖residuePrefixSum X m q b w‖ ≤ (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by
      intro q b m hq hqQ hb hm hmsmall
      exact mobiusSelectedPTWShortPrefix hbeta heta0 hXprefix hHlower hHX
        (by simpa [cutoff] using hmsmall) ν hν T q b
    have hlong : ∀ q b m : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log (X : ℝ)) ^ a →
        b < q → m ≤ H → cutoff ≤ (m : ℝ) →
          ‖residuePrefixSum X m q b w‖ ≤
            selectedMobiusPTWEventualCanonicalEnvelopeConstant a *
              ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) := by
      intro q b m hq hqQ hb hm hmLong
      have hmH : (m : ℝ) ≤ (H : ℝ) := by exact_mod_cast hm
      have hmposR : 0 < (m : ℝ) := lt_of_lt_of_le hcutoffPos hmLong
      have hMnat : 0 < m := by exact_mod_cast hmposR
      have hHXreal : (H : ℝ) ≤ (X : ℝ) := by exact_mod_cast hHX
      have hmleX : (m : ℝ) ≤ (X : ℝ) := hmH.trans hHXreal
      have hqpos : 0 < q := by omega
      have hqlog : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ a := hqQ
      rcases selectedPTWResidueReduction q b hqpos with
        ⟨d, Q, r, hd, hQred, hqfactor, hdb, _hdq, _hcopNat, hcopInt⟩
      have hresInt : (d : ℤ) * (r : ℤ) = (b : ℤ) := by
        exact_mod_cast hdb
      let fd := selectedMobiusPTWFullFrequencyResidueData hXlarge hν
        (m : ℝ) hmposR hmleX q ((d : ℤ) * (r : ℤ)) T
      have hIntegral : ∀ U ∈ Set.Icc ((X : ℝ) / (m : ℝ))
          (((X : ℝ) / (m : ℝ)) * selectedMobiusPTWTransferW (X : ℝ) a ^ 4),
          (∫ t in Set.Icc (-U) U,
            ‖fullFrequencyMellinPolynomial fd t‖ ∂MeasureTheory.volume) ≤
            selectedPTWSourceIntegralConstant * Real.sqrt (X : ℝ) *
              (Real.log (X : ℝ)) ^ selectedMobiusPTWSourceIntegralExponent a := by
        intro U hU
        have hlocal := selectedMobiusPTWLocalPrefixWindowFacts
          ha heta0 heta hXlocal hHlower hHupper
          (by simpa [cutoff] using hmLong) hmH hTlower hTupper hU
        rcases hlocal with ⟨_hmpos, _hmleX, hU0, hUsource, hfreq⟩
        have hUsource' : U ≤ (X : ℝ) ^ (3 / 8 - 2 * (eta / 4)) := by
          have heq : (3 / 8 : ℝ) - 2 * (eta / 4) = 3 / 8 - eta / 2 := by ring
          rw [heq]
          exact hUsource
        have hpoint := selectedMobiusPTW_fullFrequencyIccIntegral_le_from_OAISource
          (X := (X : ℝ)) (U := U) (a := a) (eps := eta / 4)
          (T := T) (H := (m : ℝ)) (d := d) (Q := Q) (q := q)
          C.outer ν hν ha2 hXMUF (by positivity) (by nlinarith [heta])
          hXcell hU0 hUsource' hmposR hmleX hd hQred hqfactor hqlog
          (r : ℤ) hcopInt hfreq hXsave hthird
        rcases hpoint with
          ⟨W, _hWdata, _hiI, _hiAlpha, _hScaleLo, _hScaleHi,
            _hTagged, _hgroupIntegral, hsourceIntegral⟩
        exact hsourceIntegral
      have hlogXpos : 0 < Real.log (X : ℝ) := by linarith [hlog]
      have hfdX : fd.X = (X : ℝ) := by rfl
      have hfdH : fd.H = (m : ℝ) := by rfl
      have hh0 : fd.h0 = selectedComponentH0 fd.X := by rfl
      have hK : fd.K ≤ prefixTwistMassScale * (Real.log fd.X) ^
          (selectedMobiusPTWComponentExponent : ℝ) := by
        rw [hfdX]
        change selectedComponentK (X : ℝ) ≤ prefixTwistMassScale *
          (Real.log (X : ℝ)) ^ (selectedMobiusPTWComponentExponent : ℝ)
        simpa [selectedMobiusPTWComponentExponent, prefixTwistBeta] using
          selectedMobiusPTW_componentK_log_majorant_local hXlarge hlog2
      have hK0 : 0 ≤ prefixTwistMassScale := by
        unfold prefixTwistMassScale
        positivity
      have hC1 : 0 ≤ selectedPTWSourceIntegralConstant :=
        selectedMobiusPTWSourceIntegralConstant_nonneg_local
      have hprefix : (H : ℝ) * (Real.log fd.X) ^ (-2 * a) ≤ fd.H := by
        rw [hfdX, hfdH]
        simpa [cutoff] using hmLong
      have hmean := selectedMobiusPTWAbsoluteTransfer_of_uniformSourceIntegral
        (d := fd) (a := a) (eta := eta) (H := (H : ℝ))
        ha heta0 (by simpa [hfdX] using hXgrowth) hHlower hprefix hh0 hK
        hK0 hC1 (by
          intro U hU
          have hUlocal : U ∈ Set.Icc ((X : ℝ) / (m : ℝ))
              (((X : ℝ) / (m : ℝ)) * selectedMobiusPTWTransferW (X : ℝ) a ^ 4) := by
            simpa only [hfdX, hfdH] using hU
          exact hIntegral U hUlocal)
      have hmeanBound : ‖fullFrequencyMellinMean fd‖ ≤
          selectedMobiusPTWEventualCanonicalEnvelopeConstant a *
            (Real.log (X : ℝ)) ^ (-a) := by
        simpa [selectedMobiusPTWEventualCanonicalEnvelopeConstant, hfdX] using hmean
      have hcoeff : ∀ n : ℕ,
          fd.a n = w (n : ℤ) *
            (if Int.ModEq (q : ℤ) (n : ℤ) (b : ℤ) then 1 else 0) := by
        intro n
        change selectedMobiusPTWResiduePrefixCoefficient ν q
            ((d : ℤ) * (r : ℤ)) T n = _
        by_cases hres : Int.ModEq (q : ℤ) (n : ℤ) (b : ℤ)
        · simp [selectedMobiusPTWResiduePrefixCoefficient,
            selectedMobiusPTWResiduePrefixWeight, w, hres, hresInt]
        · simp [selectedMobiusPTWResiduePrefixCoefficient,
            selectedMobiusPTWResiduePrefixWeight, w, hres, hresInt]
      have hprefixMean := residuePrefixSum_norm_le_of_fullFrequencyMean
        fd X m q b w hMnat hfdX hfdH hcoeff hmeanBound
      have hfactor : 0 ≤ selectedMobiusPTWEventualCanonicalEnvelopeConstant a *
          (Real.log (X : ℝ)) ^ (-a) :=
        mul_nonneg (le_trans (by norm_num) hconst)
          (Real.rpow_nonneg (by linarith) _)
      calc
        ‖residuePrefixSum X m q b w‖ ≤
            (m : ℝ) * (selectedMobiusPTWEventualCanonicalEnvelopeConstant a *
              (Real.log (X : ℝ)) ^ (-a)) := hprefixMean
        _ ≤ (H : ℝ) * (selectedMobiusPTWEventualCanonicalEnvelopeConstant a *
              (Real.log (X : ℝ)) ^ (-a)) :=
          mul_le_mul_of_nonneg_right hmH hfactor
        _ = selectedMobiusPTWEventualCanonicalEnvelopeConstant a *
              ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) := by ring
    have henv := residuePrefixEnvelope_le_of_short_long X H w hQ hB hconst
      hshort hlong
    calc
      _ ≤ selectedMobiusPTWEventualCanonicalEnvelopeConstant a *
          ((H : ℝ) * (Real.log (X : ℝ)) ^ (-a)) := henv
      _ = selectedMobiusPTWEventualCanonicalEnvelopeConstant a *
          (H : ℝ) * (Real.log (X : ℝ)) ^ (-a) := by ring
  exact hbound

#print axioms selectedMobiusPTWEventualCanonicalTagIIEnvelopeBound_from_OAISource

end FractionalPrimes.Literature.DirichletMean

end
