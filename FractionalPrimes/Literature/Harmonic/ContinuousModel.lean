module

public import FractionalPrimes.ArithmeticBasicsCore
public import FractionalPrimes.ArithmeticBasics
public import FractionalPrimes.Literature.Multiplier.Data
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The continuous fractional-power model (`ha:model`)

This module fixes a smooth cutoff with the exact plateau and support
requirements in the approved blueprint, defines its inverse Fourier transform,
and realizes the continuous model as a torus `L²` Fourier multiplier on finite
integer sequences.  The symbol is represented on the half-open fundamental
interval `[-1/2,1/2)`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace FractionalPrimes.Literature.Harmonic

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : IsProbabilityMeasure FractionalPrimes.Literature.Multiplier.torusHaar :=
  FractionalPrimes.Literature.Multiplier.torusHaar_isProbability

open FractionalPrimes.Literature.Multiplier

/-- The fixed cutoff used in the continuous model.  It is the already checked
even bump with plateau radius `1/8` and support radius `3/16`, which satisfies
the approved requirements `1/10` and `1/4` with room to spare. -/
def continuousModelEta : ℝ → ℝ := ψ

theorem continuousModelEta_even (x : ℝ) :
    continuousModelEta (-x) = continuousModelEta x := ψ_even x

theorem continuousModelEta_nonneg (x : ℝ) : 0 ≤ continuousModelEta x :=
  ψ_nonneg x

theorem continuousModelEta_le_one (x : ℝ) : continuousModelEta x ≤ 1 :=
  ψ_le_one x

theorem continuousModelEta_eq_one_of_abs_le_tenth (x : ℝ)
    (hx : |x| ≤ 1 / 10) : continuousModelEta x = 1 := by
  apply ψ_eq_one_of_abs_le
  have h : (1 / 10 : ℝ) ≤ 1 / 8 := by norm_num
  exact hx.trans h

theorem continuousModelEta_tsupport_subset :
    tsupport continuousModelEta ⊆ Set.Ioo (-(1 / 4 : ℝ)) (1 / 4) := by
  exact tsupport_ψ_subset

theorem continuousModelEta_contDiff :
    ContDiff ℝ (∞ : ℕ∞ω) continuousModelEta := ψ_contDiff

theorem continuousModelEta_hasCompactSupport : HasCompactSupport continuousModelEta :=
  ψ_hasCompactSupport

private theorem continuousModelEta_eq_zero_of_abs_ge_quarter {x : ℝ}
    (hx : 1 / 4 ≤ |x|) : continuousModelEta x = 0 := by
  have hnot : x ∉ tsupport continuousModelEta := by
    intro hts
    have hts' := continuousModelEta_tsupport_subset hts
    have habs : |x| < (1 / 4 : ℝ) := by
      rw [abs_lt]
      exact ⟨by linarith [hts'.1], hts'.2⟩
    exact (not_lt_of_ge hx) habs
  have hzero : ¬ continuousModelEta x ≠ 0 := by
    intro hne
    have hsupp : x ∈ Function.support continuousModelEta := by
      change continuousModelEta x ≠ 0
      exact hne
    exact hnot (subset_tsupport continuousModelEta hsupp)
  exact not_ne_iff.mp hzero

/-- The cutoff as a real-valued Schwartz function. -/
noncomputable def continuousModelEtaSchwartz : SchwartzMap ℝ ℝ :=
  continuousModelEta_hasCompactSupport.toSchwartzMap continuousModelEta_contDiff

/-- The same cutoff embedded in complex-valued Schwartz space. -/
noncomputable def continuousModelEtaComplexSchwartz : SchwartzMap ℝ ℂ :=
  continuousModelEtaSchwartz.postcompCLM Complex.ofRealCLM

@[simp]
theorem continuousModelEtaComplexSchwartz_apply (x : ℝ) :
    continuousModelEtaComplexSchwartz x = (continuousModelEta x : ℂ) := rfl

/-- The inverse real-line Fourier transform `ψ = 𝓕⁻¹ η` in Mathlib's
Fourier-transform convention. -/
noncomputable def continuousModelPsiSchwartz : SchwartzMap ℝ ℂ :=
  𝓕⁻ continuousModelEtaComplexSchwartz

/-- Pointwise representative of the inverse transform. -/
def continuousModelPsi : ℝ → ℂ := continuousModelPsiSchwartz

theorem continuousModelPsi_eq_inverseFourier (x : ℝ) :
    continuousModelPsi x = (𝓕⁻ continuousModelEtaComplexSchwartz) x := rfl

/-- The continuous fractional-power symbol
`v_N(ξ) = ∫₀¹ e(-ξ N^c u^c) du`. -/
def continuousModelV (c N ξ : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..1, unitFrequencyPhase (-ξ * N ^ c * u ^ c)

/-- The exact sign bridge to the already checked normalized continuous model:
the paper's negative phase at frequency `ξ` is the existing positive-phase
model at frequency `-ξ`. -/
theorem continuousModelV_eq_continuousFractionalModel_neg {c N ξ : ℝ}
    (hN : 0 < N) :
    continuousModelV c N ξ = continuousFractionalModel c N (-ξ) := by
  rw [continuousModelV, continuousFractionalModel_eq_unitIntegral hN]

/-- At zero frequency the continuous symbol has the prescribed value one. -/
theorem continuousModelV_zero {c N : ℝ} (hN : 0 < N) :
    continuousModelV c N 0 = 1 := by
  rw [continuousModelV_eq_continuousFractionalModel_neg hN, neg_zero,
    continuousFractionalModel_zero hN]

/-- The blueprint minimum, with its stated value `1` at zero frequency. -/
def continuousModelMin (c N ξ : ℝ) : ℝ :=
  if ξ = 0 then 1 else min 1 ((|ξ| * N ^ c) ^ (-c⁻¹))

/-- An explicit finite choice for the constant `K_c` in `ha:symbol`. -/
def continuousModelK (c : ℝ) : ℝ := 1 + (Real.pi * c)⁻¹

theorem continuousModelV_norm_le_min {c N ξ : ℝ} (hc : 1 < c) (hN : 0 < N) :
    ‖continuousModelV c N ξ‖ ≤ continuousModelK c * continuousModelMin c N ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    rw [continuousModelV_zero hN]
    simp [continuousModelMin, continuousModelK]
    positivity
  · rw [continuousModelV_eq_continuousFractionalModel_neg hN]
    have hbase := continuousFractionalModel_norm_le_min hc hN (neg_ne_zero.mpr hξ)
    simpa [continuousModelMin, continuousModelK, hξ, abs_neg] using hbase

/-- The exact small-frequency estimate in `ha:symbol`, including arbitrary
`N>0` and the factor `N^c`. -/
theorem continuousModelV_close_to_one {c N ξ : ℝ} (hc : 1 < c) (hN : 0 < N) :
    ‖continuousModelV c N ξ - 1‖ ≤
      (2 * Real.pi / (c + 1)) * N ^ c * |ξ| := by
  rw [continuousModelV_eq_continuousFractionalModel_neg hN]
  calc
    ‖continuousFractionalModel c N (-ξ) - 1‖ ≤
        (2 * Real.pi / (c + 1)) * |-ξ| * N ^ c :=
      continuousFractionalModel_close_to_one hc hN
    _ = (2 * Real.pi / (c + 1)) * N ^ c * |ξ| := by
      rw [abs_neg]
      ring

theorem continuousModelV_continuous (c N : ℝ) (hc : 1 < c) :
    Continuous (continuousModelV c N) := by
  have hc0 : 0 ≤ c := by linarith
  have hpow : Continuous (fun u : ℝ => u ^ c) := Real.continuous_rpow_const hc0
  have hphase : Continuous (fun t : ℝ => unitFrequencyPhase t) := by
    unfold unitFrequencyPhase
    fun_prop
  have harg : Continuous (fun p : ℝ × ℝ => -p.1 * N ^ c * p.2 ^ c) := by
    exact continuous_fst.neg.mul continuous_const |>.mul (hpow.comp continuous_snd)
  have hIntegrand : Continuous (fun p : ℝ × ℝ =>
      unitFrequencyPhase (-p.1 * N ^ c * p.2 ^ c)) := hphase.comp harg
  change Continuous (fun ξ : ℝ =>
    ∫ u in (0 : ℝ)..1, unitFrequencyPhase (-ξ * N ^ c * u ^ c))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun ξ u => unitFrequencyPhase (-ξ * N ^ c * u ^ c)) hIntegrand 0 1

theorem norm_continuousModelV_le_one (c N ξ : ℝ) :
    ‖continuousModelV c N ξ‖ ≤ 1 := by
  change ‖∫ u in (0 : ℝ)..1, unitFrequencyPhase (-ξ * N ^ c * u ^ c)‖ ≤ 1
  calc
    _ ≤ ∫ u in (0 : ℝ)..1, ‖unitFrequencyPhase (-ξ * N ^ c * u ^ c)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = 1 := by simp [norm_unitFrequencyPhase]

/-- The real-line lift of the continuous-model torus symbol. -/
def continuousModelSymbolLift (c N ξ : ℝ) : ℂ :=
  (continuousModelEta ξ : ℂ) * continuousModelV c N ξ

theorem continuousModelSymbolLift_continuous (c N : ℝ) (hc : 1 < c) :
    Continuous (continuousModelSymbolLift c N) := by
  have hη : Continuous (fun x : ℝ => (continuousModelEta x : ℂ)) :=
    Complex.continuous_ofReal.comp continuousModelEta_contDiff.continuous
  exact hη.mul (continuousModelV_continuous c N hc)

theorem continuousModelSymbolLift_norm_le_one (c N ξ : ℝ) :
    ‖continuousModelSymbolLift c N ξ‖ ≤ 1 := by
  have hη : ‖(continuousModelEta ξ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (continuousModelEta_nonneg ξ)]
    exact continuousModelEta_le_one ξ
  calc
    ‖continuousModelSymbolLift c N ξ‖ =
        ‖(continuousModelEta ξ : ℂ)‖ * ‖continuousModelV c N ξ‖ := norm_mul _ _
    _ ≤ ‖(continuousModelEta ξ : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_continuousModelV_le_one c N ξ) (norm_nonneg _)
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_right hη (by norm_num)
    _ = 1 := by norm_num

theorem continuousModelSymbolLift_eq_zero_of_abs_ge_quarter (c N ξ : ℝ)
    (hξ : 1 / 4 ≤ |ξ|) : continuousModelSymbolLift c N ξ = 0 := by
  simp [continuousModelSymbolLift,
    continuousModelEta_eq_zero_of_abs_ge_quarter hξ]

/-- The continuous-model symbol on `AddCircle 1`, using the approved
representatives in `[-1/2,1/2)`. -/
def continuousModelTorusSymbol (c N : ℝ) : Torus → ℂ :=
  AddCircle.liftIco (1 : ℝ) (-(1 / 2 : ℝ)) (continuousModelSymbolLift c N)

theorem continuousModelTorusSymbol_apply_coe (c N : ℝ)
    {ξ : ℝ} (hξ : ξ ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2)) :
    continuousModelTorusSymbol c N (ξ : Torus) =
      (continuousModelEta ξ : ℂ) * continuousModelV c N ξ := by
  have hξ' : ξ ∈ Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    simpa only [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num] using hξ
  rw [continuousModelTorusSymbol, AddCircle.liftIco_coe_apply
    (p := (1 : ℝ)) (a := -(1 / 2 : ℝ)) hξ']
  rfl

theorem continuousModelTorusSymbol_continuous (c N : ℝ) (hc : 1 < c) :
    Continuous (continuousModelTorusSymbol c N) := by
  have hleft : continuousModelEta (-(1 / 2 : ℝ)) = 0 := by
    apply continuousModelEta_eq_zero_of_abs_ge_quarter
    norm_num
  have hright : continuousModelEta (1 / 2 : ℝ) = 0 := by
    apply continuousModelEta_eq_zero_of_abs_ge_quarter
    norm_num
  have hleft' : continuousModelEta (-2⁻¹ : ℝ) = 0 := by
    simpa only [show (-2⁻¹ : ℝ) = -(1 / 2 : ℝ) by norm_num] using hleft
  have hright' : continuousModelEta (2⁻¹ : ℝ) = 0 := by
    simpa only [show (2⁻¹ : ℝ) = 1 / 2 by norm_num] using hright
  have hend : continuousModelSymbolLift c N (-(1 / 2 : ℝ)) =
      continuousModelSymbolLift c N (-(1 / 2 : ℝ) + 1) := by
    rw [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num]
    simp [continuousModelSymbolLift, hleft', hright']
  unfold continuousModelTorusSymbol
  exact AddCircle.liftIco_continuous (p := (1 : ℝ)) (a := -(1 / 2 : ℝ))
    hend (continuousModelSymbolLift_continuous c N hc).continuousOn

theorem continuousModelTorusSymbol_norm_le_one (c N : ℝ) (ξ : Torus) :
    ‖continuousModelTorusSymbol c N ξ‖ ≤ 1 := by
  let y : Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
    AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) ξ
  have hy : (y : Torus) = ξ := AddCircle.coe_equivIco
  have hy' : (y : ℝ) ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2) := by
    simpa only [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num] using y.property
  have hvalue : continuousModelTorusSymbol c N ξ =
      continuousModelSymbolLift c N y := by
    rw [← hy]
    simpa [continuousModelSymbolLift] using continuousModelTorusSymbol_apply_coe c N hy'
  rw [hvalue]
  exact continuousModelSymbolLift_norm_le_one c N y

/-- The continuous-model symbol as an `L∞` multiplier on normalized circle
Haar measure. -/
def continuousModelSymbolLp (c N : ℝ) (hc : 1 < c) : Lp ℂ ⊤ torusHaar := by
  have hmeas : AEStronglyMeasurable (continuousModelTorusSymbol c N) torusHaar :=
    (continuousModelTorusSymbol_continuous c N hc).measurable.aestronglyMeasurable
  have hbound : ∀ᵐ ξ ∂torusHaar,
      ‖continuousModelTorusSymbol c N ξ‖ ≤ 1 :=
    Filter.Eventually.of_forall (continuousModelTorusSymbol_norm_le_one c N)
  exact (MemLp.of_bound hmeas 1 hbound).toLp (continuousModelTorusSymbol c N)

/-- The continuous averaging operator `C_N` on finitely supported sequences,
defined by conjugating multiplication by `η(ξ)v_N(ξ)` with the unitary circle
Fourier transform. -/
def continuousModelC (c : ℝ) (hc : 1 < c) (N : ℝ) (_hN : 0 < N)
    (f : ℤ →₀ ℂ) : lp (fun _ : ℤ => ℂ) 2 :=
  sequenceToCircleL2.symm
    (continuousModelSymbolLp c N hc • sequenceToCircleL2 (finiteSequenceL2 f))

theorem sequenceToCircleL2_continuousModelC (c : ℝ) (hc : 1 < c)
    (N : ℝ) (_hN : 0 < N) (f : ℤ →₀ ℂ) :
    sequenceToCircleL2 (continuousModelC c hc N _hN f) =
      continuousModelSymbolLp c N hc • sequenceToCircleL2 (finiteSequenceL2 f) := by
  simp [continuousModelC]

end

end FractionalPrimes.Literature.Harmonic
