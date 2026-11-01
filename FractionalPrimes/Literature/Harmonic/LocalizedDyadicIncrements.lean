module

public import FractionalPrimes.Literature.Harmonic.InterpolatedAverageLipschitz
public import FractionalPrimes.Literature.Harmonic.DyadicSpectralError
public import FractionalPrimes.Literature.Harmonic.FrequencyResolutionLp
public import FractionalPrimes.DiscreteLpBridge
public import FractionalPrimes.Core
public import Mathlib.MeasureTheory.Group.Measure

set_option maxHeartbeats 600000

/-!
# Localized dyadic increments (`ha:localized`)

This module starts with the time-smoothness half of the localized increment
estimate.  The frequency-localized decay is proved below once its Fourier
action bridge is available.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.Harmonic

open FractionalPrimes.Literature.Multiplier

noncomputable section

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
local instance : IsProbabilityMeasure torusHaar := torusHaar_isProbability

/-! The explicit presentation is local to this module: the imported system
definition is intentionally opaque at module boundaries, while this local
copy lets the sequence/counting-measure Fourier bridge reduce definitionally. -/
abbrev localizedIntegerShiftSystem : InvertibleSystem ℤ := {
  μ := Measure.count
  sigmaFinite := inferInstance
  T := MeasurableEquiv.addLeft (-1)
  preserves := by
    simpa [sub_eq_add_neg, add_comm] using
      (MeasureTheory.measurePreserving_add_left (Measure.count : Measure ℤ) (-1)) }

@[simp] theorem localizedIntegerShiftSystem_iterate_apply (m n : ℤ) :
    localizedIntegerShiftSystem.iterate m n = n - m := by
  simp [InvertibleSystem.iterate, localizedIntegerShiftSystem, sub_eq_add_neg]
  abel

theorem localizedIntegerShiftMeasure_eq_count :
    localizedIntegerShiftSystem.μ = (Measure.count : Measure ℤ) := rfl

/-- The bounded circle function given by one Fourier character. -/
noncomputable def localizedFourierCharacterLp (a : ℤ) : Lp ℂ ⊤ torusHaar := by
  let χ : Torus → ℂ := fourier (T := (1 : ℝ)) a
  have hmeas : AEStronglyMeasurable χ torusHaar :=
    (map_continuous (fourier (T := (1 : ℝ)) a)).measurable.aestronglyMeasurable
  have hbound : ∀ᵐ ξ ∂torusHaar, ‖χ ξ‖ ≤ 1 := by
    filter_upwards with ξ
    have hχ : ‖fourier (T := (1 : ℝ)) a ξ‖ = 1 := by
      rw [fourier_apply, Circle.norm_coe]
    simpa [χ] using hχ.le
  exact (MemLp.of_bound hmeas 1 hbound).toLp χ

theorem localizedFourierCharacterLp_coeFn (a : ℤ) :
    (localizedFourierCharacterLp a : Torus → ℂ) =ᵐ[torusHaar]
      fourier (T := (1 : ℝ)) a := by
  unfold localizedFourierCharacterLp
  exact MemLp.coeFn_toLp _

/-- Multiplication by a circle character shifts the coefficients of the
inverse sequence Fourier transform by the matching integer. -/
theorem sequenceToCircleL2_symm_fourierCharacter_mul
    (g : Lp ℂ 2 torusHaar) (a k : ℤ) :
    sequenceToCircleL2.symm (localizedFourierCharacterLp a • g) k =
      sequenceToCircleL2.symm g (k + a) := by
  have hprod : ((localizedFourierCharacterLp a • g : Lp ℂ 2 torusHaar) :
      Torus → ℂ) =ᵐ[torusHaar]
      fun ξ => g ξ * fourier (T := (1 : ℝ)) a ξ := by
    filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      (localizedFourierCharacterLp a) g,
      localizedFourierCharacterLp_coeFn a] with ξ hmul hχ
    have hmul' : ((localizedFourierCharacterLp a • g : Lp ℂ 2 torusHaar) :
        Torus → ℂ) ξ =
        (localizedFourierCharacterLp a : Torus → ℂ) ξ * g ξ := by
      simpa only [Pi.smul_apply', smul_eq_mul] using hmul
    rw [hmul', hχ]
    ring
  calc
    sequenceToCircleL2.symm (localizedFourierCharacterLp a • g) k =
        fourierCoeff (fun ξ : Torus => g ξ * fourier (T := (1 : ℝ)) a ξ) (-k) := by
          rw [sequenceToCircleL2_symm_apply]
          calc
            (@fourierBasis (1 : ℝ) ⟨by norm_num⟩).repr
                (localizedFourierCharacterLp a • g) (-k) =
                fourierCoeff (localizedFourierCharacterLp a • g) (-k) :=
                  fourierBasis_repr (T := (1 : ℝ))
                    (localizedFourierCharacterLp a • g) (-k)
            _ = fourierCoeff (fun ξ : Torus => g ξ * fourier (T := (1 : ℝ)) a ξ)
                  (-k) := congrFun (fourierCoeff_congr_ae hprod) (-k)
    _ = fourierCoeff g (-k - a) := by
          exact fourierCoeff_mul_fourier_shift g a (-k)
    _ = sequenceToCircleL2.symm g (k + a) := by
          rw [sequenceToCircleL2_symm_apply]
          rw [fourierBasis_repr (T := (1 : ℝ)) g (-(k + a))]
          congr 1
          omega

/-- Translation on sequence `ℓ²`, routed through counting-measure `L²`. -/
noncomputable def localizedSequenceTranslate (y : ℤ)
    (f : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  countLpToLp (Lp.compMeasurePreserving
    (MeasurableEquiv.addLeft (-y))
    (measurePreserving_add_left (Measure.count : Measure ℤ) (-y))
    (lpToCountLp f))

theorem localizedSequenceTranslate_apply (y : ℤ)
    (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    localizedSequenceTranslate y f x = f (x - y) := by
  change (Lp.compMeasurePreserving (MeasurableEquiv.addLeft (-y))
      (measurePreserving_add_left (Measure.count : Measure ℤ) (-y))
      (lpToCountLp f) : ℤ → ℂ) x = _
  have hcomp := Lp.coeFn_compMeasurePreserving (lpToCountLp f)
    (measurePreserving_add_left (Measure.count : Measure ℤ) (-y))
  have hx := ae_count_int_iff_forall.mp hcomp x
  calc
    (Lp.compMeasurePreserving (MeasurableEquiv.addLeft (-y))
        (measurePreserving_add_left (Measure.count : Measure ℤ) (-y))
        (lpToCountLp f) : ℤ → ℂ) x =
        (lpToCountLp f : ℤ → ℂ) (MeasurableEquiv.addLeft (-y) x) := hx
    _ = f (MeasurableEquiv.addLeft (-y) x) := lpToCountLp_apply f _
    _ = f (x - y) := by
      apply congrArg f
      simp [MeasurableEquiv.addLeft, sub_eq_add_neg, add_comm]

theorem sequenceToCircleL2_localizedSequenceTranslate (y : ℤ)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    sequenceToCircleL2 (localizedSequenceTranslate y f) =
      localizedFourierCharacterLp (-y) • sequenceToCircleL2 f := by
  apply sequenceToCircleL2.symm.injective
  apply lp.ext
  funext x
  calc
    sequenceToCircleL2.symm (sequenceToCircleL2
        (localizedSequenceTranslate y f)) x =
        localizedSequenceTranslate y f x := by
          rw [sequenceToCircleL2.symm_apply_apply]
    _ = f (x - y) := localizedSequenceTranslate_apply y f x
    _ = sequenceToCircleL2.symm (sequenceToCircleL2 f) (x - y) := by
          rw [sequenceToCircleL2.symm_apply_apply]
    _ = sequenceToCircleL2.symm
          (localizedFourierCharacterLp (-y) • sequenceToCircleL2 f) x := by
          rw [sequenceToCircleL2_symm_fourierCharacter_mul]
          congr 1

/-- The source integer-time average transferred to the sequence model of
`ℓ²(ℤ)`. -/
noncomputable def localizedIntegerUnweightedAverageL2 (c : ℝ) (N : Scale)
    (f : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  countLpToLp (unweightedAverageLpCLM (p := (2 : ℝ≥0∞))
    localizedIntegerShiftSystem c N (lpToCountLp f))

theorem localizedIntegerUnweightedAverageL2_apply (c : ℝ) (N : Scale)
    (f : lp (fun _ : ℤ => ℂ) 2) (x : ℤ) :
    localizedIntegerUnweightedAverageL2 c N f x =
      (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
        f (x - floorPower c n) := by
  have havg := unweightedAverageLpCLM_apply_ae (p := (2 : ℝ≥0∞))
    localizedIntegerShiftSystem c N (lpToCountLp f)
  have hx := ae_count_int_iff_forall.mp havg x
  rw [localizedIntegerUnweightedAverageL2, countLpToLp_apply]
  calc
    (unweightedAverageLpCLM (p := (2 : ℝ≥0∞))
        localizedIntegerShiftSystem c N (lpToCountLp f) : ℤ → ℂ) x =
        unweightedAverage localizedIntegerShiftSystem c
          (lpToCountLp f : ℤ → ℂ) N x := hx
    _ = ((N.1 : ℂ)⁻¹ • ∑ n ∈ Finset.Icc 1 N.1,
          localizedIntegerShiftSystem.shift (floorPower c n)
            (lpToCountLp f : ℤ → ℂ)) x := by
        rw [unweightedAverage_eq_smul_sum_shift_floorPower]
    _ = (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
        f (x - floorPower c n) := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
          InvertibleSystem.shift, localizedIntegerShiftSystem_iterate_apply]
        simp [lpToCountLp_apply]

theorem localizedIntegerUnweightedAverageL2_eq_translation_sum
    (c : ℝ) (N : Scale) (f : lp (fun _ : ℤ => ℂ) 2) :
    localizedIntegerUnweightedAverageL2 c N f =
      (N.1 : ℂ)⁻¹ • ∑ n ∈ Finset.Icc 1 N.1,
        localizedSequenceTranslate (floorPower c n) f := by
  apply lp.ext
  funext x
  rw [localizedIntegerUnweightedAverageL2_apply]
  change (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
      f (x - floorPower c n) =
    ((N.1 : ℂ)⁻¹ • ∑ n ∈ Finset.Icc 1 N.1,
      localizedSequenceTranslate (floorPower c n) f :
        lp (fun _ : ℤ => ℂ) 2) x
  rw [lp.coeFn_smul, lp.coeFn_sum]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact (localizedSequenceTranslate_apply (floorPower c n) f x).symm

/-- The finite Fourier symbol of the unweighted floor-power average. -/
noncomputable def localizedIntegerUnweightedAverageSymbolLp (c : ℝ) (N : Scale) :
    Lp ℂ ⊤ torusHaar :=
  (N.1 : ℂ)⁻¹ • ∑ n ∈ Finset.Icc 1 N.1,
    localizedFourierCharacterLp (-(floorPower c n))

theorem localizedIntegerUnweightedAverageSymbolLp_coeFn (c : ℝ) (N : Scale) :
    (localizedIntegerUnweightedAverageSymbolLp c N : Torus → ℂ) =ᵐ[torusHaar]
      fun ξ => (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
        fourier (T := (1 : ℝ)) (-(floorPower c n)) ξ := by
  rw [localizedIntegerUnweightedAverageSymbolLp]
  have hsmul := Lp.coeFn_smul (N.1 : ℂ)⁻¹
    (∑ n ∈ Finset.Icc 1 N.1,
      localizedFourierCharacterLp (-(floorPower c n)))
  have hsum := Lp.coeFn_finsetSum (Finset.Icc 1 N.1)
    (fun n => localizedFourierCharacterLp (-(floorPower c n)))
  have hchars : ∀ᵐ ξ ∂torusHaar, ∀ n : ℕ,
      (localizedFourierCharacterLp (-(floorPower c n)) : Torus → ℂ) ξ =
        fourier (T := (1 : ℝ)) (-(floorPower c n)) ξ :=
    ae_all_iff.2 (fun n => localizedFourierCharacterLp_coeFn (-(floorPower c n)))
  filter_upwards [hsmul, hsum, hchars] with ξ hsmul hsum hchars
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  rw [hsmul, hsum]
  simp only [Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact hchars n

theorem sequenceToCircleL2_localizedIntegerUnweightedAverage
    (c : ℝ) (N : Scale) (f : lp (fun _ : ℤ => ℂ) 2) :
    sequenceToCircleL2 (localizedIntegerUnweightedAverageL2 c N f) =
      localizedIntegerUnweightedAverageSymbolLp c N • sequenceToCircleL2 f := by
  have hmul : localizedIntegerUnweightedAverageL2 c N f =
      frequencyProjectionTmL2FromSymbolLp
        (localizedIntegerUnweightedAverageSymbolLp c N) f := by
    apply sequenceToCircleL2.injective
    rw [localizedIntegerUnweightedAverageL2_eq_translation_sum]
    rw [localizedIntegerUnweightedAverageSymbolLp,
      frequencyProjectionTmL2FromSymbolLp_smul,
      frequencyProjectionTmL2FromSymbolLp_sum]
    simp only [map_smul, map_sum,
      sequenceToCircleL2_localizedSequenceTranslate,
      frequencyProjectionTmL2FromSymbolLp,
      sequenceToCircleL2.apply_symm_apply]
  calc
    sequenceToCircleL2 (localizedIntegerUnweightedAverageL2 c N f) =
        sequenceToCircleL2
          (frequencyProjectionTmL2FromSymbolLp
            (localizedIntegerUnweightedAverageSymbolLp c N) f) := congrArg _ hmul
    _ = localizedIntegerUnweightedAverageSymbolLp c N • sequenceToCircleL2 f := by
        simp [frequencyProjectionTmL2FromSymbolLp]

/-- The finite torus symbol of an integer-time average agrees pointwise with
the paper's `b_N` multiplier when evaluated at the canonical real
representative of a torus frequency. -/
theorem localizedIntegerAverageSymbol_eq_bN_at_representative
    (c : ℝ) (N : Scale) :
    (localizedIntegerUnweightedAverageSymbolLp c N : Torus → ℂ) =ᵐ[torusHaar]
      fun ξ => bN c (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ) N := by
  filter_upwards [localizedIntegerUnweightedAverageSymbolLp_coeFn c N]
    with ξ hξ
  let r : Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
    AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ
  have hrval : (r : ℝ) =
      (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ) := rfl
  have hcoe : (r : Torus) = ξ := AddCircle.coe_equivIoc
  have hphase (n : ℕ) :
      fourier (T := (1 : ℝ)) (-(floorPower c n)) (r : Torus) =
        unitFrequencyPhase (-((r : ℝ) * (floorPower c n : ℝ))) := by
    rw [← unitFrequencyPhase_int_mul_eq_addCircleFourier]
    congr 1
    push_cast
    ring
  calc
    (localizedIntegerUnweightedAverageSymbolLp c N : Torus → ℂ) ξ =
        (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
          fourier (T := (1 : ℝ)) (-(floorPower c n)) ξ := hξ
    _ = (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
          fourier (T := (1 : ℝ)) (-(floorPower c n)) (r : Torus) := by
            rw [← hcoe]
    _ = (N.1 : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
          unitFrequencyPhase (-((r : ℝ) * (floorPower c n : ℝ))) := by
            congr 1
            apply Finset.sum_congr rfl
            intro n hn
            exact hphase n
    _ = bN c (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ : ℝ) N := by
            simp [bN, hrval, mul_comm, mul_left_comm, mul_assoc]

/-- The elementary first-moment estimate for the normalized finite multiplier.
It uses the exact floor times in `b_N`. -/
theorem bN_sub_one_norm_le_firstMoment
    (c ξ : ℝ) (N : Scale) (hc : 1 < c) :
    ‖bN c ξ N - 1‖ ≤ 2 * Real.pi * (N.1 : ℝ) ^ c * |ξ| := by
  have hNpos : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
  have hNcomplex : (N.1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hNpos)
  have hone :
      ((N.1 : ℂ)⁻¹) *
        (∑ n ∈ Finset.Icc 1 N.1, (1 : ℂ)) = 1 := by
    simp [hNcomplex]
  have halg : bN c ξ N - 1 =
      ((N.1 : ℂ)⁻¹) *
        (∑ n ∈ Finset.Icc 1 N.1,
          (unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) - 1)) := by
    rw [bN]
    calc
      (↑N.1)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
            unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) - 1 =
          (↑N.1)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1,
            unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) -
            (↑N.1)⁻¹ * ∑ n ∈ Finset.Icc 1 N.1, (1 : ℂ) := by
              rw [hone]
      _ = (↑N.1)⁻¹ *
            ((∑ n ∈ Finset.Icc 1 N.1,
              unitFrequencyPhase (-ξ * (floorPower c n : ℝ))) -
             ∑ n ∈ Finset.Icc 1 N.1, (1 : ℂ)) := by ring
      _ = (↑N.1)⁻¹ *
            (∑ n ∈ Finset.Icc 1 N.1,
              (unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) - 1)) := by
              rw [Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.Icc 1 N.1,
      ‖unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) - 1‖ ≤
        2 * Real.pi * (N.1 : ℝ) ^ c * |ξ| := by
    intro n hn
    have hnN : (n : ℝ) ≤ (N.1 : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hfloorle : (floorPower c n : ℝ) ≤ (n : ℝ) ^ c := by
      dsimp [floorPower]
      exact_mod_cast (Int.floor_le ((n : ℝ) ^ c))
    have hcpos : 0 < c := by linarith
    have hpow : (n : ℝ) ^ c ≤ (N.1 : ℝ) ^ c := by
      apply Real.rpow_le_rpow (by positivity) hnN
      exact hcpos.le
    have hfloor_nonneg : 0 ≤ (floorPower c n : ℝ) := by
      exact_mod_cast floorPower_nonneg c n
    have hfloorabs : |(floorPower c n : ℝ)| ≤ (N.1 : ℝ) ^ c := by
      rw [abs_of_nonneg hfloor_nonneg]
      exact hfloorle.trans hpow
    have hchord := norm_one_sub_unitFrequencyPhase_neg_le
      (ξ * (floorPower c n : ℝ))
    have hreverse :
        ‖unitFrequencyPhase (-(ξ * (floorPower c n : ℝ))) - 1‖ =
          ‖1 - unitFrequencyPhase (-(ξ * (floorPower c n : ℝ)))‖ :=
      norm_sub_rev _ _
    have harg : -ξ * (floorPower c n : ℝ) =
        -(ξ * (floorPower c n : ℝ)) := by ring
    rw [harg, hreverse]
    calc
      ‖1 - unitFrequencyPhase (-(ξ * (floorPower c n : ℝ)))‖ ≤
          2 * Real.pi * |ξ * (floorPower c n : ℝ)| := hchord
      _ = 2 * Real.pi * |ξ| * |(floorPower c n : ℝ)| := by
        rw [abs_mul]
        ring
      _ ≤ 2 * Real.pi * |ξ| * (N.1 : ℝ) ^ c := by
        exact mul_le_mul_of_nonneg_left hfloorabs
          (by positivity : 0 ≤ 2 * Real.pi * |ξ|)
      _ = 2 * Real.pi * (N.1 : ℝ) ^ c * |ξ| := by ring
  have hsum : ‖∑ n ∈ Finset.Icc 1 N.1,
      (unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) - 1)‖ ≤
      (N.1 : ℝ) * (2 * Real.pi * (N.1 : ℝ) ^ c * |ξ|) := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N.1,
          ‖unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) - 1‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Icc 1 N.1,
          2 * Real.pi * (N.1 : ℝ) ^ c * |ξ| := by
        apply Finset.sum_le_sum
        intro n hn
        exact hterm n hn
      _ = _ := by simp
  rw [halg]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (N.1 : ℝ)⁻¹ *
        ‖∑ n ∈ Finset.Icc 1 N.1,
          (unitFrequencyPhase (-ξ * (floorPower c n : ℝ)) - 1)‖ ≤
      (N.1 : ℝ)⁻¹ *
        ((N.1 : ℝ) * (2 * Real.pi * (N.1 : ℝ) ^ c * |ξ|)) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNpos.le)
    _ = 2 * Real.pi * (N.1 : ℝ) ^ c * |ξ| := by
          field_simp

theorem bN_norm_le_one (c ξ : ℝ) (N : Scale) : ‖bN c ξ N‖ ≤ 1 := by
  have hNpos : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
  have hNcomplex : (N.1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hNpos)
  rw [bN, norm_mul]
  calc
    ‖(N.1 : ℂ)⁻¹‖ *
        ‖∑ n ∈ Finset.Icc 1 N.1,
          unitFrequencyPhase (-ξ * (floorPower c n : ℝ))‖ ≤
      ‖(N.1 : ℂ)⁻¹‖ *
        ∑ n ∈ Finset.Icc 1 N.1,
          ‖unitFrequencyPhase (-ξ * (floorPower c n : ℝ))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖(N.1 : ℂ)⁻¹‖ * (N.1 : ℝ) := by simp [norm_unitFrequencyPhase]
    _ = 1 := by
      rw [norm_inv, Complex.norm_natCast]
      field_simp

private theorem localizedDyadicUpperPowerIdentity
    (c : ℝ) (j k : ℤ) :
    ((2 : ℝ) ^ k) ^ c *
        Real.rpow 2 (-((((j + k : ℤ) : ℝ) - 1) * c)) =
      Real.rpow 2 ((1 - (j : ℝ)) * c) := by
  let q : ℝ := Real.rpow 2 c
  let d : ℤ := -((j + k : ℤ) - 1)
  have hexp : -((((j + k : ℤ) : ℝ) - 1) * c) = c * d := by
    dsimp [d]
    push_cast
    ring
  have hmul : Real.rpow 2 (c * d) = q ^ d := by
    calc
      Real.rpow 2 (c * (d : ℝ)) = (Real.rpow 2 c) ^ (d : ℝ) :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) c (d : ℝ)
      _ = q ^ d := by rw [Real.rpow_intCast]
  calc
    ((2 : ℝ) ^ k) ^ c *
        Real.rpow 2 (-((((j + k : ℤ) : ℝ) - 1) * c)) =
      q ^ k * Real.rpow 2 (c * d) := by
        conv_lhs => rw [← Real.rpow_zpow_comm (by norm_num : (0 : ℝ) ≤ 2) c k]
        dsimp [q]
        rw [hexp]
    _ = q ^ k * q ^ d := by rw [hmul]
    _ = q ^ (k + -((j + k : ℤ) - 1)) := by
      dsimp [q]
      rw [← zpow_add₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) c))]
    _ = q ^ (1 - j) := by congr 1 <;> omega
    _ = Real.rpow 2 ((1 - (j : ℝ)) * c) := by
      dsimp [q]
      rw [Real.rpow_zpow_comm (by norm_num : (0 : ℝ) ≤ 2) c (1 - j)]
      rw [← Real.rpow_intCast (2 : ℝ) (1 - j)]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring

private theorem localizedPositiveIntegerMultiplier_firstMoment
    {c : ℝ} (hc : 1 < c) {j k : ℤ} (hj : 0 ≤ j) (hk : 0 ≤ k)
    (N : Scale) (hNupper : (N.1 : ℝ) ≤ 3 * (2 : ℝ) ^ k)
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))
    (hs : frequencyProjectionSymbol c (j + k) ξ ≠ 0) :
    ‖bN c ξ N - 1‖ ≤ 2 * Real.pi * (3 : ℝ) ^ c * Real.rpow 2 c *
      Real.rpow 2 (-(j : ℝ)) := by
  have hcpos : 0 < c := by linarith
  have hkpow : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hNpos : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
  have hjR : 0 ≤ (j : ℝ) := by exact_mod_cast hj
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast hk
  have hsum0 : 0 ≤ j + k := add_nonneg hj hk
  by_cases hzero : j + k = 0
  · have hj0 : j = 0 := by omega
    have hk0 : k = 0 := by omega
    subst j
    subst k
    have hK : (2 : ℝ) ^ (0 : ℤ) = 1 := zpow_zero _
    have hNle : (N.1 : ℝ) ≤ 3 := by simpa [hK] using hNupper
    have hpow : (N.1 : ℝ) ^ c ≤ (3 : ℝ) ^ c :=
      Real.rpow_le_rpow hNpos.le hNle hcpos.le
    have hξabs : |ξ| ≤ 1 / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hξ.1], hξ.2⟩
    have hfirst := bN_sub_one_norm_le_firstMoment c ξ N hc
    have hbound : 2 * Real.pi * (N.1 : ℝ) ^ c * |ξ| ≤
        2 * Real.pi * (3 : ℝ) ^ c := by
      calc
        _ ≤ 2 * Real.pi * ((3 : ℝ) ^ c) * |ξ| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (by positivity)) (abs_nonneg ξ)
        _ ≤ 2 * Real.pi * (3 : ℝ) ^ c := by
          have hcoeff : 0 ≤ 2 * Real.pi * (3 : ℝ) ^ c := by positivity
          nlinarith
    have hone : 1 ≤ Real.rpow 2 c := Real.one_le_rpow (by norm_num) (by linarith)
    have hscale : 2 * Real.pi * (3 : ℝ) ^ c ≤
        2 * Real.pi * (3 : ℝ) ^ c * Real.rpow 2 c := by
      have hcoeff : 0 ≤ 2 * Real.pi * (3 : ℝ) ^ c := by positivity
      calc
        2 * Real.pi * (3 : ℝ) ^ c =
            (2 * Real.pi * (3 : ℝ) ^ c) * 1 := by ring
        _ ≤ (2 * Real.pi * (3 : ℝ) ^ c) * (2 : ℝ) ^ c :=
          mul_le_mul_of_nonneg_left hone hcoeff
    simpa [Real.rpow_zero] using (hfirst.trans hbound).trans hscale
  · have hsumpos : 1 ≤ j + k := by omega
    have hsupp := frequencyProjectionSymbol_support_positive hc hsumpos hξ hs
    have hNpow : (N.1 : ℝ) ^ c ≤ (3 * (2 : ℝ) ^ k) ^ c :=
      Real.rpow_le_rpow hNpos.le hNupper hcpos.le
    have hsplit : (3 * (2 : ℝ) ^ k) ^ c =
        (3 : ℝ) ^ c * ((2 : ℝ) ^ k) ^ c :=
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hkpow.le
    have hprod : (N.1 : ℝ) ^ c * |ξ| ≤
        ((3 : ℝ) ^ c / 2) * Real.rpow 2 ((1 - (j : ℝ)) * c) := by
      calc
        (N.1 : ℝ) ^ c * |ξ| ≤
            (3 * (2 : ℝ) ^ k) ^ c * |ξ| :=
          mul_le_mul_of_nonneg_right hNpow (abs_nonneg ξ)
        _ ≤ (3 * (2 : ℝ) ^ k) ^ c *
            ((1 / 2 : ℝ) * Real.rpow 2
              (-((((j + k : ℤ) : ℝ) - 1) * c))) :=
          mul_le_mul_of_nonneg_left hsupp.2.le
            (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 3 * (2 : ℝ) ^ k) c)
        _ = ((3 : ℝ) ^ c / 2) *
              (((2 : ℝ) ^ k) ^ c * Real.rpow 2
                (-((((j + k : ℤ) : ℝ) - 1) * c))) := by
          rw [hsplit]
          ring
        _ = ((3 : ℝ) ^ c / 2) * Real.rpow 2 ((1 - (j : ℝ)) * c) := by
          rw [localizedDyadicUpperPowerIdentity]
    have hfirst := bN_sub_one_norm_le_firstMoment c ξ N hc
    by_cases hjzero : j = 0
    · have hprod0 : (N.1 : ℝ) ^ c * |ξ| ≤
          ((3 : ℝ) ^ c / 2) * Real.rpow 2 c := by
        simpa [hjzero] using hprod
      have hbound : ‖bN c ξ N - 1‖ ≤
          2 * Real.pi * ((3 : ℝ) ^ c / 2) * Real.rpow 2 c := by
        calc
          _ ≤ 2 * Real.pi * ((N.1 : ℝ) ^ c * |ξ|) := by
            simpa [mul_assoc] using hfirst
          _ ≤ 2 * Real.pi * (((3 : ℝ) ^ c / 2) * Real.rpow 2 c) :=
            mul_le_mul_of_nonneg_left hprod0 (by positivity)
          _ = 2 * Real.pi * ((3 : ℝ) ^ c / 2) * Real.rpow 2 c := by ring
      have hpi : 0 < Real.pi := Real.pi_pos
      have h3 : 0 < (3 : ℝ) ^ c := Real.rpow_pos_of_pos (by norm_num) c
      have h2 : 0 < Real.rpow 2 c := Real.rpow_pos_of_pos (by norm_num) c
      have hnonneg : 0 ≤ 2 * Real.pi * (3 : ℝ) ^ c * Real.rpow 2 c := by
        positivity
      have htarget : 2 * Real.pi * ((3 : ℝ) ^ c / 2) * Real.rpow 2 c ≤
          2 * Real.pi * (3 : ℝ) ^ c * Real.rpow 2 c := by
        have hX : 0 ≤ Real.pi * (3 : ℝ) ^ c * Real.rpow 2 c := by positivity
        calc
          2 * Real.pi * ((3 : ℝ) ^ c / 2) * Real.rpow 2 c =
              Real.pi * (3 : ℝ) ^ c * Real.rpow 2 c := by ring
          _ ≤ 2 * (Real.pi * (3 : ℝ) ^ c * Real.rpow 2 c) := by nlinarith
          _ = 2 * Real.pi * (3 : ℝ) ^ c * Real.rpow 2 c := by ring
      simpa [hjzero, Real.rpow_zero] using hbound.trans htarget
    · have hjpos : 1 ≤ (j : ℝ) := by
        have hjposI : 0 < j := by omega
        exact_mod_cast hjposI
      have hexp : ((1 - (j : ℝ)) * c) ≤ 1 - (j : ℝ) := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (by linarith : 1 ≤ c))
          (sub_nonpos.mpr (by linarith : 1 ≤ (j : ℝ)))]
      have hpowcomp : Real.rpow 2 ((1 - (j : ℝ)) * c) ≤
          Real.rpow 2 (1 - (j : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
      have hsplitj : Real.rpow 2 (1 - (j : ℝ)) =
          2 * Real.rpow 2 (-(j : ℝ)) := by
        change (2 : ℝ) ^ (1 - (j : ℝ)) =
          2 * (2 : ℝ) ^ (-(j : ℝ))
        rw [show 1 - (j : ℝ) = 1 + (-(j : ℝ)) by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      have hcoef : 0 ≤ (3 : ℝ) ^ c / 2 := by positivity
      have hfinal : 2 * Real.pi * (N.1 : ℝ) ^ c * |ξ| ≤
          2 * Real.pi * (3 : ℝ) ^ c * Real.rpow 2 (-(j : ℝ)) := by
        calc
          _ = 2 * Real.pi * ((N.1 : ℝ) ^ c * |ξ|) := by ring
          _ ≤ 2 * Real.pi * (((3 : ℝ) ^ c / 2) *
              Real.rpow 2 ((1 - (j : ℝ)) * c)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
          _ ≤ 2 * Real.pi * (((3 : ℝ) ^ c / 2) *
              Real.rpow 2 (1 - (j : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hpowcomp hcoef) (by positivity)
          _ = 2 * Real.pi * (3 : ℝ) ^ c * Real.rpow 2 (-(j : ℝ)) := by
            rw [hsplitj]
            ring
      have hone : 1 ≤ Real.rpow 2 c := Real.one_le_rpow (by norm_num) (by linarith)
      have hscale : 2 * Real.pi * (3 : ℝ) ^ c * Real.rpow 2 (-(j : ℝ)) ≤
          2 * Real.pi * (3 : ℝ) ^ c * Real.rpow 2 c *
            Real.rpow 2 (-(j : ℝ)) := by
        have hcoeff : 0 ≤ 2 * Real.pi * (3 : ℝ) ^ c := by positivity
        have hscale0 : 2 * Real.pi * (3 : ℝ) ^ c ≤
            2 * Real.pi * (3 : ℝ) ^ c * Real.rpow 2 c := by
          calc
            2 * Real.pi * (3 : ℝ) ^ c =
                (2 * Real.pi * (3 : ℝ) ^ c) * 1 := by ring
            _ ≤ (2 * Real.pi * (3 : ℝ) ^ c) * (2 : ℝ) ^ c :=
              mul_le_mul_of_nonneg_left hone hcoeff
        exact mul_le_mul_of_nonneg_right hscale0
          (Real.rpow_nonneg (by norm_num) _)
      exact (hfirst.trans hfinal).trans hscale

/-- The exact progression exponent used by the source multiplier comparison. -/
noncomputable def localizedProgressionDelta (c : ℝ) : ℝ :=
  ((1 / 100 : ℝ) /
    (100 * ((Nat.ceil c + 2 : ℕ) : ℝ) *
      (2 : ℝ) ^ ((Nat.ceil c + 2 : ℕ) : ℝ))) / 4

private theorem localizedProgressionDelta_bounds {c : ℝ} (hc : 1 < c) :
    0 < localizedProgressionDelta c ∧ localizedProgressionDelta c < 1 := by
  simpa [localizedProgressionDelta] using progressionParameters_delta_bounds hc

private theorem localizedZpowRpowProduct (k : ℤ) (a : ℝ) :
    ((2 : ℝ) ^ k) ^ a = Real.rpow 2 ((k : ℝ) * a) := by
  rw [← Real.rpow_intCast (2 : ℝ) k]
  exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (k : ℝ) a).symm

private theorem localizedNegativeFrequencyProductLower
    {c : ℝ} (hc : 1 < c) {j k : ℤ}
    (hj : j < 0) (hjk : 0 ≤ j + k) (N : Scale)
    (hNlower : (2 : ℝ) ^ k ≤ (N.1 : ℝ))
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))
    (hs : frequencyProjectionSymbol c (j + k) ξ ≠ 0) :
    (1 / 4 : ℝ) * Real.rpow 2 (-(j : ℝ) * c) ≤
      (N.1 : ℝ) ^ c * |ξ| := by
  have hcpos : 0 < c := by linarith
  have hjkLower : (1 / 4 : ℝ) *
      Real.rpow 2 (-((((j + k : ℤ) : ℝ)) * c)) ≤ |ξ| := by
    by_cases hzero : j + k = 0
    · have hs0 : frequencyProjectionSymbol c 0 ξ ≠ 0 := by
        simpa [hzero] using hs
      have hsupport := frequencyProjectionSymbol_support_zero (c := c) hξ hs0
      rw [hzero]
      norm_num at hsupport ⊢
      exact hsupport.le
    · have hpos : 1 ≤ j + k := by omega
      exact (frequencyProjectionSymbol_support_positive hc hpos hξ hs).1.le
  have h2kpos : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hNpos : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
  have hNpow : ((2 : ℝ) ^ k) ^ c ≤ (N.1 : ℝ) ^ c :=
    Real.rpow_le_rpow h2kpos.le hNlower hcpos.le
  have hidentity :
      ((2 : ℝ) ^ k) ^ c *
        Real.rpow 2 (-((((j + k : ℤ) : ℝ)) * c)) =
      Real.rpow 2 (-(j : ℝ) * c) := by
    rw [localizedZpowRpowProduct]
    change (2 : ℝ) ^ ((k : ℝ) * c) *
      (2 : ℝ) ^ (-((((j + k : ℤ) : ℝ)) * c)) =
      (2 : ℝ) ^ (-(j : ℝ) * c)
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  calc
    (1 / 4 : ℝ) * Real.rpow 2 (-(j : ℝ) * c) =
        (1 / 4 : ℝ) * (((2 : ℝ) ^ k) ^ c) *
          Real.rpow 2 (-((((j + k : ℤ) : ℝ)) * c)) := by
            rw [← hidentity]
            ring
    _ = ((2 : ℝ) ^ k) ^ c *
          ((1 / 4 : ℝ) *
            Real.rpow 2 (-((((j + k : ℤ) : ℝ)) * c))) := by ring
    _ ≤ ((2 : ℝ) ^ k) ^ c * |ξ| :=
      mul_le_mul_of_nonneg_left hjkLower (by positivity)
    _ ≤ (N.1 : ℝ) ^ c * |ξ| :=
      mul_le_mul_of_nonneg_right hNpow (abs_nonneg ξ)

private theorem localizedNegativeFrequencyProductLowerSimple
    {c : ℝ} (hc : 1 < c) {j k : ℤ}
    (hj : j < 0) (hjk : 0 ≤ j + k) (N : Scale)
    (hNlower : (2 : ℝ) ^ k ≤ (N.1 : ℝ))
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))
    (hs : frequencyProjectionSymbol c (j + k) ξ ≠ 0) :
    Real.rpow 2 (((-(j : ℝ)) - 2) * c) ≤
      (N.1 : ℝ) ^ c * |ξ| := by
  have hmain := localizedNegativeFrequencyProductLower hc hj hjk N
    hNlower ξ hξ hs
  have ha : 0 ≤ Real.rpow 2 (((-(j : ℝ)) - 2) * c) :=
    Real.rpow_nonneg (by norm_num) _
  have hpow4 : 4 ≤ Real.rpow 2 (2 * c) := by
    calc
      (4 : ℝ) = Real.rpow 2 2 := by norm_num
      _ ≤ Real.rpow 2 (2 * c) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by nlinarith)
  have hsplit : Real.rpow 2 (-(j : ℝ) * c) =
      Real.rpow 2 (((-(j : ℝ)) - 2) * c) * Real.rpow 2 (2 * c) := by
    change (2 : ℝ) ^ (-(j : ℝ) * c) =
      (2 : ℝ) ^ (((-(j : ℝ)) - 2) * c) * (2 : ℝ) ^ (2 * c)
    rw [show -(j : ℝ) * c =
      ((-(j : ℝ)) - 2) * c + 2 * c by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hfactor : Real.rpow 2 (((-(j : ℝ)) - 2) * c) ≤
      (1 / 4 : ℝ) * Real.rpow 2 (-(j : ℝ) * c) := by
    rw [hsplit]
    have hmul := mul_le_mul_of_nonneg_left hpow4 ha
    nlinarith
  exact hfactor.trans hmain

private theorem localizedNegativeModelPowerDecay
    {c a X : ℝ} (hc : 1 < c) (ha : 0 < a)
    (hX : 0 < X)
    (hXlower : Real.rpow 2 ((a - 2) * c) ≤ X) :
    Real.rpow X (-c⁻¹) ≤
      4 * Real.rpow 2 (-(localizedProgressionDelta c) * a) := by
  have hδ := localizedProgressionDelta_bounds hc
  have hpow4 : 4 ≤ Real.rpow 2 (2 * c) := by
    calc
      (4 : ℝ) = Real.rpow 2 2 := by norm_num
      _ ≤ Real.rpow 2 (2 * c) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by nlinarith)
  have hsplit : Real.rpow 2 (a * c) =
      Real.rpow 2 ((a - 2) * c) * Real.rpow 2 (2 * c) := by
    change (2 : ℝ) ^ (a * c) =
      (2 : ℝ) ^ ((a - 2) * c) * (2 : ℝ) ^ (2 * c)
    rw [show a * c = (a - 2) * c + 2 * c by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hfactor : Real.rpow 2 ((a - 2) * c) ≤
      (1 / 4 : ℝ) * Real.rpow 2 (a * c) := by
    rw [hsplit]
    have hA := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((a - 2) * c)
    have hmul := mul_le_mul_of_nonneg_left hpow4 hA
    have hmul' : 4 * Real.rpow 2 ((a - 2) * c) ≤
        Real.rpow 2 ((a - 2) * c) * Real.rpow 2 (2 * c) := by
      calc
        4 * Real.rpow 2 ((a - 2) * c) =
            Real.rpow 2 ((a - 2) * c) * 4 := by ring
        _ ≤ Real.rpow 2 ((a - 2) * c) * Real.rpow 2 (2 * c) := hmul
    calc
      Real.rpow 2 ((a - 2) * c) =
          (1 / 4 : ℝ) * (4 * Real.rpow 2 ((a - 2) * c)) := by ring
      _ ≤ (1 / 4 : ℝ) *
          (Real.rpow 2 ((a - 2) * c) * Real.rpow 2 (2 * c)) :=
        mul_le_mul_of_nonneg_left hmul' (by norm_num)
  have hXpos' : 0 < Real.rpow 2 ((a - 2) * c) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hcinv : 0 < c⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hc)
  have hneg : Real.rpow X (-c⁻¹) ≤
      Real.rpow (Real.rpow 2 ((a - 2) * c)) (-c⁻¹) :=
    Real.rpow_le_rpow_of_nonpos hXpos' hXlower (neg_nonpos.mpr hcinv.le)
  have hpowid : Real.rpow (Real.rpow 2 ((a - 2) * c)) (-c⁻¹) =
      Real.rpow 2 (((a - 2) * c) * (-c⁻¹)) :=
    (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
  have hexp : ((a - 2) * c) * (-c⁻¹) = 2 - a := by
    field_simp [ne_of_gt (lt_trans zero_lt_one hc)]
    ring
  have hsplit2 : Real.rpow 2 (2 - a) =
      4 * Real.rpow 2 (-a) := by
    change (2 : ℝ) ^ (2 - a) = 4 * (2 : ℝ) ^ (-a)
    rw [show 2 - a = 2 + (-a) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hδexp : -a ≤ -localizedProgressionDelta c * a := by
    nlinarith [hδ.2]
  have hδpow : Real.rpow 2 (-a) ≤
      Real.rpow 2 (-localizedProgressionDelta c * a) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hδexp
  calc
    Real.rpow X (-c⁻¹) ≤
        Real.rpow (Real.rpow 2 ((a - 2) * c)) (-c⁻¹) := hneg
    _ = Real.rpow 2 (2 - a) := by rw [hpowid, hexp]
    _ = 4 * Real.rpow 2 (-a) := hsplit2
    _ ≤ 4 * Real.rpow 2 (-localizedProgressionDelta c * a) :=
      mul_le_mul_of_nonneg_left hδpow (by norm_num)

private theorem localizedbNNegEqStar (c ξ : ℝ) (N : Scale) :
    bN c (-ξ) N = star (bN c ξ N) := by
  have hpos : bN c (-ξ) N = positiveFloorPowerMultiplier c ξ N := by
    simp [bN, positiveFloorPowerMultiplier,
      ← unitFrequencyPhase_neg_eq_conj]
  have hstar : star (positiveFloorPowerMultiplier c ξ N) = bN c ξ N := by
    simp [positiveFloorPowerMultiplier, bN, map_mul, map_sum,
      ← unitFrequencyPhase_neg_eq_conj]
  calc
    bN c (-ξ) N = positiveFloorPowerMultiplier c ξ N := hpos
    _ = star (star (positiveFloorPowerMultiplier c ξ N)) := by simp
    _ = star (bN c ξ N) := congrArg star hstar

private theorem localizedContinuousModelVNegEqStar {c N ξ : ℝ}
    (hN : 0 < N) :
    continuousModelV c N (-ξ) = star (continuousModelV c N ξ) := by
  calc
    continuousModelV c N (-ξ) = continuousFractionalModel c N ξ :=
      by
        simpa only [neg_neg] using
          (continuousModelV_eq_continuousFractionalModel_neg
            (c := c) (N := N) (ξ := -ξ) hN)
    _ = star (continuousModelV c N ξ) := by
      have h := continuousModelV_eq_star_continuousFractionalModel
        (c := c) (N := N) (ξ := ξ) hN
      simpa using (congrArg star h).symm

private theorem localizedbNModelEndpointNormNeg {c N ξ : ℝ}
    (hN : 0 < N) (Nscale : Scale) :
    ‖bN c (-ξ) Nscale - continuousModelV c N (-ξ)‖ =
      ‖bN c ξ Nscale - continuousModelV c N ξ‖ := by
  rw [localizedbNNegEqStar, localizedContinuousModelVNegEqStar hN,
    ← star_sub, norm_star]

noncomputable def localizedProgressionComparisonConstant
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) : ℝ :=
  Classical.choose (bN_close_continuousModelV hc hcNon)

private theorem localizedProgressionComparisonConstant_spec
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) :
    0 ≤ localizedProgressionComparisonConstant hc hcNon ∧
      ∀ N : Scale, 3 ≤ (N.1 : ℝ) →
        ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
          ‖bN c ξ N - continuousModelV c (N.1 : ℝ) ξ‖ ≤
            localizedProgressionComparisonConstant hc hcNon *
              (N.1 : ℝ) ^ (-localizedProgressionDelta c) := by
  dsimp [localizedProgressionComparisonConstant]
  exact Classical.choose_spec (bN_close_continuousModelV hc hcNon)

def localizedNegativeMultiplierConstant
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) : ℝ :=
  localizedProgressionComparisonConstant hc hcNon +
    4 * continuousModelK c + 2

/-- On the source annulus, the integer-time averaging symbol is small at
negative frequency indices, uniformly over scales at least the dyadic base. -/
private theorem localizedNegativeIntegerMultiplier_decay
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c)
    {j k : ℤ} (hj : j < 0) (hjk : 0 ≤ j + k)
    (N : Scale) (hNlower : (2 : ℝ) ^ k ≤ (N.1 : ℝ))
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))
    (hs : frequencyProjectionSymbol c (j + k) ξ ≠ 0) :
    ‖bN c ξ N‖ ≤ localizedNegativeMultiplierConstant hc hcNon *
      Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) := by
  have hcpos : 0 < c := by linarith
  have hδ := localizedProgressionDelta_bounds hc
  have hδpos := hδ.1
  have hδlt := hδ.2
  have hjabs : 0 < -(j : ℝ) := by exact_mod_cast (neg_pos.mpr hj)
  have hka : -(j : ℝ) ≤ (k : ℝ) := by
    have hk : -j ≤ k := by omega
    exact_mod_cast hk
  have h2kpos : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hNpos : 0 < (N.1 : ℝ) := by exact_mod_cast N.2
  have hprod := localizedNegativeFrequencyProductLowerSimple
    hc hj hjk N hNlower ξ hξ hs
  have hXpos : 0 < (N.1 : ℝ) ^ c * |ξ| := by
    have hlow : 0 < Real.rpow 2 (((-(j : ℝ)) - 2) * c) :=
      Real.rpow_pos_of_pos (by norm_num) _
    exact lt_of_lt_of_le hlow hprod
  have hmodeldecay := localizedNegativeModelPowerDecay
    hc hjabs hXpos hprod
  have hdecayBase : (N.1 : ℝ) ^ (-localizedProgressionDelta c) ≤
      Real.rpow 2 (-(localizedProgressionDelta c) * (-(j : ℝ))) := by
    have hmon := Real.rpow_le_rpow_of_nonpos h2kpos hNlower
      (neg_nonpos.mpr hδpos.le)
    calc
      (N.1 : ℝ) ^ (-localizedProgressionDelta c) ≤
          ((2 : ℝ) ^ k) ^ (-localizedProgressionDelta c) := hmon
      _ = Real.rpow 2 ((k : ℝ) * (-localizedProgressionDelta c)) :=
        localizedZpowRpowProduct k (-localizedProgressionDelta c)
      _ ≤ Real.rpow 2 (-(localizedProgressionDelta c) * (-(j : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by
          nlinarith [hka, hδpos])
  have hCspec := localizedProgressionComparisonConstant_spec hc hcNon
  have hC : 0 ≤ localizedProgressionComparisonConstant hc hcNon := hCspec.1
  let C : ℝ := localizedProgressionComparisonConstant hc hcNon
  have hclose := hCspec.2
  let δ : ℝ := localizedProgressionDelta c
  have hclose' : ∀ N : Scale, 3 ≤ (N.1 : ℝ) →
      ∀ ξ : ℝ, -(1 / 2 : ℝ) ≤ ξ → ξ < 1 / 2 →
        ‖bN c ξ N - continuousModelV c (N.1 : ℝ) ξ‖ ≤
          C * (N.1 : ℝ) ^ (-δ) := by
    simpa [C, δ, localizedProgressionDelta] using hclose
  let D : ℝ := localizedNegativeMultiplierConstant hc hcNon
  have hK : 0 ≤ continuousModelK c := by
    unfold continuousModelK
    positivity
  have hD : 0 ≤ D := by
    dsimp [D, localizedNegativeMultiplierConstant]
    linarith
  change ‖bN c ξ N‖ ≤ D * Real.rpow 2
    (-localizedProgressionDelta c * (-(j : ℝ)))
  by_cases hN3 : 3 ≤ (N.1 : ℝ)
  · have hxiNe : ξ ≠ 0 := by
      intro hz
      subst ξ
      have hpos : 0 < (N.1 : ℝ) ^ c * |(0 : ℝ)| := by simpa using hXpos
      norm_num at hpos
    have hcloseN : ‖bN c ξ N - continuousModelV c (N.1 : ℝ) ξ‖ ≤
        C * (N.1 : ℝ) ^ (-δ) := by
      by_cases hhalf : ξ = 1 / 2
      · have hcloseNeg := hclose' N hN3 (-(1 / 2 : ℝ)) (by norm_num) (by norm_num)
        have hendpoint := localizedbNModelEndpointNormNeg
          (c := c) (N := (N.1 : ℝ)) (ξ := (1 / 2 : ℝ)) hNpos N
        rw [hendpoint] at hcloseNeg
        simpa [hhalf] using hcloseNeg
      · exact hclose' N hN3 ξ (le_of_lt hξ.1) (lt_of_le_of_ne hξ.2 hhalf)
    have hmodel := continuousModelV_norm_le_min (ξ := ξ) hc hNpos
    rw [continuousModelMin, if_neg hxiNe] at hmodel
    have hmodel' : ‖continuousModelV c (N.1 : ℝ) ξ‖ ≤
        continuousModelK c * Real.rpow ((N.1 : ℝ) ^ c * |ξ|) (-c⁻¹) := by
      have hmin :
          min 1 ((|ξ| * (N.1 : ℝ) ^ c) ^ (-c⁻¹)) ≤
            Real.rpow ((N.1 : ℝ) ^ c * |ξ|) (-c⁻¹) := by
        calc
          min 1 ((|ξ| * (N.1 : ℝ) ^ c) ^ (-c⁻¹)) ≤
              ((|ξ| * (N.1 : ℝ) ^ c) ^ (-c⁻¹)) := min_le_right _ _
          _ = Real.rpow ((N.1 : ℝ) ^ c * |ξ|) (-c⁻¹) := by
            change (|ξ| * (N.1 : ℝ) ^ c) ^ (-c⁻¹) =
              ((N.1 : ℝ) ^ c * |ξ|) ^ (-c⁻¹)
            rw [mul_comm]
      exact hmodel.trans
        (mul_le_mul_of_nonneg_left hmin hK)
    have hmodel'' : ‖continuousModelV c (N.1 : ℝ) ξ‖ ≤
        4 * continuousModelK c *
          Real.rpow 2 (-(localizedProgressionDelta c) * (-(j : ℝ))) := by
      calc
        _ ≤ continuousModelK c *
            Real.rpow ((N.1 : ℝ) ^ c * |ξ|) (-c⁻¹) := hmodel'
        _ ≤ continuousModelK c *
            (4 * Real.rpow 2
              (-(localizedProgressionDelta c) * (-(j : ℝ)))) :=
          mul_le_mul_of_nonneg_left hmodeldecay hK
        _ = _ := by ring
    have herror : ‖bN c ξ N - continuousModelV c (N.1 : ℝ) ξ‖ ≤
        C * Real.rpow 2 (-(localizedProgressionDelta c) * (-(j : ℝ))) :=
      hcloseN.trans (mul_le_mul_of_nonneg_left hdecayBase hC)
    calc
      ‖bN c ξ N‖ ≤ ‖bN c ξ N - continuousModelV c (N.1 : ℝ) ξ‖ +
          ‖continuousModelV c (N.1 : ℝ) ξ‖ := by
        calc
          _ = ‖(bN c ξ N - continuousModelV c (N.1 : ℝ) ξ) +
              continuousModelV c (N.1 : ℝ) ξ‖ := by congr 1 <;> abel
          _ ≤ _ := norm_add_le _ _
      _ ≤ C * Real.rpow 2
            (-(localizedProgressionDelta c) * (-(j : ℝ))) +
          4 * continuousModelK c * Real.rpow 2
            (-(localizedProgressionDelta c) * (-(j : ℝ))) :=
        add_le_add herror hmodel''
      _ ≤ D * Real.rpow 2
          (-(localizedProgressionDelta c) * (-(j : ℝ))) := by
        have hcoeff : C + 4 * continuousModelK c ≤ D := by
          dsimp [D, localizedNegativeMultiplierConstant, C]
          linarith
        have hpow : 0 ≤ Real.rpow 2
            (-(localizedProgressionDelta c) * (-(j : ℝ))) :=
          Real.rpow_nonneg (by norm_num) _
        calc
          C * Real.rpow 2
              (-(localizedProgressionDelta c) * (-(j : ℝ))) +
            4 * continuousModelK c * Real.rpow 2
              (-(localizedProgressionDelta c) * (-(j : ℝ))) =
              (C + 4 * continuousModelK c) * Real.rpow 2
                (-(localizedProgressionDelta c) * (-(j : ℝ))) := by ring
          _ ≤ D * Real.rpow 2
              (-(localizedProgressionDelta c) * (-(j : ℝ))) :=
            mul_le_mul_of_nonneg_right hcoeff hpow
  · have hNnatlt : N.1 < 3 := by
      have hnot : ¬ (3 : ℕ) ≤ N.1 := by
        intro h
        exact hN3 (by exact_mod_cast h)
      omega
    have hNle2 : (N.1 : ℝ) ≤ 2 := by
      exact_mod_cast (Nat.le_of_lt_succ hNnatlt)
    have h2leN : (2 : ℝ) ≤ (N.1 : ℝ) := by
      have hkone : 1 ≤ k := by omega
      have h2lek : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
        calc
          (2 : ℝ) = (2 : ℝ) ^ (1 : ℤ) := by norm_num
          _ ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hkone
      exact h2lek.trans hNlower
    have hNcast : (N.1 : ℝ) = 2 := le_antisymm hNle2 h2leN
    have hkupper : k ≤ 1 := by
      by_contra hknot
      have hk2 : 2 ≤ k := by omega
      have h4lek : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
        calc
          (4 : ℝ) = (2 : ℝ) ^ (2 : ℤ) := by norm_num
          _ ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hk2
      have hcontra : (4 : ℝ) ≤ 2 := by
        rw [← hNcast]
        exact h4lek.trans hNlower
      norm_num at hcontra
    have hkone : k = 1 := by omega
    have hjone : j = -1 := by omega
    have hnorm := bN_norm_le_one c ξ N
    have hpowLower : (1 / 2 : ℝ) ≤ Real.rpow 2
        (-(localizedProgressionDelta c) * (-(j : ℝ))) := by
      have hlt : -(1 : ℝ) < -localizedProgressionDelta c := by linarith
      have hpow := Real.rpow_lt_rpow_of_exponent_lt
        (by norm_num : (1 : ℝ) < 2) hlt
      have hpowhalf : (2 : ℝ) ^ (-(1 : ℝ)) = (1 / 2 : ℝ) := by
        rw [Real.rpow_neg_one]
        norm_num
      have hpowLower' : (1 / 2 : ℝ) ≤ Real.rpow 2
          (-localizedProgressionDelta c) := by
        change (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-localizedProgressionDelta c)
        rw [← hpowhalf]
        exact hpow.le
      have hexp : -localizedProgressionDelta c * (-(j : ℝ)) =
          -localizedProgressionDelta c := by
        rw [hjone]
        norm_num
      rw [hexp]
      exact hpowLower'
    have hD2 : 2 ≤ D := by
      dsimp [D, localizedNegativeMultiplierConstant, C]
      linarith
    calc
      ‖bN c ξ N‖ ≤ 1 := bN_norm_le_one c ξ N
      _ ≤ D * Real.rpow 2
          (-(localizedProgressionDelta c) * (-(j : ℝ))) := by
        have hpow := hpowLower
        nlinarith

private theorem localizedDyadicLowerPowerIdentity
    (c : ℝ) (j k : ℤ) :
    ((2 : ℝ) ^ k) ^ c *
        Real.rpow 2 (-((((j + k : ℤ) : ℝ)) * c)) =
      Real.rpow 2 (-(j : ℝ) * c) := by
  let q : ℝ := Real.rpow 2 c
  let d : ℤ := -(j + k : ℤ)
  have hexp : -((((j + k : ℤ) : ℝ)) * c) = c * d := by
    dsimp [d]
    push_cast
    ring
  have hmul : Real.rpow 2 (c * d) = q ^ d := by
    calc
      Real.rpow 2 (c * (d : ℝ)) = (Real.rpow 2 c) ^ (d : ℝ) :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) c (d : ℝ)
      _ = q ^ d := by rw [Real.rpow_intCast]
  calc
    ((2 : ℝ) ^ k) ^ c * Real.rpow 2 (-((((j + k : ℤ) : ℝ)) * c)) =
      q ^ k * Real.rpow 2 (c * d) := by
        conv_lhs => rw [← Real.rpow_zpow_comm (by norm_num : (0 : ℝ) ≤ 2) c k]
        dsimp [q]
        rw [hexp]
    _ = q ^ k * q ^ d := by rw [hmul]
    _ = q ^ (k + -(j + k : ℤ)) := by
      dsimp [q]
      rw [← zpow_add₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) c))]
    _ = q ^ (-j) := by congr 1 <;> omega
    _ = Real.rpow 2 (-(j : ℝ) * c) := by
      dsimp [q]
      rw [Real.rpow_zpow_comm (by norm_num : (0 : ℝ) ≤ 2) c (-j)]
      rw [← Real.rpow_intCast (2 : ℝ) (-j)]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring

/-- The source piecewise-linear average, conjugated to the explicit sequence
model while retaining its exact finite-time definition. -/
noncomputable def localizedInterpolatedAverageL2 (c t : ℝ) (ht : 0 < t)
    (f : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  countLpToLp (interpolatedUnweightedAverage (p := (2 : ℝ≥0∞))
    localizedIntegerShiftSystem c t ht (lpToCountLp f))

theorem localizedInterpolatedAverageL2_at_integer
    (c : ℝ) (N : ℕ) (hN : 1 ≤ N) (f : lp (fun _ : ℤ => ℂ) 2) :
    localizedInterpolatedAverageL2 c (N : ℝ)
        (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hN)) f =
      localizedIntegerUnweightedAverageL2 c
        ⟨N, Nat.lt_of_lt_of_le Nat.zero_lt_one hN⟩ f := by
  unfold localizedInterpolatedAverageL2 localizedIntegerUnweightedAverageL2
  rw [interpolatedUnweightedAverage_at_integer
    (p := (2 : ℝ≥0∞)) localizedIntegerShiftSystem c N hN]

theorem localizedInterpolatedAverageL2_eq_convex_combo
    (c t : ℝ) (ht : 1 < t) (f : lp (fun _ : ℤ => ℂ) 2) :
    let N : ℕ := ⌊t⌋₊
    let a : ℝ := t - (N : ℝ)
    localizedInterpolatedAverageL2 c t (by linarith) f =
      ((1 - a : ℝ) : ℂ) •
          localizedIntegerUnweightedAverageL2 c ⟨N, by
            dsimp [N]
            exact Nat.le_floor (by exact_mod_cast ht.le)
          ⟩ f +
        (a : ℝ) • localizedIntegerUnweightedAverageL2 c ⟨N + 1, by omega⟩ f := by
  classical
  let N : ℕ := ⌊t⌋₊
  let a : ℝ := t - (N : ℝ)
  have hN : 1 ≤ N := by
    dsimp [N]
    exact Nat.le_floor (by exact_mod_cast ht.le)
  have hconvex :
      localizedInterpolatedAverageL2 c t (by linarith) f =
        ((1 - a : ℝ) : ℂ) •
            localizedIntegerUnweightedAverageL2 c ⟨N, hN⟩ f +
          (a : ℝ) • localizedIntegerUnweightedAverageL2 c ⟨N + 1, by omega⟩ f := by
    unfold localizedInterpolatedAverageL2
    simp [interpolatedUnweightedAverage, not_le_of_gt ht, a, N,
      localizedIntegerUnweightedAverageL2, LinearMap.map_add, LinearMap.map_smul,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simpa [N, a] using hconvex

private theorem localizedLpCast_apply {p q : ℝ≥0∞} (hpq : p = q)
    (f : lp (fun _ : ℤ => ℂ) p) (k : ℤ) :
    (hpq ▸ f) k = f k := by
  cases hpq
  rfl

/-- The source's natural-index projection, transported to the explicit
sequence model used by the Fourier bridge. -/
def localizedFrequencyProjectionL2 (c : ℝ) (hc : 1 < c) (h : ℕ)
    (f : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  if h = 0 then frequencyProjectionPartialLpOperatorL2 c hc 0 f
  else frequencyProjectionPartialLpOperatorL2 c hc h f -
    frequencyProjectionPartialLpOperatorL2 c hc (h - 1) f

/-- Fourier action of one finite partial projection. -/
theorem localizedPartialProjectionL2_fourier
    (c : ℝ) (hc : 1 < c) (N : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    sequenceToCircleL2 (frequencyProjectionPartialLpOperatorL2 c hc N f) =
      torusSymbolLp (frequencyProjectionPartialData c hc N) • sequenceToCircleL2 f := by
  have hFU :
      (frequencyProjectionLpTwoToMultiplier f : ℤ → ℂ) = (f : ℤ → ℂ) := by
    funext k
    exact localizedLpCast_apply frequencyProjectionLpTwoExponent.symm f k
  have hmul := finiteMultiplierLpExtension_eq_TmL2_of_lp2
    (frequencyProjectionPartialData c hc N) (by norm_num)
    (frequencyProjectionLpTwoToMultiplier f) f hFU
  have hop : frequencyProjectionPartialLpOperatorL2 c hc N f =
      TmL2 (frequencyProjectionPartialData c hc N) f := by
    apply lp.ext
    funext k
    change (frequencyProjectionLpTwoExponent ▸
      frequencyProjectionPartialLpOperator c hc (by norm_num : 1 < (2 : ℝ)) N
        (frequencyProjectionLpTwoToMultiplier f)) k =
      (TmL2 (frequencyProjectionPartialData c hc N) f : ℤ → ℂ) k
    rw [localizedLpCast_apply frequencyProjectionLpTwoExponent]
    exact congrFun hmul k
  rw [hop, TmL2_eq_frequencyProjectionTmL2FromSymbolLp]
  simp [frequencyProjectionTmL2FromSymbolLp]

/-- A natural frequency projection has the exact finite-difference symbol
from the source's resolution. -/
def localizedFrequencyProjectionSymbolLp (c : ℝ) (hc : 1 < c) (h : ℕ) :
    Lp ℂ ⊤ torusHaar :=
  frequencyProjectionPartialSymbolDifferenceLp c hc h

theorem localizedFrequencyProjectionSymbolLp_coeFn
    (c : ℝ) (hc : 1 < c) (h : ℕ) :
    (localizedFrequencyProjectionSymbolLp c hc h : Torus → ℂ) =ᵐ[torusHaar]
      fun ξ => (frequencyProjectionSymbol c (h : ℤ) ξ : ℂ) := by
  cases h with
  | zero =>
      simp only [localizedFrequencyProjectionSymbolLp,
        frequencyProjectionPartialSymbolDifferenceLp, if_true]
      filter_upwards [Lp.coeFn_sub
          (torusSymbolLp (frequencyProjectionPartialData c hc 0)) 0,
        torusSymbolLp_coeFn (frequencyProjectionPartialData c hc 0),
        Lp.coeFn_zero ℂ ⊤ torusHaar] with ξ hsub hcur hzero
      rw [hsub, Pi.sub_apply, hcur, hzero]
      simpa using (frequencyProjectionPartialData_difference_eq_projection c hc 0 ξ)
  | succ h =>
      simp only [localizedFrequencyProjectionSymbolLp,
        frequencyProjectionPartialSymbolDifferenceLp, Nat.succ_ne_zero, if_false,
        Nat.succ_sub_one]
      filter_upwards [Lp.coeFn_sub
          (torusSymbolLp (frequencyProjectionPartialData c hc (h + 1)))
          (torusSymbolLp (frequencyProjectionPartialData c hc h)),
        torusSymbolLp_coeFn (frequencyProjectionPartialData c hc (h + 1)),
        torusSymbolLp_coeFn (frequencyProjectionPartialData c hc h)] with ξ hsub hcur hprev
      rw [hsub, Pi.sub_apply, hcur, hprev]
      exact frequencyProjectionPartialData_difference_eq_projection c hc (h + 1) ξ

private theorem localizedLpSymbol_sub_smul
    (g₁ g₂ : Lp ℂ ⊤ torusHaar) (F : Lp ℂ 2 torusHaar) :
    g₁ • F - g₂ • F = (g₁ - g₂) • F := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (g₁ • F) (g₂ • F),
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) g₁ F,
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) g₂ F,
    Lp.coeFn_sub g₁ g₂,
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) (g₁ - g₂) F]
      with ξ hsub hmul₁ hmul₂ hsubₛ hmul
  calc
    ((g₁ • F - g₂ • F : Lp ℂ 2 torusHaar) : Torus → ℂ) ξ =
        ((g₁ • F : Lp ℂ 2 torusHaar) : Torus → ℂ) ξ -
          ((g₂ • F : Lp ℂ 2 torusHaar) : Torus → ℂ) ξ := hsub
    _ = ((g₁ - g₂) • F : Lp ℂ 2 torusHaar) ξ := by
      rw [hmul₁, hmul₂, hmul]
      simp only [Pi.smul_apply', smul_eq_mul]
      rw [hsubₛ]
      simp only [Pi.sub_apply]
      ring

theorem localizedFrequencyProjectionL2_fourier
    (c : ℝ) (hc : 1 < c) (h : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    sequenceToCircleL2 (localizedFrequencyProjectionL2 c hc h f) =
      localizedFrequencyProjectionSymbolLp c hc h • sequenceToCircleL2 f := by
  cases h with
  | zero =>
      simp [localizedFrequencyProjectionL2]
      rw [localizedPartialProjectionL2_fourier]
      simp [localizedFrequencyProjectionSymbolLp,
        frequencyProjectionPartialSymbolDifferenceLp]
  | succ h =>
      simp [localizedFrequencyProjectionL2]
      rw [localizedPartialProjectionL2_fourier,
        localizedPartialProjectionL2_fourier]
      exact localizedLpSymbol_sub_smul _ _ _

private theorem localizedFrequencyProjectionL2_fourier_coeFn
    (c : ℝ) (hc : 1 < c) (h : ℕ) (f : lp (fun _ : ℤ => ℂ) 2) :
    (sequenceToCircleL2 (localizedFrequencyProjectionL2 c hc h f) :
        Torus → ℂ) =ᵐ[torusHaar]
      fun ξ => (frequencyProjectionSymbol c (h : ℤ) ξ : ℂ) *
        sequenceToCircleL2 f ξ := by
  have hFourier := localizedFrequencyProjectionL2_fourier c hc h f
  have hEq : (sequenceToCircleL2 (localizedFrequencyProjectionL2 c hc h f) :
      Torus → ℂ) =ᵐ[torusHaar]
      (localizedFrequencyProjectionSymbolLp c hc h • sequenceToCircleL2 f :
        Lp ℂ 2 torusHaar) :=
    Lp.ext_iff.mp hFourier
  have hmul := Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
    (localizedFrequencyProjectionSymbolLp c hc h) (sequenceToCircleL2 f)
  have hsymbol := localizedFrequencyProjectionSymbolLp_coeFn c hc h
  filter_upwards [hEq, hmul, hsymbol] with ξ hEq hmul hsymbol
  have hmul' :
      (localizedFrequencyProjectionSymbolLp c hc h • sequenceToCircleL2 f :
        Lp ℂ 2 torusHaar) ξ =
      (localizedFrequencyProjectionSymbolLp c hc h : Torus → ℂ) ξ *
        sequenceToCircleL2 f ξ := by
    change (localizedFrequencyProjectionSymbolLp c hc h • sequenceToCircleL2 f :
      Lp ℂ 2 torusHaar) ξ = _
    simpa only [Pi.smul_apply', smul_eq_mul] using hmul
  calc
    (sequenceToCircleL2 (localizedFrequencyProjectionL2 c hc h f) :
        Torus → ℂ) ξ =
        (localizedFrequencyProjectionSymbolLp c hc h • sequenceToCircleL2 f :
          Lp ℂ 2 torusHaar) ξ := hEq
    _ = (localizedFrequencyProjectionSymbolLp c hc h : Torus → ℂ) ξ *
          sequenceToCircleL2 f ξ := hmul'
    _ = (frequencyProjectionSymbol c (h : ℤ) ξ : ℂ) *
          sequenceToCircleL2 f ξ := by rw [hsymbol]

def localizedPositiveMultiplierConstant (c : ℝ) : ℝ :=
  2 * Real.pi * (3 : ℝ) ^ c * Real.rpow 2 c

private theorem localizedIntegerAveragePositiveProjectionError_norm_le
    {c : ℝ} (hc : 1 < c) {j k : ℤ}
    (hj : 0 ≤ j) (hk : 0 ≤ k)
    (N : Scale) (hNupper : (N.1 : ℝ) ≤ 3 * (2 : ℝ) ^ k)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    ‖localizedIntegerUnweightedAverageL2 c N
        (localizedFrequencyProjectionL2 c hc (j + k).toNat f) -
      localizedFrequencyProjectionL2 c hc (j + k).toNat f‖ ≤
      localizedPositiveMultiplierConstant c *
        Real.rpow 2 (-(localizedProgressionDelta c) * (j : ℝ)) *
        ‖localizedFrequencyProjectionL2 c hc (j + k).toNat f‖ := by
  let h : ℕ := (j + k).toNat
  have hcast : (h : ℤ) = j + k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (add_nonneg hj hk)
  let P : lp (fun _ : ℤ => ℂ) 2 := localizedFrequencyProjectionL2 c hc h f
  let F : Lp ℂ 2 torusHaar := sequenceToCircleL2 P
  let g : Lp ℂ ⊤ torusHaar := localizedIntegerUnweightedAverageSymbolLp c N
  have hFourierAvg := sequenceToCircleL2_localizedIntegerUnweightedAverage c N P
  have hImage :
      sequenceToCircleL2 (localizedIntegerUnweightedAverageL2 c N P - P) =
        g • F - F := by
    simpa [g, F] using
      congrArg (fun z : Lp ℂ 2 torusHaar => z - sequenceToCircleL2 P) hFourierAvg
  have hposC : 0 ≤ localizedPositiveMultiplierConstant c := by
    unfold localizedPositiveMultiplierConstant
    have hpi : 0 < Real.pi := Real.pi_pos
    have h3 : 0 < (3 : ℝ) ^ c := Real.rpow_pos_of_pos (by norm_num) c
    have h2 : 0 < Real.rpow 2 c := Real.rpow_pos_of_pos (by norm_num) c
    positivity
  have hδ := localizedProgressionDelta_bounds hc
  have hδexp : -(j : ℝ) ≤
      -localizedProgressionDelta c * (j : ℝ) := by
    have hjR : 0 ≤ (j : ℝ) := by exact_mod_cast hj
    nlinarith [hδ.2]
  have hpower :
      Real.rpow 2 (-(j : ℝ)) ≤
        Real.rpow 2 (-(localizedProgressionDelta c) * (j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hδexp
  have hbound :
      ∀ᵐ ξ ∂torusHaar, ‖(g • F - F : Lp ℂ 2 torusHaar) ξ‖ ≤
        (localizedPositiveMultiplierConstant c *
          Real.rpow 2 (-(localizedProgressionDelta c) * (j : ℝ))) * ‖F ξ‖ := by
    have hsub := Lp.coeFn_sub (g • F) F
    have hmul := Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) g F
    have havg := localizedIntegerAverageSymbol_eq_bN_at_representative c N
    have hproj := localizedFrequencyProjectionL2_fourier_coeFn c hc h f
    filter_upwards [hsub, hmul, havg, hproj] with ξ hsub hmul havg hproj
    let r : Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
      AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ
    have hr : (r : ℝ) ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
      rcases r.property with ⟨hrlo, hrhi⟩
      exact ⟨hrlo, by linarith⟩
    have hcoe : (r : Torus) = ξ := AddCircle.coe_equivIoc
    have hsub' : (g • F - F : Lp ℂ 2 torusHaar) ξ =
        (g • F : Lp ℂ 2 torusHaar) ξ - F ξ := hsub
    have hmul' : (g • F : Lp ℂ 2 torusHaar) ξ =
        (g : Torus → ℂ) ξ * F ξ := by
      change (g • F : Lp ℂ 2 torusHaar) ξ = _
      simpa only [Pi.smul_apply', smul_eq_mul] using hmul
    have hFzero (hzero : frequencyProjectionSymbol c (h : ℤ) ξ = 0) :
        F ξ = 0 := by
      rw [hproj, hzero]
      simp
    by_cases hactive : frequencyProjectionSymbol c (h : ℤ) ξ = 0
    · have hF0 := hFzero hactive
      rw [hsub', hmul', hF0]
      simp [hF0]
    · have hrealActive :
          frequencyProjectionSymbol c (j + k) (r : ℝ) ≠ 0 := by
        intro hz
        have hsym : frequencyProjectionSymbol c (h : ℤ) ξ =
            frequencyProjectionSymbol c (j + k) (r : ℝ) := by
          rw [← hcoe, ← hcast]
        exact hactive (by rw [hsym, hz])
      have hscalar := localizedPositiveIntegerMultiplier_firstMoment
        hc hj hk N hNupper (r : ℝ) hr hrealActive
      have havg' : (g : Torus → ℂ) ξ = bN c (r : ℝ) N := by
        simpa [g, r] using havg
      have hscalar' :
          ‖bN c (r : ℝ) N - 1‖ ≤ localizedPositiveMultiplierConstant c *
            Real.rpow 2 (-(localizedProgressionDelta c) * (j : ℝ)) :=
        hscalar.trans (mul_le_mul_of_nonneg_left hpower hposC)
      have hfactor : ‖(g : Torus → ℂ) ξ - 1‖ ≤
          localizedPositiveMultiplierConstant c *
            Real.rpow 2 (-(localizedProgressionDelta c) * (j : ℝ)) := by
        rw [havg']
        exact hscalar'
      have hpoint :
          ‖((g : Torus → ℂ) ξ - 1) * F ξ‖ ≤
            (localizedPositiveMultiplierConstant c *
              Real.rpow 2 (-(localizedProgressionDelta c) * (j : ℝ))) * ‖F ξ‖ := by
        calc
          _ = ‖(g : Torus → ℂ) ξ - 1‖ * ‖F ξ‖ := norm_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      have hE : (g • F - F : Lp ℂ 2 torusHaar) ξ =
          ((g : Torus → ℂ) ξ - 1) * F ξ := by
        rw [hsub', hmul']
        ring
      rw [hE]
      exact hpoint
  have hLp := Lp.norm_le_mul_norm_of_ae_le_mul (c :=
    localizedPositiveMultiplierConstant c *
      Real.rpow 2 (-(localizedProgressionDelta c) * (j : ℝ))) hbound
  calc
    ‖localizedIntegerUnweightedAverageL2 c N P - P‖ =
        ‖sequenceToCircleL2
          (localizedIntegerUnweightedAverageL2 c N P - P)‖ :=
      (sequenceToCircleL2.norm_map _).symm
    _ = ‖g • F - F‖ := by rw [hImage]
    _ ≤ (localizedPositiveMultiplierConstant c *
        Real.rpow 2 (-(localizedProgressionDelta c) * (j : ℝ))) * ‖F‖ := hLp
    _ = (localizedPositiveMultiplierConstant c *
        Real.rpow 2 (-(localizedProgressionDelta c) * (j : ℝ))) * ‖P‖ := by
          rw [sequenceToCircleL2.norm_map]

private theorem localizedIntegerAverageNegativeProjection_norm_le
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) {j k : ℤ}
    (hj : j < 0) (hjk : 0 ≤ j + k)
    (N : Scale) (hNlower : (2 : ℝ) ^ k ≤ (N.1 : ℝ))
    (f : lp (fun _ : ℤ => ℂ) 2) :
    ‖localizedIntegerUnweightedAverageL2 c N
        (localizedFrequencyProjectionL2 c hc (j + k).toNat f)‖ ≤
      localizedNegativeMultiplierConstant hc hcNon *
        Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) *
        ‖localizedFrequencyProjectionL2 c hc (j + k).toNat f‖ := by
  let h : ℕ := (j + k).toNat
  have hcast : (h : ℤ) = j + k := by
    dsimp [h]
    exact Int.toNat_of_nonneg hjk
  let P : lp (fun _ : ℤ => ℂ) 2 := localizedFrequencyProjectionL2 c hc h f
  let F : Lp ℂ 2 torusHaar := sequenceToCircleL2 P
  let g : Lp ℂ ⊤ torusHaar := localizedIntegerUnweightedAverageSymbolLp c N
  have hFourierAvg := sequenceToCircleL2_localizedIntegerUnweightedAverage c N P
  have hImage :
      sequenceToCircleL2 (localizedIntegerUnweightedAverageL2 c N P) = g • F := by
    simpa [g, F] using hFourierAvg
  have hCspec := localizedProgressionComparisonConstant_spec hc hcNon
  have hC : 0 ≤ localizedNegativeMultiplierConstant hc hcNon := by
    unfold localizedNegativeMultiplierConstant
    have hK : 0 ≤ continuousModelK c := by
      unfold continuousModelK
      positivity
    linarith [hCspec.1]
  have hpow : 0 ≤ Real.rpow 2
      (-localizedProgressionDelta c * (-(j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hbound :
      ∀ᵐ ξ ∂torusHaar, ‖(g • F : Lp ℂ 2 torusHaar) ξ‖ ≤
        (localizedNegativeMultiplierConstant hc hcNon *
          Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ)))) * ‖F ξ‖ := by
    have hmul := Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) g F
    have havg := localizedIntegerAverageSymbol_eq_bN_at_representative c N
    have hproj := localizedFrequencyProjectionL2_fourier_coeFn c hc h f
    filter_upwards [hmul, havg, hproj] with ξ hmul havg hproj
    let r : Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
      AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) ξ
    have hr : (r : ℝ) ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
      rcases r.property with ⟨hrlo, hrhi⟩
      exact ⟨hrlo, by linarith⟩
    have hcoe : (r : Torus) = ξ := AddCircle.coe_equivIoc
    have hmul' : (g • F : Lp ℂ 2 torusHaar) ξ =
        (g : Torus → ℂ) ξ * F ξ := by
      change (g • F : Lp ℂ 2 torusHaar) ξ = _
      simpa only [Pi.smul_apply', smul_eq_mul] using hmul
    have hFzero (hzero : frequencyProjectionSymbol c (h : ℤ) ξ = 0) :
        F ξ = 0 := by
      rw [hproj, hzero]
      simp
    by_cases hactive : frequencyProjectionSymbol c (h : ℤ) ξ = 0
    · have hF0 := hFzero hactive
      rw [hmul', hF0]
      simp [hF0]
    · have hrealActive :
          frequencyProjectionSymbol c (j + k) (r : ℝ) ≠ 0 := by
        intro hz
        have hsym : frequencyProjectionSymbol c (h : ℤ) ξ =
            frequencyProjectionSymbol c (j + k) (r : ℝ) := by
          rw [← hcoe, ← hcast]
        exact hactive (by rw [hsym, hz])
      have hscalar := localizedNegativeIntegerMultiplier_decay
        hc hcNon hj hjk N hNlower (r : ℝ) hr hrealActive
      have havg' : (g : Torus → ℂ) ξ = bN c (r : ℝ) N := by
        simpa [g, r] using havg
      rw [hmul', havg']
      calc
        ‖bN c (r : ℝ) N * F ξ‖ =
            ‖bN c (r : ℝ) N‖ * ‖F ξ‖ := norm_mul _ _
        _ ≤ (localizedNegativeMultiplierConstant hc hcNon *
              Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ)))) *
              ‖F ξ‖ := by
          exact mul_le_mul_of_nonneg_right hscalar (norm_nonneg _)
  have hLp := Lp.norm_le_mul_norm_of_ae_le_mul
    (c := localizedNegativeMultiplierConstant hc hcNon *
      Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ)))) hbound
  calc
    ‖localizedIntegerUnweightedAverageL2 c N P‖ =
        ‖sequenceToCircleL2 (localizedIntegerUnweightedAverageL2 c N P)‖ :=
          (sequenceToCircleL2.norm_map _).symm
    _ = ‖g • F‖ := by rw [hImage]
    _ ≤ (localizedNegativeMultiplierConstant hc hcNon *
        Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ)))) * ‖F‖ := hLp
    _ = (localizedNegativeMultiplierConstant hc hcNon *
        Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ)))) * ‖P‖ := by
          rw [sequenceToCircleL2.norm_map]

/-- The left endpoint of the source dyadic subinterval. -/
def localizedDyadicLeftTime (k : ℤ) (l m : ℕ) : ℝ :=
  (2 : ℝ) ^ k + (2 : ℝ) ^ (k - (l : ℤ)) * (m : ℝ)

/-- Its mesh length, with the blueprint's exponent convention. -/
def localizedDyadicMesh (k : ℤ) (l : ℕ) : ℝ :=
  (2 : ℝ) ^ (k - (l : ℤ))

theorem localizedDyadicLeftTime_pos (k : ℤ) (l m : ℕ) :
    0 < localizedDyadicLeftTime k l m := by
  unfold localizedDyadicLeftTime
  positivity

theorem localizedDyadicMesh_pos (k : ℤ) (l : ℕ) :
    0 < localizedDyadicMesh k l := by
  unfold localizedDyadicMesh
  positivity

theorem localizedDyadicRightTime_pos (k : ℤ) (l m : ℕ) :
    0 < localizedDyadicLeftTime k l m + localizedDyadicMesh k l := by
  exact lt_of_lt_of_le (localizedDyadicLeftTime_pos k l m)
    (le_add_of_nonneg_right (le_of_lt (localizedDyadicMesh_pos k l)))

/-- The mesh is at most `2^-l` times the dyadic left scale. -/
theorem localizedDyadicMesh_le_scale (k : ℤ) (l : ℕ) :
    localizedDyadicMesh k l ≤ (2 : ℝ) ^ (-(l : ℤ)) * (2 : ℝ) ^ k := by
  unfold localizedDyadicMesh
  have hpow : (2 : ℝ) ^ (k - (l : ℤ)) =
      (2 : ℝ) ^ k * (2 : ℝ) ^ (-(l : ℤ)) := by
    rw [show k - (l : ℤ) = k + (-(l : ℤ)) by omega,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simpa [mul_comm] using hpow.le

/-- Every source grid left endpoint is at least its base dyadic scale. -/
theorem localizedDyadicLeftTime_ge_base (k : ℤ) (l m : ℕ) :
    (2 : ℝ) ^ k ≤ localizedDyadicLeftTime k l m := by
  unfold localizedDyadicLeftTime
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hmesh : 0 ≤ (2 : ℝ) ^ (k - (l : ℤ)) := by positivity
  nlinarith

/-- The time-smoothness estimate on each source dyadic subinterval.  This
records the first `2^-l` half of `ha:localized`, before frequency localization. -/
theorem interpolatedAverage_dyadicTimeIncrement_norm_le
    (c : ℝ) (k : ℤ) (l m : ℕ)
    (f : Lp ℂ (2 : ℝ≥0∞) localizedIntegerShiftSystem.μ) :
    ‖(interpolatedUnweightedAverage (p := (2 : ℝ≥0∞)) localizedIntegerShiftSystem c
          (localizedDyadicLeftTime k l m + localizedDyadicMesh k l)
          (by linarith [localizedDyadicLeftTime_pos k l m,
            localizedDyadicMesh_pos k l]) -
        interpolatedUnweightedAverage (p := (2 : ℝ≥0∞)) localizedIntegerShiftSystem c
          (localizedDyadicLeftTime k l m)
          (localizedDyadicLeftTime_pos k l m)) f‖ ≤
      4 * (2 : ℝ) ^ (-(l : ℤ)) * ‖f‖ := by
  have ht := localizedDyadicLeftTime_pos k l m
  have hmesh := localizedDyadicMesh_pos k l
  have hLipschitz := interpolatedAverageLipschitz (p := (2 : ℝ≥0∞)) localizedIntegerShiftSystem c
    (localizedDyadicLeftTime k l m) (localizedDyadicMesh k l) ht hmesh
  have hbase := localizedDyadicLeftTime_ge_base k l m
  have hratio : localizedDyadicMesh k l /
      localizedDyadicLeftTime k l m ≤ (2 : ℝ) ^ (-(l : ℤ)) := by
    rw [div_le_iff₀ ht]
    have hmeshScale := localizedDyadicMesh_le_scale k l
    have hbase := localizedDyadicLeftTime_ge_base k l m
    calc
      localizedDyadicMesh k l ≤ (2 : ℝ) ^ (-(l : ℤ)) * (2 : ℝ) ^ k := hmeshScale
      _ ≤ (2 : ℝ) ^ (-(l : ℤ)) * localizedDyadicLeftTime k l m :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
  calc
    _ ≤ ‖(interpolatedUnweightedAverage (p := (2 : ℝ≥0∞)) localizedIntegerShiftSystem c
            (localizedDyadicLeftTime k l m + localizedDyadicMesh k l)
            (by linarith [ht, hmesh]) -
          interpolatedUnweightedAverage (p := (2 : ℝ≥0∞)) localizedIntegerShiftSystem c
            (localizedDyadicLeftTime k l m) ht)‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (4 * localizedDyadicMesh k l /
          localizedDyadicLeftTime k l m) * ‖f‖ := by
      exact mul_le_mul_of_nonneg_right hLipschitz (norm_nonneg f)
    _ ≤ (4 * (2 : ℝ) ^ (-(l : ℤ))) * ‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      have hratio4 := mul_le_mul_of_nonneg_left hratio
        (by norm_num : 0 ≤ (4 : ℝ))
      simpa [div_eq_mul_inv, mul_assoc] using hratio4
    _ = _ := by ring

theorem localizedInterpolatedAverage_dyadicTimeIncrement_norm_le
    (c : ℝ) (k : ℤ) (l m : ℕ)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    ‖localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m + localizedDyadicMesh k l)
          (by linarith [localizedDyadicLeftTime_pos k l m,
            localizedDyadicMesh_pos k l]) f -
        localizedInterpolatedAverageL2 c (localizedDyadicLeftTime k l m)
          (localizedDyadicLeftTime_pos k l m) f‖ ≤
      4 * (2 : ℝ) ^ (-(l : ℤ)) * ‖f‖ := by
  have hmap :
      localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m + localizedDyadicMesh k l)
          (by linarith [localizedDyadicLeftTime_pos k l m,
            localizedDyadicMesh_pos k l]) f -
        localizedInterpolatedAverageL2 c (localizedDyadicLeftTime k l m)
          (localizedDyadicLeftTime_pos k l m) f =
      countLpToLp
        ((interpolatedUnweightedAverage (p := (2 : ℝ≥0∞))
            localizedIntegerShiftSystem c
            (localizedDyadicLeftTime k l m + localizedDyadicMesh k l)
            (by linarith [localizedDyadicLeftTime_pos k l m,
              localizedDyadicMesh_pos k l]) -
          interpolatedUnweightedAverage (p := (2 : ℝ≥0∞))
            localizedIntegerShiftSystem c (localizedDyadicLeftTime k l m)
            (localizedDyadicLeftTime_pos k l m)) (lpToCountLp f)) := by
    simp [localizedInterpolatedAverageL2, LinearMap.map_sub]
  rw [hmap]
  calc
    ‖countLpToLp
        ((interpolatedUnweightedAverage (p := (2 : ℝ≥0∞))
            localizedIntegerShiftSystem c
            (localizedDyadicLeftTime k l m + localizedDyadicMesh k l)
            (by linarith [localizedDyadicLeftTime_pos k l m,
              localizedDyadicMesh_pos k l]) -
          interpolatedUnweightedAverage (p := (2 : ℝ≥0∞))
            localizedIntegerShiftSystem c (localizedDyadicLeftTime k l m)
            (localizedDyadicLeftTime_pos k l m)) (lpToCountLp f))‖ =
        ‖(interpolatedUnweightedAverage (p := (2 : ℝ≥0∞))
            localizedIntegerShiftSystem c
            (localizedDyadicLeftTime k l m + localizedDyadicMesh k l)
            (by linarith [localizedDyadicLeftTime_pos k l m,
              localizedDyadicMesh_pos k l]) -
          interpolatedUnweightedAverage (p := (2 : ℝ≥0∞))
            localizedIntegerShiftSystem c (localizedDyadicLeftTime k l m)
            (localizedDyadicLeftTime_pos k l m)) (lpToCountLp f)‖ :=
      countLpToLpIsometry.norm_map _
    _ ≤ 4 * (2 : ℝ) ^ (-(l : ℤ)) *
        ‖(lpToCountLp f : Lp ℂ 2 (Measure.count : Measure ℤ))‖ :=
      interpolatedAverage_dyadicTimeIncrement_norm_le c k l m (lpToCountLp f)
    _ = 4 * (2 : ℝ) ^ (-(l : ℤ)) * ‖f‖ := by
      congr 1
      exact lpToCountLpIsometry.norm_map f

def localizedSignedFrequencyProjectionL2 (c : ℝ) (hc : 1 < c)
    (h : ℤ) (f : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  if 0 ≤ h then localizedFrequencyProjectionL2 c hc h.toNat f else 0

theorem localizedSignedFrequencyProjectionL2_of_nonneg
    (c : ℝ) (hc : 1 < c) (h : ℤ) (hh : 0 ≤ h)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    localizedSignedFrequencyProjectionL2 c hc h f =
      localizedFrequencyProjectionL2 c hc h.toNat f := by
  simp [localizedSignedFrequencyProjectionL2, hh]

theorem localizedSignedFrequencyProjectionL2_of_neg
    (c : ℝ) (hc : 1 < c) (h : ℤ) (hh : h < 0)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    localizedSignedFrequencyProjectionL2 c hc h f = 0 := by
  simp [localizedSignedFrequencyProjectionL2, not_le_of_gt hh]

def localizedIncrementSigma (c : ℝ) : ℝ :=
  min 1 (localizedProgressionDelta c)

private theorem localizedIncrementSigma_eq_progressionDelta
    {c : ℝ} (hc : 1 < c) :
    localizedIncrementSigma c = localizedProgressionDelta c := by
  unfold localizedIncrementSigma
  exact min_eq_right (localizedProgressionDelta_bounds hc).2.le

def localizedUnweightedIncrementConstant
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c) : ℝ :=
  max 4 (2 * max (localizedPositiveMultiplierConstant c)
    (localizedNegativeMultiplierConstant hc hcNon))

private theorem localizedDyadicBase_eq_nat (k : ℤ) (hk : 0 ≤ k) :
    (2 : ℝ) ^ k = ((2 ^ k.toNat : ℕ) : ℝ) := by
  rw [← Int.toNat_of_nonneg hk]
  norm_cast

theorem localizedDyadicRightTime_le_upper
    (k : ℤ) (l m : ℕ) (hm : m < 2 ^ l) :
    localizedDyadicLeftTime k l m + localizedDyadicMesh k l ≤
      (2 : ℝ) ^ (k + 1) := by
  have hpow : (2 : ℝ) ^ (k - (l : ℤ)) * (2 : ℝ) ^ (l : ℤ) =
      (2 : ℝ) ^ k := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  have hmcast : (m : ℝ) + 1 ≤ (2 : ℝ) ^ (l : ℤ) := by
    have hnat : m + 1 ≤ 2 ^ l := Nat.succ_le_of_lt hm
    exact_mod_cast hnat
  have hmeshNonneg : 0 ≤ (2 : ℝ) ^ (k - (l : ℤ)) := by positivity
  calc
    localizedDyadicLeftTime k l m + localizedDyadicMesh k l =
        (2 : ℝ) ^ k + (2 : ℝ) ^ (k - (l : ℤ)) * ((m : ℝ) + 1) := by
          simp [localizedDyadicLeftTime, localizedDyadicMesh]
          ring
    _ ≤ (2 : ℝ) ^ k + (2 : ℝ) ^ (k - (l : ℤ)) *
          (2 : ℝ) ^ (l : ℤ) := by
        nlinarith [mul_le_mul_of_nonneg_left hmcast hmeshNonneg]
    _ = (2 : ℝ) ^ k + (2 : ℝ) ^ k := by rw [hpow]
    _ = (2 : ℝ) ^ (k + 1) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring

private theorem localizedNatFloorInterpolationFraction_bounds {s : ℝ}
    (hs : 1 < s) :
    0 ≤ s - (⌊s⌋₊ : ℝ) ∧ s - (⌊s⌋₊ : ℝ) ≤ 1 := by
  have hfloor : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le (by linarith)
  have hnext : s < (⌊s⌋₊ : ℝ) + 1 := by
    exact_mod_cast (Nat.lt_floor_add_one s)
  constructor <;> linarith

private theorem localizedInterpolatedPositiveProjectionError_norm_le
    {c : ℝ} (hc : 1 < c) {j k : ℤ}
    (hj : 0 ≤ j) (hk : 0 ≤ k)
    (s : ℝ) (hslo : (2 : ℝ) ^ k ≤ s)
    (hshi : s ≤ (2 : ℝ) ^ (k + 1))
    (f : lp (fun _ : ℤ => ℂ) 2) :
    ‖localizedInterpolatedAverageL2 c s
        (lt_of_lt_of_le (zpow_pos (by norm_num) k) hslo)
        (localizedFrequencyProjectionL2 c hc (j + k).toNat f) -
      localizedFrequencyProjectionL2 c hc (j + k).toNat f‖ ≤
      localizedPositiveMultiplierConstant c *
        Real.rpow 2 (-localizedProgressionDelta c * (j : ℝ)) *
        ‖localizedFrequencyProjectionL2 c hc (j + k).toNat f‖ := by
  let P : lp (fun _ : ℤ => ℂ) 2 :=
    localizedFrequencyProjectionL2 c hc (j + k).toNat f
  have hC : 0 ≤ localizedPositiveMultiplierConstant c := by
    unfold localizedPositiveMultiplierConstant
    have hpi : 0 < Real.pi := Real.pi_pos
    have h3 : 0 < (3 : ℝ) ^ c := Real.rpow_pos_of_pos (by norm_num) c
    have h2 : 0 < Real.rpow 2 c := Real.rpow_pos_of_pos (by norm_num) c
    positivity
  have hpow : 0 ≤ Real.rpow 2
      (-localizedProgressionDelta c * (j : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hT : 0 ≤ localizedPositiveMultiplierConstant c *
      Real.rpow 2 (-localizedProgressionDelta c * (j : ℝ)) * ‖P‖ :=
    mul_nonneg (mul_nonneg hC hpow) (norm_nonneg _)
  by_cases hsone : s ≤ 1
  · have hs_eq : s = 1 := by
      have hbase : 1 ≤ (2 : ℝ) ^ k := by
        calc
          (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) := by norm_num
          _ ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hk
      linarith
    subst s
    have hbaseupper : (1 : ℝ) ≤ 3 * (2 : ℝ) ^ k := by
      have hbase : 1 ≤ (2 : ℝ) ^ k := by
        calc
          (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) := by norm_num
          _ ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hk
      nlinarith
    have hN := localizedIntegerAveragePositiveProjectionError_norm_le
      hc hj hk ⟨1, by norm_num⟩ (by simpa using hbaseupper) f
    have hAt : localizedInterpolatedAverageL2 c 1
        (lt_of_lt_of_le (zpow_pos (by norm_num) k) hslo)
        (localizedFrequencyProjectionL2 c hc (j + k).toNat f) =
        localizedIntegerUnweightedAverageL2 c ⟨1, by norm_num⟩
          (localizedFrequencyProjectionL2 c hc (j + k).toNat f) := by
      simpa using localizedInterpolatedAverageL2_at_integer c 1 (by norm_num)
        (localizedFrequencyProjectionL2 c hc (j + k).toNat f)
    rw [hAt]
    simpa [P] using hN
  · have hsone : 1 < s := lt_of_not_ge hsone
    let N : ℕ := ⌊s⌋₊
    let a : ℝ := s - (N : ℝ)
    have hNpos : 1 ≤ N := by
      dsimp [N]
      exact Nat.le_floor (by exact_mod_cast hsone.le)
    have hNfloor : (N : ℝ) ≤ s := by
      dsimp [N]
      exact Nat.floor_le (by linarith)
    have hkpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    have h2k : 1 ≤ (2 : ℝ) ^ k := by
      calc
        (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) := by norm_num
        _ ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hk
    have hNupper : (N : ℝ) ≤ 3 * (2 : ℝ) ^ k := by
      calc
        (N : ℝ) ≤ s := hNfloor
        _ ≤ (2 : ℝ) ^ (k + 1) := hshi
        _ = 2 * (2 : ℝ) ^ k := hkpow
        _ ≤ 3 * (2 : ℝ) ^ k := by nlinarith
    have hN1upper : (N + 1 : ℝ) ≤ 3 * (2 : ℝ) ^ k := by
      calc
        (N + 1 : ℝ) = (N : ℝ) + 1 := by norm_num
        _ ≤ s + 1 := by linarith [hNfloor]
        _ ≤ (2 : ℝ) ^ (k + 1) + 1 := by linarith [hshi]
        _ = 2 * (2 : ℝ) ^ k + 1 := by rw [hkpow]
        _ ≤ 3 * (2 : ℝ) ^ k := by nlinarith
    have hN := localizedIntegerAveragePositiveProjectionError_norm_le
      hc hj hk ⟨N, by omega⟩ (by simpa using hNupper) f
    have hN1 := localizedIntegerAveragePositiveProjectionError_norm_le
      hc hj hk ⟨N + 1, by omega⟩ (by simpa using hN1upper) f
    have hconv : localizedInterpolatedAverageL2 c s (by linarith)
        (localizedFrequencyProjectionL2 c hc (j + k).toNat f) =
        ((1 - a : ℝ) : ℂ) • localizedIntegerUnweightedAverageL2 c
            ⟨N, by omega⟩ P +
          (a : ℝ) • localizedIntegerUnweightedAverageL2 c
            ⟨N + 1, by omega⟩ P := by
      simpa [P, N, a] using
        localizedInterpolatedAverageL2_eq_convex_combo c s hsone
          (localizedFrequencyProjectionL2 c hc (j + k).toNat f)
    have hdecomp :
        ((1 - a : ℝ) : ℂ) • localizedIntegerUnweightedAverageL2 c
            ⟨N, by omega⟩ P +
          (a : ℝ) • localizedIntegerUnweightedAverageL2 c
            ⟨N + 1, by omega⟩ P - P =
        ((1 - a : ℝ) : ℂ) •
            (localizedIntegerUnweightedAverageL2 c ⟨N, by omega⟩ P - P) +
          (a : ℝ) •
            (localizedIntegerUnweightedAverageL2 c ⟨N + 1, by omega⟩ P - P) := by
      module
    have ha := localizedNatFloorInterpolationFraction_bounds hsone
    rw [hconv, hdecomp]
    calc
      ‖((1 - a : ℝ) : ℂ) •
            (localizedIntegerUnweightedAverageL2 c ⟨N, by omega⟩ P - P) +
          (a : ℝ) •
            (localizedIntegerUnweightedAverageL2 c ⟨N + 1, by omega⟩ P - P)‖ ≤
        ‖((1 - a : ℝ) : ℂ) •
            (localizedIntegerUnweightedAverageL2 c ⟨N, by omega⟩ P - P)‖ +
          ‖(a : ℝ) •
            (localizedIntegerUnweightedAverageL2 c ⟨N + 1, by omega⟩ P - P)‖ :=
          norm_add_le _ _
      _ = |1 - a| *
            ‖localizedIntegerUnweightedAverageL2 c ⟨N, by omega⟩ P - P‖ +
          |a| *
            ‖localizedIntegerUnweightedAverageL2 c ⟨N + 1, by omega⟩ P - P‖ := by
          rw [norm_smul, norm_smul]
          simp only [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |1 - a| *
            (localizedPositiveMultiplierConstant c *
              Real.rpow 2 (-localizedProgressionDelta c * (j : ℝ)) * ‖P‖) +
          |a| *
            (localizedPositiveMultiplierConstant c *
              Real.rpow 2 (-localizedProgressionDelta c * (j : ℝ)) * ‖P‖) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hN (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hN1 (abs_nonneg _))
      _ = localizedPositiveMultiplierConstant c *
            Real.rpow 2 (-localizedProgressionDelta c * (j : ℝ)) * ‖P‖ := by
          rw [abs_of_nonneg (by linarith [ha.2]), abs_of_nonneg ha.1]
          ring

private theorem localizedInterpolatedNegativeProjection_norm_le
    {c : ℝ} (hc : 1 < c) (hcNon : NonIntegral c) {j k : ℤ}
    (hj : j < 0) (hjk : 0 ≤ j + k) (hk : 0 ≤ k)
    (s : ℝ) (hslo : (2 : ℝ) ^ k ≤ s)
    (hshi : s ≤ (2 : ℝ) ^ (k + 1))
    (f : lp (fun _ : ℤ => ℂ) 2) :
    ‖localizedInterpolatedAverageL2 c s
        (lt_of_lt_of_le (zpow_pos (by norm_num) k) hslo)
        (localizedFrequencyProjectionL2 c hc (j + k).toNat f)‖ ≤
      localizedNegativeMultiplierConstant hc hcNon *
        Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) *
        ‖localizedFrequencyProjectionL2 c hc (j + k).toNat f‖ := by
  let P : lp (fun _ : ℤ => ℂ) 2 :=
    localizedFrequencyProjectionL2 c hc (j + k).toNat f
  have hC : 0 ≤ localizedNegativeMultiplierConstant hc hcNon := by
    unfold localizedNegativeMultiplierConstant
    have hCspec := localizedProgressionComparisonConstant_spec hc hcNon
    have hK : 0 ≤ continuousModelK c := by
      unfold continuousModelK
      positivity
    linarith [hCspec.1]
  have hpow : 0 ≤ Real.rpow 2
      (-localizedProgressionDelta c * (-(j : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hT : 0 ≤ localizedNegativeMultiplierConstant hc hcNon *
      Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) * ‖P‖ := by positivity
  have hkone : 1 ≤ k := by omega
  have hbase2 : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℤ) := by norm_num
      _ ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hkone
  have hsone : 1 < s := by linarith [hbase2, hslo]
  let N : ℕ := ⌊s⌋₊
  let a : ℝ := s - (N : ℝ)
  have hNpos : 1 ≤ N := by
    dsimp [N]
    exact Nat.le_floor (by exact_mod_cast hsone.le)
  have hNfloor : (N : ℝ) ≤ s := by
    dsimp [N]
    exact Nat.floor_le (by linarith)
  have hbaseNat : (2 : ℝ) ^ k = ((2 ^ k.toNat : ℕ) : ℝ) :=
    localizedDyadicBase_eq_nat k hk
  have hNlower : (2 : ℝ) ^ k ≤ (N : ℝ) := by
    calc
      (2 : ℝ) ^ k = ((2 ^ k.toNat : ℕ) : ℝ) := hbaseNat
      _ ≤ (N : ℝ) := by
        have hnat : 2 ^ k.toNat ≤ N := by
          dsimp [N]
          apply Nat.le_floor
          rw [← hbaseNat]
          exact hslo
        exact_mod_cast hnat
  have hN1lower : (2 : ℝ) ^ k ≤ (N + 1 : ℝ) := by
    calc
      (2 : ℝ) ^ k ≤ (N : ℝ) := hNlower
      _ ≤ (N + 1 : ℝ) := by norm_num
  have hN := localizedIntegerAverageNegativeProjection_norm_le
    hc hcNon hj hjk ⟨N, by omega⟩ (by simpa using hNlower) f
  have hN1 := localizedIntegerAverageNegativeProjection_norm_le
    hc hcNon hj hjk ⟨N + 1, by omega⟩ (by simpa using hN1lower) f
  have hconv : localizedInterpolatedAverageL2 c s (by linarith)
      (localizedFrequencyProjectionL2 c hc (j + k).toNat f) =
      ((1 - a : ℝ) : ℂ) • localizedIntegerUnweightedAverageL2 c
          ⟨N, by omega⟩ P +
        (a : ℝ) • localizedIntegerUnweightedAverageL2 c
          ⟨N + 1, by omega⟩ P := by
    simpa [P, N, a] using
      localizedInterpolatedAverageL2_eq_convex_combo c s hsone
        (localizedFrequencyProjectionL2 c hc (j + k).toNat f)
  have ha := localizedNatFloorInterpolationFraction_bounds hsone
  rw [hconv]
  calc
    ‖((1 - a : ℝ) : ℂ) • localizedIntegerUnweightedAverageL2 c
          ⟨N, by omega⟩ P +
        (a : ℝ) • localizedIntegerUnweightedAverageL2 c
          ⟨N + 1, by omega⟩ P‖ ≤
      ‖((1 - a : ℝ) : ℂ) • localizedIntegerUnweightedAverageL2 c
          ⟨N, by omega⟩ P‖ +
        ‖(a : ℝ) • localizedIntegerUnweightedAverageL2 c
          ⟨N + 1, by omega⟩ P‖ := norm_add_le _ _
    _ = |1 - a| * ‖localizedIntegerUnweightedAverageL2 c ⟨N, by omega⟩ P‖ +
        |a| * ‖localizedIntegerUnweightedAverageL2 c ⟨N + 1, by omega⟩ P‖ := by
      rw [norm_smul, norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |1 - a| *
          (localizedNegativeMultiplierConstant hc hcNon *
            Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) * ‖P‖) +
        |a| *
          (localizedNegativeMultiplierConstant hc hcNon *
            Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) * ‖P‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hN (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hN1 (abs_nonneg _))
    _ = localizedNegativeMultiplierConstant hc hcNon *
          Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) * ‖P‖ := by
      rw [abs_of_nonneg (by linarith [ha.2]), abs_of_nonneg ha.1]
      ring

end

end FractionalPrimes.Literature.Harmonic

namespace FractionalPrimes.Literature.Harmonic

/-- The exact localized dyadic increment bound from `ha:localized`. The
projection at a negative source index is zero, and all dyadic cells, including
those with `l > k`, use the same endpoint convention as the paper. -/
theorem localizedUnweightedIncrement_core
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j k : ℤ) (l m : ℕ) (hm : m < 2 ^ l)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    ‖localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m + localizedDyadicMesh k l)
          (localizedDyadicRightTime_pos k l m)
          (localizedSignedFrequencyProjectionL2 c hc (j + k) f) -
        localizedInterpolatedAverageL2 c (localizedDyadicLeftTime k l m)
          (localizedDyadicLeftTime_pos k l m)
          (localizedSignedFrequencyProjectionL2 c hc (j + k) f)‖ ≤
      localizedUnweightedIncrementConstant c hc hcNon *
        min ((2 : ℝ) ^ (-(l : ℤ)))
          (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|)) *
        ‖localizedSignedFrequencyProjectionL2 c hc (j + k) f‖ := by
  let P : lp (fun _ : ℤ => ℂ) 2 :=
    localizedSignedFrequencyProjectionL2 c hc (j + k) f
  let t : ℝ := localizedDyadicLeftTime k l m
  let u : ℝ := t + localizedDyadicMesh k l
  have htPos : 0 < t := by simpa [t] using localizedDyadicLeftTime_pos k l m
  have huPos : 0 < u := by simpa [u, t] using localizedDyadicRightTime_pos k l m
  change ‖localizedInterpolatedAverageL2 c u huPos P -
      localizedInterpolatedAverageL2 c t htPos P‖ ≤
    localizedUnweightedIncrementConstant c hc hcNon *
      min ((2 : ℝ) ^ (-(l : ℤ)))
        (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|)) * ‖P‖
  let D : ℝ := localizedUnweightedIncrementConstant c hc hcNon
  have hD4 : 4 ≤ D := by
    dsimp [D, localizedUnweightedIncrementConstant]
    exact le_max_left _ _
  have hDpos : 2 * localizedPositiveMultiplierConstant c ≤ D := by
    dsimp [D, localizedUnweightedIncrementConstant]
    calc
      2 * localizedPositiveMultiplierConstant c ≤
          2 * max (localizedPositiveMultiplierConstant c)
            (localizedNegativeMultiplierConstant hc hcNon) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
      _ ≤ max 4 (2 * max (localizedPositiveMultiplierConstant c)
          (localizedNegativeMultiplierConstant hc hcNon)) := le_max_right _ _
  have hDneg : 2 * localizedNegativeMultiplierConstant hc hcNon ≤ D := by
    dsimp [D, localizedUnweightedIncrementConstant]
    calc
      2 * localizedNegativeMultiplierConstant hc hcNon ≤
          2 * max (localizedPositiveMultiplierConstant c)
            (localizedNegativeMultiplierConstant hc hcNon) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
      _ ≤ max 4 (2 * max (localizedPositiveMultiplierConstant c)
          (localizedNegativeMultiplierConstant hc hcNon)) := le_max_right _ _
  have hDnonneg : 0 ≤ D := le_trans (by norm_num : 0 ≤ (4 : ℝ)) hD4
  have hqtime : 0 ≤ (2 : ℝ) ^ (-(l : ℤ)) := zpow_nonneg (by norm_num) _
  have hqfreq : 0 ≤ Real.rpow 2
      (-localizedIncrementSigma c * |(j : ℝ)|) := Real.rpow_nonneg (by norm_num) _
  have hnormP : 0 ≤ ‖P‖ := norm_nonneg _
  have htargetNonneg : 0 ≤ D *
      min ((2 : ℝ) ^ (-(l : ℤ)))
        (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|)) * ‖P‖ := by
    positivity
  by_cases hkneg : k < 0
  · have huUpper := localizedDyadicRightTime_le_upper k l m hm
    have htop : (2 : ℝ) ^ (k + 1) ≤ 1 := by
      calc
        (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (0 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 1 := by norm_num
    have huLeOne : u ≤ 1 := by
      dsimp [u, t]
      exact huUpper.trans htop
    have hleftLeRight : t ≤ u := by
      dsimp [u]
      exact le_add_of_nonneg_right (le_of_lt (localizedDyadicMesh_pos k l))
    have htLeOne : t ≤ 1 := hleftLeRight.trans huLeOne
    have hsame : localizedInterpolatedAverageL2 c u huPos P =
        localizedInterpolatedAverageL2 c t htPos P := by
      simp [localizedInterpolatedAverageL2, interpolatedUnweightedAverage,
        huLeOne, htLeOne]
    rw [hsame]
    simpa using htargetNonneg
  · have hk : 0 ≤ k := le_of_not_gt hkneg
    by_cases hjkneg : j + k < 0
    · have hPzero : P = 0 := by
        dsimp [P]
        exact localizedSignedFrequencyProjectionL2_of_neg c hc (j + k)
          hjkneg f
      rw [hPzero]
      simp [localizedInterpolatedAverageL2]
    · have hjk : 0 ≤ j + k := le_of_not_gt hjkneg
      have hbaseT : (2 : ℝ) ^ k ≤ t := by
        dsimp [t]
        exact localizedDyadicLeftTime_ge_base k l m
      have hleftLeRight : t ≤ u := by
        dsimp [u]
        exact le_add_of_nonneg_right (le_of_lt (localizedDyadicMesh_pos k l))
      have huUpper : u ≤ (2 : ℝ) ^ (k + 1) := by
        dsimp [u, t]
        exact localizedDyadicRightTime_le_upper k l m hm
      have htUpper : t ≤ (2 : ℝ) ^ (k + 1) := hleftLeRight.trans huUpper
      have hbaseU : (2 : ℝ) ^ k ≤ u := hbaseT.trans hleftLeRight
      have htime := localizedInterpolatedAverage_dyadicTimeIncrement_norm_le
        c k l m P
      have htime' :
          ‖localizedInterpolatedAverageL2 c u huPos P -
            localizedInterpolatedAverageL2 c t htPos P‖ ≤
            4 * (2 : ℝ) ^ (-(l : ℤ)) * ‖P‖ := by
        simpa [t, u] using htime
      have htimeD :
          ‖localizedInterpolatedAverageL2 c u huPos P -
            localizedInterpolatedAverageL2 c t htPos P‖ ≤
            D * (2 : ℝ) ^ (-(l : ℤ)) * ‖P‖ := by
        calc
          _ ≤ 4 * (2 : ℝ) ^ (-(l : ℤ)) * ‖P‖ := htime'
          _ = 4 * ((2 : ℝ) ^ (-(l : ℤ)) * ‖P‖) := by ring
          _ ≤ D * ((2 : ℝ) ^ (-(l : ℤ)) * ‖P‖) :=
            mul_le_mul_of_nonneg_right hD4 (mul_nonneg hqtime hnormP)
          _ = _ := by ring
      by_cases hjnonneg : 0 ≤ j
      · have hposT := localizedInterpolatedPositiveProjectionError_norm_le
          hc hjnonneg hk t hbaseT htUpper f
        have hposU := localizedInterpolatedPositiveProjectionError_norm_le
          hc hjnonneg hk u hbaseU huUpper f
        have hposT' :
            ‖localizedInterpolatedAverageL2 c t htPos P - P‖ ≤
              localizedPositiveMultiplierConstant c *
                Real.rpow 2 (-localizedProgressionDelta c * (j : ℝ)) * ‖P‖ := by
          simpa [P, localizedSignedFrequencyProjectionL2, hjk] using hposT
        have hposU' :
            ‖localizedInterpolatedAverageL2 c u huPos P - P‖ ≤
              localizedPositiveMultiplierConstant c *
                Real.rpow 2 (-localizedProgressionDelta c * (j : ℝ)) * ‖P‖ := by
          simpa [P, localizedSignedFrequencyProjectionL2, hjk] using hposU
        have hjR : 0 ≤ (j : ℝ) := by exact_mod_cast hjnonneg
        have hpower :
            Real.rpow 2 (-localizedProgressionDelta c * (j : ℝ)) =
              Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|) := by
          rw [localizedIncrementSigma_eq_progressionDelta hc,
            abs_of_nonneg hjR]
        have hfreqD :
            ‖localizedInterpolatedAverageL2 c u huPos P -
              localizedInterpolatedAverageL2 c t htPos P‖ ≤
              D * Real.rpow 2
                (-localizedIncrementSigma c * |(j : ℝ)|) * ‖P‖ := by
          calc
            _ = ‖(localizedInterpolatedAverageL2 c u huPos P - P) -
                (localizedInterpolatedAverageL2 c t htPos P - P)‖ := by
                  congr 1 <;> abel
            _ ≤ ‖localizedInterpolatedAverageL2 c u huPos P - P‖ +
                ‖localizedInterpolatedAverageL2 c t htPos P - P‖ :=
                  norm_sub_le _ _
            _ ≤ 2 * (localizedPositiveMultiplierConstant c *
                Real.rpow 2 (-localizedProgressionDelta c * (j : ℝ)) * ‖P‖) := by
                  calc
                    _ ≤ (localizedPositiveMultiplierConstant c *
                        Real.rpow 2 (-localizedProgressionDelta c * (j : ℝ)) * ‖P‖) +
                        (localizedPositiveMultiplierConstant c *
                          Real.rpow 2 (-localizedProgressionDelta c * (j : ℝ)) * ‖P‖) :=
                        add_le_add hposU' hposT'
                    _ = _ := by ring
            _ = (2 * localizedPositiveMultiplierConstant c) *
                (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|) * ‖P‖) := by
                  rw [hpower]
                  ring
            _ ≤ D * (Real.rpow 2
                (-localizedIncrementSigma c * |(j : ℝ)|) * ‖P‖) :=
                  mul_le_mul_of_nonneg_right hDpos (mul_nonneg hqfreq hnormP)
            _ = _ := by ring
        have hfreqD' :
            ‖localizedInterpolatedAverageL2 c u (by positivity) P -
              localizedInterpolatedAverageL2 c t (by positivity) P‖ ≤
              D * Real.rpow 2
                (-localizedIncrementSigma c * |(j : ℝ)|) * ‖P‖ := hfreqD
        rcases le_total ((2 : ℝ) ^ (-(l : ℤ)))
            (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|)) with hle | hle
        · rw [min_eq_left hle]
          simpa [D] using htimeD
        · rw [min_eq_right hle]
          simpa [D] using hfreqD'
      · have hjneg : j < 0 := lt_of_not_ge hjnonneg
        have hnegT := localizedInterpolatedNegativeProjection_norm_le
          hc hcNon hjneg hjk hk t hbaseT htUpper f
        have hnegU := localizedInterpolatedNegativeProjection_norm_le
          hc hcNon hjneg hjk hk u hbaseU huUpper f
        have hnegT' :
            ‖localizedInterpolatedAverageL2 c t htPos P‖ ≤
              localizedNegativeMultiplierConstant hc hcNon *
                Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) * ‖P‖ := by
          simpa [P, localizedSignedFrequencyProjectionL2, hjk] using hnegT
        have hnegU' :
            ‖localizedInterpolatedAverageL2 c u huPos P‖ ≤
              localizedNegativeMultiplierConstant hc hcNon *
                Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) * ‖P‖ := by
          simpa [P, localizedSignedFrequencyProjectionL2, hjk] using hnegU
        have hjR : (j : ℝ) < 0 := by exact_mod_cast hjneg
        have hpower :
            Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) =
              Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|) := by
          rw [localizedIncrementSigma_eq_progressionDelta hc,
            abs_of_neg hjR]
        have hfreqD :
            ‖localizedInterpolatedAverageL2 c u huPos P -
              localizedInterpolatedAverageL2 c t htPos P‖ ≤
              D * Real.rpow 2
                (-localizedIncrementSigma c * |(j : ℝ)|) * ‖P‖ := by
          calc
            _ ≤ ‖localizedInterpolatedAverageL2 c u huPos P‖ +
                ‖localizedInterpolatedAverageL2 c t htPos P‖ :=
                  norm_sub_le _ _
            _ ≤ 2 * (localizedNegativeMultiplierConstant hc hcNon *
                Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) * ‖P‖) := by
                  calc
                    _ ≤ (localizedNegativeMultiplierConstant hc hcNon *
                        Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) * ‖P‖) +
                        (localizedNegativeMultiplierConstant hc hcNon *
                          Real.rpow 2 (-localizedProgressionDelta c * (-(j : ℝ))) * ‖P‖) :=
                        add_le_add hnegU' hnegT'
                    _ = _ := by ring
            _ = (2 * localizedNegativeMultiplierConstant hc hcNon) *
                (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|) * ‖P‖) := by
                  rw [hpower]
                  ring
            _ ≤ D * (Real.rpow 2
                (-localizedIncrementSigma c * |(j : ℝ)|) * ‖P‖) :=
                  mul_le_mul_of_nonneg_right hDneg (mul_nonneg hqfreq hnormP)
            _ = _ := by ring
        rcases le_total ((2 : ℝ) ^ (-(l : ℤ)))
            (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|)) with hle | hle
        · rw [min_eq_left hle]
          simpa [D] using htimeD
        · rw [min_eq_right hle]
          simpa [D] using hfreqD

end FractionalPrimes.Literature.Harmonic

namespace FractionalPrimes

open Literature.Harmonic

/-- The paper-facing `ha:localized` theorem. -/
theorem localizedUnweightedIncrement
    (c : ℝ) (hc : 1 < c) (hcNon : NonIntegral c)
    (j k : ℤ) (l m : ℕ) (hm : m < 2 ^ l)
    (f : lp (fun _ : ℤ => ℂ) 2) :
    ‖localizedInterpolatedAverageL2 c
          (localizedDyadicLeftTime k l m + localizedDyadicMesh k l)
          (localizedDyadicRightTime_pos k l m)
          (localizedSignedFrequencyProjectionL2 c hc (j + k) f) -
        localizedInterpolatedAverageL2 c (localizedDyadicLeftTime k l m)
          (localizedDyadicLeftTime_pos k l m)
          (localizedSignedFrequencyProjectionL2 c hc (j + k) f)‖ ≤
      localizedUnweightedIncrementConstant c hc hcNon *
        min ((2 : ℝ) ^ (-(l : ℤ)))
          (Real.rpow 2 (-localizedIncrementSigma c * |(j : ℝ)|)) *
        ‖localizedSignedFrequencyProjectionL2 c hc (j + k) f‖ := by
  exact Literature.Harmonic.localizedUnweightedIncrement_core
    c hc hcNon j k l m hm f

end FractionalPrimes

end
