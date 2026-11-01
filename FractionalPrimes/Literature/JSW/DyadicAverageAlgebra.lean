module

public import FractionalPrimes.Literature.JSW.DyadicAverage
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Algebraic facts for dyadic averages

This module starts the structural part of `lj:dyadic-properties` with the
pointwise consequence of the half-open cell convention: `E_m f` is constant
on every cell of `D_m`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace FractionalPrimes.Literature.JSW

noncomputable section

private theorem dyadicScale_pos' (m : ℤ) : 0 < (2 : ℝ) ^ m :=
  zpow_pos (by norm_num) m

/-- Membership in a dyadic cell identifies the floor-selected cell index. -/
theorem dyadicIntervalIndex_eq_of_mem {m j : ℤ} {x : ℝ}
    (hx : x ∈ dyadicInterval m j) :
    dyadicIntervalIndex m x = j := by
  have hs : 0 < (2 : ℝ) ^ m := dyadicScale_pos' m
  rw [dyadicInterval, Set.mem_Ico] at hx
  change Int.floor (x / (2 : ℝ) ^ m) = j
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hs).2
    exact hx.1
  · apply (div_lt_iff₀ hs).2
    simpa [Int.cast_add, Int.cast_one] using hx.2

/-- The Lebesgue measure of a scale-`m` dyadic cell is exactly `2^m`. -/
theorem dyadicInterval_volume_real (m j : ℤ) :
    volume.real (dyadicInterval m j) = (2 : ℝ) ^ m := by
  rw [MeasureTheory.Measure.real_def, dyadicInterval, Real.volume_Ico]
  have hlen : (((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) -
      (j : ℝ) * (2 : ℝ) ^ m = (2 : ℝ) ^ m := by
    push_cast
    ring
  rw [hlen, ENNReal.toReal_ofReal (le_of_lt (dyadicScale_pos' m))]

/-- The averaging operator is constant on each half-open cell at its scale. -/
theorem dyadicAverage_eq_of_mem_same_cell (m j : ℤ) (f : ℝ → ℂ)
    {x y : ℝ} (hx : x ∈ dyadicInterval m j) (hy : y ∈ dyadicInterval m j) :
    dyadicAverage m f x = dyadicAverage m f y := by
  have hix := dyadicIntervalIndex_eq_of_mem hx
  have hiy := dyadicIntervalIndex_eq_of_mem hy
  unfold dyadicAverage
  rw [hix, hiy]

private theorem dyadicInterval_lower_mem (m j : ℤ) :
    (j : ℝ) * (2 : ℝ) ^ m ∈ dyadicInterval m j := by
  rw [dyadicInterval, Set.mem_Ico]
  constructor
  · exact le_rfl
  · have hs : 0 < (2 : ℝ) ^ m := dyadicScale_pos' m
    have hlen : (((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) -
        (j : ℝ) * (2 : ℝ) ^ m = (2 : ℝ) ^ m := by
      push_cast
      ring
    linarith

/-- The averaging operator is measurable because it is constant on each cell
of its countable measurable dyadic partition. -/
theorem measurable_dyadicAverage (m : ℤ) (f : ℝ → ℂ) :
    Measurable (dyadicAverage m f) := by
  classical
  let Q : ℤ → Set ℝ := fun j => dyadicInterval m j
  let c : (j : ℤ) → {x : ℝ // x ∈ Q j} → ℂ :=
    fun j _ => dyadicAverage m f ((j : ℝ) * (2 : ℝ) ^ m)
  have hcover : ⋃ j, Q j = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨dyadicIntervalIndex m x,
      by simpa [Q] using mem_dyadicIntervalIndex m x⟩
  have hQ : ∀ j, MeasurableSet (Q j) := by
    intro j
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hcompat : ∀ i j x (hxi : x ∈ Q i) (hxj : x ∈ Q j),
      c i ⟨x, hxi⟩ = c j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    have heq : i = j := by
      calc
        i = dyadicIntervalIndex m x :=
          (dyadicIntervalIndex_eq_of_mem (by simpa [Q] using hxi)).symm
        _ = j := dyadicIntervalIndex_eq_of_mem (by simpa [Q] using hxj)
    subst j
    rfl
  have hc : ∀ j, Measurable (c j) := by
    intro j
    exact measurable_const
  have hcover_meas : Measurable (Set.liftCover Q c hcompat hcover) :=
    measurable_liftCover Q hQ c hc hcompat hcover
  have heq : dyadicAverage m f = Set.liftCover Q c hcompat hcover := by
    funext x
    let j := dyadicIntervalIndex m x
    have hx : x ∈ Q j := by
      simpa [Q, j] using mem_dyadicIntervalIndex m x
    have ha : (j : ℝ) * (2 : ℝ) ^ m ∈ Q j := by
      simpa [Q] using dyadicInterval_lower_mem m j
    rw [Set.liftCover_of_mem hx]
    exact dyadicAverage_eq_of_mem_same_cell m j f
      (by simpa [Q, j] using mem_dyadicIntervalIndex m x)
      (by simpa [Q] using ha)
  rw [heq]
  exact hcover_meas

/-- Integrating `E_m f` over a scale-`m` cell recovers the integral of `f`.
The identity is totalized for arbitrary inputs and in particular applies to
locally integrable functions. -/
theorem integral_dyadicAverage_eq_integral (m j : ℤ) (f : ℝ → ℂ) :
    ∫ x in dyadicInterval m j, dyadicAverage m f x ∂volume =
      ∫ x in dyadicInterval m j, f x ∂volume := by
  let s : ℝ := (2 : ℝ) ^ m
  let a : ℝ := (j : ℝ) * s
  have hs : 0 < s := by dsimp [s]; exact dyadicScale_pos' m
  have hlen : (((j + 1 : ℤ) : ℝ) * s) - (j : ℝ) * s = s := by
    push_cast
    dsimp [a, s]
    ring
  have hmem : a ∈ dyadicInterval m j := by
    rw [dyadicInterval, Set.mem_Ico]
    constructor
    · dsimp [a, s]
      exact le_rfl
    · dsimp [a]
      have hlen' : (((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) -
          (j : ℝ) * (2 : ℝ) ^ m = (2 : ℝ) ^ m := by
        push_cast
        ring
      have hs' : 0 < (2 : ℝ) ^ m := dyadicScale_pos' m
      linarith
  have hvol : volume.real (dyadicInterval m j) = s := by
    simpa [s] using dyadicInterval_volume_real m j
  have hindex : dyadicIntervalIndex m a = j := dyadicIntervalIndex_eq_of_mem hmem
  have hvalue : dyadicAverage m f a =
      s⁻¹ • ∫ y in dyadicInterval m j, f y ∂volume := by
    simp [dyadicAverage, hindex, a, s]
  have hconstant : ∀ x ∈ dyadicInterval m j,
      dyadicAverage m f x = dyadicAverage m f a := by
    intro x hx
    exact dyadicAverage_eq_of_mem_same_cell m j f hx hmem
  calc
    ∫ x in dyadicInterval m j, dyadicAverage m f x ∂volume =
        ∫ x in dyadicInterval m j, (fun _ : ℝ => dyadicAverage m f a) x ∂volume :=
      MeasureTheory.setIntegral_congr_fun
        (by dsimp [dyadicInterval]; exact measurableSet_Ico) hconstant
    _ = volume.real (dyadicInterval m j) • dyadicAverage m f a := by
      rw [MeasureTheory.setIntegral_const]
    _ = ∫ x in dyadicInterval m j, f x ∂volume := by
      rw [hvol, hvalue, smul_smul]
      simp [s, hs.ne']

/-- The norm of a dyadic average is bounded by the average of the input norm. -/
theorem norm_dyadicAverage_le_average_norm {f : ℝ → ℂ}
    (m : ℤ) (x : ℝ) :
    ‖dyadicAverage m f x‖ ≤
      ((2 : ℝ) ^ m)⁻¹ *
        ∫ y in dyadicInterval m (dyadicIntervalIndex m x), ‖f y‖ ∂volume := by
  have hs : 0 < (2 : ℝ) ^ m := dyadicScale_pos' m
  have hinv : 0 ≤ ((2 : ℝ) ^ m)⁻¹ := inv_nonneg.mpr hs.le
  change ‖((2 : ℝ) ^ m)⁻¹ •
      ∫ y in dyadicInterval m (dyadicIntervalIndex m x), f y ∂volume‖ ≤ _
  calc
    _ = ‖((2 : ℝ) ^ m)⁻¹‖ *
        ‖∫ y in dyadicInterval m (dyadicIntervalIndex m x), f y ∂volume‖ := norm_smul _ _
    _ = ((2 : ℝ) ^ m)⁻¹ *
        ‖∫ y in dyadicInterval m (dyadicIntervalIndex m x), f y ∂volume‖ := by
      rw [Real.norm_of_nonneg hinv]
    _ ≤ ((2 : ℝ) ^ m)⁻¹ *
        ∫ y in dyadicInterval m (dyadicIntervalIndex m x), ‖f y‖ ∂volume :=
      mul_le_mul_of_nonneg_left
        (MeasureTheory.norm_integral_le_integral_norm (μ :=
          volume.restrict (dyadicInterval m (dyadicIntervalIndex m x))) f) hinv

private theorem integrableOn_dyadicInterval_of_locallyIntegrable
    {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) (m j : ℤ) :
    IntegrableOn f (dyadicInterval m j) volume := by
  let a := (j : ℝ) * (2 : ℝ) ^ m
  let b := ((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m
  have hsubset : dyadicInterval m j ⊆ Set.Icc a b := by
    intro x hx
    rw [dyadicInterval, Set.mem_Ico] at hx
    constructor
    · simpa [a] using hx.1
    · simpa [b] using hx.2.le
  have hlocal : LocallyIntegrableOn f (Set.Icc a b) volume :=
    hf.locallyIntegrableOn (Set.Icc a b)
  exact (hlocal.integrableOn_isCompact isCompact_Icc).mono_set hsubset

/-- If the input varies by at most `ε` on the cell containing `x`, then its
dyadic average at `x` differs from `f x` by at most `ε`. -/
theorem norm_dyadicAverage_sub_le_of_cell_bound {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (m : ℤ) (x ε : ℝ)
    (hbound : ∀ y ∈ dyadicInterval m (dyadicIntervalIndex m x),
      ‖f y - f x‖ ≤ ε) :
    ‖dyadicAverage m f x - f x‖ ≤ ε := by
  let j := dyadicIntervalIndex m x
  let Q := dyadicInterval m j
  let s := (2 : ℝ) ^ m
  have hs : 0 < s := by dsimp [s]; exact dyadicScale_pos' m
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hx : x ∈ Q := by simpa [Q, j] using mem_dyadicIntervalIndex m x
  have hfinite : volume Q ≠ ⊤ := by
    dsimp [Q, dyadicInterval]
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have hvolume : volume.real Q = s := by
    simpa [Q, j, s] using dyadicInterval_volume_real m j
  have hfQ : Integrable (fun y : ℝ => f y) (volume.restrict Q) := by
    change IntegrableOn f Q volume
    exact integrableOn_dyadicInterval_of_locallyIntegrable hf m j
  have hconstComplex : Integrable (fun _ : ℝ => f x)
      (volume.restrict Q) := by
    change IntegrableOn (fun _ : ℝ => f x) Q volume
    exact MeasureTheory.integrableOn_const hfinite
  have hdiff : Integrable (fun y : ℝ => f y - f x)
      (volume.restrict Q) := hfQ.sub hconstComplex
  have hIntSub :
      ∫ y in Q, (f y - f x) ∂volume =
        (∫ y in Q, f y ∂volume) - volume.real Q • f x := by
    calc
      ∫ y in Q, (f y - f x) ∂volume =
          ∫ y, (f y - f x) ∂(volume.restrict Q) := rfl
      _ = (∫ y, f y ∂(volume.restrict Q)) -
          ∫ y, f x ∂(volume.restrict Q) := integral_sub hfQ hconstComplex
      _ = (∫ y in Q, f y ∂volume) - volume.real Q • f x := by
        rw [MeasureTheory.setIntegral_const]
  have hinv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs.ne'
  have hform : dyadicAverage m f x - f x =
      s⁻¹ • ∫ y in Q, (f y - f x) ∂volume := by
    unfold dyadicAverage
    rw [dyadicIntervalIndex_eq_of_mem hx]
    change s⁻¹ • ∫ y in Q, f y ∂volume - f x =
      s⁻¹ • ∫ y in Q, (f y - f x) ∂volume
    rw [hIntSub, hvolume, smul_sub, smul_smul]
    simp [hinv]
  have hinv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hboundInt :
      ∫ y in Q, ‖f y - f x‖ ∂volume ≤ volume.real Q * ε := by
    have hnormInt : Integrable (fun y : ℝ => ‖f y - f x‖)
        (volume.restrict Q) := hdiff.norm
    have hconst : Integrable (fun _ : ℝ => ε) (volume.restrict Q) := by
      change IntegrableOn (fun _ : ℝ => ε) Q volume
      exact MeasureTheory.integrableOn_const hfinite
    have hae : (fun y : ℝ => ‖f y - f x‖) ≤ᵐ[volume.restrict Q]
        (fun _ : ℝ => ε) := by
      filter_upwards [MeasureTheory.ae_restrict_mem hQ] with y hy
      exact hbound y (by simpa [Q, j] using hy)
    have h := integral_mono_ae hnormInt hconst hae
    change (∫ y in Q, ‖f y - f x‖ ∂volume) ≤
      ∫ y in Q, (fun _ : ℝ => ε) y ∂volume at h
    rw [MeasureTheory.setIntegral_const] at h
    simpa [smul_eq_mul] using h
  calc
    ‖dyadicAverage m f x - f x‖ =
        ‖s⁻¹ • ∫ y in Q, (f y - f x) ∂volume‖ := by rw [hform]
    _ = s⁻¹ * ‖∫ y in Q, (f y - f x) ∂volume‖ := by
      rw [norm_smul, Real.norm_of_nonneg hinv_nonneg]
    _ ≤ s⁻¹ * ∫ y in Q, ‖f y - f x‖ ∂volume := by
      gcongr
      exact MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict Q) (fun y : ℝ => f y - f x)
    _ ≤ s⁻¹ * (volume.real Q * ε) :=
      mul_le_mul_of_nonneg_left hboundInt hinv_nonneg
    _ = ε := by rw [hvolume]; field_simp [hs.ne']

/-- Fine-scale dyadic averages converge pointwise for uniformly continuous
inputs. The estimate is independent of any maximal theorem. -/
theorem dyadicAverage_tendsto_atBot_of_uniformContinuous {f : ℝ → ℂ}
    (hf : UniformContinuous f) (x : ℝ) :
    Tendsto (fun m : ℤ => dyadicAverage m f x) atBot (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ :=
    (Metric.uniformContinuous_iff.mp hf) (ε / 2) (by linarith)
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmallEventually : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ^ n < δ := by
    filter_upwards [(Metric.tendsto_nhds.mp hpow) δ hδ] with n hn
    simpa [Real.dist_eq, Real.norm_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n)]
      using hn
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hsmallEventually)
  have hscaleN : (2 : ℝ) ^ (-(N : ℤ)) = (1 / 2 : ℝ) ^ N := by
    simp [zpow_neg, zpow_natCast, one_div, inv_pow]
  have hsmall : (2 : ℝ) ^ (-(N : ℤ)) < δ := by
    rw [hscaleN]
    exact hN N le_rfl
  have hloc : LocallyIntegrable f volume := hf.continuous.locallyIntegrable
  have hevent : ∀ᶠ m : ℤ in atBot, m ≤ -(N : ℤ) :=
    eventually_atBot.2 ⟨-(N : ℤ), fun m hm => hm⟩
  filter_upwards [hevent] with m hm
  have hscale : (2 : ℝ) ^ m < δ := by
    exact (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm).trans_lt hsmall
  have hx : x ∈ dyadicInterval m (dyadicIntervalIndex m x) :=
    mem_dyadicIntervalIndex m x
  have hbound : ∀ y ∈ dyadicInterval m (dyadicIntervalIndex m x),
      ‖f y - f x‖ ≤ ε / 2 := by
    intro y hy
    have hs : 0 < (2 : ℝ) ^ m := dyadicScale_pos' m
    have hj := dyadicIntervalIndex_eq_of_mem hx
    rw [dyadicInterval, Set.mem_Ico] at hy hx
    have hwidth :
        (((dyadicIntervalIndex m x + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) -
          (dyadicIntervalIndex m x : ℝ) * (2 : ℝ) ^ m = (2 : ℝ) ^ m := by
      push_cast
      ring
    have hdist : dist y x < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · have hylo : (dyadicIntervalIndex m x : ℝ) * (2 : ℝ) ^ m ≤ y := hy.1
        have hxhi : x < (((dyadicIntervalIndex m x + 1 : ℤ) : ℝ) *
            (2 : ℝ) ^ m) := hx.2
        linarith
      · have hyhi : y < (((dyadicIntervalIndex m x + 1 : ℤ) : ℝ) *
            (2 : ℝ) ^ m) := hy.2
        have hxlo : (dyadicIntervalIndex m x : ℝ) * (2 : ℝ) ^ m ≤ x := hx.1
        linarith
    have hdistout := hmod (a := y) (b := x) hdist
    have hnorm : ‖f y - f x‖ < ε / 2 := by
      simpa [dist_eq_norm] using hdistout
    exact hnorm.le
  have hpoint := norm_dyadicAverage_sub_le_of_cell_bound hloc m x (ε / 2) hbound
  have hdistout : dist (dyadicAverage m f x) (f x) < ε := by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hpoint (by linarith)
  exact hdistout

/-- A locally integrable input bounded almost everywhere by `C` has every
dyadic average bounded by the same `C`. -/
theorem norm_dyadicAverage_le_of_ae_bound {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (m : ℤ) (x C : ℝ)
    (hbound : ∀ᵐ y ∂volume, ‖f y‖ ≤ C) :
    ‖dyadicAverage m f x‖ ≤ C := by
  let Q := dyadicInterval m (dyadicIntervalIndex m x)
  let s := (2 : ℝ) ^ m
  have hs : 0 < s := by dsimp [s]; exact dyadicScale_pos' m
  have hfcell : IntegrableOn (fun y : ℝ => ‖f y‖) Q volume := by
    have h := integrableOn_dyadicInterval_of_locallyIntegrable hf m
      (dyadicIntervalIndex m x)
    change Integrable (fun y : ℝ => ‖f y‖) (volume.restrict Q)
    exact h.norm
  have hfinite : volume Q ≠ ⊤ := by
    dsimp [Q, dyadicInterval]
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have hconst : IntegrableOn (fun _ : ℝ => C) Q volume :=
    MeasureTheory.integrableOn_const hfinite
  have hboundQ : ∀ᵐ y ∂volume.restrict Q, ‖f y‖ ≤ C :=
    MeasureTheory.ae_restrict_of_ae hbound
  have hint : ∫ y in Q, ‖f y‖ ∂volume ≤ s * C := by
    have hmono :
        ∫ y in Q, ‖f y‖ ∂volume ≤ ∫ y in Q, C ∂volume := by
      exact MeasureTheory.integral_mono_ae hfcell hconst hboundQ
    calc
      ∫ y in Q, ‖f y‖ ∂volume ≤ ∫ y in Q, C ∂volume := hmono
      _ = volume.real Q * C := by
        rw [MeasureTheory.setIntegral_const]
        simp [smul_eq_mul]
      _ = s * C := by simp [Q, s, dyadicInterval_volume_real]
  have hnorm := norm_dyadicAverage_le_average_norm (f := f) m x
  calc
    ‖dyadicAverage m f x‖ ≤ s⁻¹ * ∫ y in Q, ‖f y‖ ∂volume := by
      simpa [s, Q] using hnorm
    _ ≤ s⁻¹ * (s * C) := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hs.le)
    _ = C := by field_simp [hs.ne']

/-- The dyadic averaging operator is contractive on the essential-supremum
norm. -/
theorem eLpNormEssSup_dyadicAverage_le {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (m : ℤ) :
    eLpNormEssSup (dyadicAverage m f) volume ≤ eLpNormEssSup f volume := by
  by_cases htop : eLpNormEssSup f volume = ⊤
  · simp [htop]
  · let C := (eLpNormEssSup f volume).toReal
    have hbound : ∀ᵐ y ∂volume, ‖f y‖ ≤ C := by
      filter_upwards [MeasureTheory.enorm_ae_le_eLpNormEssSup f volume] with y hy
      have hle : ENNReal.ofReal ‖f y‖ ≤ eLpNormEssSup f volume := by
        simpa using hy
      exact (ENNReal.ofReal_le_iff_le_toReal htop).1 hle
    have hpt (x : ℝ) :
        ‖dyadicAverage m f x‖ₑ ≤ eLpNormEssSup f volume := by
      rw [← ofReal_norm]
      apply (ENNReal.ofReal_le_iff_le_toReal htop).2
      simpa [C] using norm_dyadicAverage_le_of_ae_bound hf m x C hbound
    exact MeasureTheory.eLpNormEssSup_le_of_ae_enorm_bound
      (Filter.Eventually.of_forall hpt)

/-- Jensen's inequality gives the `L¹` contraction on each dyadic cell. -/
theorem integral_norm_dyadicAverage_le_on_cell {f : ℝ → ℂ}
    (m j : ℤ) :
    ∫ x in dyadicInterval m j, ‖dyadicAverage m f x‖ ∂volume ≤
      ∫ x in dyadicInterval m j, ‖f x‖ ∂volume := by
  let Q := dyadicInterval m j
  let s := (2 : ℝ) ^ m
  let a := (j : ℝ) * s
  have hs : 0 < s := by dsimp [s]; exact dyadicScale_pos' m
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have ha : a ∈ Q := by
    change a ∈ dyadicInterval m j
    rw [dyadicInterval, Set.mem_Ico]
    constructor
    · dsimp [a]
      exact le_rfl
    · have hlen : (((j + 1 : ℤ) : ℝ) * s) - (j : ℝ) * s = s := by
        push_cast
        ring
      dsimp [a]
      linarith
  have hidx : dyadicIntervalIndex m a = j :=
    dyadicIntervalIndex_eq_of_mem (by simpa [Q] using ha)
  have hpoint :
      ‖dyadicAverage m f a‖ ≤ s⁻¹ * ∫ x in Q, ‖f x‖ ∂volume := by
    simpa [s, Q, hidx] using norm_dyadicAverage_le_average_norm (f := f) m a
  have hconst : ∀ x ∈ Q, ‖dyadicAverage m f x‖ = ‖dyadicAverage m f a‖ := by
    intro x hx
    apply congrArg norm
    exact dyadicAverage_eq_of_mem_same_cell m j f (by simpa [Q] using hx)
      (by simpa [Q] using ha)
  calc
    ∫ x in Q, ‖dyadicAverage m f x‖ ∂volume =
        volume.real Q * ‖dyadicAverage m f a‖ := by
      rw [MeasureTheory.setIntegral_congr_fun hQ hconst,
        MeasureTheory.setIntegral_const]
      simp [smul_eq_mul]
    _ = s * ‖dyadicAverage m f a‖ := by
      rw [show volume.real Q = s by simp [Q, s, dyadicInterval_volume_real]]
    _ ≤ s * (s⁻¹ * ∫ x in Q, ‖f x‖ ∂volume) :=
      mul_le_mul_of_nonneg_left hpoint hs.le
    _ = ∫ x in Q, ‖f x‖ ∂volume := by field_simp [hs.ne']

/-- On each dyadic cell, averaging is self-adjoint for the restricted
integral pairing. -/
theorem integral_dyadicAverage_selfAdjoint_on_cell {f g : ℝ → ℂ}
    (m j : ℤ) :
    ∫ x in dyadicInterval m j,
      dyadicAverage m f x * star (g x) ∂volume =
    ∫ x in dyadicInterval m j,
      f x * star (dyadicAverage m g x) ∂volume := by
  let Q := dyadicInterval m j
  let a := (j : ℝ) * (2 : ℝ) ^ m
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have ha : a ∈ Q := by
    change a ∈ dyadicInterval m j
    rw [dyadicInterval, Set.mem_Ico]
    constructor
    · dsimp [a]
      exact le_rfl
    · have hpos := dyadicScale_pos' m
      have hlen : (((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) -
          (j : ℝ) * (2 : ℝ) ^ m = (2 : ℝ) ^ m := by
        push_cast
        ring
      dsimp [a]
      linarith
  have hEf : dyadicAverage m f a =
      ((2 : ℝ) ^ m)⁻¹ • ∫ x in Q, f x ∂volume := by
    unfold dyadicAverage
    rw [dyadicIntervalIndex_eq_of_mem ha]
  have hEg : dyadicAverage m g a =
      ((2 : ℝ) ^ m)⁻¹ • ∫ x in Q, g x ∂volume := by
    unfold dyadicAverage
    rw [dyadicIntervalIndex_eq_of_mem ha]
  have hleft :
      ∫ x in Q, dyadicAverage m f x * star (g x) ∂volume =
        dyadicAverage m f a * star (∫ x in Q, g x ∂volume) := by
    calc
      ∫ x in Q, dyadicAverage m f x * star (g x) ∂volume =
          ∫ x in Q, dyadicAverage m f a * star (g x) ∂volume := by
        apply MeasureTheory.setIntegral_congr_fun hQ
        intro x hx
        change dyadicAverage m f x * star (g x) =
          dyadicAverage m f a * star (g x)
        rw [dyadicAverage_eq_of_mem_same_cell m j f hx ha]
      _ = dyadicAverage m f a * ∫ x in Q, star (g x) ∂volume := by
        rw [MeasureTheory.integral_const_mul]
      _ = dyadicAverage m f a * star (∫ x in Q, g x ∂volume) := by
        congr 1
        exact integral_conj
  have hright :
      ∫ x in Q, f x * star (dyadicAverage m g x) ∂volume =
        (∫ x in Q, f x ∂volume) * star (dyadicAverage m g a) := by
    calc
      ∫ x in Q, f x * star (dyadicAverage m g x) ∂volume =
          ∫ x in Q, f x * star (dyadicAverage m g a) ∂volume := by
        apply MeasureTheory.setIntegral_congr_fun hQ
        intro x hx
        change f x * star (dyadicAverage m g x) =
          f x * star (dyadicAverage m g a)
        rw [dyadicAverage_eq_of_mem_same_cell m j g hx ha]
      _ = (∫ x in Q, f x ∂volume) * star (dyadicAverage m g a) := by
        rw [MeasureTheory.integral_mul_const]
  rw [show dyadicInterval m j = Q by rfl, hleft, hright, hEf, hEg]
  simp
  ring

/-- If an input is constant on a cell, its dyadic average on that cell is that
same constant. -/
theorem dyadicAverage_eq_of_eqOn_cell {m j : ℤ} (f : ℝ → ℂ) (c : ℂ)
    {x : ℝ} (hx : x ∈ dyadicInterval m j)
    (hfc : ∀ y ∈ dyadicInterval m j, f y = c) :
    dyadicAverage m f x = c := by
  have hs : 0 < (2 : ℝ) ^ m := dyadicScale_pos' m
  have hindex := dyadicIntervalIndex_eq_of_mem hx
  have hset : MeasurableSet (dyadicInterval m j) := by
    dsimp [dyadicInterval]
    exact measurableSet_Ico
  have hint :
      ∫ y in dyadicInterval m j, f y ∂volume =
        volume.real (dyadicInterval m j) • c := by
    rw [MeasureTheory.setIntegral_congr_fun hset hfc,
      MeasureTheory.setIntegral_const]
  unfold dyadicAverage
  rw [hindex, hint, dyadicInterval_volume_real]
  rw [Complex.real_smul, Complex.real_smul, Complex.ofReal_inv]
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hs.ne'), one_mul]

private theorem integrableOn_dyadicAverage_cell (m j : ℤ) (f : ℝ → ℂ) :
    IntegrableOn (dyadicAverage m f) (dyadicInterval m j) volume := by
  let a := (j : ℝ) * (2 : ℝ) ^ m
  have ha : a ∈ dyadicInterval m j := by
    rw [dyadicInterval, Set.mem_Ico]
    constructor
    · dsimp [a]
      exact le_rfl
    · have hs := dyadicScale_pos' m
      have hlen : (((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) -
          (j : ℝ) * (2 : ℝ) ^ m = (2 : ℝ) ^ m := by
        push_cast
        ring
      dsimp [a]
      linarith
  let c := dyadicAverage m f a
  have hset : MeasurableSet (dyadicInterval m j) := by
    dsimp [dyadicInterval]
    exact measurableSet_Ico
  have hfinite : volume (dyadicInterval m j) ≠ ⊤ := by
    rw [dyadicInterval, Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have hc : IntegrableOn (fun _ : ℝ => c) (dyadicInterval m j) volume :=
    MeasureTheory.integrableOn_const hfinite
  change Integrable (dyadicAverage m f) (volume.restrict (dyadicInterval m j))
  apply (show Integrable (fun _ : ℝ => c) (volume.restrict (dyadicInterval m j)) from hc).congr
  filter_upwards [MeasureTheory.ae_restrict_mem hset] with x hx
  exact (dyadicAverage_eq_of_mem_same_cell m j f hx ha).symm

/-- The dyadic average is contractive on `L¹`; the proof sums Jensen's
inequality over the disjoint half-open dyadic partition. -/
theorem eLpNorm_one_dyadicAverage_le {f : ℝ → ℂ}
    (hf : MemLp f 1 volume) (m : ℤ) :
    eLpNorm (dyadicAverage m f) 1 volume ≤ eLpNorm f 1 volume := by
  let Q : ℤ → Set ℝ := fun j => dyadicInterval m j
  have hcover : ⋃ j, Q j = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨dyadicIntervalIndex m x,
      by simpa [Q] using mem_dyadicIntervalIndex m x⟩
  have hQ : ∀ j, MeasurableSet (Q j) := by
    intro j
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hdisj : Pairwise (fun i j : ℤ => Disjoint (Q i) (Q j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    calc
      i = dyadicIntervalIndex m x :=
        (dyadicIntervalIndex_eq_of_mem (by simpa [Q] using hxi)).symm
      _ = j := dyadicIntervalIndex_eq_of_mem (by simpa [Q] using hxj)
  have hcell (j : ℤ) :
      ∫⁻ x in Q j, ‖dyadicAverage m f x‖ₑ ∂volume ≤
        ∫⁻ x in Q j, ‖f x‖ₑ ∂volume := by
    have hfi : Integrable f volume := memLp_one_iff_integrable.mp hf
    have hinput : Integrable f (volume.restrict (Q j)) := hfi.restrict
    have houtput : Integrable (dyadicAverage m f) (volume.restrict (Q j)) := by
      change IntegrableOn (dyadicAverage m f) (Q j) volume
      simpa [Q] using integrableOn_dyadicAverage_cell m j f
    have hlocal :
        ∫ x in Q j, ‖dyadicAverage m f x‖ ∂volume ≤
          ∫ x in Q j, ‖f x‖ ∂volume := by
      simpa [Q] using integral_norm_dyadicAverage_le_on_cell m j (f := f)
    calc
      ∫⁻ x in Q j, ‖dyadicAverage m f x‖ₑ ∂volume =
          ENNReal.ofReal (∫ x in Q j, ‖dyadicAverage m f x‖ ∂volume) := by
        simpa [Q] using
          (ofReal_integral_norm_eq_lintegral_enorm
            (μ := volume.restrict (Q j)) (f := dyadicAverage m f) houtput).symm
      _ ≤ ENNReal.ofReal (∫ x in Q j, ‖f x‖ ∂volume) :=
        ENNReal.ofReal_le_ofReal hlocal
      _ = ∫⁻ x in Q j, ‖f x‖ₑ ∂volume := by
        simpa [Q] using
          (ofReal_integral_norm_eq_lintegral_enorm
            (μ := volume.restrict (Q j)) (f := f) hinput)
  have hE :
      ∫⁻ x, ‖dyadicAverage m f x‖ₑ ∂volume =
        ∑' j : ℤ, ∫⁻ x in Q j, ‖dyadicAverage m f x‖ₑ ∂volume := by
    have h := MeasureTheory.lintegral_iUnion (μ := volume) hQ hdisj
      (fun x : ℝ => ‖dyadicAverage m f x‖ₑ)
    rw [hcover] at h
    simpa using h
  have hF :
      ∫⁻ x, ‖f x‖ₑ ∂volume =
        ∑' j : ℤ, ∫⁻ x in Q j, ‖f x‖ₑ ∂volume := by
    have h := MeasureTheory.lintegral_iUnion (μ := volume) hQ hdisj
      (fun x : ℝ => ‖f x‖ₑ)
    rw [hcover] at h
    simpa using h
  rw [eLpNorm_one_eq_lintegral_enorm
      (measurable_dyadicAverage m f).aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  calc
    ∫⁻ x, ‖dyadicAverage m f x‖ₑ ∂volume =
        ∑' j : ℤ, ∫⁻ x in Q j, ‖dyadicAverage m f x‖ₑ ∂volume := hE
    _ ≤ ∑' j : ℤ, ∫⁻ x in Q j, ‖f x‖ₑ ∂volume :=
      ENNReal.tsum_le_tsum hcell
    _ = ∫⁻ x, ‖f x‖ₑ ∂volume := hF.symm

/-- Jensen's inequality gives the `L²` contraction on each dyadic cell. -/
theorem integral_sq_dyadicAverage_le_on_cell {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (m j : ℤ) :
    ∫ x in dyadicInterval m j, ‖dyadicAverage m f x‖ ^ 2 ∂volume ≤
      ∫ x in dyadicInterval m j, ‖f x‖ ^ 2 ∂volume := by
  let Q := dyadicInterval m j
  let s := (2 : ℝ) ^ m
  let a := (j : ℝ) * s
  have hs : 0 < s := by dsimp [s]; exact dyadicScale_pos' m
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have ha : a ∈ Q := by
    simpa [Q, a, s] using dyadicInterval_lower_mem m j
  have hlen : (((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) -
      (j : ℝ) * (2 : ℝ) ^ m = (2 : ℝ) ^ m := by
    push_cast
    ring
  have hvolume : volume.real Q = s := by
    simp [Q, s, dyadicInterval_volume_real]
  have hfinite : volume Q ≠ ⊤ := by
    dsimp [Q, dyadicInterval]
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have hfiniteInstance : IsFiniteMeasure (volume.restrict Q) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hfinite
  have hnonzero : volume Q ≠ 0 := by
    dsimp [Q, dyadicInterval]
    rw [Real.volume_Ico, hlen]
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hs))
  have hfQ : MemLp f 2 (volume.restrict Q) := hf.restrict Q
  have hfInt : Integrable f (volume.restrict Q) :=
    @MemLp.integrable ℝ ℂ _ (volume.restrict Q) inferInstance inferInstance
      2 (by norm_num) f hfiniteInstance hfQ
  have hnormSqInt : Integrable (fun x : ℝ => ‖f x‖ ^ 2)
      (volume.restrict Q) := hfQ.integrable_norm_pow (by norm_num)
  have hE : dyadicAverage m f a =
      s⁻¹ • ∫ x in Q, f x ∂volume := by
    unfold dyadicAverage
    rw [dyadicIntervalIndex_eq_of_mem ha]
  have haverage : (⨍ x in Q, f x ∂volume) = dyadicAverage m f a := by
    rw [average_eq, measureReal_restrict_apply_univ, hvolume]
    exact hE.symm
  have hconvex : ConvexOn ℝ (Set.univ : Set ℂ)
      (fun z : ℂ => ‖z‖ ^ 2) :=
    (convexOn_univ_norm (E := ℂ)).pow (fun _ _ => norm_nonneg _) 2
  have hcontinuous : ContinuousOn (fun z : ℂ => ‖z‖ ^ 2) Set.univ :=
    (continuous_norm.pow 2).continuousOn
  have hfIOn : IntegrableOn f Q volume := hfInt
  have hnormSqIOn : IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2) Q volume :=
    hnormSqInt
  have hjensen := hconvex.map_set_average_le hcontinuous isClosed_univ
    hnonzero hfinite (ae_of_all _ (fun _ => Set.mem_univ _)) hfIOn hnormSqIOn
  have hpoint : ‖dyadicAverage m f a‖ ^ 2 ≤
      s⁻¹ * ∫ x in Q, ‖f x‖ ^ 2 ∂volume := by
    calc
      ‖dyadicAverage m f a‖ ^ 2 = ‖⨍ x in Q, f x ∂volume‖ ^ 2 := by
        rw [haverage]
      _ ≤ ⨍ x in Q, ‖f x‖ ^ 2 ∂volume := hjensen
      _ = s⁻¹ * ∫ x in Q, ‖f x‖ ^ 2 ∂volume := by
        rw [average_eq, measureReal_restrict_apply_univ, hvolume, smul_eq_mul]
  have hconst : ∀ x ∈ Q,
      ‖dyadicAverage m f x‖ ^ 2 = ‖dyadicAverage m f a‖ ^ 2 := by
    intro x hx
    apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
    exact dyadicAverage_eq_of_mem_same_cell m j f
      (by simpa [Q] using hx) (by simpa [Q] using ha)
  calc
    ∫ x in Q, ‖dyadicAverage m f x‖ ^ 2 ∂volume =
        volume.real Q * ‖dyadicAverage m f a‖ ^ 2 := by
      rw [MeasureTheory.setIntegral_congr_fun hQ hconst,
        MeasureTheory.setIntegral_const]
      simp [smul_eq_mul]
    _ = s * ‖dyadicAverage m f a‖ ^ 2 := by rw [hvolume]
    _ ≤ s * (s⁻¹ * ∫ x in Q, ‖f x‖ ^ 2 ∂volume) :=
      mul_le_mul_of_nonneg_left hpoint hs.le
    _ = ∫ x in Q, ‖f x‖ ^ 2 ∂volume := by field_simp [hs.ne']

/-- Jensen's inequality gives the finite-exponent cell contraction. -/
theorem integral_rpow_dyadicAverage_le_on_cell {f : ℝ → ℂ} {p : ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) (hp : 1 ≤ p) (m j : ℤ) :
    ∫ x in dyadicInterval m j, ‖dyadicAverage m f x‖ ^ p ∂volume ≤
      ∫ x in dyadicInterval m j, ‖f x‖ ^ p ∂volume := by
  let Q := dyadicInterval m j
  let s := (2 : ℝ) ^ m
  let a := (j : ℝ) * s
  have hs : 0 < s := by dsimp [s]; exact dyadicScale_pos' m
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have ha : a ∈ Q := by
    simpa [Q, a, s] using dyadicInterval_lower_mem m j
  have hlen : (((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) -
      (j : ℝ) * (2 : ℝ) ^ m = (2 : ℝ) ^ m := by
    push_cast
    ring
  have hvolume : volume.real Q = s := by
    simp [Q, s, dyadicInterval_volume_real]
  have hfinite : volume Q ≠ ⊤ := by
    dsimp [Q, dyadicInterval]
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have hfiniteInstance : IsFiniteMeasure (volume.restrict Q) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hfinite
  have hnonzero : volume Q ≠ 0 := by
    dsimp [Q, dyadicInterval]
    rw [Real.volume_Ico, hlen]
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hs))
  have hpENN : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hfQ : MemLp f (ENNReal.ofReal p) (volume.restrict Q) := hf.restrict Q
  haveI : IsFiniteMeasure (volume.restrict Q) := hfiniteInstance
  have hfInt : Integrable f (volume.restrict Q) := hfQ.integrable hpENN
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hpntop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hnormPowInt : Integrable (fun x : ℝ => ‖f x‖ ^ p)
      (volume.restrict Q) := by
    simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using
      hfQ.integrable_norm_rpow hpne hpntop
  have hE : dyadicAverage m f a =
      s⁻¹ • ∫ x in Q, f x ∂volume := by
    unfold dyadicAverage
    rw [dyadicIntervalIndex_eq_of_mem ha]
  have haverage : (⨍ x in Q, f x ∂volume) = dyadicAverage m f a := by
    rw [average_eq, measureReal_restrict_apply_univ, hvolume]
    exact hE.symm
  have himage : (fun z : ℂ => ‖z‖) '' (Set.univ : Set ℂ) = Set.Ici (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨z, _, rfl⟩
      exact norm_nonneg z
    · intro ht
      refine ⟨(t : ℂ), Set.mem_univ _, ?_⟩
      exact Complex.norm_of_nonneg ht
  have hpow : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => t ^ p) :=
    convexOn_rpow hp
  have hmono : MonotoneOn (fun t : ℝ => t ^ p)
      ((fun z : ℂ => ‖z‖) '' (Set.univ : Set ℂ)) := by
    rw [himage]
    exact Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by linarith)
  have hconvex : ConvexOn ℝ (Set.univ : Set ℂ)
      (fun z : ℂ => ‖z‖ ^ p) := by
    rw [← himage] at hpow
    simpa [Function.comp_def] using hpow.comp (convexOn_univ_norm (E := ℂ)) hmono
  have hcontinuous : ContinuousOn (fun z : ℂ => ‖z‖ ^ p) Set.univ := by
    exact (continuous_norm.continuousOn).rpow_const (fun _ _ => Or.inr (by linarith))
  have hnormPowIOn : IntegrableOn (fun x : ℝ => ‖f x‖ ^ p) Q volume := hnormPowInt
  have hjensen := hconvex.map_set_average_le hcontinuous isClosed_univ
    hnonzero hfinite (ae_of_all _ (fun _ => Set.mem_univ _)) hfInt hnormPowIOn
  have hpoint : ‖dyadicAverage m f a‖ ^ p ≤
      s⁻¹ * ∫ x in Q, ‖f x‖ ^ p ∂volume := by
    calc
      ‖dyadicAverage m f a‖ ^ p = ‖⨍ x in Q, f x ∂volume‖ ^ p := by
        rw [haverage]
      _ ≤ ⨍ x in Q, ‖f x‖ ^ p ∂volume := hjensen
      _ = s⁻¹ * ∫ x in Q, ‖f x‖ ^ p ∂volume := by
        rw [average_eq, measureReal_restrict_apply_univ, hvolume, smul_eq_mul]
  have hconst : ∀ x ∈ Q, ‖dyadicAverage m f x‖ ^ p =
      ‖dyadicAverage m f a‖ ^ p := by
    intro x hx
    apply congrArg (fun z : ℝ => z ^ p)
    apply congrArg norm
    exact dyadicAverage_eq_of_mem_same_cell m j f
      (by simpa [Q] using hx) (by simpa [Q] using ha)
  calc
    ∫ x in Q, ‖dyadicAverage m f x‖ ^ p ∂volume =
        volume.real Q * ‖dyadicAverage m f a‖ ^ p := by
      rw [MeasureTheory.setIntegral_congr_fun hQ hconst,
        MeasureTheory.setIntegral_const]
      simp [smul_eq_mul]
    _ = s * ‖dyadicAverage m f a‖ ^ p := by rw [hvolume]
    _ ≤ s * (s⁻¹ * ∫ x in Q, ‖f x‖ ^ p ∂volume) :=
      mul_le_mul_of_nonneg_left hpoint hs.le
    _ = ∫ x in Q, ‖f x‖ ^ p ∂volume := by field_simp [hs.ne']

/-- The dyadic average is contractive on every finite `Lᵖ`, `p ≥ 1`, by
integrating the cellwise Jensen inequality over the half-open partition. -/
theorem eLpNorm_finite_dyadicAverage_le {f : ℝ → ℂ} {p : ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) (hp : 1 ≤ p) (m : ℤ) :
    eLpNorm (dyadicAverage m f) (ENNReal.ofReal p) volume ≤
      eLpNorm f (ENNReal.ofReal p) volume := by
  have hpnonneg : 0 ≤ p := by linarith
  have hpqpos : 0 < p := by linarith
  have hqzero : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hpqpos).ne'
  have hqtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  let Q : ℤ → Set ℝ := fun j => dyadicInterval m j
  have hcover : ⋃ j, Q j = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨dyadicIntervalIndex m x,
      by simpa [Q] using mem_dyadicIntervalIndex m x⟩
  have hQ : ∀ j, MeasurableSet (Q j) := by
    intro j
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hdisj : Pairwise (fun i j : ℤ => Disjoint (Q i) (Q j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    calc
      i = dyadicIntervalIndex m x :=
        (dyadicIntervalIndex_eq_of_mem (by simpa [Q] using hxi)).symm
      _ = j := dyadicIntervalIndex_eq_of_mem (by simpa [Q] using hxj)
  have hcell (j : ℤ) :
      ∫⁻ x in Q j, ‖dyadicAverage m f x‖ₑ ^ p ∂volume ≤
        ∫⁻ x in Q j, ‖f x‖ₑ ^ p ∂volume := by
    let Qj := Q j
    let a := (j : ℝ) * (2 : ℝ) ^ m
    have hset : MeasurableSet Qj := by simpa [Qj, Q] using hQ j
    have ha : a ∈ Qj := by
      simpa [a, Qj, Q] using dyadicInterval_lower_mem m j
    have hfinite : volume Qj ≠ ⊤ := by
      dsimp [Qj, Q, dyadicInterval]
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top
    have houtputPowInt : Integrable
        (fun x : ℝ => ‖dyadicAverage m f x‖ ^ p)
        (volume.restrict Qj) := by
      let c := ‖dyadicAverage m f a‖ ^ p
      have hc : Integrable (fun _ : ℝ => c) (volume.restrict Qj) := by
        change IntegrableOn (fun _ : ℝ => c) Qj volume
        exact MeasureTheory.integrableOn_const hfinite
      apply hc.congr
      filter_upwards [MeasureTheory.ae_restrict_mem hset] with x hx
      exact (congrArg (fun z : ℂ => ‖z‖ ^ p)
        (dyadicAverage_eq_of_mem_same_cell m j f
          (by simpa [Qj, Q] using hx)
          (by simpa [a, Qj, Q] using ha))).symm
    have hinputPowInt : Integrable (fun x : ℝ => ‖f x‖ ^ p)
        (volume.restrict Qj) := by
      have hfQ : MemLp f (ENNReal.ofReal p) (volume.restrict Qj) :=
        hf.restrict Qj
      have h := hfQ.integrable_norm_rpow hqzero hqtop
      simpa [ENNReal.toReal_ofReal hpnonneg] using h
    have houtputConv :
        ENNReal.ofReal (∫ x in Qj, ‖dyadicAverage m f x‖ ^ p ∂volume) =
          ∫⁻ x in Qj, ‖dyadicAverage m f x‖ₑ ^ p ∂volume := by
      have h := ofReal_integral_eq_lintegral_ofReal houtputPowInt
        (ae_of_all _ (fun x => by positivity))
      simpa only [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpnonneg,
        ofReal_norm] using h
    have hinputConv :
        ENNReal.ofReal (∫ x in Qj, ‖f x‖ ^ p ∂volume) =
          ∫⁻ x in Qj, ‖f x‖ₑ ^ p ∂volume := by
      have h := ofReal_integral_eq_lintegral_ofReal hinputPowInt
        (ae_of_all _ (fun x => by positivity))
      simpa only [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpnonneg,
        ofReal_norm] using h
    have hlocal := integral_rpow_dyadicAverage_le_on_cell hf hp m j
    calc
      ∫⁻ x in Q j, ‖dyadicAverage m f x‖ₑ ^ p ∂volume =
          ENNReal.ofReal (∫ x in Qj,
            ‖dyadicAverage m f x‖ ^ p ∂volume) := by
        simpa [Qj, Q] using houtputConv.symm
      _ ≤ ENNReal.ofReal (∫ x in Qj, ‖f x‖ ^ p ∂volume) :=
        ENNReal.ofReal_le_ofReal (by simpa [Qj, Q] using hlocal)
      _ = ∫⁻ x in Q j, ‖f x‖ₑ ^ p ∂volume := by
        simpa [Qj, Q] using hinputConv
  have hE :
      ∫⁻ x, ‖dyadicAverage m f x‖ₑ ^ p ∂volume =
        ∑' j : ℤ, ∫⁻ x in Q j, ‖dyadicAverage m f x‖ₑ ^ p ∂volume := by
    have h := MeasureTheory.lintegral_iUnion (μ := volume) hQ hdisj
      (fun x : ℝ => ‖dyadicAverage m f x‖ₑ ^ p)
    rw [hcover] at h
    simpa using h
  have hF :
      ∫⁻ x, ‖f x‖ₑ ^ p ∂volume =
        ∑' j : ℤ, ∫⁻ x in Q j, ‖f x‖ₑ ^ p ∂volume := by
    have h := MeasureTheory.lintegral_iUnion (μ := volume) hQ hdisj
      (fun x : ℝ => ‖f x‖ₑ ^ p)
    rw [hcover] at h
    simpa using h
  have hlin :
      ∫⁻ x, ‖dyadicAverage m f x‖ₑ ^ p ∂volume ≤
        ∫⁻ x, ‖f x‖ₑ ^ p ∂volume := by
    calc
      ∫⁻ x, ‖dyadicAverage m f x‖ₑ ^ p ∂volume =
          ∑' j : ℤ, ∫⁻ x in Q j, ‖dyadicAverage m f x‖ₑ ^ p ∂volume := hE
      _ ≤ ∑' j : ℤ, ∫⁻ x in Q j, ‖f x‖ₑ ^ p ∂volume :=
        ENNReal.tsum_le_tsum hcell
      _ = ∫⁻ x, ‖f x‖ₑ ^ p ∂volume := hF.symm
  have hp_toReal : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal hpnonneg
  have hformulaOut :
      eLpNorm (dyadicAverage m f) (ENNReal.ofReal p) volume =
        (∫⁻ x, ‖dyadicAverage m f x‖ₑ ^ p ∂volume) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqzero hqtop
      (measurable_dyadicAverage m f).aestronglyMeasurable, hp_toReal]
  have hformulaIn :
      eLpNorm f (ENNReal.ofReal p) volume =
        (∫⁻ x, ‖f x‖ₑ ^ p ∂volume) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqzero hqtop
      hf.aestronglyMeasurable, hp_toReal]
  rw [hformulaOut, hformulaIn]
  exact ENNReal.rpow_le_rpow hlin (by positivity)

/-- The dyadic average is contractive on `L²`; sum the cellwise Jensen
inequality over the half-open partition. -/
theorem eLpNorm_two_dyadicAverage_le {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (m : ℤ) :
    eLpNorm (dyadicAverage m f) 2 volume ≤ eLpNorm f 2 volume := by
  let Q : ℤ → Set ℝ := fun j => dyadicInterval m j
  have hcover : ⋃ j, Q j = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨dyadicIntervalIndex m x,
      by simpa [Q] using mem_dyadicIntervalIndex m x⟩
  have hQ : ∀ j, MeasurableSet (Q j) := by
    intro j
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hdisj : Pairwise (fun i j : ℤ => Disjoint (Q i) (Q j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    calc
      i = dyadicIntervalIndex m x :=
        (dyadicIntervalIndex_eq_of_mem (by simpa [Q] using hxi)).symm
      _ = j := dyadicIntervalIndex_eq_of_mem (by simpa [Q] using hxj)
  have hcell (j : ℤ) :
      ∫⁻ x in Q j, ‖dyadicAverage m f x‖ₑ ^ 2 ∂volume ≤
        ∫⁻ x in Q j, ‖f x‖ₑ ^ 2 ∂volume := by
    let Qj := Q j
    let a := (j : ℝ) * (2 : ℝ) ^ m
    have hset : MeasurableSet Qj := by simpa [Qj, Q] using hQ j
    have ha : a ∈ Qj := by
      simpa [a, Qj, Q] using dyadicInterval_lower_mem m j
    have hfinite : volume Qj ≠ ⊤ := by
      dsimp [Qj, Q, dyadicInterval]
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top
    have houtputSqInt :
        Integrable (fun x : ℝ => ‖dyadicAverage m f x‖ ^ 2)
          (volume.restrict Qj) := by
      let c := ‖dyadicAverage m f a‖ ^ 2
      have hc : Integrable (fun _ : ℝ => c) (volume.restrict Qj) := by
        change IntegrableOn (fun _ : ℝ => c) Qj volume
        exact MeasureTheory.integrableOn_const hfinite
      apply hc.congr
      filter_upwards [MeasureTheory.ae_restrict_mem hset] with x hx
      exact (congrArg (fun z : ℂ => ‖z‖ ^ 2)
        (dyadicAverage_eq_of_mem_same_cell m j f
          (by simpa [Qj, Q] using hx)
          (by simpa [a, Qj, Q] using ha))).symm
    have hinputSqInt :
        Integrable (fun x : ℝ => ‖f x‖ ^ 2) (volume.restrict Qj) := by
      have hlocal : MemLp f 2 (volume.restrict Qj) := hf.restrict Qj
      exact hlocal.integrable_norm_pow (by norm_num)
    have hlocal := integral_sq_dyadicAverage_le_on_cell hf m j
    have houtputConv :
        ENNReal.ofReal (∫ x in Qj, ‖dyadicAverage m f x‖ ^ 2 ∂volume) =
          ∫⁻ x in Qj, ‖dyadicAverage m f x‖ₑ ^ 2 ∂volume := by
      have h := ofReal_integral_eq_lintegral_ofReal houtputSqInt
        (ae_of_all _ (fun x => sq_nonneg ‖dyadicAverage m f x‖))
      simpa [ENNReal.ofReal_pow, ofReal_norm] using h
    have hinputConv :
        ENNReal.ofReal (∫ x in Qj, ‖f x‖ ^ 2 ∂volume) =
          ∫⁻ x in Qj, ‖f x‖ₑ ^ 2 ∂volume := by
      have h := ofReal_integral_eq_lintegral_ofReal hinputSqInt
        (ae_of_all _ (fun x => sq_nonneg ‖f x‖))
      simpa [ENNReal.ofReal_pow, ofReal_norm] using h
    calc
      ∫⁻ x in Q j, ‖dyadicAverage m f x‖ₑ ^ 2 ∂volume =
          ENNReal.ofReal (∫ x in Qj, ‖dyadicAverage m f x‖ ^ 2 ∂volume) := by
        simpa [Qj, Q] using houtputConv.symm
      _ ≤ ENNReal.ofReal (∫ x in Qj, ‖f x‖ ^ 2 ∂volume) :=
        ENNReal.ofReal_le_ofReal (by simpa [Qj, Q] using hlocal)
      _ = ∫⁻ x in Q j, ‖f x‖ₑ ^ 2 ∂volume := by
        simpa [Qj, Q] using hinputConv
  have hE :
      ∫⁻ x, ‖dyadicAverage m f x‖ₑ ^ 2 ∂volume =
        ∑' j : ℤ, ∫⁻ x in Q j, ‖dyadicAverage m f x‖ₑ ^ 2 ∂volume := by
    have h := MeasureTheory.lintegral_iUnion (μ := volume) hQ hdisj
      (fun x : ℝ => ‖dyadicAverage m f x‖ₑ ^ 2)
    rw [hcover] at h
    simpa using h
  have hF :
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂volume =
        ∑' j : ℤ, ∫⁻ x in Q j, ‖f x‖ₑ ^ 2 ∂volume := by
    have h := MeasureTheory.lintegral_iUnion (μ := volume) hQ hdisj
      (fun x : ℝ => ‖f x‖ₑ ^ 2)
    rw [hcover] at h
    simpa using h
  have hlin :
      ∫⁻ x, ‖dyadicAverage m f x‖ₑ ^ 2 ∂volume ≤
        ∫⁻ x, ‖f x‖ₑ ^ 2 ∂volume := by
    calc
      ∫⁻ x, ‖dyadicAverage m f x‖ₑ ^ 2 ∂volume =
          ∑' j : ℤ, ∫⁻ x in Q j, ‖dyadicAverage m f x‖ₑ ^ 2 ∂volume := hE
      _ ≤ ∑' j : ℤ, ∫⁻ x in Q j, ‖f x‖ₑ ^ 2 ∂volume :=
        ENNReal.tsum_le_tsum hcell
      _ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂volume := hF.symm
  have hformulaOut :
      eLpNorm (dyadicAverage m f) 2 volume =
        (∫⁻ x, ‖dyadicAverage m f x‖ₑ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (measurable_dyadicAverage m f).aestronglyMeasurable]
    norm_num [ENNReal.rpow_natCast]
  have hformulaIn : eLpNorm f 2 volume =
      (∫⁻ x, ‖f x‖ₑ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hf.aestronglyMeasurable]
    norm_num [ENNReal.rpow_natCast]
  rw [hformulaOut, hformulaIn]
  exact ENNReal.rpow_le_rpow hlin (by norm_num)

/-- `E_m` is idempotent pointwise, the algebraic projection identity. -/
theorem dyadicAverage_idempotent (m : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    dyadicAverage m (dyadicAverage m f) x = dyadicAverage m f x := by
  change ((2 : ℝ) ^ m)⁻¹ •
      ∫ y in dyadicInterval m (dyadicIntervalIndex m x), dyadicAverage m f y ∂volume =
    ((2 : ℝ) ^ m)⁻¹ •
      ∫ y in dyadicInterval m (dyadicIntervalIndex m x), f y ∂volume
  rw [integral_dyadicAverage_eq_integral m (dyadicIntervalIndex m x) f]

private theorem dyadicInterval_parent_subset (m j : ℤ) :
    dyadicInterval m j ⊆ dyadicInterval (m + 1) (j / 2) := by
  have hmod : j % 2 = 0 ∨ j % 2 = 1 := Int.emod_two_eq_zero_or_one j
  have hlen : 0 < (2 : ℝ) ^ m := dyadicScale_pos' m
  have hscale : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 := by
    rw [show m + 1 = m + (1 : ℤ) by rfl, zpow_add₀ (by norm_num), zpow_one]
  have hdecomp : j % 2 + 2 * (j / 2) = j := Int.emod_add_mul_ediv j 2
  rcases hmod with hmod | hmod
  · have hji : (j : ℝ) = 2 * ((j / 2 : ℤ) : ℝ) := by
      have h := hdecomp
      rw [hmod] at h
      exact_mod_cast (by omega : j = 2 * (j / 2))
    intro x hx
    simp only [dyadicInterval, Set.mem_Ico] at hx ⊢
    rw [hscale]
    constructor
    · nlinarith [hx.1]
    · have hupper : ((j + 1 : ℤ) : ℝ) =
          2 * ((j / 2 : ℤ) : ℝ) + 1 := by rw [Int.cast_add, Int.cast_one, hji]
      rw [hupper] at hx
      have hcmp :
          (2 * ((j / 2 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ m ≤
            (((j / 2 + 1 : ℤ) : ℝ)) * ((2 : ℝ) ^ m * 2) := by
        rw [Int.cast_add, Int.cast_one]
        calc
          _ = (((j / 2 : ℤ) : ℝ) + 1) * ((2 : ℝ) ^ m * 2) - (2 : ℝ) ^ m := by ring
          _ ≤ _ := by linarith [hlen]
      exact lt_of_lt_of_le hx.2 hcmp
  · have hji : (j : ℝ) = 2 * ((j / 2 : ℤ) : ℝ) + 1 := by
      have h := hdecomp
      rw [hmod] at h
      exact_mod_cast (by omega : j = 2 * (j / 2) + 1)
    intro x hx
    simp only [dyadicInterval, Set.mem_Ico] at hx ⊢
    rw [hscale]
    constructor
    · nlinarith [hx.1]
    · have hupper : ((j + 1 : ℤ) : ℝ) =
          2 * ((j / 2 : ℤ) : ℝ) + 2 := by rw [Int.cast_add, Int.cast_one, hji]; ring
      rw [hupper] at hx
      calc
        x < (2 * ((j / 2 : ℤ) : ℝ) + 2) * (2 : ℝ) ^ m := hx.2
        _ = ((j / 2 + 1 : ℤ) : ℝ) * ((2 : ℝ) ^ m * 2) := by
          rw [Int.cast_add, Int.cast_one]
          ring

private theorem dyadicScale_child (m : ℤ) :
    (2 : ℝ) ^ (m - 1) * 2 = (2 : ℝ) ^ m := by
  calc
    (2 : ℝ) ^ (m - 1) * 2 = (2 : ℝ) ^ (m - 1) * (2 : ℝ) ^ (1 : ℤ) := by
      rw [zpow_one]
    _ = (2 : ℝ) ^ (m - 1 + 1) := by rw [zpow_add₀ (by norm_num)]
    _ = (2 : ℝ) ^ m := by congr 1; omega

/-- A dyadic cell is the disjoint union of its two half-size children. -/
theorem dyadicInterval_eq_two_children (m j : ℤ) :
    dyadicInterval m j =
      dyadicInterval (m - 1) (2 * j) ∪ dyadicInterval (m - 1) (2 * j + 1) := by
  let s := (2 : ℝ) ^ (m - 1)
  let p := (2 : ℝ) ^ m
  let a := (j : ℝ) * p
  let c := a + s
  let b := ((j + 1 : ℤ) : ℝ) * p
  have hs : 0 < s := by dsimp [s]; exact dyadicScale_pos' (m - 1)
  have hscale : s * 2 = p := by dsimp [s, p]; exact dyadicScale_child m
  have hleft : ((2 * j : ℤ) : ℝ) * s = a := by
    dsimp [a]
    calc
      ((2 * j : ℤ) : ℝ) * s = (2 * (j : ℝ)) * s := by push_cast; ring
      _ = (j : ℝ) * (s * 2) := by ring
      _ = (j : ℝ) * p := by rw [hscale]
  have hmid : ((2 * j + 1 : ℤ) : ℝ) * s = c := by
    dsimp [c, a, p]
    calc
      ((2 * j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (m - 1) =
          (2 * (j : ℝ) + 1) * (2 : ℝ) ^ (m - 1) := by push_cast; ring
      _ = (j : ℝ) * ((2 : ℝ) ^ (m - 1) * 2) + (2 : ℝ) ^ (m - 1) := by ring
      _ = (j : ℝ) * (2 : ℝ) ^ m + (2 : ℝ) ^ (m - 1) := by
        rw [dyadicScale_child]
  have hright : ((2 * j + 1 + 1 : ℤ) : ℝ) * s = b := by
    dsimp [b, p]
    calc
      ((2 * j + 1 + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (m - 1) =
          (2 * (j : ℝ) + 2) * (2 : ℝ) ^ (m - 1) := by push_cast; ring
      _ = ((j : ℝ) + 1) * ((2 : ℝ) ^ (m - 1) * 2) := by ring
      _ = ((j : ℝ) + 1) * (2 : ℝ) ^ m := by rw [dyadicScale_child]
      _ = ((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m := by rw [Int.cast_add, Int.cast_one]
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by
    dsimp [c, a, b, p, s] at *
    rw [Int.cast_add, Int.cast_one]
    nlinarith [dyadicScale_child m, dyadicScale_pos' (m - 1)]
  ext x
  simp only [dyadicInterval, Set.mem_Ico, Set.mem_union]
  rw [hleft, hmid, hright]
  constructor
  · rintro ⟨hlo, hhi⟩
    by_cases hxc : x < c
    · exact Or.inl ⟨hlo, hxc⟩
    · exact Or.inr ⟨le_of_not_gt hxc, hhi⟩
  · rintro (⟨hlo, hhi⟩ | ⟨hlo, hhi⟩)
    · exact ⟨hlo, lt_trans hhi hcb⟩
    · exact ⟨le_trans (le_of_lt hac) hlo, hhi⟩

/-- Integrating the finer average over a parent cell recovers the parent
integral. This is the cancellation identity for one martingale difference. -/
theorem integral_dyadicAverage_child_over_parent {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (m j : ℤ) :
    ∫ x in dyadicInterval m j, dyadicAverage (m - 1) f x ∂volume =
      ∫ x in dyadicInterval m j, f x ∂volume := by
  let left := dyadicInterval (m - 1) (2 * j)
  let right := dyadicInterval (m - 1) (2 * j + 1)
  have hdisj : Disjoint left right := by
    apply Set.disjoint_left.mpr
    intro x hxL hxR
    dsimp [left, right] at hxL hxR
    rw [dyadicInterval, Set.mem_Ico] at hxL hxR
    exact (not_le_of_gt hxL.2) hxR.1
  have hmeasRight : MeasurableSet right := by
    dsimp [right, dyadicInterval]
    exact measurableSet_Ico
  have hleftAvg :
      IntegrableOn (dyadicAverage (m - 1) f) left volume := by
    exact integrableOn_dyadicAverage_cell (m - 1) (2 * j) f
  have hrightAvg :
      IntegrableOn (dyadicAverage (m - 1) f) right volume := by
    exact integrableOn_dyadicAverage_cell (m - 1) (2 * j + 1) f
  have hleftF : IntegrableOn f left volume := by
    exact integrableOn_dyadicInterval_of_locallyIntegrable hf (m - 1) (2 * j)
  have hrightF : IntegrableOn f right volume := by
    exact integrableOn_dyadicInterval_of_locallyIntegrable hf (m - 1) (2 * j + 1)
  calc
    ∫ x in dyadicInterval m j, dyadicAverage (m - 1) f x ∂volume =
        ∫ x in left ∪ right, dyadicAverage (m - 1) f x ∂volume := by
          rw [dyadicInterval_eq_two_children]
    _ = (∫ x in left, dyadicAverage (m - 1) f x ∂volume) +
        ∫ x in right, dyadicAverage (m - 1) f x ∂volume :=
      MeasureTheory.setIntegral_union hdisj hmeasRight hleftAvg hrightAvg
    _ = (∫ x in left, f x ∂volume) + ∫ x in right, f x ∂volume := by
      rw [integral_dyadicAverage_eq_integral (m - 1) (2 * j) f,
        integral_dyadicAverage_eq_integral (m - 1) (2 * j + 1) f]
    _ = ∫ x in left ∪ right, f x ∂volume :=
      (MeasureTheory.setIntegral_union hdisj hmeasRight hleftF hrightF).symm
    _ = ∫ x in dyadicInterval m j, f x ∂volume := by
      rw [dyadicInterval_eq_two_children]

private theorem dyadicInterval_succ_eq_children (m j : ℤ) :
    dyadicInterval (m + 1) j =
      dyadicInterval m (2 * j) ∪ dyadicInterval m (2 * j + 1) := by
  have hm : m + 1 - 1 = m := by omega
  simpa [hm] using dyadicInterval_eq_two_children (m + 1) j

private theorem dyadicInterval_children_disjoint (m j : ℤ) :
    Disjoint (dyadicInterval m (2 * j)) (dyadicInterval m (2 * j + 1)) := by
  apply Set.disjoint_left.mpr
  intro x hxL hxR
  rw [dyadicInterval, Set.mem_Ico] at hxL hxR
  exact (not_le_of_gt hxL.2) hxR.1

/-- On a cell `n` scales coarser than `E_m`, that average is integrable and
has the same integral as the input. The proof uses only finite dyadic
subdivision and local integrability of the input. -/
theorem dyadicAverage_integral_coarseCell_nat {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (m : ℤ) (n : ℕ) (j : ℤ) :
    IntegrableOn (dyadicAverage m f) (dyadicInterval (m + n) j) volume ∧
      ∫ x in dyadicInterval (m + n) j, dyadicAverage m f x ∂volume =
        ∫ x in dyadicInterval (m + n) j, f x ∂volume := by
  induction n generalizing m j with
  | zero =>
      constructor
      · simpa using integrableOn_dyadicAverage_cell m j f
      · simpa using integral_dyadicAverage_eq_integral m j f
  | succ n ih =>
      let k : ℤ := m + n
      have hk : m + ((n + 1 : ℕ) : ℤ) = k + 1 := by dsimp [k]; omega
      rw [hk]
      have hleft :
          IntegrableOn (dyadicAverage m f) (dyadicInterval k (2 * j)) volume ∧
            ∫ x in dyadicInterval k (2 * j), dyadicAverage m f x ∂volume =
              ∫ x in dyadicInterval k (2 * j), f x ∂volume := by
        simpa [k] using ih (m := m) (j := 2 * j)
      have hright :
          IntegrableOn (dyadicAverage m f) (dyadicInterval k (2 * j + 1)) volume ∧
            ∫ x in dyadicInterval k (2 * j + 1), dyadicAverage m f x ∂volume =
              ∫ x in dyadicInterval k (2 * j + 1), f x ∂volume := by
        simpa [k] using ih (m := m) (j := 2 * j + 1)
      have hdisj := dyadicInterval_children_disjoint k j
      have hmeasRight : MeasurableSet (dyadicInterval k (2 * j + 1)) := by
        dsimp [dyadicInterval]
        exact measurableSet_Ico
      have hleftF : IntegrableOn f (dyadicInterval k (2 * j)) volume :=
        integrableOn_dyadicInterval_of_locallyIntegrable hf k (2 * j)
      have hrightF : IntegrableOn f (dyadicInterval k (2 * j + 1)) volume :=
        integrableOn_dyadicInterval_of_locallyIntegrable hf k (2 * j + 1)
      refine ⟨?_, ?_⟩
      · rw [dyadicInterval_succ_eq_children, MeasureTheory.integrableOn_union]
        exact ⟨hleft.1, hright.1⟩
      · calc
          ∫ x in dyadicInterval (k + 1) j, dyadicAverage m f x ∂volume =
              (∫ x in dyadicInterval k (2 * j), dyadicAverage m f x ∂volume) +
                ∫ x in dyadicInterval k (2 * j + 1), dyadicAverage m f x ∂volume :=
            by
              rw [dyadicInterval_succ_eq_children]
              exact MeasureTheory.setIntegral_union hdisj hmeasRight hleft.1 hright.1
          _ = (∫ x in dyadicInterval k (2 * j), f x ∂volume) +
                ∫ x in dyadicInterval k (2 * j + 1), f x ∂volume := by
            rw [hleft.2, hright.2]
          _ = ∫ x in dyadicInterval k (2 * j) ∪ dyadicInterval k (2 * j + 1),
                f x ∂volume :=
            (MeasureTheory.setIntegral_union hdisj hmeasRight hleftF hrightF).symm
          _ = ∫ x in dyadicInterval (k + 1) j, f x ∂volume := by
            rw [dyadicInterval_succ_eq_children]

/-- A martingale difference has integral zero on every cell at its scale or
any coarser scale. -/
theorem dyadicDifference_integral_coarseCell_nat {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (m : ℤ) (n : ℕ) (j : ℤ) :
    ∫ x in dyadicInterval (m + n) j, dyadicDifference m f x ∂volume = 0 := by
  have hscale : m - 1 + ((n + 1 : ℕ) : ℤ) = m + n := by omega
  have hleft := dyadicAverage_integral_coarseCell_nat hf (m - 1) (n + 1) j
  have hright := dyadicAverage_integral_coarseCell_nat hf m n j
  have hleftInt :
      IntegrableOn (dyadicAverage (m - 1) f) (dyadicInterval (m + n) j) volume := by
    simpa only [hscale] using hleft.1
  have hrightInt :
      IntegrableOn (dyadicAverage m f) (dyadicInterval (m + n) j) volume := hright.1
  change ∫ x in dyadicInterval (m + n) j,
      dyadicAverage (m - 1) f x - dyadicAverage m f x ∂volume = 0
  rw [MeasureTheory.integral_sub hleftInt hrightInt]
  have hleftEq :
      ∫ x in dyadicInterval (m + n) j, dyadicAverage (m - 1) f x ∂volume =
        ∫ x in dyadicInterval (m + n) j, f x ∂volume := by
    simpa only [hscale] using hleft.2
  rw [hleftEq, hright.2]
  simp

/-- Averaging `E_{m-1} f` at the coarser scale recovers `E_m f`. -/
theorem dyadicAverage_coarse_fine_comp {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (m : ℤ) (x : ℝ) :
    dyadicAverage m (dyadicAverage (m - 1) f) x = dyadicAverage m f x := by
  change ((2 : ℝ) ^ m)⁻¹ •
      ∫ y in dyadicInterval m (dyadicIntervalIndex m x),
        dyadicAverage (m - 1) f y ∂volume =
    ((2 : ℝ) ^ m)⁻¹ •
      ∫ y in dyadicInterval m (dyadicIntervalIndex m x), f y ∂volume
  rw [integral_dyadicAverage_child_over_parent hf m (dyadicIntervalIndex m x)]

/-- Each dyadic difference has integral zero on every cell at its coarser
scale, as in `lj:dyadic-properties`. -/
theorem dyadicDifference_integral_eq_zero {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (m j : ℤ) :
    ∫ x in dyadicInterval m j, dyadicDifference m f x ∂volume = 0 := by
  have hleft :
      IntegrableOn (dyadicAverage (m - 1) f) (dyadicInterval m j) volume := by
    rw [dyadicInterval_eq_two_children]
    rw [MeasureTheory.integrableOn_union]
    exact ⟨integrableOn_dyadicAverage_cell (m - 1) (2 * j) f,
      integrableOn_dyadicAverage_cell (m - 1) (2 * j + 1) f⟩
  have hright :
      IntegrableOn (dyadicAverage m f) (dyadicInterval m j) volume :=
    integrableOn_dyadicAverage_cell m j f
  change ∫ x in dyadicInterval m j,
      dyadicAverage (m - 1) f x - dyadicAverage m f x ∂volume = 0
  rw [MeasureTheory.integral_sub hleft hright,
    integral_dyadicAverage_child_over_parent hf,
    integral_dyadicAverage_eq_integral m j f]
  simp

/-- Averaging a coarser dyadic average on a finer cell leaves it unchanged. -/
theorem dyadicAverage_fine_coarse_comp (m : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    dyadicAverage (m - 1) (dyadicAverage m f) x = dyadicAverage m f x := by
  let j := dyadicIntervalIndex (m - 1) x
  have hx : x ∈ dyadicInterval (m - 1) j := by
    dsimp [j]
    exact mem_dyadicIntervalIndex (m - 1) x
  have hparent := dyadicInterval_parent_subset (m - 1) j
  have hm : m - 1 + 1 = m := by omega
  have hparent' :
      dyadicInterval (m - 1) j ⊆ dyadicInterval m (j / 2) := by
    simpa [hm] using hparent
  have hconstant : ∀ y ∈ dyadicInterval (m - 1) j,
      dyadicAverage m f y = dyadicAverage m f x := by
    intro y hy
    exact dyadicAverage_eq_of_mem_same_cell m (j / 2) f
      (hparent' hy) (hparent' hx)
  exact dyadicAverage_eq_of_eqOn_cell (m := m - 1) (j := j)
    (dyadicAverage m f) (dyadicAverage m f x) hx hconstant

/-- A fine-scale average leaves every coarser dyadic average unchanged. -/
theorem dyadicAverage_fine_coarse_comp_nat (m : ℤ) (n : ℕ)
    (f : ℝ → ℂ) (x : ℝ) :
    dyadicAverage m (dyadicAverage (m + n) f) x = dyadicAverage (m + n) f x := by
  induction n generalizing m f with
  | zero => simpa using dyadicAverage_idempotent m f x
  | succ n ih =>
      let k : ℤ := m + n
      have hk : m + ((n + 1 : ℕ) : ℤ) = k + 1 := by dsimp [k]; omega
      rw [hk]
      have hfun : dyadicAverage k (dyadicAverage (k + 1) f) =
          dyadicAverage (k + 1) f := by
        funext y
        simpa [k] using dyadicAverage_fine_coarse_comp (k + 1) f y
      have hih :
          dyadicAverage m (dyadicAverage k (dyadicAverage (k + 1) f)) x =
            dyadicAverage k (dyadicAverage (k + 1) f) x := by
        simpa [k] using (ih (m := m) (f := dyadicAverage (k + 1) f))
      calc
        dyadicAverage m (dyadicAverage (k + 1) f) x =
            dyadicAverage m (dyadicAverage k (dyadicAverage (k + 1) f)) x := by
          exact congrArg (fun g : ℝ → ℂ => dyadicAverage m g x) hfun.symm
        _ = dyadicAverage k (dyadicAverage (k + 1) f) x := hih
        _ = dyadicAverage (k + 1) f x := congrFun hfun x

/-- If `m ≤ j`, then `E_m E_j = E_j` pointwise. -/
theorem dyadicAverage_comp_of_le {m j : ℤ} (hmj : m ≤ j)
    (f : ℝ → ℂ) (x : ℝ) :
    dyadicAverage m (dyadicAverage j f) x = dyadicAverage j f x := by
  let n : ℕ := (j - m).toNat
  have hn : (n : ℤ) = j - m := by
    dsimp [n]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hmj)
  have hj : m + (n : ℤ) = j := by omega
  rw [← hj]
  exact dyadicAverage_fine_coarse_comp_nat m n f x

/-- If `m ≤ j` and `f` is locally integrable, then `E_j(E_m f)=E_j f`. -/
theorem dyadicAverage_reverse_comp_of_le {m j : ℤ} (hmj : m ≤ j)
    {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) (x : ℝ) :
    dyadicAverage j (dyadicAverage m f) x = dyadicAverage j f x := by
  let n : ℕ := (j - m).toNat
  have hn : (n : ℤ) = j - m := by
    dsimp [n]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hmj)
  have hj : m + (n : ℤ) = j := by omega
  change ((2 : ℝ) ^ j)⁻¹ •
      ∫ y in dyadicInterval j (dyadicIntervalIndex j x), dyadicAverage m f y ∂volume =
    ((2 : ℝ) ^ j)⁻¹ •
      ∫ y in dyadicInterval j (dyadicIntervalIndex j x), f y ∂volume
  congr 1
  simpa only [hj] using
    (dyadicAverage_integral_coarseCell_nat hf m n (dyadicIntervalIndex j x)).2

/-- The pointwise composition identity `E_m E_j = E_max(m,j)` for locally
integrable inputs. -/
theorem dyadicAverage_comp {m j : ℤ} {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (x : ℝ) :
    dyadicAverage m (dyadicAverage j f) x =
      dyadicAverage (max m j) f x := by
  by_cases hmj : m ≤ j
  · rw [dyadicAverage_comp_of_le hmj]
    simp [max_eq_right hmj]
  · have hjm : j ≤ m := le_of_not_ge hmj
    rw [dyadicAverage_reverse_comp_of_le hjm hf]
    simp [max_eq_left hjm]

/-- The two adjacent-scale compositions both equal the coarser average. -/
theorem dyadicAverage_adjacent_composition {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (m : ℤ) (x : ℝ) :
    dyadicAverage m (dyadicAverage (m + 1) f) x = dyadicAverage (m + 1) f x ∧
      dyadicAverage (m + 1) (dyadicAverage m f) x = dyadicAverage (m + 1) f x := by
  have hscale : m + 1 - 1 = m := by omega
  constructor
  · simpa only [hscale] using dyadicAverage_fine_coarse_comp (m + 1) f x
  · simpa only [hscale] using dyadicAverage_coarse_fine_comp hf (m + 1) x

/-- `Δ_m f` is constant on every cell of length `2^(m-1)`. -/
theorem dyadicDifference_eq_of_mem_same_fine_cell (m j : ℤ) (f : ℝ → ℂ)
    {x y : ℝ} (hx : x ∈ dyadicInterval (m - 1) j)
    (hy : y ∈ dyadicInterval (m - 1) j) :
    dyadicDifference m f x = dyadicDifference m f y := by
  have hxParent := dyadicInterval_parent_subset (m - 1) j hx
  have hyParent := dyadicInterval_parent_subset (m - 1) j hy
  have hm : m - 1 + 1 = m := by omega
  have hxParent' : x ∈ dyadicInterval m (j / 2) := by simpa [hm] using hxParent
  have hyParent' : y ∈ dyadicInterval m (j / 2) := by simpa [hm] using hyParent
  have hfine := dyadicAverage_eq_of_mem_same_cell (m - 1) j f hx hy
  have hcoarse := dyadicAverage_eq_of_mem_same_cell m (j / 2) f hxParent' hyParent'
  unfold dyadicDifference
  rw [hfine, hcoarse]

/-- On each scale-`n-1` cell, a finer martingale difference is orthogonal to
the scale-`n` difference: the latter is constant there, and the former has
zero integral on that cell. -/
theorem dyadicDifference_localOrthogonality {f g : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) {m n : ℤ} (hmn : m < n) (j : ℤ) :
    ∫ x in dyadicInterval (n - 1) j,
      dyadicDifference m f x * star (dyadicDifference n g x) ∂volume = 0 := by
  have hgap_nonneg : 0 ≤ n - 1 - m := by omega
  let q : ℕ := (n - 1 - m).toNat
  have hq : (q : ℤ) = n - 1 - m := by
    dsimp [q]
    exact Int.toNat_of_nonneg hgap_nonneg
  have hscale : m + (q : ℤ) = n - 1 := by omega
  let s := dyadicInterval (n - 1) j
  let a := (j : ℝ) * (2 : ℝ) ^ (n - 1)
  have ha : a ∈ s := by
    change a ∈ dyadicInterval (n - 1) j
    rw [dyadicInterval, Set.mem_Ico]
    constructor
    · dsimp [a]
      exact le_rfl
    · have hpos := dyadicScale_pos' (n - 1)
      have hlen : (((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (n - 1)) -
          (j : ℝ) * (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ (n - 1) := by
        push_cast
        ring
      dsimp [a]
      linarith
  have hconst : ∀ x ∈ s, dyadicDifference n g x = dyadicDifference n g a := by
    intro x hx
    exact dyadicDifference_eq_of_mem_same_fine_cell n j g hx ha
  have hset : MeasurableSet s := by
    dsimp [s, dyadicInterval]
    exact measurableSet_Ico
  have hIntLeft :
      IntegrableOn (dyadicAverage (m - 1) f) s volume := by
    have h := dyadicAverage_integral_coarseCell_nat hf (m - 1) (q + 1) j
    have hscale' : m - 1 + ((q + 1 : ℕ) : ℤ) = n - 1 := by omega
    change IntegrableOn (dyadicAverage (m - 1) f) (dyadicInterval (n - 1) j) volume
    simpa only [hscale'] using h.1
  have hIntRight : IntegrableOn (dyadicAverage m f) s volume := by
    have h := dyadicAverage_integral_coarseCell_nat hf m q j
    change IntegrableOn (dyadicAverage m f) (dyadicInterval (n - 1) j) volume
    simpa only [hscale] using h.1
  have hDeltaInt : IntegrableOn (dyadicDifference m f) s volume := by
    change IntegrableOn
      (dyadicAverage (m - 1) f - dyadicAverage m f) s volume
    exact hIntLeft.sub hIntRight
  have hzero : ∫ x in s, dyadicDifference m f x ∂volume = 0 := by
    have h := dyadicDifference_integral_coarseCell_nat hf m q j
    change ∫ x in dyadicInterval (n - 1) j, dyadicDifference m f x ∂volume = 0
    simpa only [hscale] using h
  have hproduct :
      ∫ x in s, dyadicDifference m f x *
          star (dyadicDifference n g x) ∂volume =
        ∫ x in s, dyadicDifference m f x *
          star (dyadicDifference n g a) ∂volume := by
    apply MeasureTheory.setIntegral_congr_fun hset
    intro x hx
    change dyadicDifference m f x * star (dyadicDifference n g x) =
      dyadicDifference m f x * star (dyadicDifference n g a)
    rw [hconst x hx]
  rw [hproduct]
  have hmul :
      ∫ x in s, dyadicDifference m f x *
          star (dyadicDifference n g a) ∂volume =
        (∫ x in s, dyadicDifference m f x ∂volume) *
          star (dyadicDifference n g a) := by
    simpa [s] using MeasureTheory.integral_mul_const
      (μ := volume.restrict s) (star (dyadicDifference n g a))
      (dyadicDifference m f)
  rw [hmul, hzero]
  simp

/-- Distinct dyadic differences are orthogonal in `L²`. -/
theorem dyadicDifference_orthogonal {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    {m n : ℤ} (hmn : m < n) :
    ∫ x, dyadicDifference m f x * star (dyadicDifference n g x) ∂volume = 0 := by
  have hEf (k : ℤ) : MemLp (dyadicAverage k f) 2 volume := by
    apply memLp_iff.mpr
    exact (eLpNorm_two_dyadicAverage_le hf k).trans_lt hf.eLpNorm_lt_top
  have hEg (k : ℤ) : MemLp (dyadicAverage k g) 2 volume := by
    apply memLp_iff.mpr
    exact (eLpNorm_two_dyadicAverage_le hg k).trans_lt hg.eLpNorm_lt_top
  have hΔf : MemLp (dyadicDifference m f) 2 volume := by
    change MemLp (dyadicAverage (m - 1) f - dyadicAverage m f) 2 volume
    exact (hEf (m - 1)).sub (hEf m)
  have hΔg : MemLp (dyadicDifference n g) 2 volume := by
    change MemLp (dyadicAverage (n - 1) g - dyadicAverage n g) 2 volume
    exact (hEg (n - 1)).sub (hEg n)
  have hproduct : Integrable
      (fun x : ℝ => dyadicDifference m f x * star (dyadicDifference n g x)) volume :=
    MemLp.integrable_mul hΔf hΔg.star
  let Q : ℤ → Set ℝ := fun j => dyadicInterval (n - 1) j
  have hcover : ⋃ j, Q j = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨dyadicIntervalIndex (n - 1) x,
      by simpa [Q] using mem_dyadicIntervalIndex (n - 1) x⟩
  have hQ : ∀ j, MeasurableSet (Q j) := by
    intro j
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hdisj : Pairwise (fun i j : ℤ => Disjoint (Q i) (Q j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    calc
      i = dyadicIntervalIndex (n - 1) x :=
        (dyadicIntervalIndex_eq_of_mem (by simpa [Q] using hxi)).symm
      _ = j := dyadicIntervalIndex_eq_of_mem (by simpa [Q] using hxj)
  have hIntUnion :
      IntegrableOn
        (fun x : ℝ => dyadicDifference m f x * star (dyadicDifference n g x))
        (⋃ j, Q j) volume := by
    rw [hcover]
    exact hproduct.integrableOn
  have hsum := MeasureTheory.integral_iUnion (μ := volume) hQ hdisj hIntUnion
  have hzero (j : ℤ) :
      ∫ x in Q j,
        dyadicDifference m f x * star (dyadicDifference n g x) ∂volume = 0 := by
    simpa [Q] using dyadicDifference_localOrthogonality
      (hf.locallyIntegrable (by norm_num)) hmn j
  rw [hcover] at hsum
  have htsum :
      ∑' j : ℤ, ∫ x in Q j,
        dyadicDifference m f x * star (dyadicDifference n g x) ∂volume = 0 := by
    simp only [hzero, tsum_zero]
  rw [htsum] at hsum
  simpa using hsum

/-- Any two different dyadic differences are orthogonal in `L²`. -/
theorem dyadicDifference_pairwise_orthogonal {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    {m n : ℤ} (hmn : m ≠ n) :
    ∫ x, dyadicDifference m f x * star (dyadicDifference n g x) ∂volume = 0 := by
  rcases lt_or_gt_of_ne hmn with hmn' | hnm
  · exact dyadicDifference_orthogonal hf hg hmn'
  · have hreverse := dyadicDifference_orthogonal hg hf hnm
    calc
      ∫ x, dyadicDifference m f x * star (dyadicDifference n g x) ∂volume =
          star (∫ x, dyadicDifference n g x * star (dyadicDifference m f x) ∂volume) := by
        calc
          ∫ x, dyadicDifference m f x * star (dyadicDifference n g x) ∂volume =
              ∫ x, star (dyadicDifference n g x *
                star (dyadicDifference m f x)) ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with x
            simp [star_mul]
          _ = star (∫ x, dyadicDifference n g x *
              star (dyadicDifference m f x) ∂volume) := integral_conj
      _ = 0 := by rw [hreverse]; simp

/-- Finite dyadic differences telescope to the difference of their endpoint
averages. -/
theorem dyadicDifference_finite_telescope (a : ℤ) (n : ℕ)
    (f : ℝ → ℂ) (x : ℝ) :
    ∑ k ∈ Finset.range n,
        dyadicDifference (a + (k : ℤ) + 1) f x =
      dyadicAverage a f x - dyadicAverage (a + n) f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold dyadicDifference
    rw [show a + (n : ℤ) + 1 - 1 = a + (n : ℤ) by omega]
    rw [show a + (n : ℤ) + 1 = a + ((n + 1 : ℕ) : ℤ) by
      push_cast
      omega]
    ring

/-- The dyadic averaging operator is self-adjoint on `L²`. -/
theorem dyadicAverage_selfAdjoint {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (m : ℤ) :
    ∫ x, dyadicAverage m f x * star (g x) ∂volume =
      ∫ x, f x * star (dyadicAverage m g x) ∂volume := by
  have hEf : MemLp (dyadicAverage m f) 2 volume := by
    apply memLp_iff.mpr
    exact (eLpNorm_two_dyadicAverage_le hf m).trans_lt hf.eLpNorm_lt_top
  have hEg : MemLp (dyadicAverage m g) 2 volume := by
    apply memLp_iff.mpr
    exact (eLpNorm_two_dyadicAverage_le hg m).trans_lt hg.eLpNorm_lt_top
  have hleftInt : Integrable
      (fun x : ℝ => dyadicAverage m f x * star (g x)) volume :=
    MemLp.integrable_mul hEf hg.star
  have hrightInt : Integrable
      (fun x : ℝ => f x * star (dyadicAverage m g x)) volume :=
    MemLp.integrable_mul hf hEg.star
  let Q : ℤ → Set ℝ := fun j => dyadicInterval m j
  have hcover : ⋃ j, Q j = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨dyadicIntervalIndex m x,
      by simpa [Q] using mem_dyadicIntervalIndex m x⟩
  have hQ : ∀ j, MeasurableSet (Q j) := by
    intro j
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hdisj : Pairwise (fun i j : ℤ => Disjoint (Q i) (Q j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    calc
      i = dyadicIntervalIndex m x :=
        (dyadicIntervalIndex_eq_of_mem (by simpa [Q] using hxi)).symm
      _ = j := dyadicIntervalIndex_eq_of_mem (by simpa [Q] using hxj)
  have hleftUnion : IntegrableOn
      (fun x : ℝ => dyadicAverage m f x * star (g x)) (⋃ j, Q j) volume := by
    rw [hcover]
    exact hleftInt.integrableOn
  have hrightUnion : IntegrableOn
      (fun x : ℝ => f x * star (dyadicAverage m g x)) (⋃ j, Q j) volume := by
    rw [hcover]
    exact hrightInt.integrableOn
  have hleftSum :
      ∫ x, dyadicAverage m f x * star (g x) ∂volume =
        ∑' j : ℤ, ∫ x in Q j, dyadicAverage m f x * star (g x) ∂volume := by
    have h := MeasureTheory.integral_iUnion (μ := volume) hQ hdisj hleftUnion
    rw [hcover] at h
    simpa using h
  have hrightSum :
      ∫ x, f x * star (dyadicAverage m g x) ∂volume =
        ∑' j : ℤ, ∫ x in Q j, f x * star (dyadicAverage m g x) ∂volume := by
    have h := MeasureTheory.integral_iUnion (μ := volume) hQ hdisj hrightUnion
    rw [hcover] at h
    simpa using h
  calc
    ∫ x, dyadicAverage m f x * star (g x) ∂volume =
        ∑' j : ℤ, ∫ x in Q j, dyadicAverage m f x * star (g x) ∂volume := hleftSum
    _ = ∑' j : ℤ, ∫ x in Q j, f x * star (dyadicAverage m g x) ∂volume := by
      apply tsum_congr
      intro j
      simpa [Q] using integral_dyadicAverage_selfAdjoint_on_cell m j
    _ = ∫ x, f x * star (dyadicAverage m g x) ∂volume := hrightSum.symm

end

end FractionalPrimes.Literature.JSW

end
