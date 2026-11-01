module

public import FractionalPrimes.Literature.JSW.Conventions
public import FractionalPrimes.Literature.JSW.DyadicAverage
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import FractionalPrimes.Literature.Variation.LayerCakeInterpolation

/-!
# Maximal averages on the line

This module formalizes the centered Hardy–Littlewood maximal operator, its
weak `(1,1)` and strong `L^p` estimates, and the weak estimate for the
half-open dyadic maximal operator from `lj:maximal`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Interval Topology
open intervalIntegral

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The average of `‖f‖` over the centered interval of radius `r`. -/
def lineCenteredAverage (f : ℝ → ℂ) (x r : ℝ) : ℝ :=
  (∫ y in x - r..x + r, ‖f y‖) / (2 * r)

/-- A primitive of the locally integrable function `‖f‖`. -/
def lineMaximalPrimitive (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, ‖f y‖

/-- The centered maximal function, with the supremum over all positive radii. -/
def lineMaximal (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ // 0 < r},
    ENNReal.ofReal (lineCenteredAverage f x r.1)

/-- The rational-radius presentation used to prove measurability. -/
def lineMaximalRat (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ r : {r : ℚ // 0 < r},
    ENNReal.ofReal (lineCenteredAverage f x (r.1 : ℝ))

/-- The real representative of the extended-valued maximal function. -/
def lineMaximalReal (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  (lineMaximal f x).toReal

/-- The strict high-magnitude part of an input at cutoff `a`. -/
def lineMaximalHighCutoff (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  {x | a < ‖f x‖}.indicator f

/-- The inclusive low-magnitude part of an input at cutoff `a`. -/
def lineMaximalLowCutoff (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  {x | ‖f x‖ ≤ a}.indicator f

private theorem locallyIntegrable_norm_intervalIntegrable
    {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) (a b : ℝ) :
    IntervalIntegrable (fun x => ‖f x‖) volume a b := by
  have hfnorm : LocallyIntegrable (fun x => ‖f x‖) volume := by
    rw [← locallyIntegrableOn_univ] at hf ⊢
    exact hf.norm
  exact intervalIntegrable_iff.mpr
    ((hfnorm.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

theorem lineMaximalPrimitive_continuous {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) :
    Continuous (lineMaximalPrimitive f) := by
  exact intervalIntegral.continuous_primitive
    (fun a b => locallyIntegrable_norm_intervalIntegrable hf a b) 0

theorem lineCenteredAverage_eq_primitive {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (x r : ℝ) :
    lineCenteredAverage f x r =
      (lineMaximalPrimitive f (x + r) - lineMaximalPrimitive f (x - r)) /
        (2 * r) := by
  unfold lineCenteredAverage lineMaximalPrimitive
  rw [← intervalIntegral.integral_interval_sub_left
    (locallyIntegrable_norm_intervalIntegrable hf 0 (x + r))
    (locallyIntegrable_norm_intervalIntegrable hf 0 (x - r))]

private theorem lineCenteredAverage_nonneg {f : ℝ → ℂ}
    (x r : ℝ) (hr : 0 < r) :
    0 ≤ lineCenteredAverage f x r := by
  unfold lineCenteredAverage
  apply div_nonneg
  · exact intervalIntegral.integral_nonneg (by linarith)
      (fun y _ => norm_nonneg (f y))
  · positivity

private theorem lineCenteredAverage_integral_le {f : ℝ → ℂ}
    (hf : Integrable f volume) (x r : ℝ) (hr : 0 < r) :
    (∫ y in x - r..x + r, ‖f y‖) ≤ ∫ y, ‖f y‖ := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  apply setIntegral_le_integral hf.norm
  filter_upwards with y
  exact norm_nonneg (f y)

private theorem lineCenteredAverage_radius_le {f : ℝ → ℂ}
    (hf : Integrable f volume) (t : ℝ) (ht : 0 < t)
    (x r : ℝ) (hr : 0 < r)
    (havg : t < lineCenteredAverage f x r) :
    r < (∫ y, ‖f y‖) / (2 * t) := by
  have hden : 0 < 2 * r := by positivity
  have hmass : t * (2 * r) < ∫ y in x - r..x + r, ‖f y‖ := by
    exact (lt_div_iff₀ hden).mp (by simpa [lineCenteredAverage] using havg)
  have hmass' : t * (2 * r) < ∫ y, ‖f y‖ :=
    lt_of_lt_of_le hmass (lineCenteredAverage_integral_le hf x r hr)
  rw [lt_div_iff₀ (by positivity : 0 < 2 * t)]
  nlinarith

private theorem lineCenteredAverage_mass_gt {f : ℝ → ℂ}
    (t : ℝ) (x r : ℝ) (hr : 0 < r)
    (havg : t < lineCenteredAverage f x r) :
    t * (2 * r) < ∫ y in Set.Ioo (x - r) (x + r), ‖f y‖ := by
  have hden : 0 < 2 * r := by positivity
  have hmass : t * (2 * r) < ∫ y in x - r..x + r, ‖f y‖ := by
    exact (lt_div_iff₀ hden).mp (by simpa [lineCenteredAverage] using havg)
  rw [intervalIntegral.integral_of_le (by linarith : x - r ≤ x + r),
    integral_Ioc_eq_integral_Ioo] at hmass
  exact hmass

private theorem continuous_lineCenteredAverage_radius
    {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) (x : ℝ) :
    ContinuousOn (fun r : ℝ => lineCenteredAverage f x r) (Ioi 0) := by
  have hprimitive := lineMaximalPrimitive_continuous hf
  have hnum : Continuous (fun r : ℝ =>
      lineMaximalPrimitive f (x + r) - lineMaximalPrimitive f (x - r)) := by
    exact (hprimitive.comp (continuous_const.add continuous_id)).sub
      (hprimitive.comp (continuous_const.sub continuous_id))
  have hdiv : ContinuousOn (fun r : ℝ =>
      (lineMaximalPrimitive f (x + r) - lineMaximalPrimitive f (x - r)) / (2 * r))
      (Ioi 0) := by
    apply hnum.continuousOn.div
    · fun_prop
    · intro r hr
      exact ne_of_gt (mul_pos (by norm_num) (mem_Ioi.mp hr))
  have hEq : (fun r : ℝ => lineCenteredAverage f x r) =
      (fun r => (lineMaximalPrimitive f (x + r) -
        lineMaximalPrimitive f (x - r)) / (2 * r)) := by
    funext r
    exact lineCenteredAverage_eq_primitive hf x r
  rw [hEq]
  exact hdiv

private theorem lineMaximal_eq_lineMaximalRat {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (x : ℝ) :
    lineMaximal f x = lineMaximalRat f x := by
  apply le_antisymm
  · apply iSup_le
    intro r
    let u := (Real.exists_seq_rat_strictAnti_tendsto r.1).choose
    have hu := (Real.exists_seq_rat_strictAnti_tendsto r.1).choose_spec
    have hpos (n : ℕ) : (0 : ℝ) < (u n : ℝ) := lt_trans r.2 (hu.2.1 n)
    have hseq : Tendsto (fun n : ℕ => (u n : ℝ)) atTop (𝓝 r.1) := hu.2.2
    have hcontinuous := continuous_lineCenteredAverage_radius hf x
    have hradius : Ioi (0 : ℝ) ∈ 𝓝 r.1 := isOpen_Ioi.mem_nhds r.2
    have havg : ContinuousAt (fun ρ : ℝ =>
        ENNReal.ofReal (lineCenteredAverage f x ρ)) r.1 := by
      exact ENNReal.continuous_ofReal.continuousAt.comp
        (hcontinuous.continuousAt hradius)
    have hlimit := havg.tendsto.comp hseq
    apply le_of_tendsto' hlimit
    intro n
    let q : {q : ℚ // 0 < q} := ⟨u n, by exact_mod_cast hpos n⟩
    change ENNReal.ofReal (lineCenteredAverage f x (u n : ℝ)) ≤ lineMaximalRat f x
    exact le_iSup_of_le q le_rfl
  · apply iSup_le
    intro r
    let s : {s : ℝ // 0 < s} := ⟨(r.1 : ℚ), by exact_mod_cast r.2⟩
    change ENNReal.ofReal (lineCenteredAverage f x (r.1 : ℝ)) ≤
      ⨆ s : {s : ℝ // 0 < s}, ENNReal.ofReal (lineCenteredAverage f x s.1)
    exact le_iSup_of_le s le_rfl

private theorem lineMaximalRat_levelSet_isOpen {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (t : ℝ) :
    IsOpen {x : ℝ | ENNReal.ofReal t < lineMaximalRat f x} := by
  have hEq : {x : ℝ | ENNReal.ofReal t < lineMaximalRat f x} =
      ⋃ r : {r : ℚ // 0 < r},
        {x : ℝ | ENNReal.ofReal t <
          ENNReal.ofReal (lineCenteredAverage f x (r.1 : ℝ))} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, lineMaximalRat]
    exact lt_iSup_iff
  rw [hEq]
  refine isOpen_iUnion fun r => ?_
  have hcont : Continuous (fun x : ℝ =>
      ENNReal.ofReal (lineCenteredAverage f x (r.1 : ℝ))) := by
    have hprimitive := lineMaximalPrimitive_continuous hf
    have hnum : Continuous (fun x : ℝ =>
        lineMaximalPrimitive f (x + (r.1 : ℝ)) -
          lineMaximalPrimitive f (x - (r.1 : ℝ))) := by
      exact (hprimitive.comp (continuous_id.add continuous_const)).sub
        (hprimitive.comp (continuous_id.sub continuous_const))
    have hEq : (fun x : ℝ => lineCenteredAverage f x (r.1 : ℝ)) =
        (fun x => (lineMaximalPrimitive f (x + (r.1 : ℝ)) -
          lineMaximalPrimitive f (x - (r.1 : ℝ))) / (2 * (r.1 : ℝ))) := by
      funext x
      exact lineCenteredAverage_eq_primitive hf x (r.1 : ℝ)
    have havg : Continuous (fun x : ℝ => lineCenteredAverage f x (r.1 : ℝ)) := by
      rw [hEq]
      exact hnum.div_const _
    exact ENNReal.continuous_ofReal.comp havg
  exact isOpen_Ioi.preimage hcont

private theorem lineMaximal_levelSet_isOpen {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (t : ℝ) :
    IsOpen {x : ℝ | ENNReal.ofReal t < lineMaximal f x} := by
  have hEq : {x : ℝ | ENNReal.ofReal t < lineMaximal f x} =
      {x : ℝ | ENNReal.ofReal t < lineMaximalRat f x} := by
    ext x
    change ENNReal.ofReal t < lineMaximal f x ↔
      ENNReal.ofReal t < lineMaximalRat f x
    rw [lineMaximal_eq_lineMaximalRat hf x]
  rw [hEq]
  exact lineMaximalRat_levelSet_isOpen hf t

private theorem lineMaximal_compact_weak_bound {f : ℝ → ℂ}
    (hf : Integrable f volume) (t : ℝ) (ht : 0 < t)
    (s : Set ℝ) (hs : s ⊆ {x | ENNReal.ofReal t < lineMaximal f x})
    (hscompact : IsCompact s) (τ : ℝ) (hτ : 3 < τ) :
    volume s ≤ ENNReal.ofReal (τ * (∫ y, ‖f y‖) / t) := by
  let hloc := hf.locallyIntegrable
  have hW : ∀ x : s, ∃ q : {q : ℚ // 0 < q},
      t < lineCenteredAverage f x.1 (q.1 : ℝ) := by
    intro x
    have hx : ENNReal.ofReal t < lineMaximalRat f x.1 := by
      rw [← lineMaximal_eq_lineMaximalRat hloc x.1]
      exact hs x.2
    have hx' : ENNReal.ofReal t <
        ⨆ q : {q : ℚ // 0 < q},
          ENNReal.ofReal (lineCenteredAverage f x.1 (q.1 : ℝ)) := by
      simpa [lineMaximalRat] using hx
    rcases lt_iSup_iff.mp hx' with ⟨q, hq⟩
    exact ⟨q, (ENNReal.ofReal_lt_ofReal_iff').mp hq |>.1⟩
  let rad : s → {q : ℚ // 0 < q} := fun x => Classical.choose (hW x)
  have hrad : ∀ x : s, t < lineCenteredAverage f x.1 ((rad x).1 : ℝ) :=
    fun x => Classical.choose_spec (hW x)
  let U : s → Set ℝ := fun x => Metric.ball x.1 ((rad x).1 : ℝ)
  have hcover : s ⊆ ⋃ x : s, U x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by exact_mod_cast (rad ⟨x, hx⟩).2)⟩
  obtain ⟨F, hF⟩ := hscompact.elim_finite_subcover U (fun x => Metric.isOpen_ball)
    (by simpa [U] using hcover)
  have hR : ∀ x : s, x ∈ (F : Set s) →
      ((rad x).1 : ℝ) ≤ (∫ y, ‖f y‖) / (2 * t) := by
    intro x _
    exact (lineCenteredAverage_radius_le hf t ht x.1 ((rad x).1 : ℝ)
      (by exact_mod_cast (rad x).2) (hrad x)).le
  obtain ⟨u, huF, huDisj, huCover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (t := (F : Set s)) (x := fun x : s => x.1)
      (r := fun x : s => (rad x).1) ((∫ y, ‖f y‖) / (2 * t)) hR τ hτ
  have hsCover : s ⊆ ⋃ x ∈ u,
      Metric.ball x.1 (τ * (rad x).1) := by
    intro y hy
    obtain ⟨x, hxF, hyx⟩ := Set.mem_iUnion₂.mp (hF hy)
    obtain ⟨z, hzu, hball⟩ := huCover x hxF
    exact Set.mem_iUnion₂.mpr ⟨z, hzu, hball hyx⟩
  have huFinite : u.Finite := F.finite_toSet.subset huF
  let uFin := huFinite.toFinset
  have huFinCo : (uFin : Set s) = u := huFinite.coe_toFinset
  have hlength : (∑ x ∈ uFin, 2 * ((rad x).1 : ℝ)) ≤ (∫ y, ‖f y‖) / t := by
    have hdisjIoo : Set.Pairwise (↑uFin) (fun x y => Disjoint
        (Set.Ioo (x.1 - ((rad x).1 : ℝ)) (x.1 + ((rad x).1 : ℝ)))
        (Set.Ioo (y.1 - ((rad y).1 : ℝ)) (y.1 + ((rad y).1 : ℝ)))) := by
      intro x hx y hy hxy
      have hxy' := huDisj (by simpa [huFinCo] using hx)
        (by simpa [huFinCo] using hy) hxy
      change Disjoint (Metric.ball x.1 ((rad x).1 : ℝ))
        (Metric.ball y.1 ((rad y).1 : ℝ)) at hxy'
      simpa only [Real.ball_eq_Ioo] using hxy'
    have hsumInt : t * (∑ x ∈ uFin, 2 * ((rad x).1 : ℝ)) ≤
        ∫ y in ⋃ x ∈ uFin,
          Set.Ioo (x.1 - ((rad x).1 : ℝ)) (x.1 + ((rad x).1 : ℝ)), ‖f y‖ := by
      calc
        t * (∑ x ∈ uFin, 2 * ((rad x).1 : ℝ)) =
            ∑ x ∈ uFin, t * (2 * ((rad x).1 : ℝ)) := by rw [Finset.mul_sum]
        _ ≤ ∑ x ∈ uFin,
            ∫ y in Set.Ioo (x.1 - ((rad x).1 : ℝ))
              (x.1 + ((rad x).1 : ℝ)), ‖f y‖ := by
              apply Finset.sum_le_sum
              intro x hx
              exact (lineCenteredAverage_mass_gt t x.1 ((rad x).1 : ℝ)
                (by exact_mod_cast (rad x).2) (hrad x)).le
        _ = ∫ y in ⋃ x ∈ uFin,
            Set.Ioo (x.1 - ((rad x).1 : ℝ)) (x.1 + ((rad x).1 : ℝ)), ‖f y‖ := by
              symm
              apply integral_biUnion_finset uFin
              · intro x hx
                exact isOpen_Ioo.measurableSet
              · exact hdisjIoo
              · intro x hx
                exact hf.norm.integrableOn
    have htotal :
        (∫ y in ⋃ x ∈ uFin,
          Set.Ioo (x.1 - ((rad x).1 : ℝ)) (x.1 + ((rad x).1 : ℝ)), ‖f y‖) ≤
          ∫ y, ‖f y‖ := by
      apply setIntegral_le_integral hf.norm
      filter_upwards with y
      exact norm_nonneg (f y)
    rw [le_div_iff₀ ht]
    nlinarith [hsumInt.trans htotal]
  have hmeasure : volume (⋃ x ∈ u,
      Metric.ball x.1 (τ * (rad x).1)) ≤
      ∑ x ∈ uFin, volume (Metric.ball x.1 (τ * (rad x).1)) := by
    rw [← huFinCo]
    exact measure_biUnion_finset_le uFin
      (fun x : s => Metric.ball x.1 (τ * (rad x).1))
  have hsumVolume :
      (∑ x ∈ uFin, volume (Metric.ball x.1 (τ * (rad x).1))) ≤
        ENNReal.ofReal (τ * (∫ y, ‖f y‖) / t) := by
    have hsumEq : (∑ x ∈ uFin, volume (Metric.ball x.1 (τ * (rad x).1))) =
        ENNReal.ofReal (∑ x ∈ uFin, 2 * τ * ((rad x).1 : ℝ)) := by
      calc
        _ = ∑ x ∈ uFin, ENNReal.ofReal (2 * τ * ((rad x).1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Real.volume_ball]
          congr 1
          ring
        _ = ENNReal.ofReal (∑ x ∈ uFin, 2 * τ * ((rad x).1 : ℝ)) := by
          exact (ENNReal.ofReal_sum_of_nonneg (fun x hx =>
            mul_nonneg (mul_nonneg (by norm_num) (by linarith))
              (by exact_mod_cast (rad x).2.le))).symm
    rw [hsumEq]
    have hsumCast : (∑ x ∈ uFin, 2 * τ * ((rad x).1 : ℝ)) =
        τ * (∑ x ∈ uFin, 2 * ((rad x).1 : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hsumCast]
    apply ENNReal.ofReal_le_ofReal
    have hmul : τ * (∑ x ∈ uFin, 2 * ((rad x).1 : ℝ)) ≤
        τ * ((∫ y, ‖f y‖) / t) :=
      mul_le_mul_of_nonneg_left hlength (by linarith)
    calc
      τ * (∑ x ∈ uFin, 2 * ((rad x).1 : ℝ)) ≤
          τ * ((∫ y, ‖f y‖) / t) := hmul
      _ = τ * (∫ y, ‖f y‖) / t := by ring
  calc
    volume s ≤ volume (⋃ x ∈ u, Metric.ball x.1 (τ * (rad x).1)) :=
      measure_mono hsCover
    _ ≤ ∑ x ∈ uFin, volume (Metric.ball x.1 (τ * (rad x).1)) := hmeasure
    _ ≤ ENNReal.ofReal (τ * (∫ y, ‖f y‖) / t) := hsumVolume

/-- The centered maximal operator obeys the exact weak `(1,1)` estimate with
constant `3`. -/
theorem lineMaximal_weakType_one {f : ℝ → ℂ} (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) :
    volume {x : ℝ | ENNReal.ofReal t < lineMaximal f x} ≤
      ENNReal.ofReal (3 * (∫ y, ‖f y‖) / t) := by
  let U : Set ℝ := {x : ℝ | ENNReal.ofReal t < lineMaximal f x}
  have hUopen : IsOpen U := lineMaximal_levelSet_isOpen hf.locallyIntegrable t
  have hτbound : ∀ τ : ℝ, 3 < τ →
      volume U ≤ ENNReal.ofReal (τ * (∫ y, ‖f y‖) / t) := by
    intro τ hτ
    rw [hUopen.measure_eq_iSup_isCompact volume]
    apply iSup_le
    intro K
    apply iSup_le
    intro hKU
    apply iSup_le
    intro hKcompact
    exact lineMaximal_compact_weak_bound hf t ht K hKU hKcompact τ hτ
  obtain ⟨u, huanti, huabove, huseq⟩ := Real.exists_seq_rat_strictAnti_tendsto (3 : ℝ)
  have hlim : Tendsto (fun n : ℕ =>
      ENNReal.ofReal ((u n : ℝ) * (∫ y, ‖f y‖) / t)) atTop
      (𝓝 (ENNReal.ofReal (3 * (∫ y, ‖f y‖) / t))) := by
    have hcont : Continuous (fun z : ℝ =>
        ENNReal.ofReal (z * (∫ y, ‖f y‖) / t)) := by
      exact ENNReal.continuous_ofReal.comp
        ((continuous_id.mul_const (∫ y, ‖f y‖)).div_const t)
    exact hcont.continuousAt.tendsto.comp huseq
  have hbound : ∀ n : ℕ, volume U ≤
      ENNReal.ofReal ((u n : ℝ) * (∫ y, ‖f y‖) / t) := by
    intro n
    exact hτbound (u n : ℝ) (huabove n)
  have hconst : Tendsto (fun _ : ℕ => volume U) atTop (𝓝 (volume U)) := tendsto_const_nhds
  have hresult := le_of_tendsto_of_tendsto' hconst hlim hbound
  simpa [U] using hresult

theorem lineMaximal_measurable_of_locallyIntegrable
    {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) :
    Measurable (lineMaximal f) := by
  have hrat : Measurable (lineMaximalRat f) := by
    apply Measurable.iSup
    intro r
    have hcont : Continuous (fun x : ℝ => lineCenteredAverage f x (r.1 : ℝ)) := by
      have hprimitive := lineMaximalPrimitive_continuous hf
      have hnum : Continuous (fun x : ℝ =>
          lineMaximalPrimitive f (x + (r.1 : ℝ)) -
            lineMaximalPrimitive f (x - (r.1 : ℝ))) := by
        exact (hprimitive.comp (continuous_id.add continuous_const)).sub
          (hprimitive.comp (continuous_id.sub continuous_const))
      have hEq : (fun x : ℝ => lineCenteredAverage f x (r.1 : ℝ)) =
          (fun x => (lineMaximalPrimitive f (x + (r.1 : ℝ)) -
            lineMaximalPrimitive f (x - (r.1 : ℝ))) / (2 * (r.1 : ℝ))) := by
        funext x
        exact lineCenteredAverage_eq_primitive hf x (r.1 : ℝ)
      rw [hEq]
      exact hnum.div_const _
    exact ENNReal.continuous_ofReal.measurable.comp hcont.measurable
  have heq : lineMaximal f = lineMaximalRat f := by
    funext x
    exact lineMaximal_eq_lineMaximalRat hf x
  rw [heq]
  exact hrat

theorem lineMaximalReal_measurable_of_locallyIntegrable
    {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) :
    Measurable (lineMaximalReal f) :=
  ENNReal.measurable_toReal.comp (lineMaximal_measurable_of_locallyIntegrable hf)

private theorem lineCenteredAverage_add_le {f g : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (x r : ℝ) (hr : 0 < r) :
    lineCenteredAverage (fun y => f y + g y) x r ≤
      lineCenteredAverage f x r + lineCenteredAverage g x r := by
  have hsum : LocallyIntegrable (fun y : ℝ => f y + g y) volume := hf.add hg
  have hsumInt := locallyIntegrable_norm_intervalIntegrable hsum (x - r) (x + r)
  have hfInt := locallyIntegrable_norm_intervalIntegrable hf (x - r) (x + r)
  have hgInt := locallyIntegrable_norm_intervalIntegrable hg (x - r) (x + r)
  have hmono :
      (∫ y in x - r..x + r, ‖f y + g y‖) ≤
        ∫ y in x - r..x + r, ‖f y‖ + ‖g y‖ := by
    apply intervalIntegral.integral_mono_on (by linarith) hsumInt
      (hfInt.add hgInt)
    intro y _
    exact norm_add_le (f y) (g y)
  have hadd :
      (∫ y in x - r..x + r, ‖f y‖ + ‖g y‖) =
        (∫ y in x - r..x + r, ‖f y‖) +
          (∫ y in x - r..x + r, ‖g y‖) :=
    intervalIntegral.integral_add hfInt hgInt
  change
    (∫ y in x - r..x + r, ‖f y + g y‖) / (2 * r) ≤
      (∫ y in x - r..x + r, ‖f y‖) / (2 * r) +
        (∫ y in x - r..x + r, ‖g y‖) / (2 * r)
  rw [← add_div]
  exact (div_le_div_of_nonneg_right (hmono.trans_eq hadd) (by positivity))

private theorem lineCenteredAverage_congr_ae {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) (x r : ℝ) :
    lineCenteredAverage f x r = lineCenteredAverage g x r := by
  unfold lineCenteredAverage
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hfg] with y hy
  simpa [hy]

private theorem lineMaximal_congr_ae {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) (x : ℝ) :
    lineMaximal f x = lineMaximal g x := by
  unfold lineMaximal
  apply iSup_congr
  intro r
  rw [lineCenteredAverage_congr_ae hfg x r.1]

private theorem lineMaximal_add_le {f g : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) (x : ℝ) :
    lineMaximal (fun y => f y + g y) x ≤ lineMaximal f x + lineMaximal g x := by
  apply iSup_le
  intro r
  have hfNonneg := lineCenteredAverage_nonneg (f := f) x r.1 r.2
  have hgNonneg := lineCenteredAverage_nonneg (f := g) x r.1 r.2
  have havg := lineCenteredAverage_add_le hf hg x r.1 r.2
  calc
    ENNReal.ofReal (lineCenteredAverage (fun y => f y + g y) x r.1) ≤
        ENNReal.ofReal (lineCenteredAverage f x r.1 +
          lineCenteredAverage g x r.1) := ENNReal.ofReal_le_ofReal havg
    _ = ENNReal.ofReal (lineCenteredAverage f x r.1) +
        ENNReal.ofReal (lineCenteredAverage g x r.1) := by
      rw [ENNReal.ofReal_add hfNonneg hgNonneg]
    _ ≤ lineMaximal f x + lineMaximal g x := by
      exact add_le_add (le_iSup (fun s : {s : ℝ // 0 < s} =>
        ENNReal.ofReal (lineCenteredAverage f x s.1)) r)
        (le_iSup (fun s : {s : ℝ // 0 < s} =>
          ENNReal.ofReal (lineCenteredAverage g x s.1)) r)

private theorem lineMaximal_bounded_by_of_norm_le {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) (a : ℝ)
    (hbound : ∀ x, ‖f x‖ ≤ a) (x : ℝ) :
    lineMaximal f x ≤ ENNReal.ofReal a := by
  apply iSup_le
  intro r
  have hr := r.2
  have hInt := locallyIntegrable_norm_intervalIntegrable hf
    (x - r.1) (x + r.1)
  have hconst : IntervalIntegrable (fun _ : ℝ => a) volume
      (x - r.1) (x + r.1) := intervalIntegrable_const
  have hmono :
      (∫ y in x - r.1..x + r.1, ‖f y‖) ≤
        ∫ y in x - r.1..x + r.1, a := by
    apply intervalIntegral.integral_mono_on (by linarith) hInt hconst
    intro y _
    exact hbound y
  have hconstInt :
      (∫ y in x - r.1..x + r.1, a) = a * (2 * r.1) := by
    rw [intervalIntegral.integral_const]
    simp
    ring
  have havg : lineCenteredAverage f x r.1 ≤ a := by
    change (∫ y in x - r.1..x + r.1, ‖f y‖) / (2 * r.1) ≤ a
    apply (div_le_iff₀ (by positivity : 0 < 2 * r.1)).2
    calc
      (∫ y in x - r.1..x + r.1, ‖f y‖) ≤
          ∫ y in x - r.1..x + r.1, a := hmono
      _ = a * (2 * r.1) := hconstInt
  exact ENNReal.ofReal_le_ofReal havg

private theorem lineMaximal_high_low_add {f : ℝ → ℂ} (a : ℝ) :
    (fun x => lineMaximalHighCutoff a f x + lineMaximalLowCutoff a f x) = f := by
  funext x
  by_cases hx : a < ‖f x‖
  · simp [lineMaximalHighCutoff, lineMaximalLowCutoff, hx, not_le_of_gt hx]
  · have hx' : ‖f x‖ ≤ a := le_of_not_gt hx
    simp [lineMaximalHighCutoff, lineMaximalLowCutoff, hx, hx']

private theorem lineMaximalLowCutoff_norm_le {f : ℝ → ℂ} (a : ℝ)
    (ha : 0 ≤ a) (x : ℝ) : ‖lineMaximalLowCutoff a f x‖ ≤ a := by
  by_cases hx : ‖f x‖ ≤ a
  · simpa [lineMaximalLowCutoff, hx] using hx
  · simp [lineMaximalLowCutoff, hx]
    exact ha

private theorem lineMaximalLowCutoff_eq_sub_high {f : ℝ → ℂ} (a : ℝ) :
    lineMaximalLowCutoff a f = fun x => f x - lineMaximalHighCutoff a f x := by
  funext x
  by_cases hx : a < ‖f x‖
  · have hx' : ¬ ‖f x‖ ≤ a := not_le_of_gt hx
    simp [lineMaximalHighCutoff, lineMaximalLowCutoff, hx, hx']
  · have hx' : ‖f x‖ ≤ a := le_of_not_gt hx
    simp [lineMaximalHighCutoff, lineMaximalLowCutoff, hx, hx']

theorem lineMaximalHighCutoff_integrable
    {f : ℝ → ℂ} {p a : ℝ} (hp : 1 < p) (ha : 0 < a)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    Integrable (lineMaximalHighCutoff a f) volume := by
  have hp0 : 0 < p := by linarith
  have hpE0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hpETop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpowInt : Integrable (fun x : ℝ => ‖f x‖ ^ p) volume := by
    simpa [ENNReal.toReal_ofReal hp0.le] using hf.integrable_norm_rpow hpE0 hpETop
  have hsetNull : NullMeasurableSet {x : ℝ | a < ‖f x‖} volume :=
    (hf.aestronglyMeasurable.norm.aemeasurable.nullMeasurableSet_preimage
      measurableSet_Ioi)
  have hhighAES : AEStronglyMeasurable (lineMaximalHighCutoff a f) volume := by
    exact hf.aestronglyMeasurable.indicator₀ hsetNull
  let C : ℝ := (a ^ (p - 1))⁻¹
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact le_of_lt (inv_pos.mpr (Real.rpow_pos_of_pos ha _))
  have hmajorant : Integrable (fun x : ℝ => C * ‖f x‖ ^ p) volume :=
    hpowInt.const_mul C
  have hdom : ∀ x : ℝ,
      ‖lineMaximalHighCutoff a f x‖ ≤ C * ‖f x‖ ^ p := by
    intro x
    by_cases hx : a < ‖f x‖
    · have hy : 0 < ‖f x‖ := lt_trans ha hx
      have hpow : a ^ (p - 1) ≤ ‖f x‖ ^ (p - 1) :=
        Real.rpow_le_rpow (le_of_lt ha) (le_of_lt hx) (by linarith)
      have hpowId : ‖f x‖ ^ (p - 1) * ‖f x‖ = ‖f x‖ ^ p := by
        calc
          ‖f x‖ ^ (p - 1) * ‖f x‖ =
              ‖f x‖ ^ (p - 1) * ‖f x‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = ‖f x‖ ^ ((p - 1) + 1) := by rw [← Real.rpow_add hy]
          _ = ‖f x‖ ^ p := by congr 1; ring
      have hprod : a ^ (p - 1) * ‖f x‖ ≤ ‖f x‖ ^ p := by
        calc
          a ^ (p - 1) * ‖f x‖ ≤ ‖f x‖ ^ (p - 1) * ‖f x‖ :=
            mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
          _ = ‖f x‖ ^ p := hpowId
      have hquot : ‖f x‖ ≤ ‖f x‖ ^ p / (a ^ (p - 1)) :=
        (le_div_iff₀ (Real.rpow_pos_of_pos ha _)).2 (by simpa [mul_comm] using hprod)
      have hindicator : lineMaximalHighCutoff a f x = f x := by
        simp [lineMaximalHighCutoff, hx]
      rw [hindicator]
      calc
        ‖f x‖ ≤ ‖f x‖ ^ p / (a ^ (p - 1)) := hquot
        _ = C * ‖f x‖ ^ p := by dsimp [C]; ring
    · have hzero : lineMaximalHighCutoff a f x = 0 := by
        simp [lineMaximalHighCutoff, hx]
      rw [hzero, norm_zero]
      exact mul_nonneg hCnonneg (Real.rpow_nonneg (norm_nonneg _) _)
  exact hmajorant.mono' hhighAES (Eventually.of_forall hdom)

/-- The strict-level distribution estimate obtained by splitting an `L^p`
input at half the output threshold. -/
theorem lineMaximal_weakLp_distribution_bound
    {f : ℝ → ℂ} {p t : ℝ} (hp : 1 < p) (ht : 0 < t)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    volume {x : ℝ | ENNReal.ofReal t < lineMaximal f x} ≤
      ENNReal.ofReal
        (3 * (∫ x, ‖lineMaximalHighCutoff (t / 2) f x‖) / (t / 2)) := by
  let high := lineMaximalHighCutoff (t / 2) f
  let low := lineMaximalLowCutoff (t / 2) f
  have ha : 0 < t / 2 := by linarith
  have ha0 : 0 ≤ t / 2 := ha.le
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hp1E : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp1
  have hfLoc : LocallyIntegrable f volume := hf.locallyIntegrable hp1E
  have hhighInt : Integrable high volume := lineMaximalHighCutoff_integrable hp ha hf
  have hhighLoc : LocallyIntegrable high volume := hhighInt.locallyIntegrable
  have hlowEq : low = fun x => f x - high x := by
    simpa [high, low] using lineMaximalLowCutoff_eq_sub_high (t / 2) (f := f)
  have hlowLoc : LocallyIntegrable low volume := by
    rw [hlowEq]
    exact hfLoc.sub hhighLoc
  have hlowBound : ∀ x, ‖low x‖ ≤ t / 2 := by
    intro x
    simpa [low] using lineMaximalLowCutoff_norm_le (t / 2) ha0 x
  have hlowMax : ∀ x, lineMaximal low x ≤ ENNReal.ofReal (t / 2) := by
    intro x
    exact lineMaximal_bounded_by_of_norm_le hlowLoc (t / 2) hlowBound x
  have hsumEq : (fun x => high x + low x) = f := by
    simpa [high, low] using lineMaximal_high_low_add (t / 2) (f := f)
  have hsubset :
      {x : ℝ | ENNReal.ofReal t < lineMaximal f x} ⊆
        {x : ℝ | ENNReal.ofReal (t / 2) < lineMaximal high x} := by
    intro x hx
    have hdecomp : lineMaximal f x ≤ lineMaximal high x + lineMaximal low x := by
      rw [← hsumEq]
      exact lineMaximal_add_le hhighLoc hlowLoc x
    have hlarge : ENNReal.ofReal t < lineMaximal high x + ENNReal.ofReal (t / 2) :=
      lt_of_lt_of_le hx (hdecomp.trans
        (add_le_add_right (hlowMax x) (lineMaximal high x)))
    by_contra hnot
    have hsmall : lineMaximal high x ≤ ENNReal.ofReal (t / 2) := le_of_not_gt hnot
    have hdouble : ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) =
        ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_add ha0 ha0]
      congr 1
      ring
    have hupper : lineMaximal high x + ENNReal.ofReal (t / 2) ≤ ENNReal.ofReal t := by
      calc
        lineMaximal high x + ENNReal.ofReal (t / 2) ≤
            ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) :=
          add_le_add_left hsmall (ENNReal.ofReal (t / 2))
        _ = ENNReal.ofReal t := hdouble
    exact (not_lt_of_ge hupper) hlarge
  calc
    volume {x : ℝ | ENNReal.ofReal t < lineMaximal f x} ≤
        volume {x : ℝ | ENNReal.ofReal (t / 2) < lineMaximal high x} :=
      measure_mono hsubset
    _ ≤ ENNReal.ofReal (3 * (∫ x, ‖high x‖) / (t / 2)) := by
      exact lineMaximal_weakType_one hhighInt (t / 2) ha

/-- For an `L^p` input with `p > 1`, the extended centered maximal function
is finite almost everywhere. -/
theorem lineMaximal_lt_top_ae_of_memLp
    {f : ℝ → ℂ} {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂(volume : Measure ℝ), lineMaximal f x < ∞ := by
  let high : ℝ → ℂ := lineMaximalHighCutoff 1 f
  let I : ℝ := ∫ x, ‖high x‖ ∂(volume : Measure ℝ)
  have hhighInt : Integrable high volume :=
    lineMaximalHighCutoff_integrable hp (by norm_num) hf
  have hI0 : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  let bad : Set ℝ := {x | lineMaximal f x = ∞}
  have hbound (n : ℕ) :
      volume bad ≤ ENNReal.ofReal (3 * I / ((n : ℝ) + 1)) := by
    let t : ℝ := 2 * ((n : ℝ) + 1)
    have ht : 0 < t := by dsimp [t]; positivity
    have hcut : 1 ≤ t / 2 := by dsimp [t]; norm_num
    have hpoint (x : ℝ) :
        ‖lineMaximalHighCutoff (t / 2) f x‖ ≤ ‖high x‖ := by
      dsimp [lineMaximalHighCutoff, high]
      by_cases hbig : 1 < ‖f x‖
      · by_cases hcur : t / 2 < ‖f x‖
        · simp [Set.indicator, hbig, hcur]
        · simp [Set.indicator, hbig, hcur]
      · have hcur : ¬ t / 2 < ‖f x‖ := by
          exact not_lt.mpr (le_trans (le_of_not_gt hbig) hcut)
        simp [Set.indicator, hbig, hcur]
    have hcurInt : Integrable (lineMaximalHighCutoff (t / 2) f) volume :=
      lineMaximalHighCutoff_integrable hp (by dsimp [t]; positivity) hf
    have hIntLe :
        (∫ x, ‖lineMaximalHighCutoff (t / 2) f x‖ ∂volume) ≤ I := by
      exact integral_mono_ae hcurInt.norm hhighInt.norm (ae_of_all volume hpoint)
    have hsubset : bad ⊆ {x : ℝ | ENNReal.ofReal t < lineMaximal f x} := by
      intro x hx
      change lineMaximal f x = ∞ at hx
      change ENNReal.ofReal t < lineMaximal f x
      rw [hx]
      exact ENNReal.ofReal_lt_top
    calc
      volume bad ≤ volume {x : ℝ | ENNReal.ofReal t < lineMaximal f x} :=
        measure_mono hsubset
      _ ≤ ENNReal.ofReal (3 *
            (∫ x, ‖lineMaximalHighCutoff (t / 2) f x‖ ∂volume) / (t / 2)) :=
        lineMaximal_weakLp_distribution_bound hp ht hf
      _ ≤ ENNReal.ofReal (3 * I / ((n : ℝ) + 1)) := by
        apply ENNReal.ofReal_le_ofReal
        have hden : t / 2 = (n : ℝ) + 1 := by dsimp [t]; ring
        calc
          3 * (∫ x, ‖lineMaximalHighCutoff (t / 2) f x‖ ∂volume) / (t / 2) ≤
              3 * I / (t / 2) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hIntLe (by norm_num)) (by positivity)
          _ = 3 * I / ((n : ℝ) + 1) := by rw [hden]
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hshift
  have hdecay : Tendsto
      (fun n : ℕ => ENNReal.ofReal (3 * I / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => 3 * I / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv)
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hbad : volume bad = 0 := by
    have hle := le_of_tendsto_of_tendsto' tendsto_const_nhds hdecay hbound
    exact le_antisymm (by simpa [bad] using hle) bot_le
  rw [ae_iff]
  simpa [bad, ENNReal.not_lt_top] using hbad

#print axioms lineMaximal_lt_top_ae_of_memLp

private def lineMaximalStrongKernel (p : ℝ) (f : ℝ → ℂ) (t x : ℝ) : ℝ≥0∞ :=
  if t < 2 * ‖f x‖ then
    ENNReal.ofReal (3 * p) * ENNReal.ofReal (2 * ‖f x‖) *
      ENNReal.ofReal t ^ (p - 2)
  else 0

private theorem lineMaximalStrongKernel_measurable {p : ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) :
    Measurable (fun z : ℝ × ℝ => lineMaximalStrongKernel p f z.1 z.2) := by
  have hnorm : Measurable (fun z : ℝ × ℝ => ‖f z.2‖) := hf.norm.comp measurable_snd
  have hcut : MeasurableSet {z : ℝ × ℝ | z.1 < 2 * ‖f z.2‖} :=
    measurableSet_lt measurable_fst (measurable_const.mul hnorm)
  have hweight : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal z.1 ^ (p - 2)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_fst.ennreal_ofReal
  have hsize : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (2 * ‖f z.2‖)) :=
    (measurable_const.mul hnorm).ennreal_ofReal
  exact Measurable.ite hcut
    ((measurable_const.mul hsize).mul hweight) measurable_const

private theorem lineMaximalStrongKernel_tail {p : ℝ} (hp : 1 < p)
    (f : ℝ → ℂ) (x : ℝ) :
    (∫⁻ t in Ioi (0 : ℝ), lineMaximalStrongKernel p f t x) =
      ENNReal.ofReal
        (3 * p * (2 ^ p / (p - 1)) * ‖f x‖ ^ p) := by
  let u : ℝ := ‖f x‖
  have hu : 0 ≤ u := norm_nonneg _
  have hp0 : 0 < p := by linarith
  by_cases hu0 : u = 0
  · have hkernel : (fun t : ℝ => lineMaximalStrongKernel p f t x) =ᵐ[
        volume.restrict (Ioi (0 : ℝ))] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht : 0 < t := mem_Ioi.mp ht
      simp [lineMaximalStrongKernel, u, hu0, ht]
    rw [lintegral_congr_ae hkernel]
    have hzero : (0 : ℝ) ^ p = 0 := Real.zero_rpow hp0.ne'
    simp [u, hu0, hzero]
  · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have htail := Variation.layerCake_highInput_tail
      (p₀ := (1 : ℝ)) (p := p) (W := (2 : ℝ)) (u := u)
      (by norm_num) (by linarith) (by norm_num) hu
    have hfun : Measurable (fun t : ℝ =>
        if t < 2 * u then
          ENNReal.ofReal (2 * u) ^ (1 : ℝ) * ENNReal.ofReal t ^ (p - 1 - 1)
        else 0) := by
      exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
        (measurable_const.mul
          (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal))
        measurable_const
    have hpoint (t : ℝ) : lineMaximalStrongKernel p f t x =
        ENNReal.ofReal (3 * p) *
          (if t < 2 * u then
            ENNReal.ofReal (2 * u) ^ (1 : ℝ) * ENNReal.ofReal t ^ (p - 1 - 1)
          else 0) := by
      by_cases hcut : t < 2 * u
      · have hcut' : t < ‖f x‖ * 2 := by simpa [u, mul_comm] using hcut
        simp [lineMaximalStrongKernel, u, hcut, hcut', mul_comm]
        rw [show p - 1 - 1 = p - 2 by ring]
        ac_rfl
      · simp [lineMaximalStrongKernel, u, hcut]
    have hscale : (∫⁻ t in Ioi (0 : ℝ), lineMaximalStrongKernel p f t x) =
        ENNReal.ofReal (3 * p) *
          (∫⁻ t in Ioi (0 : ℝ),
            if t < 2 * u then
              ENNReal.ofReal (2 * u) ^ (1 : ℝ) * ENNReal.ofReal t ^ (p - 1 - 1)
            else 0) := by
      calc
        _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (3 * p) *
            (if t < 2 * u then
              ENNReal.ofReal (2 * u) ^ (1 : ℝ) * ENNReal.ofReal t ^ (p - 1 - 1)
            else 0) := by
              apply lintegral_congr_ae
              filter_upwards with t
              exact hpoint t
        _ = _ := by rw [lintegral_const_mul _ hfun]
    have hbase : (∫⁻ t in Ioi (0 : ℝ),
        if t < 2 * u then
          ENNReal.ofReal (2 * u) ^ (1 : ℝ) * ENNReal.ofReal t ^ (p - 1 - 1)
        else 0) = ENNReal.ofReal (2 ^ p * u ^ p / (p - 1)) := by
      simpa [u, Real.rpow_one] using htail
    rw [hscale, hbase]
    have hcoef : 0 ≤ 3 * p := by positivity
    have htailcoef : 0 ≤ 2 ^ p * u ^ p / (p - 1) := by
      apply div_nonneg
      · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hu _)
      · linarith
    rw [← ENNReal.ofReal_mul hcoef]
    congr 1
    have hpow : (2 : ℝ) ^ p = 2 ^ (p - 1) * 2 := by
      calc
        (2 : ℝ) ^ p = 2 ^ ((p - 1) + 1) := by congr 1 <;> ring
        _ = 2 ^ (p - 1) * 2 := by rw [Real.rpow_add (by norm_num)]; simp
    rw [hpow]
    ring

private theorem lineMaximalStrongKernel_lintegral
    {p t : ℝ} {f : ℝ → ℂ} (hp : 1 < p) (ht : 0 < t)
    (hf : Measurable f)
    (hLp : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, lineMaximalStrongKernel p f t x) =
      ENNReal.ofReal (3 * p) * ENNReal.ofReal (t ^ (p - 2)) *
        ENNReal.ofReal (2 * (∫ x, ‖lineMaximalHighCutoff (t / 2) f x‖)) := by
  let high := lineMaximalHighCutoff (t / 2) f
  have hp0 : 0 < p := by linarith
  have hcut : MeasurableSet {x : ℝ | t / 2 < ‖f x‖} :=
    measurableSet_lt measurable_const hf.norm
  have hhighInt : Integrable high volume := lineMaximalHighCutoff_integrable hp
    (by linarith) hLp
  have hhighFun : Measurable (fun x : ℝ =>
      if t / 2 < ‖f x‖ then ENNReal.ofReal ‖f x‖ else 0) := by
    exact Measurable.ite hcut (hf.norm.ennreal_ofReal) measurable_const
  have hhighLin : (∫⁻ x, if t / 2 < ‖f x‖ then ENNReal.ofReal ‖f x‖ else 0) =
      ENNReal.ofReal (∫ x, ‖high x‖) := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal ‖high x‖ := by
        apply lintegral_congr_ae
        filter_upwards with x
        by_cases hx : t / 2 < ‖f x‖
        · simp [high, lineMaximalHighCutoff, hx]
        · simp [high, lineMaximalHighCutoff, hx]
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hhighInt.norm
        (Eventually.of_forall fun x => norm_nonneg (high x))).symm
  have hscaledFun : Measurable (fun x : ℝ =>
      if t / 2 < ‖f x‖ then ENNReal.ofReal (2 * ‖f x‖) else 0) := by
    exact Measurable.ite hcut ((measurable_const.mul hf.norm).ennreal_ofReal)
      measurable_const
  have hscaledLin :
      (∫⁻ x, if t / 2 < ‖f x‖ then ENNReal.ofReal (2 * ‖f x‖) else 0) =
        ENNReal.ofReal (2 * (∫ x, ‖high x‖)) := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal 2 *
          (if t / 2 < ‖f x‖ then ENNReal.ofReal ‖f x‖ else 0) := by
            apply lintegral_congr_ae
            filter_upwards with x
            by_cases hx : t / 2 < ‖f x‖
            · rw [if_pos hx, if_pos hx, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            · simp [hx]
      _ = ENNReal.ofReal 2 *
          (∫⁻ x, if t / 2 < ‖f x‖ then ENNReal.ofReal ‖f x‖ else 0) :=
            lintegral_const_mul _ hhighFun
      _ = _ := by rw [hhighLin, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  let C : ℝ≥0∞ := ENNReal.ofReal (3 * p) * ENNReal.ofReal t ^ (p - 2)
  have hkernelPoint (x : ℝ) : lineMaximalStrongKernel p f t x =
      C * (if t / 2 < ‖f x‖ then ENNReal.ofReal (2 * ‖f x‖) else 0) := by
    by_cases hx : t / 2 < ‖f x‖
    · have hx' : t < 2 * ‖f x‖ := by
        rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)] at hx
        nlinarith
      simp [lineMaximalStrongKernel, C, hx, hx', ENNReal.ofReal_rpow_of_pos ht]
      ac_rfl
    · have hx' : ¬ t < 2 * ‖f x‖ := by
        intro h
        apply hx
        rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
        linarith
      simp [lineMaximalStrongKernel, C, hx, hx', ENNReal.ofReal_rpow_of_pos ht]
  calc
    (∫⁻ x, lineMaximalStrongKernel p f t x) =
        ∫⁻ x, C * (if t / 2 < ‖f x‖ then ENNReal.ofReal (2 * ‖f x‖) else 0) := by
          apply lintegral_congr_ae
          filter_upwards with x
          exact hkernelPoint x
    _ = C * (∫⁻ x,
        if t / 2 < ‖f x‖ then ENNReal.ofReal (2 * ‖f x‖) else 0) :=
          lintegral_const_mul _ hscaledFun
    _ = _ := by
      rw [hscaledLin]
      dsimp [C]
      rw [ENNReal.ofReal_rpow_of_pos ht]

private theorem lineMaximal_strongLp_moment_measurable
    {f : ℝ → ℂ} {p : ℝ} (hp : 1 < p) (hf : Measurable f)
    (hLp : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, ENNReal.ofReal (lineMaximalReal f x ^ p)) ≤
      ENNReal.ofReal (6 * p * 2 ^ (p - 1) / (p - 1)) *
        Variation.complexLpMoment p volume f := by
  have hp0 : 0 < p := by linarith
  have hfLoc : LocallyIntegrable f volume :=
    hLp.locallyIntegrable (by
      simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
  have hMmeas := lineMaximalReal_measurable_of_locallyIntegrable hfLoc
  have hMnonneg : ∀ x, 0 ≤ lineMaximalReal f x := fun x => ENNReal.toReal_nonneg
  have hLayer := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
    (μ := volume) (f := lineMaximalReal f)
    (Eventually.of_forall hMnonneg) hMmeas.aemeasurable hp0
  have hkernelMeas := lineMaximalStrongKernel_measurable (p := p) hf
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hswap :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, lineMaximalStrongKernel p f t x ∂volume) =
        ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), lineMaximalStrongKernel p f t x ∂volume ∂volume := by
    exact MeasureTheory.lintegral_lintegral_swap
      (μ := ν) (ν := volume)
      (f := fun t x => lineMaximalStrongKernel p f t x) hkernelMeas.aemeasurable
  have hcoeffEq : 3 * p * (2 ^ p / (p - 1)) =
      6 * p * 2 ^ (p - 1) / (p - 1) := by
    have hpow : (2 : ℝ) ^ p = 2 ^ (p - 1) * 2 := by
      calc
        (2 : ℝ) ^ p = 2 ^ ((p - 1) + 1) := by congr 1 <;> ring
        _ = 2 ^ (p - 1) * 2 := by rw [Real.rpow_add (by norm_num)]; simp
    rw [hpow]
    have hden : p - 1 ≠ 0 := ne_of_gt (by linarith)
    field_simp [hden]
    ring
  have hcoeffNonneg : 0 ≤ 6 * p * 2 ^ (p - 1) / (p - 1) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) (by linarith))
        (Real.rpow_nonneg (by norm_num) _)
    · linarith
  have hpoint (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal p *
          (volume {x | t < lineMaximalReal f x} * ENNReal.ofReal (t ^ (p - 1))) ≤
        ∫⁻ x, lineMaximalStrongKernel p f t x := by
    let L : ℝ := ∫ x, ‖lineMaximalHighCutoff (t / 2) f x‖
    have hsubset : {x : ℝ | t < lineMaximalReal f x} ⊆
        {x | ENNReal.ofReal t < lineMaximal f x} := by
      intro x hx
      have htop : lineMaximal f x ≠ ∞ := by
        intro htop
        simp [lineMaximalReal, htop] at hx
        linarith
      have hx' : t < (lineMaximal f x).toReal := by
        simpa [lineMaximalReal] using hx
      exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le htop).2 hx'
    have hlevel : volume {x | t < lineMaximalReal f x} ≤
        ENNReal.ofReal (3 * L / (t / 2)) := by
      calc
        _ ≤ volume {x | ENNReal.ofReal t < lineMaximal f x} := measure_mono hsubset
        _ ≤ _ := by
          exact lineMaximal_weakLp_distribution_bound hp ht hLp
    have hLnonneg : 0 ≤ L := integral_nonneg (fun x => norm_nonneg _)
    have hpowpos : 0 < t ^ (p - 1) := Real.rpow_pos_of_pos ht _
    have hpowKernel : 0 < t ^ (p - 2) := Real.rpow_pos_of_pos ht _
    have hrealPow : t ^ (p - 2) = t ^ (p - 1) / t := by
      calc
        t ^ (p - 2) = t ^ ((p - 1) - 1) := by congr 1 <;> ring
        _ = t ^ (p - 1) / t ^ (1 : ℝ) := Real.rpow_sub ht _ _
        _ = t ^ (p - 1) / t := by rw [Real.rpow_one]
    have hrealEq : p * ((3 * L / (t / 2)) * t ^ (p - 1)) =
        (3 * p) * t ^ (p - 2) * (2 * L) := by
      rw [hrealPow]
      field_simp [ne_of_gt ht]
    have hA : 0 ≤ 3 * L / (t / 2) := by positivity
    have hB : 0 ≤ t ^ (p - 1) := hpowpos.le
    have hP : 0 ≤ p := hp0.le
    have hthreeP : 0 ≤ 3 * p := by positivity
    have htwoL : 0 ≤ 2 * L := by positivity
    have halgebra :
        ENNReal.ofReal p *
            (ENNReal.ofReal (3 * L / (t / 2)) * ENNReal.ofReal (t ^ (p - 1))) =
          ENNReal.ofReal (3 * p) * ENNReal.ofReal (t ^ (p - 2)) *
            ENNReal.ofReal (2 * L) := by
      calc
        _ = ENNReal.ofReal (p * ((3 * L / (t / 2)) * t ^ (p - 1))) := by
          rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hP]
        _ = ENNReal.ofReal ((3 * p) * t ^ (p - 2) * (2 * L)) := by
          rw [hrealEq]
        _ = _ := by
          calc
            _ = ENNReal.ofReal (3 * p * (t ^ (p - 2) * (2 * L))) := by ring_nf
            _ = ENNReal.ofReal (3 * p) * ENNReal.ofReal (t ^ (p - 2) * (2 * L)) :=
              ENNReal.ofReal_mul hthreeP
            _ = _ := by
              rw [ENNReal.ofReal_mul (by positivity : 0 ≤ t ^ (p - 2))]
              ac_rfl
    have hkernelInt := lineMaximalStrongKernel_lintegral hp ht hf hLp
    change ENNReal.ofReal p *
        (volume {x | t < lineMaximalReal f x} * ENNReal.ofReal (t ^ (p - 1))) ≤ _
    calc
      _ = volume {x | t < lineMaximalReal f x} *
          (ENNReal.ofReal p * ENNReal.ofReal (t ^ (p - 1))) := by ac_rfl
      _ ≤ ENNReal.ofReal (3 * L / (t / 2)) *
          (ENNReal.ofReal p * ENNReal.ofReal (t ^ (p - 1))) :=
            mul_le_mul_of_nonneg_right hlevel (by positivity)
      _ = ENNReal.ofReal (3 * p) * ENNReal.ofReal (t ^ (p - 2)) *
          ENNReal.ofReal (2 * L) := by
            calc
              _ = ENNReal.ofReal p *
                  (ENNReal.ofReal (3 * L / (t / 2)) *
                    ENNReal.ofReal (t ^ (p - 1))) := by ac_rfl
              _ = _ := halgebra
      _ = ∫⁻ x, lineMaximalStrongKernel p f t x := hkernelInt.symm
  have hweighted :
      (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal p *
          (volume {x | t < lineMaximalReal f x} * ENNReal.ofReal (t ^ (p - 1)))) ≤
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, lineMaximalStrongKernel p f t x ∂volume := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpoint t (mem_Ioi.mp ht)
  have hmomentKernel :
      (∫⁻ x, ENNReal.ofReal (lineMaximalReal f x ^ p)) ≤
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, lineMaximalStrongKernel p f t x ∂volume := by
    calc
      _ = ENNReal.ofReal p *
          (∫⁻ t in Ioi (0 : ℝ),
            volume {x | t < lineMaximalReal f x} *
              ENNReal.ofReal (t ^ (p - 1))) := hLayer
      _ = ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal p *
            (volume {x | t < lineMaximalReal f x} *
              ENNReal.ofReal (t ^ (p - 1))) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := hweighted
  have htail :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, lineMaximalStrongKernel p f t x ∂volume) =
        ∫⁻ x, ENNReal.ofReal
          (3 * p * (2 ^ p / (p - 1)) * ‖f x‖ ^ p) ∂volume := by
    rw [hswap]
    apply lintegral_congr_ae
    filter_upwards with x
    exact lineMaximalStrongKernel_tail hp f x
  have htail' :
      (∫⁻ x, ENNReal.ofReal
        (3 * p * (2 ^ p / (p - 1)) * ‖f x‖ ^ p) ∂volume) =
        ENNReal.ofReal (6 * p * 2 ^ (p - 1) / (p - 1)) *
          Variation.complexLpMoment p volume f := by
    have hpointInput (x : ℝ) :
        ENNReal.ofReal (3 * p * (2 ^ p / (p - 1)) * ‖f x‖ ^ p) =
          ENNReal.ofReal (6 * p * 2 ^ (p - 1) / (p - 1)) * ‖f x‖ₑ ^ p := by
      rw [hcoeffEq, ENNReal.ofReal_mul hcoeffNonneg,
        ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hp0.le,
        ← ofReal_norm]
    calc
      _ = ∫⁻ x, ENNReal.ofReal (6 * p * 2 ^ (p - 1) / (p - 1)) *
          ‖f x‖ₑ ^ p ∂volume := by
            apply lintegral_congr_ae
            exact ae_of_all _ hpointInput
      _ = ENNReal.ofReal (6 * p * 2 ^ (p - 1) / (p - 1)) *
          Variation.complexLpMoment p volume f := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            unfold Variation.complexLpMoment
            congr 1
            apply lintegral_congr_ae
            filter_upwards with x
            simp [ENNReal.rpow_eq_pow, ← ofReal_norm]
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x,
        lineMaximalStrongKernel p f t x ∂volume := hmomentKernel
    _ = ∫⁻ x, ENNReal.ofReal
        (3 * p * (2 ^ p / (p - 1)) * ‖f x‖ ^ p) ∂volume := htail
    _ = _ := htail'

/-- The exact strong `L^p` moment bound for the centered maximal function,
first stated on arbitrary representatives of the `L^p` class. -/
theorem lineMaximal_strongLp_moment
    {f : ℝ → ℂ} {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, ENNReal.ofReal (lineMaximalReal f x ^ p)) ≤
      ENNReal.ofReal (6 * p * 2 ^ (p - 1) / (p - 1)) *
        Variation.complexLpMoment p volume f := by
  let hs := hf.aestronglyMeasurable
  let g := hs.mk f
  have hgmeas : Measurable g := hs.measurable_mk
  have hfg : f =ᵐ[volume] g := hs.ae_eq_mk
  have hgLp : MemLp g (ENNReal.ofReal p) volume := hf.ae_eq hfg
  have hM : lineMaximalReal f = lineMaximalReal g := by
    funext x
    simp only [lineMaximalReal]
    rw [lineMaximal_congr_ae hfg x]
  have hmomentInput : Variation.complexLpMoment p volume g =
      Variation.complexLpMoment p volume f := by
    unfold Variation.complexLpMoment
    apply lintegral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (lineMaximalReal g x ^ p) := by rw [hM]
    _ ≤ ENNReal.ofReal (6 * p * 2 ^ (p - 1) / (p - 1)) *
        Variation.complexLpMoment p volume g :=
      lineMaximal_strongLp_moment_measurable hp hgmeas hgLp
    _ = _ := by rw [hmomentInput]

/-- The exact strong `L^p` estimate for the centered maximal function on the
line, with the source constant `H_p`. -/
theorem lineMaximal_strongLp
    {f : ℝ → ℂ} {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (lineMaximalReal f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((6 * p * 2 ^ (p - 1) / (p - 1)) ^ (1 / p)) *
        eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hmoment := lineMaximal_strongLp_moment hp hf
  have hp1E : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have hfLoc : LocallyIntegrable f volume := hf.locallyIntegrable hp1E
  have hFmeas := lineMaximalReal_measurable_of_locallyIntegrable hfLoc
  have hFnonneg : ∀ x, 0 ≤ lineMaximalReal f x := fun x => ENNReal.toReal_nonneg
  have hOutMoment :
      (∫⁻ x, ENNReal.ofReal (lineMaximalReal f x ^ p)) =
        eLpNorm (lineMaximalReal f) (ENNReal.ofReal p) volume ^ p := by
    have hpE0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
    have hpETop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
    calc
      _ = ∫⁻ x, ‖lineMaximalReal f x‖ₑ ^ p ∂volume := by
        apply lintegral_congr_ae
        filter_upwards with x
        rw [← ENNReal.ofReal_rpow_of_nonneg (hFnonneg x) hp0.le]
        have hbase : ENNReal.ofReal (lineMaximalReal f x) =
            ‖lineMaximalReal f x‖ₑ := by
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hFnonneg x)]
        rw [hbase]
      _ = _ := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpE0 hpETop
          hFmeas.aestronglyMeasurable,
          ENNReal.toReal_ofReal hp0.le]
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  have hInMoment :
      Variation.complexLpMoment p volume f =
        eLpNorm f (ENNReal.ofReal p) volume ^ p := by
    have hpE0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
    have hpETop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
    calc
      Variation.complexLpMoment p volume f = ∫⁻ x, ‖f x‖ₑ ^ p ∂volume := by
        unfold Variation.complexLpMoment
        apply lintegral_congr_ae
        filter_upwards with x
        simp [ENNReal.rpow_eq_pow, ← ofReal_norm]
      _ = _ := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpE0 hpETop
          hf.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  rw [hOutMoment, hInMoment] at hmoment
  have hroot := ENNReal.rpow_le_rpow hmoment (by positivity : 0 ≤ 1 / p)
  have hrootExp : p * (1 / p) = 1 := by field_simp [hp0.ne']
  have hOutRoot :
      (eLpNorm (lineMaximalReal f) (ENNReal.ofReal p) volume ^ p) ^ (1 / p) =
        eLpNorm (lineMaximalReal f) (ENNReal.ofReal p) volume := by
    rw [← ENNReal.rpow_mul, hrootExp, ENNReal.rpow_one]
  have hInRoot :
      (eLpNorm f (ENNReal.ofReal p) volume ^ p) ^ (1 / p) =
        eLpNorm f (ENNReal.ofReal p) volume := by
    rw [← ENNReal.rpow_mul, hrootExp, ENNReal.rpow_one]
  have hConstRoot :
      ENNReal.ofReal (6 * p * 2 ^ (p - 1) / (p - 1)) ^ (1 / p) =
        ENNReal.ofReal ((6 * p * 2 ^ (p - 1) / (p - 1)) ^ (1 / p)) := by
    have hcoeffNonneg : 0 ≤ 6 * p * 2 ^ (p - 1) / (p - 1) := by positivity
    rw [← ENNReal.ofReal_rpow_of_nonneg hcoeffNonneg (by positivity : 0 ≤ 1 / p)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p), hOutRoot,
    hConstRoot, hInRoot] at hroot
  exact hroot

private abbrev jswDyadicInterval := dyadicInterval

private theorem jswDyadicInterval_length (m j : ℤ) :
    ((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m - (j : ℝ) * (2 : ℝ) ^ m = (2 : ℝ) ^ m := by
  push_cast
  ring

/-- Each half-open dyadic cell lies in its unique parent at the next coarser
scale. This is the lattice fact used to select maximal witnesses. -/
private theorem jswDyadicInterval_parent_subset (m j : ℤ) :
    jswDyadicInterval m j ⊆ jswDyadicInterval (m + 1) (j / 2) := by
  have hmod : j % 2 = 0 ∨ j % 2 = 1 := Int.emod_two_eq_zero_or_one j
  have hlen : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hscale : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 := by
    rw [show m + 1 = m + (1 : ℤ) by rfl, zpow_add₀ (by norm_num), zpow_one]
  have hdecomp : j % 2 + 2 * (j / 2) = j := Int.emod_add_mul_ediv j 2
  rcases hmod with hmod | hmod
  · have hji : (j : ℝ) = 2 * ((j / 2 : ℤ) : ℝ) := by
      have h := hdecomp
      rw [hmod] at h
      exact_mod_cast (by omega : j = 2 * (j / 2))
    intro x hx
    simp only [jswDyadicInterval, dyadicInterval, Set.mem_Ico] at hx ⊢
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
    simp only [jswDyadicInterval, dyadicInterval, Set.mem_Ico] at hx ⊢
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

private def jswDyadicAncestor : ℕ → ℤ → ℤ
  | 0, j => j
  | n + 1, j => jswDyadicAncestor n (j / 2)

private theorem jswDyadicInterval_ancestor_subset (m j : ℤ) (n : ℕ) :
    jswDyadicInterval m j ⊆ jswDyadicInterval (m + n) (jswDyadicAncestor n j) := by
  induction n generalizing m j with
  | zero => simp [jswDyadicAncestor]
  | succ n ih =>
      calc
        jswDyadicInterval m j ⊆ jswDyadicInterval (m + 1) (j / 2) :=
          jswDyadicInterval_parent_subset m j
        _ ⊆ jswDyadicInterval ((m + 1) + n) (jswDyadicAncestor n (j / 2)) :=
          ih (m := m + 1) (j := j / 2)
        _ = jswDyadicInterval (m + (n + 1)) (jswDyadicAncestor (n + 1) j) := by
          simp [jswDyadicAncestor, add_assoc, add_comm, add_left_comm]

private theorem jswDyadicInterval_index_eq_of_inter
    (m j k : ℤ) (h : (jswDyadicInterval m j ∩ jswDyadicInterval m k).Nonempty) :
    j = k := by
  obtain ⟨x, hxj, hxk⟩ := h
  have hlen : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  simp only [jswDyadicInterval, dyadicInterval, Set.mem_Ico, Int.cast_add,
    Int.cast_one] at hxj hxk
  have hjk : (j : ℝ) < (k : ℝ) + 1 := by
    by_contra h
    have hle : (k : ℝ) + 1 ≤ (j : ℝ) := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hle hlen.le
    linarith [hxj.1, hxk.2]
  have hkj : (k : ℝ) < (j : ℝ) + 1 := by
    by_contra h
    have hle : (j : ℝ) + 1 ≤ (k : ℝ) := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hle hlen.le
    linarith [hxk.1, hxj.2]
  have hjk' : j < k + 1 := by exact_mod_cast hjk
  have hkj' : k < j + 1 := by exact_mod_cast hkj
  omega

private theorem jswDyadicInterval_nested_of_inter
    {m n j k : ℤ} (hinter : (jswDyadicInterval m j ∩ jswDyadicInterval n k).Nonempty) :
    jswDyadicInterval m j ⊆ jswDyadicInterval n k ∨
      jswDyadicInterval n k ⊆ jswDyadicInterval m j := by
  rcases le_total m n with hmn | hnm
  · let d : ℕ := (n - m).toNat
    have hdiff : (d : ℤ) = n - m := by
      dsimp [d]
      exact Int.toNat_of_nonneg (by omega)
    have hscale : m + (d : ℤ) = n := by omega
    have hsub : jswDyadicInterval m j ⊆
        jswDyadicInterval n (jswDyadicAncestor d j) := by
      simpa [hscale] using jswDyadicInterval_ancestor_subset m j d
    obtain ⟨x, hxj, hxk⟩ := hinter
    have hancestorInter :
        (jswDyadicInterval n (jswDyadicAncestor d j) ∩ jswDyadicInterval n k).Nonempty :=
      ⟨x, hsub hxj, hxk⟩
    have hindex := jswDyadicInterval_index_eq_of_inter n
      (jswDyadicAncestor d j) k hancestorInter
    rw [hindex] at hsub
    exact Or.inl hsub
  · let d : ℕ := (m - n).toNat
    have hdiff : (d : ℤ) = m - n := by
      dsimp [d]
      exact Int.toNat_of_nonneg (by omega)
    have hscale : n + (d : ℤ) = m := by omega
    have hsub : jswDyadicInterval n k ⊆
        jswDyadicInterval m (jswDyadicAncestor d k) := by
      simpa [hscale] using jswDyadicInterval_ancestor_subset n k d
    obtain ⟨x, hxj, hxk⟩ := hinter
    have hancestorInter :
        (jswDyadicInterval m (jswDyadicAncestor d k) ∩ jswDyadicInterval m j).Nonempty :=
      ⟨x, hsub hxk, hxj⟩
    have hindex := jswDyadicInterval_index_eq_of_inter m
      (jswDyadicAncestor d k) j hancestorInter
    rw [hindex] at hsub
    exact Or.inr hsub

/-- The dyadic average of the norm of f on the half-open cell at scale m. -/
def dyadicMaximalAverage (f : ℝ → ℂ) (m j : ℤ) : ℝ :=
  (∫ x in dyadicInterval m j, ‖f x‖) / (2 : ℝ) ^ m

theorem dyadicMaximalAverage_nonneg (f : ℝ → ℂ) (m j : ℤ) :
    0 ≤ dyadicMaximalAverage f m j := by
  unfold dyadicMaximalAverage
  apply div_nonneg
  · exact setIntegral_nonneg measurableSet_Ico (by intro x hx; exact norm_nonneg _)
  · exact le_of_lt (zpow_pos (by norm_num) m)

def dyadicMaximal (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ := by
  classical
  exact ⨆ q : ℤ × ℤ,
    if x ∈ dyadicInterval q.1 q.2 then
      ENNReal.ofReal (dyadicMaximalAverage f q.1 q.2) else 0

private def jswDyadicIndexBox (N : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ)

private theorem jswDyadicIndexBox_mono {N M : ℕ} (hNM : N ≤ M) :
    jswDyadicIndexBox N ⊆ jswDyadicIndexBox M := by
  intro q hq
  simp only [jswDyadicIndexBox, Finset.mem_product, Finset.mem_Icc] at hq ⊢
  omega

private theorem jswDyadicIndexBox_cover (m j : ℤ) :
    ∃ N : ℕ, (m, j) ∈ jswDyadicIndexBox N := by
  refine ⟨m.natAbs + j.natAbs, ?_⟩
  simp only [jswDyadicIndexBox, Finset.mem_product, Finset.mem_Icc]
  constructor <;> omega

/-- Finite dyadic witness families obey the constant-one weak estimate. -/
private theorem jswDyadicFiniteWeak (f : ℝ → ℂ) (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) (F : Finset (ℤ × ℤ)) :
    volume (⋃ q ∈ F.filter (fun q => t < dyadicMaximalAverage f q.1 q.2),
      dyadicInterval q.1 q.2) ≤
        ENNReal.ofReal ((∫ x, ‖f x‖) / t) := by
  classical
  let W := F.filter (fun q => t < dyadicMaximalAverage f q.1 q.2)
  let S := W.image (fun q => dyadicInterval q.1 q.2)
  let M := S.filter (fun Q => Maximal (fun Q' : Set ℝ => Q' ∈ S) Q)
  have hS_nonempty_of_witness {x : ℝ} (hx : x ∈ ⋃ q ∈ W, dyadicInterval q.1 q.2) :
      ∃ Q ∈ S, x ∈ Q := by
    rcases Set.mem_iUnion.mp hx with ⟨q, hq⟩
    rcases Set.mem_iUnion.mp hq with ⟨hqw, hxq⟩
    exact ⟨dyadicInterval q.1 q.2, Finset.mem_image.mpr ⟨q, hqw, rfl⟩, hxq⟩
  let idx : Set ℝ → ℤ × ℤ := fun Q =>
    if hQ : Q ∈ S then Classical.choose (Finset.mem_image.mp hQ) else (0, 0)
  have hidx (Q : Set ℝ) (hQ : Q ∈ S) :
      idx Q ∈ W ∧ dyadicInterval (idx Q).1 (idx Q).2 = Q := by
    simp only [idx, dif_pos hQ]
    exact Classical.choose_spec (Finset.mem_image.mp hQ)
  have hunion : (⋃ Q ∈ M, Q) = ⋃ q ∈ W, dyadicInterval q.1 q.2 := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨Q, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hQM, hxQ⟩
      obtain ⟨q, hqW, hqEq⟩ :=
        Finset.mem_image.mp ((Finset.mem_filter.mp hQM).1)
      exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hqW, hqEq ▸ hxQ⟩⟩
    · intro hx
      obtain ⟨Q, hQS, hxQ⟩ := hS_nonempty_of_witness (by simpa [W] using hx)
      obtain ⟨Q', hQQ', hmax⟩ := S.exists_le_maximal hQS
      exact Set.mem_iUnion.mpr ⟨Q', Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hmax.1, hmax⟩,
        hQQ' hxQ⟩⟩
  have hdisj : PairwiseDisjoint (↑M) (fun Q : Set ℝ => Q) := by
    intro A hA B hB hne
    apply Set.disjoint_iff_inter_eq_empty.mpr
    by_contra hAB
    have hinter : (A ∩ B).Nonempty := Set.nonempty_iff_ne_empty.mpr hAB
    rcases jswDyadicInterval_nested_of_inter (by
      obtain ⟨x, hxA, hxB⟩ := hinter
      obtain ⟨_, hAeq⟩ := hidx A (Finset.mem_filter.mp hA).1
      obtain ⟨_, hBeq⟩ := hidx B (Finset.mem_filter.mp hB).1
      exact ⟨x, hAeq ▸ hxA, hBeq ▸ hxB⟩) with hsub | hsub
    · have ⟨_, hAeq⟩ := hidx A (Finset.mem_filter.mp hA).1
      have ⟨_, hBeq⟩ := hidx B (Finset.mem_filter.mp hB).1
      have hAB : A ⊆ B := hAeq.symm.subset.trans (hsub.trans hBeq.subset)
      have hEq := (Finset.mem_filter.mp hA).2.eq_of_subset (Finset.mem_filter.mp hB).1 hAB
      exact hne hEq
    · have ⟨_, hAeq⟩ := hidx A (Finset.mem_filter.mp hA).1
      have ⟨_, hBeq⟩ := hidx B (Finset.mem_filter.mp hB).1
      have hBA : B ⊆ A := hBeq.symm.subset.trans (hsub.trans hAeq.subset)
      have hEq := (Finset.mem_filter.mp hB).2.eq_of_subset (Finset.mem_filter.mp hA).1 hBA
      exact hne hEq.symm
  let width : Set ℝ → ℝ := fun Q => (2 : ℝ) ^ (idx Q).1
  have hlocal : ∀ Q ∈ M,
      t * width Q ≤ ∫ x in Q, ‖f x‖ := by
    intro Q hQM
    have hQ : Q ∈ S := (Finset.mem_filter.mp hQM).1
    obtain ⟨hidxW, hidxEq⟩ := hidx Q hQ
    have havg : t < dyadicMaximalAverage f (idx Q).1 (idx Q).2 :=
      (Finset.mem_filter.mp hidxW).2
    have hscale : 0 < (2 : ℝ) ^ (idx Q).1 := zpow_pos (by norm_num) _
    have hnum : t * (2 : ℝ) ^ (idx Q).1 <
        ∫ x in dyadicInterval (idx Q).1 (idx Q).2, ‖f x‖ := by
      exact (lt_div_iff₀ hscale).mp havg
    have hnum' : t * width Q <
        ∫ x in dyadicInterval (idx Q).1 (idx Q).2, ‖f x‖ := by
      change t * (2 : ℝ) ^ (idx Q).1 < _
      exact hnum
    have hnum'' : t * width Q < ∫ x in Q, ‖f x‖ := by
      simpa [hidxEq] using hnum'
    exact hnum''.le
  have hsum_local :
      t * (∑ Q ∈ M, width Q) ≤ ∑ Q ∈ M, ∫ x in Q, ‖f x‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun Q hQ => hlocal Q hQ
  have hsum_int :
      (∑ Q ∈ M, ∫ x in Q, ‖f x‖) ≤ ∫ x, ‖f x‖ := by
    rw [← integral_biUnion_finset (t := M) (s := fun Q : Set ℝ => Q)
      (f := fun x : ℝ => ‖f x‖) (μ := volume)
      (by
        intro Q hQ
        obtain ⟨_, hQeq⟩ := hidx Q ((Finset.mem_filter.mp hQ).1)
        rw [← hQeq]
        simpa [dyadicInterval] using measurableSet_Ico)
      hdisj
      (by
        intro Q hQ
        obtain ⟨_, hQeq⟩ := hidx Q ((Finset.mem_filter.mp hQ).1)
        rw [← hQeq]
        exact hf.norm.integrableOn)]
    apply setIntegral_le_integral hf.norm
    filter_upwards with x
    exact norm_nonneg (f x)
  have hwidth_nonneg : ∀ Q ∈ M, 0 ≤ width Q := by
    intro Q hQ
    exact le_of_lt (zpow_pos (by norm_num) _)
  have hsum_bound : ∑ Q ∈ M, width Q ≤ (∫ x, ‖f x‖) / t := by
    apply (le_div_iff₀ ht).2
    calc
      (∑ Q ∈ M, width Q) * t = t * (∑ Q ∈ M, width Q) := by ring
      _ ≤ ∫ x, ‖f x‖ := hsum_local.trans hsum_int
  have hmeasure : volume (⋃ Q ∈ M, Q) = ∑ Q ∈ M, ENNReal.ofReal (width Q) := by
    rw [measure_biUnion_finset hdisj (by
      intro Q hQ
      obtain ⟨_, hQeq⟩ := hidx Q ((Finset.mem_filter.mp hQ).1)
      rw [← hQeq]
      simpa [dyadicInterval] using measurableSet_Ico)]
    apply Finset.sum_congr rfl
    intro Q hQ
    have hVolQ : volume Q = ENNReal.ofReal (width Q) := by
      obtain ⟨_, hQeq⟩ := hidx Q ((Finset.mem_filter.mp hQ).1)
      calc
        volume Q = volume (dyadicInterval (idx Q).1 (idx Q).2) :=
          congrArg volume hQeq.symm
        _ = ENNReal.ofReal ((2 : ℝ) ^ (idx Q).1) := by
          rw [dyadicInterval, Real.volume_Ico]
          congr 1
          exact jswDyadicInterval_length _ _
        _ = ENNReal.ofReal (width Q) := rfl
    exact hVolQ
  have hsum_ofReal :
      (∑ Q ∈ M, ENNReal.ofReal (width Q)) = ENNReal.ofReal (∑ Q ∈ M, width Q) := by
    symm
    exact ENNReal.ofReal_sum_of_nonneg hwidth_nonneg
  calc
    volume (⋃ q ∈ W, dyadicInterval q.1 q.2) = volume (⋃ Q ∈ M, Q) := by rw [← hunion]
    _ = ENNReal.ofReal (∑ Q ∈ M, width Q) := by rw [hmeasure, hsum_ofReal]
    _ ≤ ENNReal.ofReal ((∫ x, ‖f x‖) / t) := ENNReal.ofReal_le_ofReal hsum_bound

private def jswDyadicFiniteLevelSet (f : ℝ → ℂ) (t : ℝ)
    (F : Finset (ℤ × ℤ)) : Set ℝ :=
  ⋃ q ∈ F.filter (fun q => t < dyadicMaximalAverage f q.1 q.2),
    dyadicInterval q.1 q.2

private theorem jswDyadicMaximal_levelSet_eq_iUnion (f : ℝ → ℂ)
    (t : ℝ) (ht : 0 < t) :
    {x : ℝ | ENNReal.ofReal t < dyadicMaximal f x} =
      ⋃ N : ℕ, jswDyadicFiniteLevelSet f t (jswDyadicIndexBox N) := by
  classical
  ext x
  constructor
  · intro hx
    have hx' :
        ENNReal.ofReal t <
          ⨆ q : ℤ × ℤ,
            if x ∈ dyadicInterval q.1 q.2 then
              ENNReal.ofReal (dyadicMaximalAverage f q.1 q.2) else 0 := by
      change ENNReal.ofReal t < dyadicMaximal f x at hx
      exact hx
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp hx'
    by_cases hmem : x ∈ dyadicInterval q.1 q.2
    · have hq' : ENNReal.ofReal t <
          ENNReal.ofReal (dyadicMaximalAverage f q.1 q.2) := by
        simpa [hmem] using hq
      have havg : t < dyadicMaximalAverage f q.1 q.2 :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp hq'
      obtain ⟨N, hqN⟩ := jswDyadicIndexBox_cover q.1 q.2
      apply Set.mem_iUnion.mpr
      refine ⟨N, ?_⟩
      simp only [jswDyadicFiniteLevelSet]
      exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hqN, havg⟩, hmem⟩⟩
    · have hfalse : ENNReal.ofReal t < 0 := by simpa [hmem] using hq
      exact False.elim (not_lt_of_ge (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal t) hfalse)
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨N, hxN⟩
    simp only [jswDyadicFiniteLevelSet] at hxN
    rcases Set.mem_iUnion.mp hxN with ⟨q, hxN⟩
    rcases Set.mem_iUnion.mp hxN with ⟨hq, hmem⟩
    have havg : t < dyadicMaximalAverage f q.1 q.2 :=
      (Finset.mem_filter.mp hq).2
    have havg_pos : 0 < dyadicMaximalAverage f q.1 q.2 := lt_trans ht havg
    have hterm :
        ENNReal.ofReal t <
          (if x ∈ dyadicInterval q.1 q.2 then
            ENNReal.ofReal (dyadicMaximalAverage f q.1 q.2) else 0) := by
      rw [if_pos hmem]
      exact (ENNReal.ofReal_lt_ofReal_iff havg_pos).mpr havg
    have hle :
        (if x ∈ dyadicInterval q.1 q.2 then
          ENNReal.ofReal (dyadicMaximalAverage f q.1 q.2) else 0) ≤ dyadicMaximal f x := by
      unfold dyadicMaximal
      exact le_iSup_of_le q le_rfl
    have hmax := lt_of_lt_of_le hterm hle
    change ENNReal.ofReal t < dyadicMaximal f x at hmax
    exact hmax

/-- The dyadic maximal function over half-open dyadic intervals has weak
(1,1) constant one. -/
theorem dyadicMaximal_weakType_one {f : ℝ → ℂ} (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) :
    volume {x : ℝ | ENNReal.ofReal t < dyadicMaximal f x} ≤
      ENNReal.ofReal ((∫ x, ‖f x‖) / t) := by
  classical
  let A : ℕ → Set ℝ := fun N =>
    jswDyadicFiniteLevelSet f t (jswDyadicIndexBox N)
  have hmono : Monotone A := by
    intro N M hNM x hx
    simp only [A, jswDyadicFiniteLevelSet] at hx ⊢
    rcases Set.mem_iUnion.mp hx with ⟨q, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hq, hmem⟩
    have hq' : q ∈ jswDyadicIndexBox M :=
      jswDyadicIndexBox_mono hNM (Finset.mem_filter.mp hq).1
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨hq', (Finset.mem_filter.mp hq).2⟩, hmem⟩⟩
  have hlim := tendsto_measure_iUnion_atTop (μ := volume) hmono
  have hconstant : Tendsto
      (fun _ : ℕ => ENNReal.ofReal ((∫ x, ‖f x‖) / t)) atTop
      (𝓝 (ENNReal.ofReal ((∫ x, ‖f x‖) / t))) := tendsto_const_nhds
  have hbound : ∀ N : ℕ,
      volume (A N) ≤ ENNReal.ofReal ((∫ x, ‖f x‖) / t) := by
    intro N
    exact jswDyadicFiniteWeak f hf t ht (jswDyadicIndexBox N)
  have hresult := le_of_tendsto_of_tendsto' hlim hconstant hbound
  rw [jswDyadicMaximal_levelSet_eq_iUnion f t ht]
  simpa [A] using hresult

/-- The complete four-clause package in blueprint `lj:maximal`: measurability
of the centered maximal operator, its exact weak `(1,1)` estimate, the stated
strong `L^p` estimate, and the constant-one weak estimate for half-open
dyadic intervals. -/
theorem lineMaximalBounds :
    (∀ (f : ℝ → ℂ), LocallyIntegrable f volume → Measurable (lineMaximal f)) ∧
    (∀ {f : ℝ → ℂ}, Integrable f volume → ∀ (t : ℝ), 0 < t →
      volume {x : ℝ | ENNReal.ofReal t < lineMaximal f x} ≤
        ENNReal.ofReal (3 * (∫ y, ‖f y‖) / t)) ∧
    (∀ {f : ℝ → ℂ} {p : ℝ}, 1 < p → MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (lineMaximalReal f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((6 * p * 2 ^ (p - 1) / (p - 1)) ^ (1 / p)) *
          eLpNorm f (ENNReal.ofReal p) volume) ∧
    (∀ {f : ℝ → ℂ}, Integrable f volume → ∀ (t : ℝ), 0 < t →
      volume {x : ℝ | ENNReal.ofReal t < dyadicMaximal f x} ≤
        ENNReal.ofReal ((∫ x, ‖f x‖) / t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun f hf => lineMaximal_measurable_of_locallyIntegrable hf
  · exact fun hf t ht => lineMaximal_weakType_one hf t ht
  · exact fun hp hf => lineMaximal_strongLp hp hf
  · exact fun hf t ht => dyadicMaximal_weakType_one hf t ht

#print axioms FractionalPrimes.Literature.JSW.lineMaximal_weakType_one
#print axioms FractionalPrimes.Literature.JSW.lineMaximal_strongLp
#print axioms FractionalPrimes.Literature.JSW.dyadicMaximal_weakType_one
#print axioms FractionalPrimes.Literature.JSW.lineMaximalBounds

end

end FractionalPrimes.Literature.JSW

end
