module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import FractionalPrimes.InterpolationLayercake
public import FractionalPrimes.Literature.Variation.WeakVariationOfJump

/-!
# Scalar tails for explicit layer-cake interpolation

These are the two Tonelli tails in blueprint `lv:interpolation`.  The first
is integrated below the cutoff `W * u` and uses exponent `p₀`; the second is
integrated above that cutoff and uses exponent `p₁`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Variation

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- The exact input domain in blueprint `lv:interpolation`: bounded
measurable complex functions with finite-measure support. -/
def LayerCakeAdmissible {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) : Prop :=
  Measurable f ∧ (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧ μ {x | f x ≠ 0} < ∞

/-- The source domain of the generic layer-cake interpolation lemma. -/
abbrev LayerCakeInput {X : Type*} [MeasurableSpace X] (μ : Measure X) :=
  {f : X → ℂ // LayerCakeAdmissible μ f}

private theorem measurableSet_nonzero_complex
    {X : Type*} [MeasurableSpace X] {f : X → ℂ} (hf : Measurable f) :
    MeasurableSet {x | f x ≠ 0} := by
  have hzero : MeasurableSet {x | f x = (0 : ℂ)} :=
    measurableSet_eq_fun hf measurable_const
  have hset : {x | f x ≠ 0} = {x | f x = (0 : ℂ)}ᶜ := by
    ext x
    simp
  rw [hset]
  exact hzero.compl

/-- The strict high part at magnitude cutoff `c`. -/
def layerCakeHighCutoff {X : Type*} (c : ℝ) (f : X → ℂ) : X → ℂ :=
  fun x => if c < ‖f x‖ then f x else 0

/-- The inclusive low part at magnitude cutoff `c`. -/
def layerCakeLowCutoff {X : Type*} (c : ℝ) (f : X → ℂ) : X → ℂ :=
  fun x => if ‖f x‖ ≤ c then f x else 0

theorem layerCakeAdmissible_highCutoff
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (c : ℝ) {f : X → ℂ}
    (hf : LayerCakeAdmissible μ f) :
    LayerCakeAdmissible μ (layerCakeHighCutoff c f) := by
  rcases hf with ⟨hfmeas, ⟨C, hCbdd⟩, hμ⟩
  refine ⟨?_, ⟨max C 0, ?_⟩, ?_⟩
  · exact Measurable.ite (measurableSet_lt measurable_const hfmeas.norm)
      hfmeas measurable_const
  · intro x
    by_cases hx : c < ‖f x‖
    · simpa [layerCakeHighCutoff, hx] using
        (le_trans (hCbdd x) (le_max_left C 0))
    · simpa [layerCakeHighCutoff, hx] using (le_max_right C 0)
  · apply lt_of_le_of_lt (measure_mono ?_) hμ
    intro x hx
    by_cases h : c < ‖f x‖
    · simpa [layerCakeHighCutoff, h] using hx
    · simp [layerCakeHighCutoff, h] at hx

theorem layerCakeAdmissible_lowCutoff
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (c : ℝ) {f : X → ℂ}
    (hf : LayerCakeAdmissible μ f) :
    LayerCakeAdmissible μ (layerCakeLowCutoff c f) := by
  rcases hf with ⟨hfmeas, ⟨C, hCbdd⟩, hμ⟩
  refine ⟨?_, ⟨max C 0, ?_⟩, ?_⟩
  · exact Measurable.ite (measurableSet_le hfmeas.norm measurable_const)
      hfmeas measurable_const
  · intro x
    by_cases hx : ‖f x‖ ≤ c
    · simpa [layerCakeLowCutoff, hx] using
        (le_trans (hCbdd x) (le_max_left C 0))
    · simpa [layerCakeLowCutoff, hx] using (le_max_right C 0)
  · apply lt_of_le_of_lt (measure_mono ?_) hμ
    intro x hx
    by_cases h : ‖f x‖ ≤ c
    · simpa [layerCakeLowCutoff, h] using hx
    · simp [layerCakeLowCutoff, h] at hx

/-- The source-faithful hypotheses for explicit weak-type interpolation.
The map is defined only on bounded measurable finite-measure-support inputs;
both weak endpoint bounds are restricted to that same domain. -/
structure LayerCakeWeakOperator {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p₀ p₁ W : ℝ) where
  apply : LayerCakeInput μ → X → ℝ
  measurable_apply : ∀ f, Measurable (apply f)
  nonneg_apply : ∀ f x, 0 ≤ apply f x
  subadditive : ∀ (f g : LayerCakeInput μ)
      (hfg : LayerCakeAdmissible μ (f.1 + g.1)) (x : X),
      apply ⟨f.1 + g.1, hfg⟩ x ≤ apply f x + apply g x
  absolutely_homogeneous : ∀ (c : ℂ) (f : LayerCakeInput μ)
      (hcf : LayerCakeAdmissible μ (c • f.1)) (x : X),
      apply ⟨c • f.1, hcf⟩ x = ‖c‖ * apply f x
  weak_p₀ : ∀ (f : LayerCakeInput μ) (t : ℝ), 0 < t →
      μ {x | t < apply f x} ≤
        (ENNReal.ofReal (W / t)).rpow p₀ * complexLpMoment p₀ μ f.1
  weak_p₁ : ∀ (f : LayerCakeInput μ) (t : ℝ), 0 < t →
      μ {x | t < apply f x} ≤
        (ENNReal.ofReal (W / t)).rpow p₁ * complexLpMoment p₁ μ f.1

/-- The strict-level estimate obtained by splitting at the source cutoff
`t / W`. The high input uses the strict condition `t / W < ‖f x‖`, while
the low input includes equality. -/
theorem layerCake_strictLevel_split
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p₀ p₁ W : ℝ} (U : LayerCakeWeakOperator μ p₀ p₁ W)
    (f : LayerCakeInput μ) (t : ℝ) (ht : 0 < t) :
    μ {x | 2 * t < U.apply f x} ≤
      (ENNReal.ofReal (W / t)).rpow p₀ *
          complexLpMoment p₀ μ (layerCakeHighCutoff (t / W) f.1) +
        (ENNReal.ofReal (W / t)).rpow p₁ *
          complexLpMoment p₁ μ (layerCakeLowCutoff (t / W) f.1) := by
  let highFn := layerCakeHighCutoff (t / W) f.1
  let lowFn := layerCakeLowCutoff (t / W) f.1
  have hsplit : highFn + lowFn = f.1 := by
    funext x
    by_cases hx : t / W < ‖f.1 x‖
    · have hx' : ¬ ‖f.1 x‖ ≤ t / W := not_le_of_gt hx
      simp [highFn, lowFn, layerCakeHighCutoff, layerCakeLowCutoff, hx, hx']
    · have hx' : ‖f.1 x‖ ≤ t / W := le_of_not_gt hx
      simp [highFn, lowFn, layerCakeHighCutoff, layerCakeLowCutoff, hx, hx']
  have hsum : LayerCakeAdmissible μ (highFn + lowFn) := by
    rw [hsplit]
    exact f.2
  let highInput : LayerCakeInput μ :=
    ⟨highFn, layerCakeAdmissible_highCutoff μ (t / W) f.2⟩
  let lowInput : LayerCakeInput μ :=
    ⟨lowFn, layerCakeAdmissible_lowCutoff μ (t / W) f.2⟩
  have hsumEq : (⟨highFn + lowFn, hsum⟩ : LayerCakeInput μ) = f :=
    Subtype.ext hsplit
  have hsub (x : X) : U.apply f x ≤ U.apply highInput x + U.apply lowInput x := by
    rw [← hsumEq]
    exact U.subadditive highInput lowInput hsum x
  have hset : {x | 2 * t < U.apply f x} ⊆
      {x | t < U.apply highInput x} ∪ {x | t < U.apply lowInput x} := by
    intro x hx
    change 2 * t < U.apply f x at hx
    by_cases hhigh : t < U.apply highInput x
    · exact Or.inl hhigh
    · by_cases hlow : t < U.apply lowInput x
      · exact Or.inr hlow
      · have hhigh' : U.apply highInput x ≤ t := le_of_not_gt hhigh
        have hlow' : U.apply lowInput x ≤ t := le_of_not_gt hlow
        have hbound : U.apply f x ≤ 2 * t := by
          calc
            U.apply f x ≤ U.apply highInput x + U.apply lowInput x := hsub x
            _ ≤ t + t := add_le_add hhigh' hlow'
            _ = 2 * t := by ring
        exfalso
        exact (not_lt_of_ge hbound) hx
  calc
    μ {x | 2 * t < U.apply f x} ≤
        μ ({x | t < U.apply highInput x} ∪ {x | t < U.apply lowInput x}) :=
      measure_mono hset
    _ ≤ μ {x | t < U.apply highInput x} + μ {x | t < U.apply lowInput x} :=
      measure_union_le _ _
    _ ≤ (ENNReal.ofReal (W / t)).rpow p₀ *
          complexLpMoment p₀ μ highFn +
        (ENNReal.ofReal (W / t)).rpow p₁ *
          complexLpMoment p₁ μ lowFn :=
      add_le_add (U.weak_p₀ highInput t ht) (U.weak_p₁ lowInput t ht)
    _ = _ := by rfl

/-- Output layer cake after the source change of variables `u = 2t`. The
strict superlevel cutoff is preserved exactly. -/
private theorem layerCake_realOutput_scaledMoment
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ}
    (hp : 0 < p) (F : X → ℝ) (hFnonneg : ∀ x, 0 ≤ F x)
    (hFmeas : Measurable F) :
    (∫⁻ x, ENNReal.ofReal (F x ^ p) ∂μ) =
      ENNReal.ofReal (2 ^ p) *
        (ENNReal.ofReal p *
          ∫⁻ t in Ioi (0 : ℝ), μ {x | 2 * t < F x} *
            ENNReal.ofReal (t ^ (p - 1))) := by
  let G : X → ℝ := fun x => F x / 2
  have hGnonneg : ∀ x, 0 ≤ G x := fun x => div_nonneg (hFnonneg x) (by norm_num)
  have hGmeas : Measurable G := hFmeas.div_const 2
  have hLayer := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
    (μ := μ) (f := G) (Eventually.of_forall hGnonneg) hGmeas.aemeasurable hp
  have hpoint (x : X) :
      ENNReal.ofReal (F x ^ p) =
        ENNReal.ofReal (2 ^ p) * ENNReal.ofReal (G x ^ p) := by
    have hreal : F x ^ p = 2 ^ p * G x ^ p := by
      dsimp [G]
      calc
        F x ^ p = (2 * (F x / 2)) ^ p := by congr 1 <;> ring
        _ = 2 ^ p * (F x / 2) ^ p :=
          Real.mul_rpow (by norm_num) (div_nonneg (hFnonneg x) (by norm_num))
    rw [hreal, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)]
  have hlevel :
      (fun t : ℝ => μ {x | t < G x} * ENNReal.ofReal (t ^ (p - 1))) =ᵐ[
        volume.restrict (Ioi (0 : ℝ))]
        (fun t => μ {x | 2 * t < F x} * ENNReal.ofReal (t ^ (p - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hset : {x | t < G x} = {x | 2 * t < F x} := by
      ext x
      change t < F x / 2 ↔ 2 * t < F x
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      ring_nf
    rw [hset]
  calc
    (∫⁻ x, ENNReal.ofReal (F x ^ p) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (2 ^ p) * ENNReal.ofReal (G x ^ p) ∂μ := by
          apply lintegral_congr_ae
          exact ae_of_all _ hpoint
    _ = ENNReal.ofReal (2 ^ p) * (∫⁻ x, ENNReal.ofReal (G x ^ p) ∂μ) := by
          rw [lintegral_const_mul _ (hGmeas.pow measurable_const).ennreal_ofReal]
    _ = ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal p *
            ∫⁻ t in Ioi (0 : ℝ), μ {x | 2 * t < F x} *
              ENNReal.ofReal (t ^ (p - 1))) := by
          rw [hLayer]
          congr 2
          exact lintegral_congr_ae hlevel

/-- The finite-endpoint power integral on `(0,c]`. -/
theorem layerCake_lintegral_rpow_Ioc
    {q c : ℝ} (hq : -1 < q) (hc : 0 ≤ c) :
    (∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal t ^ q) =
      ENNReal.ofReal (c ^ (q + 1) / (q + 1)) := by
  by_cases hc0 : c = 0
  · subst c
    have hq1 : 0 < q + 1 := by linarith
    simp [Real.zero_rpow hq1.ne']
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hinterval : IntervalIntegrable (fun t : ℝ => t ^ q) volume 0 c :=
    intervalIntegral.intervalIntegrable_rpow' hq
  have hIcc : IntegrableOn (fun t : ℝ => t ^ q) (Icc 0 c) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hc).mp hinterval
  have hIcc' : Integrable (fun t : ℝ => t ^ q) (volume.restrict (Icc 0 c)) := hIcc
  have hIoc : Integrable (fun t : ℝ => t ^ q) (volume.restrict (Ioc 0 c)) :=
    hIcc'.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 c)] (fun t : ℝ => t ^ q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le q
  rw [show (∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal t ^ q) =
      ∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal (t ^ q) by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact ENNReal.ofReal_rpow_of_pos ht.1]
  rw [← ofReal_integral_eq_lintegral_ofReal hIoc hnonneg]
  rw [show (∫ t, t ^ q ∂volume.restrict (Ioc (0 : ℝ) c)) =
      ∫ t in Ioc (0 : ℝ) c, t ^ q by rfl]
  rw [← intervalIntegral.integral_of_le hc]
  rw [integral_rpow (Or.inl hq)]
  have hq1 : 0 < q + 1 := by linarith
  simp only [Real.zero_rpow hq1.ne', sub_zero]

/-- The infinite-endpoint power integral above a positive cutoff. -/
theorem layerCake_lintegral_rpow_Ioi
    {q c : ℝ} (hq : q < -1) (hc : 0 < c) :
    (∫⁻ t in Ioi c, ENNReal.ofReal t ^ q) =
      ENNReal.ofReal (c ^ (q + 1) / (-(q + 1))) := by
  have hIoi : Integrable (fun t : ℝ => t ^ q) (volume.restrict (Ioi c)) :=
    integrableOn_Ioi_rpow_of_lt hq hc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi c)] (fun t : ℝ => t ^ q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hc.trans ht).le q
  rw [show (∫⁻ t in Ioi c, ENNReal.ofReal t ^ q) =
      ∫⁻ t in Ioi c, ENNReal.ofReal (t ^ q) by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact ENNReal.ofReal_rpow_of_pos (hc.trans ht)]
  rw [← ofReal_integral_eq_lintegral_ofReal hIoi hnonneg]
  rw [show (∫ t, t ^ q ∂volume.restrict (Ioi c)) =
      ∫ t in Ioi c, t ^ q by rfl]
  rw [integral_Ioi_rpow_of_lt hq hc]
  congr 1
  have hq1 : q + 1 ≠ 0 := ne_of_lt (by linarith)
  field_simp [hq1]

/-- The high-input Tonelli tail in `lv:interpolation`, with its exact
`W^p u^p / (p-p₀)` value. -/
theorem layerCake_highInput_tail
    {p₀ p W u : ℝ} (hp₀ : 0 < p₀) (hp : p₀ < p)
    (hW : 0 < W) (hu : 0 ≤ u) :
    (∫⁻ t in Ioi (0 : ℝ),
      (if t < W * u then
        (ENNReal.ofReal (W * u)).rpow p₀ * ENNReal.ofReal t ^ (p - p₀ - 1)
      else 0)) =
      ENNReal.ofReal (W ^ p * u ^ p / (p - p₀)) := by
  by_cases hu0 : u = 0
  · subst u
    have hp0 : 0 < p := hp₀.trans hp
    have hvanish : (fun t : ℝ =>
        if t < 0 then (ENNReal.ofReal (0 : ℝ)).rpow p₀ *
          ENNReal.ofReal t ^ (p - p₀ - 1) else 0) =ᵐ[volume.restrict (Ioi 0)] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp [not_lt_of_gt (mem_Ioi.mp ht)]
    simp only [mul_zero]
    rw [lintegral_congr_ae hvanish]
    simp [Real.zero_rpow hp0.ne']
  have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hc : 0 < W * u := mul_pos hW hu'
  have hq : -1 < p - p₀ - 1 := by linarith
  have hbranch :
      (fun t : ℝ =>
        (if t < W * u then
          (ENNReal.ofReal (W * u)).rpow p₀ * ENNReal.ofReal t ^ (p - p₀ - 1)
        else 0)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => (Ioo (0 : ℝ) (W * u)).indicator
        (fun t => (ENNReal.ofReal (W * u)).rpow p₀ *
          ENNReal.ofReal t ^ (p - p₀ - 1)) t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
    by_cases htc : t < W * u
    · have htmem : t ∈ Ioo (0 : ℝ) (W * u) := ⟨ht0, htc⟩
      simp [htmem, htc]
    · have htmem : t ∉ Ioo (0 : ℝ) (W * u) := by
        simp only [mem_Ioo, not_and, not_le]
        intro _ hcut
        exact htc hcut
      simp [htmem, htc]
  calc
    (∫⁻ t in Ioi (0 : ℝ),
        (if t < W * u then
          (ENNReal.ofReal (W * u)).rpow p₀ * ENNReal.ofReal t ^ (p - p₀ - 1)
        else 0)) =
      ∫⁻ t, (Ioo (0 : ℝ) (W * u)).indicator
        (fun t => (ENNReal.ofReal (W * u)).rpow p₀ *
          ENNReal.ofReal t ^ (p - p₀ - 1)) t
            ∂volume.restrict (Ioi (0 : ℝ)) := by
      exact lintegral_congr_ae hbranch
    _ = ∫⁻ t in Ioo (0 : ℝ) (W * u),
        (ENNReal.ofReal (W * u)).rpow p₀ *
          ENNReal.ofReal t ^ (p - p₀ - 1)
            ∂volume.restrict (Ioi (0 : ℝ)) := by
      rw [lintegral_indicator measurableSet_Ioo]
    _ = ∫⁻ t in Ioc (0 : ℝ) (W * u),
        (ENNReal.ofReal (W * u)).rpow p₀ *
          ENNReal.ofReal t ^ (p - p₀ - 1) := by
      rw [Measure.restrict_restrict measurableSet_Ioo]
      have hIoo : Ioo (0 : ℝ) (W * u) =ᵐ[volume] Ioc (0 : ℝ) (W * u) :=
        Ioo_ae_eq_Ioc (μ := volume) (a := 0) (b := W * u)
      have hset : Ioo (0 : ℝ) (W * u) ∩ Ioi (0 : ℝ) =ᵐ[volume]
          Ioc (0 : ℝ) (W * u) := by
        filter_upwards [hIoo] with t ht
        apply propext
        simp only [mem_inter_iff, mem_Ioo, mem_Ioi, mem_Ioc]
        constructor
        · rintro ⟨⟨ht0, htc⟩, _⟩
          exact ⟨ht0, htc.le⟩
        · intro htIoc
          have htIoo : t ∈ Ioo (0 : ℝ) (W * u) := by
            rw [ht]
            exact htIoc
          exact ⟨htIoo, htIoc.1⟩
      rw [Measure.restrict_congr_set hset]
    _ = (ENNReal.ofReal (W * u)).rpow p₀ *
        (∫⁻ t in Ioc (0 : ℝ) (W * u), ENNReal.ofReal t ^ (p - p₀ - 1)) := by
      exact lintegral_const_mul _
        (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal)
    _ = ENNReal.ofReal ((W * u) ^ p / (p - p₀)) := by
      rw [layerCake_lintegral_rpow_Ioc hq hc.le]
      rw [show p - p₀ - 1 + 1 = p - p₀ by ring]
      change ENNReal.ofReal (W * u) ^ p₀ *
        ENNReal.ofReal ((W * u) ^ (p - p₀) / (p - p₀)) = _
      rw [ENNReal.ofReal_rpow_of_nonneg hc.le hp₀.le]
      rw [← ENNReal.ofReal_mul'
        (div_nonneg (Real.rpow_nonneg hc.le _) (by linarith : 0 ≤ p - p₀))]
      congr 1
      have hdenom : 0 < p - p₀ := by linarith
      have hpow : (W * u) ^ p₀ * (W * u) ^ (p - p₀) = (W * u) ^ p := by
        rw [← Real.rpow_add (mul_pos hW hu')]
        congr 1
        ring
      rw [← hpow]
      field_simp [hdenom.ne']
    _ = ENNReal.ofReal (W ^ p * u ^ p / (p - p₀)) := by
      congr 1
      rw [Real.mul_rpow hW.le hu]

/-- The low-input Tonelli tail in `lv:interpolation`, with its exact
`W^p u^p / (p₁-p)` value. -/
theorem layerCake_lowInput_tail
    {p p₁ W u : ℝ} (hp0 : 0 < p) (hp : p < p₁) (hp₁ : 0 < p₁)
    (hW : 0 < W) (hu : 0 ≤ u) :
    (∫⁻ t in Ioi (0 : ℝ),
      (if W * u ≤ t then
        (ENNReal.ofReal (W * u)).rpow p₁ * ENNReal.ofReal t ^ (p - p₁ - 1)
      else 0)) =
      ENNReal.ofReal (W ^ p * u ^ p / (p₁ - p)) := by
  by_cases hu0 : u = 0
  · subst u
    have hvanish : (fun t : ℝ =>
        if (0 : ℝ) ≤ t then (ENNReal.ofReal (0 : ℝ)).rpow p₁ *
          ENNReal.ofReal t ^ (p - p₁ - 1) else 0) =ᵐ[volume.restrict (Ioi 0)] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := mem_Ioi.mp ht
      simp [htpos.le, ENNReal.zero_rpow_of_pos hp₁]
    simp only [mul_zero]
    rw [lintegral_congr_ae hvanish]
    simp [Real.zero_rpow hp0.ne']
  have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hc : 0 < W * u := mul_pos hW hu'
  have hq : p - p₁ - 1 < -1 := by linarith
  have hbranch :
      (fun t : ℝ =>
        (if W * u ≤ t then
          (ENNReal.ofReal (W * u)).rpow p₁ * ENNReal.ofReal t ^ (p - p₁ - 1)
        else 0)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => (Ici (W * u)).indicator
        (fun t => (ENNReal.ofReal (W * u)).rpow p₁ *
          ENNReal.ofReal t ^ (p - p₁ - 1)) t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
    by_cases hcut : W * u ≤ t
    · simp [hcut]
    · simp [hcut]
  calc
    (∫⁻ t in Ioi (0 : ℝ),
        (if W * u ≤ t then
          (ENNReal.ofReal (W * u)).rpow p₁ * ENNReal.ofReal t ^ (p - p₁ - 1)
        else 0)) =
      ∫⁻ t, (Ici (W * u)).indicator
        (fun t => (ENNReal.ofReal (W * u)).rpow p₁ *
          ENNReal.ofReal t ^ (p - p₁ - 1)) t
            ∂volume.restrict (Ioi (0 : ℝ)) := by
      exact lintegral_congr_ae hbranch
    _ = ∫⁻ t in Ici (W * u),
        (ENNReal.ofReal (W * u)).rpow p₁ *
          ENNReal.ofReal t ^ (p - p₁ - 1)
            ∂volume.restrict (Ioi (0 : ℝ)) := by
      rw [lintegral_indicator measurableSet_Ici]
    _ = ∫⁻ t in Ioi (W * u),
        (ENNReal.ofReal (W * u)).rpow p₁ *
          ENNReal.ofReal t ^ (p - p₁ - 1) := by
      rw [Measure.restrict_restrict measurableSet_Ici]
      have hIci : Ici (W * u) =ᵐ[volume] Ioi (W * u) :=
        (Ioi_ae_eq_Ici (μ := volume) (a := W * u)).symm
      have hset : Ici (W * u) ∩ Ioi (0 : ℝ) =ᵐ[volume] Ioi (W * u) := by
        filter_upwards [hIci] with t ht
        apply propext
        simp only [mem_inter_iff, mem_Ici, mem_Ioi]
        constructor
        · rintro ⟨htc, _⟩
          have hstrict : t ∈ Ioi (W * u) := by
            rw [← ht]
            exact htc
          exact hstrict
        · intro hstrict
          have hclosed : t ∈ Ici (W * u) := by
            rw [ht]
            exact hstrict
          exact ⟨hclosed, lt_trans hc hstrict⟩
      rw [Measure.restrict_congr_set hset]
    _ = (ENNReal.ofReal (W * u)).rpow p₁ *
        (∫⁻ t in Ioi (W * u), ENNReal.ofReal t ^ (p - p₁ - 1)) := by
      exact lintegral_const_mul _
        (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal)
    _ = ENNReal.ofReal ((W * u) ^ p / (p₁ - p)) := by
      rw [layerCake_lintegral_rpow_Ioi hq hc]
      rw [show p - p₁ - 1 + 1 = p - p₁ by ring,
        show -(p - p₁) = p₁ - p by ring]
      change ENNReal.ofReal (W * u) ^ p₁ *
        ENNReal.ofReal ((W * u) ^ (p - p₁) / (p₁ - p)) = _
      rw [ENNReal.ofReal_rpow_of_nonneg hc.le hp₁.le]
      rw [← ENNReal.ofReal_mul'
        (div_nonneg (Real.rpow_nonneg hc.le _) (by linarith : 0 ≤ p₁ - p))]
      congr 1
      have hpow : (W * u) ^ p₁ * (W * u) ^ (p - p₁) = (W * u) ^ p := by
        rw [← Real.rpow_add (mul_pos hW hu')]
        congr 1
        ring
      rw [← hpow]
      field_simp [ne_of_gt (by linarith : 0 < p₁ - p)]
    _ = ENNReal.ofReal (W ^ p * u ^ p / (p₁ - p)) := by
      congr 1
      rw [Real.mul_rpow hW.le hu]

private def layerCakeHighKernel {X : Type*} (p₀ p W : ℝ) (f : X → ℂ)
    (t : ℝ) (x : X) : ℝ≥0∞ :=
  if t < W * ‖f x‖ then
    (ENNReal.ofReal (W * ‖f x‖)).rpow p₀ * ENNReal.ofReal t ^ (p - p₀ - 1)
  else 0

private def layerCakeLowKernel {X : Type*} (p p₁ W : ℝ) (f : X → ℂ)
    (t : ℝ) (x : X) : ℝ≥0∞ :=
  if W * ‖f x‖ ≤ t then
    (ENNReal.ofReal (W * ‖f x‖)).rpow p₁ * ENNReal.ofReal t ^ (p - p₁ - 1)
  else 0

private theorem layerCake_highWeight_formula
    {p₀ p W t u : ℝ} (hp₀ : 0 < p₀) (hp₀p : p₀ < p)
    (hW : 0 < W) (ht : 0 < t) (hu : 0 ≤ u) :
    ENNReal.ofReal (W / t) ^ p₀ *
        ENNReal.ofReal u ^ p₀ * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (W * u) ^ p₀ * ENNReal.ofReal t ^ (p - p₀ - 1) := by
  have hwt : 0 ≤ W / t := div_nonneg hW.le ht.le
  have hwu : 0 ≤ W * u := mul_nonneg hW.le hu
  have htpow : t ^ (p - 1) / t ^ p₀ = t ^ (p - p₀ - 1) := by
    rw [← Real.rpow_sub ht]
    congr 1
    ring
  have hreal : (W / t) ^ p₀ * u ^ p₀ * t ^ (p - 1) =
      (W * u) ^ p₀ * t ^ (p - p₀ - 1) := by
    calc
      (W / t) ^ p₀ * u ^ p₀ * t ^ (p - 1) =
          (W ^ p₀ / t ^ p₀) * u ^ p₀ * t ^ (p - 1) := by
            rw [Real.div_rpow hW.le ht.le]
      _ = (W ^ p₀ * u ^ p₀) * (t ^ (p - 1) / t ^ p₀) := by ring
      _ = W ^ p₀ * u ^ p₀ * t ^ (p - p₀ - 1) := by rw [htpow]
      _ = (W * u) ^ p₀ * t ^ (p - p₀ - 1) := by
            rw [← Real.mul_rpow hW.le hu]
  calc
    _ = ENNReal.ofReal ((W / t) ^ p₀ * u ^ p₀ * t ^ (p - 1)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hwt hp₀.le,
        ENNReal.ofReal_rpow_of_nonneg hu hp₀.le]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hwt p₀)]
      rw [← ENNReal.ofReal_mul
        (mul_nonneg (Real.rpow_nonneg hwt p₀) (Real.rpow_nonneg hu p₀))]
    _ = ENNReal.ofReal ((W * u) ^ p₀ * t ^ (p - p₀ - 1)) := by rw [hreal]
    _ = _ := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hwu p₀),
        ENNReal.ofReal_rpow_of_nonneg hwu hp₀.le,
        ENNReal.ofReal_rpow_of_pos ht]

private theorem layerCake_lowWeight_formula
    {p p₁ W t u : ℝ} (hp : 0 < p) (hpp₁ : p < p₁) (hp₁ : 0 < p₁)
    (hW : 0 < W) (ht : 0 < t) (hu : 0 ≤ u) :
    ENNReal.ofReal (W / t) ^ p₁ *
        ENNReal.ofReal u ^ p₁ * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (W * u) ^ p₁ * ENNReal.ofReal t ^ (p - p₁ - 1) := by
  have hwt : 0 ≤ W / t := div_nonneg hW.le ht.le
  have hwu : 0 ≤ W * u := mul_nonneg hW.le hu
  have htpow : t ^ (p - 1) / t ^ p₁ = t ^ (p - p₁ - 1) := by
    rw [← Real.rpow_sub ht]
    congr 1
    ring
  have hreal : (W / t) ^ p₁ * u ^ p₁ * t ^ (p - 1) =
      (W * u) ^ p₁ * t ^ (p - p₁ - 1) := by
    calc
      (W / t) ^ p₁ * u ^ p₁ * t ^ (p - 1) =
          (W ^ p₁ / t ^ p₁) * u ^ p₁ * t ^ (p - 1) := by
            rw [Real.div_rpow hW.le ht.le]
      _ = (W ^ p₁ * u ^ p₁) * (t ^ (p - 1) / t ^ p₁) := by ring
      _ = W ^ p₁ * u ^ p₁ * t ^ (p - p₁ - 1) := by rw [htpow]
      _ = (W * u) ^ p₁ * t ^ (p - p₁ - 1) := by
            rw [← Real.mul_rpow hW.le hu]
  calc
    _ = ENNReal.ofReal ((W / t) ^ p₁ * u ^ p₁ * t ^ (p - 1)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hwt hp₁.le,
        ENNReal.ofReal_rpow_of_nonneg hu hp₁.le]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hwt p₁)]
      rw [← ENNReal.ofReal_mul
        (mul_nonneg (Real.rpow_nonneg hwt p₁) (Real.rpow_nonneg hu p₁))]
    _ = ENNReal.ofReal ((W * u) ^ p₁ * t ^ (p - p₁ - 1)) := by rw [hreal]
    _ = _ := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hwu p₁),
        ENNReal.ofReal_rpow_of_nonneg hwu hp₁.le,
        ENNReal.ofReal_rpow_of_pos ht]

private def layerCakeHighMoment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p₀ W : ℝ) (f : X → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (if t < W * ‖f x‖ then
    ENNReal.ofReal ‖f x‖ ^ p₀ else 0) ∂μ

private def layerCakeLowMoment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p₁ W : ℝ) (f : X → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (if W * ‖f x‖ ≤ t then
    ENNReal.ofReal ‖f x‖ ^ p₁ else 0) ∂μ

private theorem measurable_layerCakeHighMoment
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (p₀ W : ℝ)
    (f : X → ℂ) (hf : Measurable f) :
    Measurable (layerCakeHighMoment μ p₀ W f) := by
  apply Antitone.measurable
  intro a b hab
  unfold layerCakeHighMoment
  apply lintegral_mono
  intro x
  by_cases hb : b < W * ‖f x‖
  · have ha : a < W * ‖f x‖ := lt_of_le_of_lt hab hb
    simp [ha, hb]
  · simp [hb]

private theorem measurable_layerCakeLowMoment
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (p₁ W : ℝ)
    (f : X → ℂ) (hf : Measurable f) :
    Measurable (layerCakeLowMoment μ p₁ W f) := by
  apply Monotone.measurable
  intro a b hab
  unfold layerCakeLowMoment
  apply lintegral_mono
  intro x
  by_cases ha : W * ‖f x‖ ≤ a
  · have hb : W * ‖f x‖ ≤ b := ha.trans hab
    simp [ha, hb]
  · simp [ha]

private theorem measurable_layerCakeHighKernel
    {X : Type*} [MeasurableSpace X] (p₀ p W : ℝ) (f : X → ℂ)
    (hf : Measurable f) :
    Measurable (fun z : ℝ × X => layerCakeHighKernel p₀ p W f z.1 z.2) := by
  have hv : Measurable (fun z : ℝ × X => W * ‖f z.2‖) :=
    measurable_const.mul (hf.norm.comp measurable_snd)
  have hcut : MeasurableSet {z : ℝ × X | z.1 < W * ‖f z.2‖} :=
    measurableSet_lt measurable_fst hv
  have hcoeff : Measurable (fun z : ℝ × X =>
      ENNReal.ofReal (W * ‖f z.2‖) ^ p₀) :=
    ENNReal.continuous_rpow_const.measurable.comp (hv.ennreal_ofReal)
  have hweight : Measurable (fun z : ℝ × X => ENNReal.ofReal z.1 ^ (p - p₀ - 1)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_fst.ennreal_ofReal
  exact Measurable.ite hcut (hcoeff.mul hweight) measurable_const

private theorem measurable_layerCakeLowKernel
    {X : Type*} [MeasurableSpace X] (p p₁ W : ℝ) (f : X → ℂ)
    (hf : Measurable f) :
    Measurable (fun z : ℝ × X => layerCakeLowKernel p p₁ W f z.1 z.2) := by
  have hv : Measurable (fun z : ℝ × X => W * ‖f z.2‖) :=
    measurable_const.mul (hf.norm.comp measurable_snd)
  have hcut : MeasurableSet {z : ℝ × X | W * ‖f z.2‖ ≤ z.1} :=
    measurableSet_le hv measurable_fst
  have hcoeff : Measurable (fun z : ℝ × X =>
      ENNReal.ofReal (W * ‖f z.2‖) ^ p₁) :=
    ENNReal.continuous_rpow_const.measurable.comp (hv.ennreal_ofReal)
  have hweight : Measurable (fun z : ℝ × X => ENNReal.ofReal z.1 ^ (p - p₁ - 1)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_fst.ennreal_ofReal
  exact Measurable.ite hcut (hcoeff.mul hweight) measurable_const

private theorem layerCake_highCutoff_moment
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p₀ W : ℝ}
    (hp₀ : 0 < p₀) (hW : 0 < W) (f : X → ℂ) (t : ℝ) :
    complexLpMoment p₀ μ (layerCakeHighCutoff (t / W) f) =
      layerCakeHighMoment μ p₀ W f t := by
  unfold complexLpMoment layerCakeHighMoment
  apply lintegral_congr_ae
  filter_upwards with x
  have hcut : t / W < ‖f x‖ ↔ t < W * ‖f x‖ := by
    rw [div_lt_iff₀ hW]
    simp [mul_comm]
  by_cases h : t / W < ‖f x‖
  · have h' : t < W * ‖f x‖ := hcut.mp h
    simp [layerCakeHighCutoff, h, h']
  · have h' : ¬ t < W * ‖f x‖ := fun hh => h (hcut.mpr hh)
    simp [layerCakeHighCutoff, h, h', ENNReal.zero_rpow_of_pos hp₀]

private theorem layerCake_lowCutoff_moment
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p₁ W : ℝ}
    (hp₁ : 0 < p₁) (hW : 0 < W) (f : X → ℂ) (t : ℝ) :
    complexLpMoment p₁ μ (layerCakeLowCutoff (t / W) f) =
      layerCakeLowMoment μ p₁ W f t := by
  unfold complexLpMoment layerCakeLowMoment
  apply lintegral_congr_ae
  filter_upwards with x
  have hcut : ‖f x‖ ≤ t / W ↔ W * ‖f x‖ ≤ t := by
    rw [le_div_iff₀ hW]
    simp [mul_comm]
  by_cases h : ‖f x‖ ≤ t / W
  · have h' : W * ‖f x‖ ≤ t := hcut.mp h
    simp [layerCakeLowCutoff, h, h']
  · have h' : ¬ W * ‖f x‖ ≤ t := fun hh => h (hcut.mpr hh)
    simp [layerCakeLowCutoff, h, h', ENNReal.zero_rpow_of_pos hp₁]

private def layerCakeHighWeightedMoment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p₀ p W : ℝ) (f : X → ℂ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (W / t)).rpow p₀ * layerCakeHighMoment μ p₀ W f t *
    ENNReal.ofReal t ^ (p - 1)

private def layerCakeLowWeightedMoment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p p₁ W : ℝ) (f : X → ℂ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (W / t)).rpow p₁ * layerCakeLowMoment μ p₁ W f t *
    ENNReal.ofReal t ^ (p - 1)

private theorem lintegral_eq_restrict_of_zero_outside
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (g : X → ℝ≥0∞)
    (hzero : ∀ x, x ∉ s → g x = 0) :
    (∫⁻ x, g x ∂μ) = ∫⁻ x, g x ∂(μ.restrict s) := by
  calc
    (∫⁻ x, g x ∂μ) = ∫⁻ x, s.indicator g x ∂μ := by
      apply lintegral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ s
      · simp [hx]
      · simp [hx, hzero x hx]
    _ = ∫⁻ x in s, g x ∂μ := by rw [lintegral_indicator hs]
    _ = ∫⁻ x, g x ∂(μ.restrict s) := rfl

private theorem complexLpMoment_restrict_support
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ}
    (hp : 0 < p) (f : X → ℂ) (hf : Measurable f) :
    complexLpMoment p μ f =
      complexLpMoment p (μ.restrict {x | f x ≠ 0}) f := by
  let s : Set X := {x | f x ≠ 0}
  have hs : MeasurableSet s := measurableSet_nonzero_complex hf
  unfold complexLpMoment
  exact lintegral_eq_restrict_of_zero_outside μ s hs _ (by
    intro x hx
    have hfx : f x = 0 := by simpa [s] using hx
    simp [hfx, ENNReal.zero_rpow_of_pos hp])

private theorem layerCakeHighWeightedMoment_restrict_support
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p₀ p W : ℝ}
    (hp₀ : 0 < p₀) (f : X → ℂ) (hf : Measurable f) (t : ℝ) :
    layerCakeHighWeightedMoment μ p₀ p W f t =
      layerCakeHighWeightedMoment (μ.restrict {x | f x ≠ 0}) p₀ p W f t := by
  let s : Set X := {x | f x ≠ 0}
  have hs : MeasurableSet s := measurableSet_nonzero_complex hf
  unfold layerCakeHighWeightedMoment layerCakeHighMoment
  congr 2
  exact lintegral_eq_restrict_of_zero_outside μ s hs _ (by
    intro x hx
    have hfx : f x = 0 := by simpa [s] using hx
    simp [hfx, ENNReal.zero_rpow_of_pos hp₀])

private theorem layerCakeLowWeightedMoment_restrict_support
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p p₁ W : ℝ}
    (hp₁ : 0 < p₁) (f : X → ℂ) (hf : Measurable f) (t : ℝ) :
    layerCakeLowWeightedMoment μ p p₁ W f t =
      layerCakeLowWeightedMoment (μ.restrict {x | f x ≠ 0}) p p₁ W f t := by
  let s : Set X := {x | f x ≠ 0}
  have hs : MeasurableSet s := measurableSet_nonzero_complex hf
  unfold layerCakeLowWeightedMoment layerCakeLowMoment
  congr 2
  exact lintegral_eq_restrict_of_zero_outside μ s hs _ (by
    intro x hx
    have hfx : f x = 0 := by simpa [s] using hx
    simp [hfx, ENNReal.zero_rpow_of_pos hp₁])

private theorem measurable_layerCakeHighWeightedMoment
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (p₀ p W : ℝ)
    (f : X → ℂ) (hf : Measurable f) :
    Measurable (layerCakeHighWeightedMoment μ p₀ p W f) := by
  have hfactor : Measurable (fun t : ℝ => ENNReal.ofReal (W / t) ^ p₀) :=
    ENNReal.continuous_rpow_const.measurable.comp
      ((measurable_const.div measurable_id).ennreal_ofReal)
  have hweight : Measurable (fun t : ℝ => ENNReal.ofReal t ^ (p - 1)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  exact (hfactor.mul (measurable_layerCakeHighMoment μ p₀ W f hf)).mul hweight

private theorem measurable_layerCakeLowWeightedMoment
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (p p₁ W : ℝ)
    (f : X → ℂ) (hf : Measurable f) :
    Measurable (layerCakeLowWeightedMoment μ p p₁ W f) := by
  have hfactor : Measurable (fun t : ℝ => ENNReal.ofReal (W / t) ^ p₁) :=
    ENNReal.continuous_rpow_const.measurable.comp
      ((measurable_const.div measurable_id).ennreal_ofReal)
  have hweight : Measurable (fun t : ℝ => ENNReal.ofReal t ^ (p - 1)) :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  exact (hfactor.mul (measurable_layerCakeLowMoment μ p₁ W f hf)).mul hweight

private theorem layerCake_highWeightedMoment_eq_kernelIntegral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p₀ p W : ℝ}
    (hp₀ : 0 < p₀) (hp₀p : p₀ < p) (hW : 0 < W)
    (f : X → ℂ) (hf : Measurable f) (t : ℝ) (ht : 0 < t) :
    layerCakeHighWeightedMoment μ p₀ p W f t =
      ∫⁻ x, layerCakeHighKernel p₀ p W f t x ∂μ := by
  let highFn := layerCakeHighCutoff (t / W) f
  have hhighMeas : Measurable highFn := by
    dsimp [highFn]
    exact Measurable.ite (measurableSet_lt measurable_const hf.norm) hf measurable_const
  have hqMeas : Measurable (fun x : X => ENNReal.ofReal ‖highFn x‖ ^ p₀) :=
    ENNReal.continuous_rpow_const.measurable.comp (hhighMeas.norm.ennreal_ofReal)
  unfold layerCakeHighWeightedMoment
  rw [show layerCakeHighMoment μ p₀ W f t =
      complexLpMoment p₀ μ highFn from
        (layerCake_highCutoff_moment hp₀ hW f t).symm]
  unfold complexLpMoment
  calc
    (ENNReal.ofReal (W / t)).rpow p₀ *
        (∫⁻ x, ENNReal.ofReal ‖highFn x‖ ^ p₀ ∂μ) *
          ENNReal.ofReal t ^ (p - 1) =
        ((ENNReal.ofReal (W / t)).rpow p₀ * ENNReal.ofReal t ^ (p - 1)) *
          (∫⁻ x, ENNReal.ofReal ‖highFn x‖ ^ p₀ ∂μ) := by ac_rfl
    _ = ∫⁻ x, ((ENNReal.ofReal (W / t)).rpow p₀ *
          ENNReal.ofReal t ^ (p - 1)) * ENNReal.ofReal ‖highFn x‖ ^ p₀ ∂μ := by
        symm
        exact lintegral_const_mul _ hqMeas
    _ = ∫⁻ x, layerCakeHighKernel p₀ p W f t x ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with x
        by_cases hx : t / W < ‖f x‖
        · have hx' : t < W * ‖f x‖ := by
            rw [div_lt_iff₀ hW] at hx
            simpa [mul_comm] using hx
          have hnorm : ‖highFn x‖ = ‖f x‖ := by
            simp [highFn, layerCakeHighCutoff, hx]
          simp only [layerCakeHighKernel, if_pos hx']
          rw [hnorm, ENNReal.ofReal_rpow_of_pos ht]
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (layerCake_highWeight_formula hp₀ hp₀p hW ht (norm_nonneg (f x)))
        · have hx' : ¬ t < W * ‖f x‖ := by
            intro hlt
            apply hx
            rw [div_lt_iff₀ hW]
            simpa [mul_comm] using hlt
          simp [layerCakeHighKernel, highFn, layerCakeHighCutoff, hx, hx',
            ENNReal.zero_rpow_of_pos hp₀]

private theorem layerCake_lowWeightedMoment_eq_kernelIntegral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p p₁ W : ℝ}
    (hp : 0 < p) (hpp₁ : p < p₁) (hp₁ : 0 < p₁) (hW : 0 < W)
    (f : X → ℂ) (hf : Measurable f) (t : ℝ) (ht : 0 < t) :
    layerCakeLowWeightedMoment μ p p₁ W f t =
      ∫⁻ x, layerCakeLowKernel p p₁ W f t x ∂μ := by
  let lowFn := layerCakeLowCutoff (t / W) f
  have hlowMeas : Measurable lowFn := by
    dsimp [lowFn]
    exact Measurable.ite (measurableSet_le hf.norm measurable_const) hf measurable_const
  have hqMeas : Measurable (fun x : X => ENNReal.ofReal ‖lowFn x‖ ^ p₁) :=
    ENNReal.continuous_rpow_const.measurable.comp (hlowMeas.norm.ennreal_ofReal)
  unfold layerCakeLowWeightedMoment
  rw [show layerCakeLowMoment μ p₁ W f t =
      complexLpMoment p₁ μ lowFn from
        (layerCake_lowCutoff_moment hp₁ hW f t).symm]
  unfold complexLpMoment
  calc
    (ENNReal.ofReal (W / t)).rpow p₁ *
        (∫⁻ x, ENNReal.ofReal ‖lowFn x‖ ^ p₁ ∂μ) *
          ENNReal.ofReal t ^ (p - 1) =
        ((ENNReal.ofReal (W / t)).rpow p₁ * ENNReal.ofReal t ^ (p - 1)) *
          (∫⁻ x, ENNReal.ofReal ‖lowFn x‖ ^ p₁ ∂μ) := by ac_rfl
    _ = ∫⁻ x, ((ENNReal.ofReal (W / t)).rpow p₁ *
          ENNReal.ofReal t ^ (p - 1)) * ENNReal.ofReal ‖lowFn x‖ ^ p₁ ∂μ := by
        symm
        exact lintegral_const_mul _ hqMeas
    _ = ∫⁻ x, layerCakeLowKernel p p₁ W f t x ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with x
        by_cases hx : ‖f x‖ ≤ t / W
        · have hx' : W * ‖f x‖ ≤ t := by
            rw [le_div_iff₀ hW] at hx
            simpa [mul_comm] using hx
          have hnorm : ‖lowFn x‖ = ‖f x‖ := by
            simp [lowFn, layerCakeLowCutoff, hx]
          simp only [layerCakeLowKernel, if_pos hx']
          rw [hnorm, ENNReal.ofReal_rpow_of_pos ht]
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (layerCake_lowWeight_formula hp hpp₁ hp₁ hW ht (norm_nonneg (f x)))
        · have hx' : ¬ W * ‖f x‖ ≤ t := by
            intro hle
            apply hx
            rw [le_div_iff₀ hW]
            simpa [mul_comm] using hle
          simp [layerCakeLowKernel, lowFn, layerCakeLowCutoff, hx, hx',
            ENNReal.zero_rpow_of_pos hp₁]

private theorem layerCake_highWeightedMoment_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p₀ p W : ℝ}
    (hp₀ : 0 < p₀) (hp₀p : p₀ < p) (hp : 0 < p) (hW : 0 < W)
    (f : X → ℂ) (hf : Measurable f)
    (hSupport : μ {x | f x ≠ 0} < ∞) :
    (∫⁻ t in Ioi (0 : ℝ), layerCakeHighWeightedMoment μ p₀ p W f t) =
      ENNReal.ofReal (W ^ p / (p - p₀)) * complexLpMoment p μ f := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let μs : Measure X := μ.restrict {x | f x ≠ 0}
  have hs : MeasurableSet {x | f x ≠ 0} := measurableSet_nonzero_complex hf
  haveI : IsFiniteMeasure μs := ⟨by
    change (μ.restrict {x | f x ≠ 0}) Set.univ < ∞
    rw [Measure.restrict_apply_univ]
    exact hSupport⟩
  have hkernel : Measurable (fun z : ℝ × X =>
      layerCakeHighKernel p₀ p W f z.1 z.2) :=
    measurable_layerCakeHighKernel p₀ p W f hf
  have hswap :
      (∫⁻ t, ∫⁻ x, layerCakeHighKernel p₀ p W f t x ∂μs ∂ν) =
        ∫⁻ x, ∫⁻ t, layerCakeHighKernel p₀ p W f t x ∂ν ∂μs := by
    exact MeasureTheory.lintegral_lintegral_swap
      (μ := ν) (ν := μs) (f := fun t x => layerCakeHighKernel p₀ p W f t x)
      hkernel.aemeasurable
  have htail (x : X) :
      (∫⁻ t, layerCakeHighKernel p₀ p W f t x ∂ν) =
        ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (p - p₀)) := by
    dsimp [ν, layerCakeHighKernel]
    exact layerCake_highInput_tail hp₀ hp₀p hW (norm_nonneg (f x))
  have hden : 0 < p - p₀ := by linarith
  have hC : 0 ≤ W ^ p / (p - p₀) :=
    div_nonneg (Real.rpow_nonneg hW.le _) hden.le
  have hqMeas : Measurable (fun x : X => ENNReal.ofReal ‖f x‖ ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp (hf.norm.ennreal_ofReal)
  have hterm (x : X) :
      ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (p - p₀)) =
        ENNReal.ofReal (W ^ p / (p - p₀)) * ENNReal.ofReal ‖f x‖ ^ p := by
    have hreal : W ^ p * ‖f x‖ ^ p / (p - p₀) =
        (W ^ p / (p - p₀)) * ‖f x‖ ^ p := by ring
    rw [hreal, ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hp.le]
  calc
    (∫⁻ t in Ioi (0 : ℝ), layerCakeHighWeightedMoment μ p₀ p W f t) =
        ∫⁻ t, ∫⁻ x, layerCakeHighKernel p₀ p W f t x ∂μs ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        layerCakeHighWeightedMoment μ p₀ p W f t =
            layerCakeHighWeightedMoment μs p₀ p W f t :=
          layerCakeHighWeightedMoment_restrict_support hp₀ f hf t
        _ = ∫⁻ x, layerCakeHighKernel p₀ p W f t x ∂μs :=
          layerCake_highWeightedMoment_eq_kernelIntegral hp₀ hp₀p hW f hf t
            (mem_Ioi.mp ht)
    _ = ∫⁻ x, ∫⁻ t, layerCakeHighKernel p₀ p W f t x ∂ν ∂μs := hswap
    _ = ∫⁻ x, ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (p - p₀)) ∂μs := by
      apply lintegral_congr_ae
      filter_upwards with x
      exact htail x
    _ = ∫⁻ x, ENNReal.ofReal (W ^ p / (p - p₀)) *
          ENNReal.ofReal ‖f x‖ ^ p ∂μs := by
      apply lintegral_congr_ae
      filter_upwards with x
      exact hterm x
    _ = ENNReal.ofReal (W ^ p / (p - p₀)) * complexLpMoment p μs f := by
      rw [lintegral_const_mul _ hqMeas]
      rfl
    _ = ENNReal.ofReal (W ^ p / (p - p₀)) * complexLpMoment p μ f := by
      rw [← complexLpMoment_restrict_support hp f hf]

private theorem layerCake_lowWeightedMoment_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p p₁ W : ℝ}
    (hp : 0 < p) (hpp₁ : p < p₁) (hp₁ : 0 < p₁) (hW : 0 < W)
    (f : X → ℂ) (hf : Measurable f)
    (hSupport : μ {x | f x ≠ 0} < ∞) :
    (∫⁻ t in Ioi (0 : ℝ), layerCakeLowWeightedMoment μ p p₁ W f t) =
      ENNReal.ofReal (W ^ p / (p₁ - p)) * complexLpMoment p μ f := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let μs : Measure X := μ.restrict {x | f x ≠ 0}
  have hs : MeasurableSet {x | f x ≠ 0} := measurableSet_nonzero_complex hf
  haveI : IsFiniteMeasure μs := ⟨by
    change (μ.restrict {x | f x ≠ 0}) Set.univ < ∞
    rw [Measure.restrict_apply_univ]
    exact hSupport⟩
  have hkernel : Measurable (fun z : ℝ × X =>
      layerCakeLowKernel p p₁ W f z.1 z.2) :=
    measurable_layerCakeLowKernel p p₁ W f hf
  have hswap :
      (∫⁻ t, ∫⁻ x, layerCakeLowKernel p p₁ W f t x ∂μs ∂ν) =
        ∫⁻ x, ∫⁻ t, layerCakeLowKernel p p₁ W f t x ∂ν ∂μs := by
    exact MeasureTheory.lintegral_lintegral_swap
      (μ := ν) (ν := μs) (f := fun t x => layerCakeLowKernel p p₁ W f t x)
      hkernel.aemeasurable
  have htail (x : X) :
      (∫⁻ t, layerCakeLowKernel p p₁ W f t x ∂ν) =
        ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (p₁ - p)) := by
    dsimp [ν, layerCakeLowKernel]
    exact layerCake_lowInput_tail hp hpp₁ hp₁ hW (norm_nonneg (f x))
  have hden : 0 < p₁ - p := by linarith
  have hC : 0 ≤ W ^ p / (p₁ - p) :=
    div_nonneg (Real.rpow_nonneg hW.le _) hden.le
  have hqMeas : Measurable (fun x : X => ENNReal.ofReal ‖f x‖ ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp (hf.norm.ennreal_ofReal)
  have hterm (x : X) :
      ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (p₁ - p)) =
        ENNReal.ofReal (W ^ p / (p₁ - p)) * ENNReal.ofReal ‖f x‖ ^ p := by
    have hreal : W ^ p * ‖f x‖ ^ p / (p₁ - p) =
        (W ^ p / (p₁ - p)) * ‖f x‖ ^ p := by ring
    rw [hreal, ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hp.le]
  calc
    (∫⁻ t in Ioi (0 : ℝ), layerCakeLowWeightedMoment μ p p₁ W f t) =
        ∫⁻ t, ∫⁻ x, layerCakeLowKernel p p₁ W f t x ∂μs ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        layerCakeLowWeightedMoment μ p p₁ W f t =
            layerCakeLowWeightedMoment μs p p₁ W f t :=
          layerCakeLowWeightedMoment_restrict_support hp₁ f hf t
        _ = ∫⁻ x, layerCakeLowKernel p p₁ W f t x ∂μs :=
          layerCake_lowWeightedMoment_eq_kernelIntegral hp hpp₁ hp₁ hW f hf t
            (mem_Ioi.mp ht)
    _ = ∫⁻ x, ∫⁻ t, layerCakeLowKernel p p₁ W f t x ∂ν ∂μs := hswap
    _ = ∫⁻ x, ENNReal.ofReal (W ^ p * ‖f x‖ ^ p / (p₁ - p)) ∂μs := by
      apply lintegral_congr_ae
      filter_upwards with x
      exact htail x
    _ = ∫⁻ x, ENNReal.ofReal (W ^ p / (p₁ - p)) *
          ENNReal.ofReal ‖f x‖ ^ p ∂μs := by
      apply lintegral_congr_ae
      filter_upwards with x
      exact hterm x
    _ = ENNReal.ofReal (W ^ p / (p₁ - p)) * complexLpMoment p μs f := by
      rw [lintegral_const_mul _ hqMeas]
      rfl
    _ = ENNReal.ofReal (W ^ p / (p₁ - p)) * complexLpMoment p μ f := by
      rw [← complexLpMoment_restrict_support hp f hf]

/-- The two Tonelli tails, including the layer-cake derivative, combine to
the exact `W^p * p * (1/(p-p₀) + 1/(p₁-p))` moment coefficient. -/
theorem layerCake_twoTail_sourceCoefficient
    {p₀ p p₁ W u : ℝ} (hp₀ : 0 < p₀) (hp : p₀ < p)
    (hp₁ : p < p₁) (hW : 0 < W) (hu : 0 ≤ u) :
    ENNReal.ofReal p *
        (ENNReal.ofReal (W ^ p * u ^ p / (p - p₀)) +
          ENNReal.ofReal (W ^ p * u ^ p / (p₁ - p))) =
      ENNReal.ofReal
        (W ^ p * u ^ p * (p * (1 / (p - p₀) + 1 / (p₁ - p)))) := by
  have hp_pos : 0 < p := hp₀.trans hp
  have hden₀ : 0 < p - p₀ := by linarith
  have hden₁ : 0 < p₁ - p := by linarith
  have hterm₀ : 0 ≤ W ^ p * u ^ p / (p - p₀) := by
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hW.le _) (Real.rpow_nonneg hu _))
      hden₀.le
  have hterm₁ : 0 ≤ W ^ p * u ^ p / (p₁ - p) := by
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hW.le _) (Real.rpow_nonneg hu _))
      hden₁.le
  rw [← ENNReal.ofReal_add hterm₀ hterm₁]
  rw [← ENNReal.ofReal_mul hp_pos.le]
  congr 1
  field_simp [ne_of_gt hden₀, ne_of_gt hden₁]

/-- Raising the source interpolation constant to the exponent `p` gives the
coefficient used in the p-moment proof. -/
theorem layerCake_sourceConstant_rpow
    {p₀ p p₁ W : ℝ} (hp₀ : 0 < p₀) (hp : p₀ < p)
    (hp₁ : p < p₁) (hW : 0 ≤ W) :
    (2 * W * (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) ^ p =
      2 ^ p * W ^ p * (p * (1 / (p - p₀) + 1 / (p₁ - p))) := by
  have hp_pos : 0 < p := hp₀.trans hp
  have hden₀ : 0 < p - p₀ := by linarith
  have hden₁ : 0 < p₁ - p := by linarith
  have hS : 0 ≤ p * (1 / (p - p₀) + 1 / (p₁ - p)) := by
    apply mul_nonneg hp_pos.le
    exact add_nonneg (div_nonneg zero_le_one hden₀.le)
      (div_nonneg zero_le_one hden₁.le)
  have hpow :
      ((p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) ^ p =
        p * (1 / (p - p₀) + 1 / (p₁ - p)) := by
    rw [← Real.rpow_mul hS (1 / p) p]
    have hexp : (1 / p) * p = 1 := by field_simp [ne_of_gt hp_pos]
    rw [hexp, Real.rpow_one]
  calc
    (2 * W * (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) ^ p =
        (2 * W) ^ p *
          ((p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) ^ p := by
      exact Real.mul_rpow (x := 2 * W)
        (y := (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p))
        (z := p) (mul_nonneg (by norm_num) hW) (Real.rpow_nonneg hS _)
    _ = (2 * W) ^ p *
          (p * (1 / (p - p₀) + 1 / (p₁ - p))) := by rw [hpow]
    _ = 2 ^ p * W ^ p *
          (p * (1 / (p - p₀) + 1 / (p₁ - p))) := by
      rw [Real.mul_rpow (x := 2) (y := W) (z := p) (by norm_num) hW]

/-- The exact `p`-moment conclusion of blueprint `lv:interpolation`.
The input measure is only restricted to the finite support of `f` inside
the Tonelli proof; no sigma-finiteness hypothesis on `μ` is assumed. -/
theorem layerCake_interpolation_moment
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p₀ p p₁ W : ℝ} (U : LayerCakeWeakOperator μ p₀ p₁ W)
    (hp₀ : 0 < p₀) (hp : p₀ < p) (hp₁ : p < p₁) (hW : 0 ≤ W)
    (f : LayerCakeInput μ) :
    (∫⁻ x, ENNReal.ofReal ((U.apply f x) ^ p) ∂μ) ≤
      ENNReal.ofReal ((2 * W *
        (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) ^ p) *
        complexLpMoment p μ f.1 := by
  have hp_pos : 0 < p := hp₀.trans hp
  have hp1_pos : 0 < p₁ := hp_pos.trans hp₁
  have hFnonneg : ∀ x, 0 ≤ U.apply f x := U.nonneg_apply f
  have hFmeas : Measurable (U.apply f) := U.measurable_apply f
  have hsupport : μ {x | f.1 x ≠ 0} < ∞ := f.2.2.2
  have hlayer := layerCake_realOutput_scaledMoment (μ := μ) hp_pos (U.apply f)
    hFnonneg hFmeas
  by_cases hWzero : W = 0
  · have hzeroLevel (t : ℝ) (ht : 0 < t) :
        μ {x | 2 * t < U.apply f x} = 0 := by
      have hsplit := layerCake_strictLevel_split U f t ht
      have hfactor₀ : (ENNReal.ofReal (W / t)).rpow p₀ = 0 := by
        rw [hWzero, zero_div, ENNReal.ofReal_zero]
        exact ENNReal.zero_rpow_of_pos hp₀
      have hfactor₁ : (ENNReal.ofReal (W / t)).rpow p₁ = 0 := by
        rw [hWzero, zero_div, ENNReal.ofReal_zero]
        exact ENNReal.zero_rpow_of_pos (hp_pos.trans hp₁)
      rw [hfactor₀, hfactor₁] at hsplit
      exact le_antisymm (by simpa using hsplit) zero_le
    have hlevelZero :
        (fun t : ℝ => μ {x | 2 * t < U.apply f x} *
          ENNReal.ofReal (t ^ (p - 1))) =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp [hzeroLevel t (mem_Ioi.mp ht)]
    have hmomentZero :
        (∫⁻ x, ENNReal.ofReal ((U.apply f x) ^ p) ∂μ) = 0 := by
      rw [hlayer]
      rw [lintegral_congr_ae hlevelZero]
      simp
    have hconstZero :
        (2 * W * (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) ^ p = 0 := by
      rw [hWzero]
      simp [Real.zero_rpow hp_pos.ne']
    rw [hmomentZero, hconstZero]
    simp
  · have hWpos : 0 < W := lt_of_le_of_ne hW (Ne.symm hWzero)
    have hhigh (t : ℝ) (ht : 0 < t) :
        layerCakeHighWeightedMoment μ p₀ p W f.1 t =
          (ENNReal.ofReal (W / t)).rpow p₀ *
            complexLpMoment p₀ μ (layerCakeHighCutoff (t / W) f.1) *
              ENNReal.ofReal t ^ (p - 1) := by
      rw [layerCake_highCutoff_moment hp₀ hWpos f.1 t]
      rfl
    have hlow (t : ℝ) (ht : 0 < t) :
        layerCakeLowWeightedMoment μ p p₁ W f.1 t =
          (ENNReal.ofReal (W / t)).rpow p₁ *
            complexLpMoment p₁ μ (layerCakeLowCutoff (t / W) f.1) *
              ENNReal.ofReal t ^ (p - 1) := by
      rw [layerCake_lowCutoff_moment hp1_pos hWpos f.1 t]
      rfl
    have hpoint (t : ℝ) (ht : 0 < t) :
        μ {x | 2 * t < U.apply f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
          layerCakeHighWeightedMoment μ p₀ p W f.1 t +
            layerCakeLowWeightedMoment μ p p₁ W f.1 t := by
      have hsplit := layerCake_strictLevel_split U f t ht
      rw [layerCake_highCutoff_moment hp₀ hWpos f.1 t,
        layerCake_lowCutoff_moment hp1_pos hWpos f.1 t] at hsplit
      have hmul :
          μ {x | 2 * t < U.apply f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
            ((ENNReal.ofReal (W / t)).rpow p₀ *
                layerCakeHighMoment μ p₀ W f.1 t +
              (ENNReal.ofReal (W / t)).rpow p₁ *
                layerCakeLowMoment μ p₁ W f.1 t) *
              ENNReal.ofReal (t ^ (p - 1)) := by
        gcongr
      rw [add_mul] at hmul
      simpa [layerCakeHighWeightedMoment, layerCakeLowWeightedMoment, mul_assoc,
        ENNReal.ofReal_rpow_of_pos ht] using hmul
    have hweighted :
        (∫⁻ t in Ioi (0 : ℝ),
          μ {x | 2 * t < U.apply f x} * ENNReal.ofReal (t ^ (p - 1))) ≤
        (∫⁻ t in Ioi (0 : ℝ),
          layerCakeHighWeightedMoment μ p₀ p W f.1 t) +
        (∫⁻ t in Ioi (0 : ℝ),
          layerCakeLowWeightedMoment μ p p₁ W f.1 t) := by
      calc
        _ ≤ ∫⁻ t in Ioi (0 : ℝ),
            layerCakeHighWeightedMoment μ p₀ p W f.1 t +
              layerCakeLowWeightedMoment μ p p₁ W f.1 t := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact hpoint t (mem_Ioi.mp ht)
        _ = _ := by
          rw [lintegral_add_left
            (measurable_layerCakeHighWeightedMoment μ p₀ p W f.1 f.2.1)]
    have hhighTail := layerCake_highWeightedMoment_integral
      hp₀ hp hp_pos hWpos f.1 f.2.1 hsupport
    have hlowTail := layerCake_lowWeightedMoment_integral
      hp_pos hp₁ hp1_pos hWpos f.1 f.2.1 hsupport
    have hden₀ : 0 < p - p₀ := by linarith
    have hden₁ : 0 < p₁ - p := by linarith
    have ha₀ : 0 ≤ W ^ p / (p - p₀) :=
      div_nonneg (Real.rpow_nonneg hWpos.le _) hden₀.le
    have ha₁ : 0 ≤ W ^ p / (p₁ - p) :=
      div_nonneg (Real.rpow_nonneg hWpos.le _) hden₁.le
    have hbracket : 0 ≤ p * (1 / (p - p₀) + 1 / (p₁ - p)) := by
      apply mul_nonneg hp_pos.le
      exact add_nonneg (div_nonneg zero_le_one hden₀.le)
        (div_nonneg zero_le_one hden₁.le)
    have hcoeff :
        ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal p *
            (ENNReal.ofReal (W ^ p / (p - p₀)) +
              ENNReal.ofReal (W ^ p / (p₁ - p)))) =
        ENNReal.ofReal ((2 * W *
          (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) ^ p) := by
      rw [← ENNReal.ofReal_add ha₀ ha₁,
        ← ENNReal.ofReal_mul hp_pos.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)]
      congr 1
      calc
        2 ^ p * (p * (W ^ p / (p - p₀) + W ^ p / (p₁ - p))) =
            2 ^ p * W ^ p * (p * (1 / (p - p₀) + 1 / (p₁ - p))) := by ring
        _ = (2 * W *
            (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) ^ p := by
          symm
          exact layerCake_sourceConstant_rpow hp₀ hp hp₁ hWpos.le
    calc
      (∫⁻ x, ENNReal.ofReal ((U.apply f x) ^ p) ∂μ) =
          ENNReal.ofReal (2 ^ p) *
            (ENNReal.ofReal p *
              ∫⁻ t in Ioi (0 : ℝ),
                μ {x | 2 * t < U.apply f x} * ENNReal.ofReal (t ^ (p - 1))) :=
        hlayer
      _ ≤ ENNReal.ofReal (2 ^ p) *
            (ENNReal.ofReal p *
              ((∫⁻ t in Ioi (0 : ℝ),
                  layerCakeHighWeightedMoment μ p₀ p W f.1 t) +
                (∫⁻ t in Ioi (0 : ℝ),
                  layerCakeLowWeightedMoment μ p p₁ W f.1 t))) := by
        gcongr
      _ = ENNReal.ofReal (2 ^ p) *
            (ENNReal.ofReal p *
              ((ENNReal.ofReal (W ^ p / (p - p₀)) * complexLpMoment p μ f.1) +
                (ENNReal.ofReal (W ^ p / (p₁ - p)) * complexLpMoment p μ f.1))) := by
        rw [hhighTail, hlowTail]
      _ = ENNReal.ofReal ((2 * W *
            (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) ^ p) *
            complexLpMoment p μ f.1 := by
        calc
          ENNReal.ofReal (2 ^ p) *
              (ENNReal.ofReal p *
                ((ENNReal.ofReal (W ^ p / (p - p₀)) * complexLpMoment p μ f.1) +
                  (ENNReal.ofReal (W ^ p / (p₁ - p)) * complexLpMoment p μ f.1))) =
            ENNReal.ofReal (2 ^ p) *
              (ENNReal.ofReal p *
                ((ENNReal.ofReal (W ^ p / (p - p₀)) +
                  ENNReal.ofReal (W ^ p / (p₁ - p))) * complexLpMoment p μ f.1)) := by
              rw [← add_mul]
          _ = (ENNReal.ofReal (2 ^ p) *
                (ENNReal.ofReal p *
                  (ENNReal.ofReal (W ^ p / (p - p₀)) +
                    ENNReal.ofReal (W ^ p / (p₁ - p)))) ) *
                complexLpMoment p μ f.1 := by ac_rfl
          _ = ENNReal.ofReal ((2 * W *
                (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) ^ p) *
                complexLpMoment p μ f.1 := by rw [hcoeff]

private theorem layerCake_complexMoment_eq_eLpNorm_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ}
    (hp : 0 < p) (f : X → ℂ) (hf : Measurable f) :
    complexLpMoment p μ f = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  calc
    complexLpMoment p μ f = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      unfold complexLpMoment
      apply lintegral_congr_ae
      filter_upwards with x
      simp [ENNReal.rpow_eq_pow]
    _ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hf.aestronglyMeasurable,
        htoReal]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

private theorem layerCake_realOutputMoment_eq_eLpNorm_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ}
    (hp : 0 < p) (F : X → ℝ) (hFnonneg : ∀ x, 0 ≤ F x)
    (hFmeas : Measurable F) :
    (∫⁻ x, ENNReal.ofReal (F x ^ p) ∂μ) =
      eLpNorm F (ENNReal.ofReal p) μ ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  calc
    (∫⁻ x, ENNReal.ofReal (F x ^ p) ∂μ) =
        ∫⁻ x, ‖F x‖ₑ ^ p ∂μ := by
      apply lintegral_congr_ae
      filter_upwards with x
      rw [← ENNReal.ofReal_rpow_of_nonneg (hFnonneg x) hp.le]
      have hbase : ENNReal.ofReal (F x) = ‖F x‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hFnonneg x)]
      rw [hbase]
    _ = eLpNorm F (ENNReal.ofReal p) μ ^ p := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hFmeas.aestronglyMeasurable,
        htoReal]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- Blueprint `lv:interpolation`, expressed as the finite-exponent `eLpNorm`
bound for the nonnegative measurable output of `U`. -/
theorem layerCake_interpolation
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p₀ p p₁ W : ℝ} (U : LayerCakeWeakOperator μ p₀ p₁ W)
    (hp₀ : 0 < p₀) (hp : p₀ < p) (hp₁ : p < p₁) (hW : 0 ≤ W)
    (f : LayerCakeInput μ) :
    eLpNorm (U.apply f) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal
        (2 * W * (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)) *
          eLpNorm f.1 (ENNReal.ofReal p) μ := by
  have hp_pos : 0 < p := hp₀.trans hp
  let C := 2 * W * (p * (1 / (p - p₀) + 1 / (p₁ - p))) ^ (1 / p)
  have hbracket : 0 ≤ p * (1 / (p - p₀) + 1 / (p₁ - p)) := by
    apply mul_nonneg hp_pos.le
    have hd₀ : 0 < p - p₀ := by linarith
    have hd₁ : 0 < p₁ - p := by linarith
    exact add_nonneg (div_nonneg zero_le_one hd₀.le)
      (div_nonneg zero_le_one hd₁.le)
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) hW)
      (Real.rpow_nonneg hbracket _)
  have hMoment := layerCake_interpolation_moment U hp₀ hp hp₁ hW f
  have hOutputMoment := layerCake_realOutputMoment_eq_eLpNorm_rpow μ hp_pos
    (U.apply f) (U.nonneg_apply f) (U.measurable_apply f)
  have hInputMoment := layerCake_complexMoment_eq_eLpNorm_rpow μ hp_pos
    f.1 f.2.1
  rw [hOutputMoment, hInputMoment, ← ENNReal.ofReal_rpow_of_nonneg hCnonneg hp_pos.le]
    at hMoment
  have hroot := ENNReal.rpow_le_rpow hMoment (by positivity : 0 ≤ 1 / p)
  rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal C ^ p)
    (eLpNorm f.1 (ENNReal.ofReal p) μ ^ p) (by positivity : 0 ≤ 1 / p)] at hroot
  have hrootExp : p * (1 / p) = 1 := by field_simp [hp_pos.ne']
  have hOutputRoot :
      (eLpNorm (U.apply f) (ENNReal.ofReal p) μ ^ p) ^ (1 / p) =
        eLpNorm (U.apply f) (ENNReal.ofReal p) μ := by
    rw [← ENNReal.rpow_mul, hrootExp, ENNReal.rpow_one]
  have hInputRoot :
      (eLpNorm f.1 (ENNReal.ofReal p) μ ^ p) ^ (1 / p) =
        eLpNorm f.1 (ENNReal.ofReal p) μ := by
    rw [← ENNReal.rpow_mul, hrootExp, ENNReal.rpow_one]
  have hConstantRoot :
      (ENNReal.ofReal C ^ p) ^ (1 / p) = ENNReal.ofReal C := by
    rw [← ENNReal.rpow_mul, hrootExp, ENNReal.rpow_one]
  rw [hOutputRoot, hConstantRoot, hInputRoot] at hroot
  simpa [C] using hroot

end

end FractionalPrimes.Literature.Variation

end
