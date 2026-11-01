module

public import FractionalPrimes.FiniteInterpolationMoments
public import FractionalPrimes.InterpolationLayercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# Weighted power tails for the finite interpolation layer cake

The following exact scalar integrals are the two Tonelli tails in the
approved proof of `lem:interpolation`.  The cutoff is scaled by a positive
parameter, so the resulting powers are exactly `a^(2-p)` and `a^(1-p)`.
-/

namespace FractionalPrimes

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem interpolation_lintegral_rpow_Ioi
    {p c : ℝ} (hp : p < 2) (hc : 0 < c) :
    (∫⁻ t in Ioi c, ENNReal.ofReal t ^ (p - 3)) =
      ENNReal.ofReal (c ^ (p - 2) / (2 - p)) := by
  have hpow : p - 3 < -1 := by linarith
  have hIoi : Integrable (fun t : ℝ => t ^ (p - 3)) (volume.restrict (Ioi c)) :=
    integrableOn_Ioi_rpow_of_lt hpow hc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi c)] (fun t : ℝ => t ^ (p - 3)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hc.trans ht).le _
  rw [show (∫⁻ t in Ioi c, ENNReal.ofReal t ^ (p - 3)) =
      ∫⁻ t in Ioi c, ENNReal.ofReal (t ^ (p - 3)) by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact ENNReal.ofReal_rpow_of_pos (hc.trans ht)]
  rw [← ofReal_integral_eq_lintegral_ofReal hIoi hnonneg]
  rw [show (∫ t, t ^ (p - 3) ∂volume.restrict (Ioi c)) =
      ∫ t in Ioi c, t ^ (p - 3) by rfl]
  rw [integral_Ioi_rpow_of_lt hpow hc]
  rw [show p - 3 + 1 = p - 2 by ring]
  have hdenom : p - 2 ≠ 0 := by linarith
  have hdenom' : 2 - p ≠ 0 := by linarith
  congr 1
  field_simp [hdenom, hdenom']
  ring

theorem interpolation_lintegral_rpow_Ioc
    {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) :
    (∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal t ^ (p - 2)) =
      ENNReal.ofReal (c ^ (p - 1) / (p - 1)) := by
  have hpow : -1 < p - 2 := by linarith
  have hinterval : IntervalIntegrable (fun t : ℝ => t ^ (p - 2)) volume 0 c :=
    intervalIntegral.intervalIntegrable_rpow' hpow
  have hIcc : IntegrableOn (fun t : ℝ => t ^ (p - 2)) (Icc 0 c) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hc).mp hinterval
  have hIcc' : Integrable (fun t : ℝ => t ^ (p - 2)) (volume.restrict (Icc 0 c)) := hIcc
  have hIoc : Integrable (fun t : ℝ => t ^ (p - 2)) (volume.restrict (Ioc 0 c)) :=
    hIcc'.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 c)] (fun t : ℝ => t ^ (p - 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [show (∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal t ^ (p - 2)) =
      ∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal (t ^ (p - 2)) by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact ENNReal.ofReal_rpow_of_pos ht.1]
  rw [← ofReal_integral_eq_lintegral_ofReal hIoc hnonneg]
  rw [show (∫ t, t ^ (p - 2) ∂volume.restrict (Ioc 0 c)) =
      ∫ t in Ioc (0 : ℝ) c, t ^ (p - 2) by rfl]
  rw [← intervalIntegral.integral_of_le hc]
  rw [integral_rpow (Or.inl hpow)]
  have hpone : 0 < p - 1 := by linarith
  rw [show p - 2 + 1 = p - 1 by ring, Real.zero_rpow hpone.ne']
  simp

theorem interpolation_low_power_tail_scaled
    {p a u : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ha : 0 < a) (hu : 0 ≤ u) :
    ENNReal.ofReal (u ^ (2 : ℕ)) *
        (∫⁻ t in Ioi (u / a), ENNReal.ofReal t ^ (p - 3)) =
      ENNReal.ofReal (a ^ (2 - p) * u ^ p / (2 - p)) := by
  by_cases hu0 : u = 0
  · subst u
    have hp0 : 0 < p := by linarith
    simp [Real.zero_rpow hp0.ne']
  · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have hc : 0 < u / a := div_pos hu' ha
    rw [interpolation_lintegral_rpow_Ioi hp2 hc]
    rw [← ENNReal.ofReal_mul (sq_nonneg u)]
    congr 1
    have hpowu : u ^ (2 : ℝ) * u ^ (p - 2) = u ^ p := by
      rw [← Real.rpow_add hu']
      congr 1
      ring
    have hdiv : (u / a) ^ (p - 2) = u ^ (p - 2) / a ^ (p - 2) :=
      Real.div_rpow hu ha.le _
    rw [show u ^ (2 : ℕ) = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm,
      hdiv]
    have haexp : a ^ (2 - p) = (a ^ (p - 2))⁻¹ := by
      rw [show 2 - p = -(p - 2) by ring, Real.rpow_neg ha.le]
    rw [haexp]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos ha _), ne_of_gt (show 0 < 2 - p by linarith)]
    rw [← hpowu]

theorem interpolation_high_power_tail_scaled
    {p a u : ℝ} (hp1 : 1 < p) (ha : 0 < a) (hu : 0 ≤ u) :
    ENNReal.ofReal u *
        (∫⁻ t in Ioc (0 : ℝ) (u / a), ENNReal.ofReal t ^ (p - 2)) =
      ENNReal.ofReal (a ^ (1 - p) * u ^ p / (p - 1)) := by
  by_cases hu0 : u = 0
  · subst u
    have hp0 : 0 < p := by linarith
    simp [Real.zero_rpow hp0.ne']
  · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have hc : 0 ≤ u / a := div_nonneg hu ha.le
    rw [interpolation_lintegral_rpow_Ioc hp1 hc]
    rw [← ENNReal.ofReal_mul hu]
    congr 1
    have hpowu : u * u ^ (p - 1) = u ^ p := by
      calc
        u * u ^ (p - 1) = u ^ (1 : ℝ) * u ^ (p - 1) := by rw [Real.rpow_one]
        _ = u ^ (1 + (p - 1)) := (Real.rpow_add hu' 1 (p - 1)).symm
        _ = u ^ p := by congr 1; ring
    have hdiv : (u / a) ^ (p - 1) = u ^ (p - 1) / a ^ (p - 1) :=
      Real.div_rpow hu ha.le _
    have haexp : a ^ (1 - p) = (a ^ (p - 1))⁻¹ := by
      rw [show 1 - p = -(p - 1) by ring, Real.rpow_neg ha.le]
    rw [hdiv, haexp]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos ha _), ne_of_gt (show 0 < p - 1 by linarith)]
    rw [← hpowu]

private theorem interpolation_low_coordinate_integral
    {p a u : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ha : 0 < a) (hu : 0 ≤ u) :
    (∫⁻ t in Ioi (0 : ℝ),
      (if u ≤ a * t then ENNReal.ofReal (u ^ (2 : ℕ)) else 0) *
        ENNReal.ofReal t ^ (p - 3)) =
      ENNReal.ofReal (a ^ (2 - p) * u ^ p / (2 - p)) := by
  let q : ℝ := u / a
  have hq : 0 ≤ q := div_nonneg hu ha.le
  have hcond (t : ℝ) : u ≤ a * t ↔ q ≤ t := by
    dsimp [q]
    rw [div_le_iff₀ ha]
    simp [mul_comm]
  have hIci : Ici q =ᵐ[volume] Ioi q := (Ioi_ae_eq_Ici (μ := volume) (a := q)).symm
  have hset : Ici q ∩ Ioi (0 : ℝ) =ᵐ[volume] Ioi q := by
    filter_upwards [hIci] with t ht
    have ht' : t ∈ Ici q ↔ t ∈ Ioi q := Iff.of_eq ht
    apply propext
    change (t ∈ Ici q ∧ t ∈ Ioi (0 : ℝ)) ↔ t ∈ Ioi q
    constructor
    · rintro ⟨hqt, ht0⟩
      exact ht'.mp hqt
    · intro hqt
      exact ⟨ht'.mpr hqt, lt_of_le_of_lt hq hqt⟩
  have hbranch :
      (fun t : ℝ =>
        (if u ≤ a * t then ENNReal.ofReal (u ^ (2 : ℕ)) else 0) *
          ENNReal.ofReal t ^ (p - 3)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => (Ici q).indicator
        (fun t => ENNReal.ofReal (u ^ (2 : ℕ)) * ENNReal.ofReal t ^ (p - 3)) t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    by_cases ht : q ≤ t
    · simp [ht, (hcond t).mpr ht]
    · simp [ht, hcond t]
  calc
    (∫⁻ t in Ioi (0 : ℝ),
        (if u ≤ a * t then ENNReal.ofReal (u ^ (2 : ℕ)) else 0) *
          ENNReal.ofReal t ^ (p - 3)) =
      ∫⁻ t, (Ici q).indicator
        (fun t => ENNReal.ofReal (u ^ (2 : ℕ)) * ENNReal.ofReal t ^ (p - 3)) t
          ∂volume.restrict (Ioi (0 : ℝ)) := by
        exact lintegral_congr_ae hbranch
    _ = ∫⁻ t in Ici q,
        ENNReal.ofReal (u ^ (2 : ℕ)) * ENNReal.ofReal t ^ (p - 3)
          ∂volume.restrict (Ioi (0 : ℝ)) := by
        rw [lintegral_indicator measurableSet_Ici]
    _ = ∫⁻ t,
        ENNReal.ofReal (u ^ (2 : ℕ)) * ENNReal.ofReal t ^ (p - 3)
          ∂volume.restrict (Ici q ∩ Ioi (0 : ℝ)) := by
        rw [Measure.restrict_restrict measurableSet_Ici]
    _ = ∫⁻ t in Ioi q,
        ENNReal.ofReal (u ^ (2 : ℕ)) * ENNReal.ofReal t ^ (p - 3) := by
        rw [Measure.restrict_congr_set hset]
    _ = ENNReal.ofReal (u ^ (2 : ℕ)) *
        (∫⁻ t in Ioi q, ENNReal.ofReal t ^ (p - 3)) := by
        exact lintegral_const_mul (ENNReal.ofReal (u ^ (2 : ℕ)))
          (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal)
    _ = ENNReal.ofReal (a ^ (2 - p) * u ^ p / (2 - p)) := by
        dsimp [q]
        exact interpolation_low_power_tail_scaled hp1 hp2 ha hu

private theorem interpolation_high_coordinate_integral
    {p a u : ℝ} (hp1 : 1 < p) (ha : 0 < a) (hu : 0 ≤ u) :
    (∫⁻ t in Ioi (0 : ℝ),
      (if a * t < u then ENNReal.ofReal u else 0) *
        ENNReal.ofReal t ^ (p - 2)) =
      ENNReal.ofReal (a ^ (1 - p) * u ^ p / (p - 1)) := by
  let q : ℝ := u / a
  have hq : 0 ≤ q := div_nonneg hu ha.le
  have hcond (t : ℝ) : a * t < u ↔ t < q := by
    dsimp [q]
    rw [lt_div_iff₀ ha]
    simp [mul_comm]
  have hbranch :
      (fun t : ℝ =>
        (if a * t < u then ENNReal.ofReal u else 0) * ENNReal.ofReal t ^ (p - 2)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => (Ioo (0 : ℝ) q).indicator
        (fun t => ENNReal.ofReal u * ENNReal.ofReal t ^ (p - 2)) t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
    by_cases ht : t < q
    · have ht' : a * t < u := (hcond t).mpr ht
      have hmem : t ∈ Ioo (0 : ℝ) q := ⟨ht0, ht⟩
      simp [hmem, ht']
    · have ht' : ¬ a * t < u := fun h => ht ((hcond t).mp h)
      have hmem : t ∉ Ioo (0 : ℝ) q := by
        rw [mem_Ioo]
        rintro ⟨_, htq⟩
        exact ht htq
      simp [hmem, ht']
  have hIoo : Ioo (0 : ℝ) q =ᵐ[volume] Ioc (0 : ℝ) q :=
    Ioo_ae_eq_Ioc (μ := volume) (a := 0) (b := q)
  calc
    (∫⁻ t in Ioi (0 : ℝ),
        (if a * t < u then ENNReal.ofReal u else 0) *
          ENNReal.ofReal t ^ (p - 2)) =
      ∫⁻ t, (Ioo (0 : ℝ) q).indicator
        (fun t => ENNReal.ofReal u * ENNReal.ofReal t ^ (p - 2)) t
          ∂volume.restrict (Ioi (0 : ℝ)) := by
        exact lintegral_congr_ae hbranch
    _ = ∫⁻ t in Ioo (0 : ℝ) q,
        ENNReal.ofReal u * ENNReal.ofReal t ^ (p - 2)
          ∂volume.restrict (Ioi (0 : ℝ)) := by
        rw [lintegral_indicator measurableSet_Ioo]
    _ = ∫⁻ t,
        ENNReal.ofReal u * ENNReal.ofReal t ^ (p - 2)
          ∂volume.restrict (Ioo (0 : ℝ) q ∩ Ioi (0 : ℝ)) := by
        rw [Measure.restrict_restrict measurableSet_Ioo]
    _ = ∫⁻ t in Ioc (0 : ℝ) q,
        ENNReal.ofReal u * ENNReal.ofReal t ^ (p - 2) := by
        have hset : Ioo (0 : ℝ) q ∩ Ioi (0 : ℝ) =ᵐ[volume] Ioc (0 : ℝ) q := by
          have hExact : Ioo (0 : ℝ) q ∩ Ioi (0 : ℝ) = Ioo (0 : ℝ) q := by
            ext t
            simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
            tauto
          rw [hExact]
          exact hIoo
        rw [Measure.restrict_congr_set hset]
    _ = ENNReal.ofReal u *
        (∫⁻ t in Ioc (0 : ℝ) q, ENNReal.ofReal t ^ (p - 2)) := by
        exact lintegral_const_mul (ENNReal.ofReal u)
          (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal)
    _ = ENNReal.ofReal (a ^ (1 - p) * u ^ p / (p - 1)) := by
        dsimp [q]
        exact interpolation_high_power_tail_scaled hp1 ha hu

theorem finiteLowWeightedLayercake_eq
    {p a : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ha : 0 < a)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∑ k ∈ s, if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) *
        ENNReal.ofReal t ^ (p - 3)) =
      ∑ k ∈ s, ENNReal.ofReal (a ^ (2 - p) * ‖f k‖ ^ p / (2 - p)) := by
  classical
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal t ^ (p - 3)) :=
    (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal)
  have hterms : ∀ k ∈ s, Measurable (fun t : ℝ =>
      (if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) *
        ENNReal.ofReal t ^ (p - 3)) := by
    intro k _
    have hE : MeasurableSet {t : ℝ | ‖f k‖ ≤ a * t} :=
      measurableSet_le measurable_const (measurable_const.mul measurable_id)
    have hI : Measurable ({t : ℝ | ‖f k‖ ≤ a * t}.indicator
        (fun _ : ℝ => ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)))) :=
      measurable_const.indicator hE
    have hEq : (fun t : ℝ =>
        (if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0)) =
        {t : ℝ | ‖f k‖ ≤ a * t}.indicator
          (fun _ : ℝ => ENNReal.ofReal (‖f k‖ ^ (2 : ℕ))) := by
      funext t
      simp [Set.indicator_apply]
    change Measurable ((fun t : ℝ =>
      if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) *
        (fun t => ENNReal.ofReal t ^ (p - 3)))
    rw [hEq]
    exact hI.mul hw
  rw [show (fun t : ℝ =>
      (∑ k ∈ s, if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) *
        ENNReal.ofReal t ^ (p - 3)) =
      fun t => ∑ k ∈ s,
        ((if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) *
          ENNReal.ofReal t ^ (p - 3)) by
    funext t
    rw [Finset.sum_mul]]
  rw [lintegral_finsetSum s hterms]
  apply Finset.sum_congr rfl
  intro k hk
  exact interpolation_low_coordinate_integral hp1 hp2 ha (norm_nonneg _)

theorem finiteHighWeightedLayercake_eq
    {p a : ℝ} (hp1 : 1 < p) (ha : 0 < a)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∑ k ∈ s, if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) *
        ENNReal.ofReal t ^ (p - 2)) =
      ∑ k ∈ s, ENNReal.ofReal (a ^ (1 - p) * ‖f k‖ ^ p / (p - 1)) := by
  classical
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal t ^ (p - 2)) :=
    (ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal)
  have hterms : ∀ k ∈ s, Measurable (fun t : ℝ =>
      (if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) *
        ENNReal.ofReal t ^ (p - 2)) := by
    intro k _
    have hE : MeasurableSet {t : ℝ | a * t < ‖f k‖} :=
      measurableSet_lt (measurable_const.mul measurable_id) measurable_const
    have hI : Measurable ({t : ℝ | a * t < ‖f k‖}.indicator
        (fun _ : ℝ => ENNReal.ofReal ‖f k‖)) :=
      measurable_const.indicator hE
    have hEq : (fun t : ℝ =>
        (if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0)) =
        {t : ℝ | a * t < ‖f k‖}.indicator
          (fun _ : ℝ => ENNReal.ofReal ‖f k‖) := by
      funext t
      simp [Set.indicator_apply]
    change Measurable ((fun t : ℝ =>
      if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) *
        (fun t => ENNReal.ofReal t ^ (p - 2)))
    rw [hEq]
    exact hI.mul hw
  rw [show (fun t : ℝ =>
      (∑ k ∈ s, if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) *
        ENNReal.ofReal t ^ (p - 2)) =
      fun t => ∑ k ∈ s,
        ((if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) *
          ENNReal.ofReal t ^ (p - 2)) by
    funext t
    rw [Finset.sum_mul]]
  rw [lintegral_finsetSum s hterms]
  apply Finset.sum_congr rfl
  intro k hk
  exact interpolation_high_coordinate_integral hp1 ha (norm_nonneg _)

/-- Integrating the exact finite low/high distribution bound produces the two
power-tail terms in the blueprint.  The hypothesis uses the approved strict
output superlevel set, the low cutoff `‖f k‖ ≤ a*t`, the strict high cutoff
`a*t < ‖f k‖`, and the exact constants `4` and `2`. -/
theorem finite_weighted_distribution_integral_le
    {p a : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ha : 0 < a)
    (C₁ C₂ : ℝ≥0∞) (s out : Finset ℤ) (f g : ℤ → ℂ)
    (hDist : ∀ t : ℝ, 0 < t →
      ((out.filter fun k => t < ‖g k‖).card : ℝ≥0∞) *
          ENNReal.ofReal (t ^ (p - 1)) ≤
        4 * C₂ *
            (∑ k ∈ s, if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) *
              ENNReal.ofReal t ^ (p - 3) +
          2 * C₁ *
            (∑ k ∈ s, if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) *
              ENNReal.ofReal t ^ (p - 2)) :
    (∫⁻ t in Ioi (0 : ℝ),
      ((out.filter fun k => t < ‖g k‖).card : ℝ≥0∞) *
        ENNReal.ofReal (t ^ (p - 1))) ≤
      4 * C₂ *
          (∑ k ∈ s, ENNReal.ofReal (a ^ (2 - p) * ‖f k‖ ^ p / (2 - p))) +
        2 * C₁ *
          (∑ k ∈ s, ENNReal.ofReal (a ^ (1 - p) * ‖f k‖ ^ p / (p - 1))) := by
  classical
  let lowWeight : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal t ^ (p - 3)
  let highWeight : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal t ^ (p - 2)
  let lowMoment : ℝ → ℝ≥0∞ := fun t =>
    ∑ k ∈ s, if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0
  let highMoment : ℝ → ℝ≥0∞ := fun t =>
    ∑ k ∈ s, if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0
  have hlowMoment : Measurable lowMoment := by
    change Measurable (fun t =>
      ∑ k ∈ s, if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0)
    exact Finset.measurable_sum s (by
      intro k hk
      exact Measurable.ite
        (measurableSet_le measurable_const (measurable_const.mul measurable_id))
        measurable_const measurable_const)
  have hhighMoment : Measurable highMoment := by
    change Measurable (fun t =>
      ∑ k ∈ s, if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0)
    exact Finset.measurable_sum s (by
      intro k hk
      exact Measurable.ite
        (measurableSet_lt (measurable_const.mul measurable_id) measurable_const)
        measurable_const measurable_const)
  have hlowWeight : Measurable lowWeight :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  have hhighWeight : Measurable highWeight :=
    ENNReal.continuous_rpow_const.measurable.comp measurable_id.ennreal_ofReal
  have hlowMeas : Measurable (fun t => 4 * C₂ * lowMoment t * lowWeight t) :=
    ((measurable_const.mul hlowMoment).mul hlowWeight)
  have hhighMeas : Measurable (fun t => 2 * C₁ * highMoment t * highWeight t) :=
    ((measurable_const.mul hhighMoment).mul hhighWeight)
  have hdist :
      (∫⁻ t in Ioi (0 : ℝ),
        ((out.filter fun k => t < ‖g k‖).card : ℝ≥0∞) *
          ENNReal.ofReal (t ^ (p - 1))) ≤
      (∫⁻ t in Ioi (0 : ℝ),
        4 * C₂ * lowMoment t * lowWeight t + 2 * C₁ * highMoment t * highWeight t) := by
    apply setLIntegral_mono_ae ((hlowMeas.add hhighMeas).aemeasurable)
    filter_upwards [] with t ht
    simpa [lowMoment, highMoment, lowWeight, highWeight] using
      hDist t (mem_Ioi.mp ht)
  calc
    (∫⁻ t in Ioi (0 : ℝ),
        ((out.filter fun k => t < ‖g k‖).card : ℝ≥0∞) *
          ENNReal.ofReal (t ^ (p - 1))) ≤
      ∫⁻ t in Ioi (0 : ℝ),
        4 * C₂ * lowMoment t * lowWeight t + 2 * C₁ * highMoment t * highWeight t := hdist
    _ = (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowMoment t * lowWeight t) +
        ∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highMoment t * highWeight t := by
      rw [lintegral_add_left hlowMeas]
    _ = 4 * C₂ * (∫⁻ t in Ioi (0 : ℝ), lowMoment t * lowWeight t) +
        2 * C₁ * (∫⁻ t in Ioi (0 : ℝ), highMoment t * highWeight t) := by
      congr 1
      · calc
          (∫⁻ t in Ioi (0 : ℝ), 4 * C₂ * lowMoment t * lowWeight t) =
              ∫⁻ t in Ioi (0 : ℝ), (4 * C₂) * (lowMoment t * lowWeight t) := by
                apply lintegral_congr
                intro t
                ac_rfl
          _ = (4 * C₂) * (∫⁻ t in Ioi (0 : ℝ), lowMoment t * lowWeight t) :=
            lintegral_const_mul (4 * C₂) (hlowMoment.mul hlowWeight)
      · calc
          (∫⁻ t in Ioi (0 : ℝ), 2 * C₁ * highMoment t * highWeight t) =
              ∫⁻ t in Ioi (0 : ℝ), (2 * C₁) * (highMoment t * highWeight t) := by
                apply lintegral_congr
                intro t
                ac_rfl
          _ = (2 * C₁) * (∫⁻ t in Ioi (0 : ℝ), highMoment t * highWeight t) :=
            lintegral_const_mul (2 * C₁) (hhighMoment.mul hhighWeight)
    _ = 4 * C₂ *
          (∑ k ∈ s, ENNReal.ofReal (a ^ (2 - p) * ‖f k‖ ^ p / (2 - p))) +
        2 * C₁ *
          (∑ k ∈ s, ENNReal.ofReal (a ^ (1 - p) * ‖f k‖ ^ p / (p - 1))) := by
      rw [show (fun t : ℝ => lowMoment t * lowWeight t) =
          fun t => (∑ k ∈ s,
            if ‖f k‖ ≤ a * t then ENNReal.ofReal (‖f k‖ ^ (2 : ℕ)) else 0) *
            ENNReal.ofReal t ^ (p - 3) by rfl]
      rw [show (fun t : ℝ => highMoment t * highWeight t) =
          fun t => (∑ k ∈ s,
            if a * t < ‖f k‖ then ENNReal.ofReal ‖f k‖ else 0) *
            ENNReal.ofReal t ^ (p - 2) by rfl]
      rw [finiteLowWeightedLayercake_eq hp1 hp2 ha s f,
        finiteHighWeightedLayercake_eq hp1 ha s f]

end

end FractionalPrimes
