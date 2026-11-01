module

public import Mathlib
public import FractionalPrimes.Literature.Reciprocal.ZetaFloorSumLemma
public import FractionalPrimes.Literature.Reciprocal.ZetaFloorCpowLemma

@[expose] public section

open MeasureTheory Set Filter Complex
open scoped LSeries.notation

namespace FractionalPrimes.Literature.Reciprocal

/-- The fractional part kernel cut off to the range used in the blueprint's
Mellin integral. -/
noncomputable def zetaFractionalPartKernel (t : ℝ) : ℂ :=
  if (1 : ℝ) < t then ((Int.fract t : ℝ) : ℂ) else 0

/-- The Mellin form of the blueprint's fractional-part correction integral. -/
noncomputable def zetaFloorCorrectionIntegral (s : ℂ) : ℂ :=
  mellin zetaFractionalPartKernel (-s)

theorem zetaFloorCorrectionIntegral_eq_setIntegral (s : ℂ) :
    zetaFloorCorrectionIntegral s =
      ∫ t : ℝ in (Ioi (1 : ℝ) : Set ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [zetaFloorCorrectionIntegral, mellin]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num)) ?_]
  · change (∫ t : ℝ in (Ioi (1 : ℝ) : Set ℝ),
      (t : ℂ) ^ (-s - 1) • zetaFractionalPartKernel t) = _
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (1 : ℝ) < t at ht
    have he : -s - 1 = -(s + 1) := by ring
    simp only [smul_eq_mul, zetaFractionalPartKernel, if_pos ht]
    rw [he, mul_comm]
  · intro t ht
    rcases ht with ⟨_, ht1⟩
    have hnot : ¬ (1 : ℝ) < t := by simpa using ht1
    simp [zetaFractionalPartKernel, hnot]

private theorem zetaFractionalPartKernel_norm_le_one (t : ℝ) :
    ‖zetaFractionalPartKernel t‖ ≤ 1 := by
  by_cases ht : 1 < t
  · simp only [zetaFractionalPartKernel, ht, ↓reduceIte]
    rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  · simp [zetaFractionalPartKernel, ht]

private theorem zetaFractionalPartKernel_memLp_top :
    MemLp zetaFractionalPartKernel ⊤ := by
  have hm : Measurable zetaFractionalPartKernel := by
    unfold zetaFractionalPartKernel
    exact Measurable.ite measurableSet_Ioi
      (Complex.measurable_ofReal.comp measurable_fract) measurable_const
  exact memLp_top_of_bound hm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall zetaFractionalPartKernel_norm_le_one)

private theorem zetaFractionalPartKernel_isBigO_atTop :
    zetaFractionalPartKernel =O[atTop] (fun t : ℝ => t ^ (-0 : ℝ)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨1, Filter.Eventually.of_forall fun t => ?_⟩
  simpa using zetaFractionalPartKernel_norm_le_one t

private theorem zetaFractionalPartKernel_isBigO_nhdsGT_zero (b : ℝ) :
    zetaFractionalPartKernel =O[nhdsWithin (0 : ℝ) (Ioi 0)] (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [
    (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono
      nhdsWithin_le_nhds] with t ht
  simp [zetaFractionalPartKernel, not_lt_of_ge ht.le]

theorem differentiableAt_zetaFloorCorrectionIntegral {s : ℂ}
    (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaFloorCorrectionIntegral s := by
  have hloc : LocallyIntegrableOn zetaFractionalPartKernel (Ioi 0) :=
    (zetaFractionalPartKernel_memLp_top.locallyIntegrable le_top).locallyIntegrableOn _
  have hd : DifferentiableAt ℂ (mellin zetaFractionalPartKernel) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow hloc
      zetaFractionalPartKernel_isBigO_atTop ?_
      (zetaFractionalPartKernel_isBigO_nhdsGT_zero (-s.re - 1)) ?_
    · simp only [Complex.neg_re]
      linarith
    · simp only [Complex.neg_re]
      linarith
  change DifferentiableAt ℂ (fun z => mellin zetaFractionalPartKernel (-z)) s
  exact hd.comp s differentiableAt_id.neg

noncomputable def zetaFloorRegularPart (s : ℂ) : ℂ :=
  1 - s * zetaFloorCorrectionIntegral s

theorem differentiableAt_zetaFloorRegularPart {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ zetaFloorRegularPart s := by
  unfold zetaFloorRegularPart
  exact (differentiableAt_id.mul (differentiableAt_zetaFloorCorrectionIntegral hs)).const_sub 1

private theorem zetaFloorFracKernel_integrableOn {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
      (Ioi (1 : ℝ)) := by
  have hpow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt
    · rw [Complex.sub_re, Complex.neg_re, Complex.one_re]
      linarith
    · exact zero_lt_one
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ((Int.fract t : ℝ) : ℂ))
      (volume.restrict (Ioi (1 : ℝ))) :=
    (Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  exact hpow.bdd_mul hmeas hbound

theorem zetaFloorRegularPart_eq_riemannZeta₀_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) : zetaFloorRegularPart s = riemannZeta₀ s := by
  have hsum : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    refine Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simp [Finset.sum_const]
  have hsum_conv : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) s := by
    change LSeriesSummable 1 s
    exact LSeriesSummable_one_iff.mpr hs
  have hL := LSeries_eq_mul_integral (fun _ : ℕ => (1 : ℂ)) (show 0 ≤ (1 : ℝ) by norm_num)
    hs hsum_conv hsum
  have hLz : LSeries (fun _ : ℕ => (1 : ℂ)) s = riemannZeta s := by
    change LSeries 1 s = riemannZeta s
    exact LSeries_one_eq_riemannZeta hs
  have hL' : LSeries (fun _ : ℕ => (1 : ℂ)) s = s *
      ∫ t in Ioi (1 : ℝ), (Nat.floor t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [hL]
    congr 2
    funext t
    rw [sum_one_Icc_eq_natCast]
  have hfloor_int : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi (1 : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt
    · rw [Complex.neg_re]
      linarith
    · exact zero_lt_one
  have hfloor_eq : EqOn
      (fun t : ℝ => (Nat.floor t : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (fun t : ℝ => (t : ℂ) ^ (-s) - ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
      (Ioi (1 : ℝ)) := by
    intro t ht
    change 1 < t at ht
    exact natFloor_cpow_split ht
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hfrac_int := zetaFloorFracKernel_integrableOn hs0
  have hfloor_int' : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (-s) - ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
      (Ioi (1 : ℝ)) := by
    exact hfloor_int.sub hfrac_int
  have hfloorIntVal :
      (∫ t in Ioi (1 : ℝ), (Nat.floor t : ℂ) * (t : ℂ) ^ (-(s + 1)))
        = (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s))
          - ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
    calc
      _ = ∫ t in Ioi (1 : ℝ),
          (t : ℂ) ^ (-s) - ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
            exact setIntegral_congr_fun measurableSet_Ioi hfloor_eq
      _ = _ := integral_sub hfloor_int hfrac_int
  have hexp : (-s).re < -1 := by
    rw [Complex.neg_re]
    linarith
  have hpowval : (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s)) = (s - 1)⁻¹ := by
    rw [integral_Ioi_cpow_of_lt hexp zero_lt_one, ofReal_one, one_cpow,
      show -(s : ℂ) + 1 = -(s - 1) by ring, neg_div_neg_eq]
    simp [div_eq_mul_inv]
  have hI : zetaFloorCorrectionIntegral s =
      ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
    calc
      zetaFloorCorrectionIntegral s =
          ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) :=
        zetaFloorCorrectionIntegral_eq_setIntegral s
      _ = ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        congr 2
        ring
  have hz : riemannZeta s = s * ((s - 1)⁻¹ - zetaFloorCorrectionIntegral s) := by
    calc
      riemannZeta s = LSeries (fun _ : ℕ => (1 : ℂ)) s := hLz.symm
      _ = s * ∫ t in Ioi (1 : ℝ), (Nat.floor t : ℂ) * (t : ℂ) ^ (-(s + 1)) := hL'
      _ = s * ((s - 1)⁻¹ - zetaFloorCorrectionIntegral s) := by
        rw [hfloorIntVal, hpowval, hI]
  have hsne : s ≠ (1 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hden : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
  have hregular : 1 - s * zetaFloorCorrectionIntegral s = riemannZeta s - (s - 1)⁻¹ := by
    rw [hz]
    field_simp [hden]
    <;> ring
  simpa [zetaFloorRegularPart, riemannZeta₀, hsne] using hregular

end FractionalPrimes.Literature.Reciprocal
