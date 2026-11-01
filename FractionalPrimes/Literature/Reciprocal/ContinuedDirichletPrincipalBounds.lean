module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletData
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

open MeasureTheory Set Complex

namespace FractionalPrimes.Literature.Reciprocal

private theorem principal_rpow_integral {σ : ℝ} (hσ : 0 < σ) :
    (∫ t : ℝ in Ioi (1 : ℝ), t ^ (-σ - 1)) = 1 / σ := by
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
  simp [Real.one_rpow, div_eq_mul_inv]

private theorem continuedDirichletI_norm_le {s : ℂ} (hs : 0 < s.re) :
    ‖continuedDirichletI s hs‖ ≤ 1 / s.re := by
  let f : ℝ → ℂ := fun t => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
  have hpow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi (1 : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt
    · rw [Complex.neg_re, Complex.add_re, Complex.one_re]
      linarith
    · exact zero_lt_one
  have hfrac_meas : AEStronglyMeasurable (fun t : ℝ => ((Int.fract t : ℝ) : ℂ))
      (volume.restrict (Ioi (1 : ℝ))) :=
    (Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable
  have hfrac_bound : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  have hf_int : IntegrableOn f (Ioi (1 : ℝ)) := by
    dsimp [f]
    exact hpow.bdd_mul hfrac_meas hfrac_bound
  have hexp : (-(s + 1)).re = -s.re - 1 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    ring
  have hnorm_ae : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖f t‖ ≤ t ^ (-s.re - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := zero_lt_one.trans (mem_Ioi.mp ht)
    have hfrac : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    calc
      ‖f t‖ = ‖((Int.fract t : ℝ) : ℂ)‖ * t ^ (-s.re - 1) := by
        dsimp [f]
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, hexp]
      _ ≤ t ^ (-s.re - 1) := by
        exact mul_le_of_le_one_left (Real.rpow_nonneg htpos.le _) hfrac
  have hmajor_int : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi (1 : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt (by linarith [hs]) zero_lt_one
  have hmajor_value :
      (∫ t : ℝ in Ioi (1 : ℝ), t ^ (-s.re - 1)) = 1 / s.re :=
    principal_rpow_integral hs
  calc
    ‖continuedDirichletI s hs‖ = ‖∫ t : ℝ in Ioi (1 : ℝ), f t‖ := by
      rw [continuedDirichletI_eq_integral]
    _ ≤ ∫ t : ℝ in Ioi (1 : ℝ), ‖f t‖ := norm_integral_le_integral_norm f
    _ ≤ ∫ t : ℝ in Ioi (1 : ℝ), t ^ (-s.re - 1) := integral_mono_ae hf_int.norm hmajor_int hnorm_ae
    _ = 1 / s.re := hmajor_value

private theorem norm_div_s_add_one_le_one {s : ℂ} (hs : 0 < s.re) :
    ‖s / (s + 1)‖ ≤ 1 := by
  rw [norm_div]
  have hden0 : s + 1 ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith
  have hden : ‖s‖ ≤ ‖s + 1‖ := by
    have hs_norm : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have hplus : ‖s + 1‖ ^ 2 = (s.re + 1) ^ 2 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        add_zero, zero_add]
      ring
    have hsq : ‖s + 1‖ ^ 2 - ‖s‖ ^ 2 = 2 * s.re + 1 := by
      rw [hplus, hs_norm]
      ring
    nlinarith [norm_nonneg s, norm_nonneg (s + 1), hs]
  exact (div_le_one (norm_pos_iff.mpr hden0)).2 hden

private theorem norm_s_sub_one_div_s_add_one_le_one {s : ℂ} (hs : 0 < s.re) :
    ‖(s - 1) / (s + 1)‖ ≤ 1 := by
  rw [norm_div]
  have hden0 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hden : ‖s - 1‖ ≤ ‖s + 1‖ := by
    have hplus : ‖s + 1‖ ^ 2 = (s.re + 1) ^ 2 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        add_zero, zero_add]
      ring
    have hminus : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
        sub_zero, zero_sub]
      ring
    have hsq : ‖s + 1‖ ^ 2 - ‖s - 1‖ ^ 2 = 4 * s.re := by
      rw [hplus, hminus]
      ring
    nlinarith [norm_nonneg (s + 1), norm_nonneg (s - 1), hs]
  have hnorm : 0 < ‖s + 1‖ := norm_pos_iff.mpr hden0
  exact (div_le_one hnorm).2 hden

/-- The exact fractional-part Mellin bound in blueprint `lrc:continued-lseries`.
It is unconditional on the half-plane `Re(s)>0`. -/
theorem norm_continuedDirichletI_le_of_pos_re {s : ℂ} (hs : 0 < s.re) :
    ‖continuedDirichletI s hs‖ ≤ 1 / s.re :=
  continuedDirichletI_norm_le hs

/-- The exact nonsingular principal regular-part bound in blueprint
`lrc:continued-lseries`. -/
theorem norm_continuedDirichletH0_le_of_pos_re {s : ℂ} (hs : 0 < s.re) :
    ‖continuedDirichletH0 s hs‖ ≤ 1 + ‖s‖ / s.re := by
  have hI := continuedDirichletI_norm_le hs
  have hrat1 := norm_div_s_add_one_le_one hs
  have hrat2 := norm_s_sub_one_div_s_add_one_le_one hs
  have hrat2' : ‖s * (s - 1) / (s + 1)‖ ≤ ‖s‖ := by
    rw [show s * (s - 1) / (s + 1) = s * ((s - 1) / (s + 1)) by ring]
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hrat2
  calc
    ‖continuedDirichletH0 s hs‖ ≤ ‖s / (s + 1)‖ +
        ‖(s * (s - 1) / (s + 1)) * continuedDirichletI s hs‖ := by
          unfold continuedDirichletH0
          exact norm_sub_le _ _
    _ ≤ 1 + ‖s‖ * (1 / s.re) := by
          rw [norm_mul]
          exact add_le_add hrat1 (mul_le_mul hrat2' hI (norm_nonneg _) (by positivity))
    _ = 1 + ‖s‖ / s.re := by ring

#print axioms norm_continuedDirichletI_le_of_pos_re
#print axioms norm_continuedDirichletH0_le_of_pos_re

end FractionalPrimes.Literature.Reciprocal
