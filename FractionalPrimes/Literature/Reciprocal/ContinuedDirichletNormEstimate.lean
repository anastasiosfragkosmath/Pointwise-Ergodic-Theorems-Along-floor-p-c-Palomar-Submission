module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletIntegrability
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

open MeasureTheory Set Complex

namespace FractionalPrimes.Literature.Reciprocal

private theorem modulus_mul_integral_rpow {q : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    (∫ t : ℝ in Ioi (1 : ℝ), (q : ℝ) * t ^ (-σ - 1)) = (q : ℝ) / σ := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
  simp [Real.one_rpow, div_eq_mul_inv]

/-- The nonprincipal continued-L function satisfies the exact bound from
`lrc:continued-lseries` throughout `Re(s)>0`. -/
theorem norm_nonprincipalContinuedDirichletL_le_of_pos_re
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q)
    (hχ : χ ≠ FractionalPrimes.Literature.Twisted.principalCharacter q)
    (s : ℂ) (hs : 0 < s.re) :
    ‖nonprincipalContinuedDirichletL χ hχ s hs‖ ≤
      (q : ℝ) * ‖s‖ / s.re := by
  let f : ℝ → ℂ := fun t =>
    continuedDirichletPartialSumFormula χ t * (t : ℂ) ^ (-(s + 1))
  have hpartial : ∀ t ∈ Ioi (1 : ℝ),
      ‖continuedDirichletPartialSumFormula χ t‖ ≤ (q : ℝ) := by
    intro t ht
    have ht1 : 1 ≤ t := (mem_Ioi.mp ht).le
    calc
      ‖continuedDirichletPartialSumFormula χ t‖ =
          ‖continuedDirichletPartialSum χ t ht1‖ := by
            rw [← continuedDirichletPartialSum_eq_formula χ t ht1]
      _ ≤ (q : ℝ) := continuedDirichletPartialSum_norm_le_modulus χ hχ t ht1
  have hf_int : IntegrableOn f (Ioi (1 : ℝ)) := by
    exact integrableOn_nonprincipalContinuedDirichletIntegrand_of_bound
      χ s hs hpartial
  have hexp : (-(s + 1)).re = -s.re - 1 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    ring
  have hnorm_ae : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖f t‖ ≤ (q : ℝ) * t ^ (-s.re - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := zero_lt_one.trans (mem_Ioi.mp ht)
    have hpart : ‖continuedDirichletPartialSumFormula χ t‖ ≤ (q : ℝ) :=
      hpartial t ht
    calc
      ‖f t‖ = ‖continuedDirichletPartialSumFormula χ t‖ * t ^ (-s.re - 1) := by
        dsimp [f]
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, hexp]
      _ ≤ (q : ℝ) * t ^ (-s.re - 1) :=
        mul_le_mul_of_nonneg_right hpart (Real.rpow_nonneg htpos.le _)
  have hmajor_int : IntegrableOn
      (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (1 : ℝ)) := by
    apply (integrableOn_Ioi_rpow_of_lt (by linarith [hs]) zero_lt_one).const_mul
  have hmajor_value :
      (∫ t : ℝ in Ioi (1 : ℝ), (q : ℝ) * t ^ (-s.re - 1)) =
        (q : ℝ) / s.re := by
    exact modulus_mul_integral_rpow hs
  have hnorm_integral :
      (∫ t : ℝ in Ioi (1 : ℝ), ‖f t‖) ≤ (q : ℝ) / s.re := by
    calc
      (∫ t : ℝ in Ioi (1 : ℝ), ‖f t‖) ≤
          ∫ t : ℝ in Ioi (1 : ℝ), (q : ℝ) * t ^ (-s.re - 1) :=
        integral_mono_ae hf_int.norm hmajor_int hnorm_ae
      _ = (q : ℝ) / s.re := hmajor_value
  calc
    ‖nonprincipalContinuedDirichletL χ hχ s hs‖ =
        ‖s‖ * ‖∫ t : ℝ in Ioi (1 : ℝ), f t‖ := by
          rw [nonprincipalContinuedDirichletL, norm_mul]
    _ ≤ ‖s‖ * (∫ t : ℝ in Ioi (1 : ℝ), ‖f t‖) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm f) (norm_nonneg _)
    _ ≤ ‖s‖ * ((q : ℝ) / s.re) :=
        mul_le_mul_of_nonneg_left hnorm_integral (norm_nonneg _)
    _ = (q : ℝ) * ‖s‖ / s.re := by ring

#print axioms norm_nonprincipalContinuedDirichletL_le_of_pos_re

end FractionalPrimes.Literature.Reciprocal
