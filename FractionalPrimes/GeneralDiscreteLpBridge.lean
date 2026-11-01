module

public import FractionalPrimes.Operators
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Counting-measure and sequence `ℓᵖ` bridge for finite exponents

This extends the project’s `p = 2` identification to finite `p ≥ 1`.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {p : ℝ≥0∞}

/-- A counting-measure `Lᵖ` function with finite positive exponent is in the
corresponding sequence `lp` space. -/
theorem memlp_seq_of_memLp_count_finite
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    Memℓp (f : ℤ → ℂ) p := by
  rw [memℓp_gen_iff (ENNReal.toReal_pos hp0 hpTop)]
  have hfinite : ∑' k : ℤ, ‖f k‖ₑ ^ p.toReal < ∞ := by
    simpa only [lintegral_count] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpTop (Lp.memLp f)
  have hsum := ENNReal.summable_toReal hfinite.ne
  refine hsum.congr ?_
  intro k
  rw [← ENNReal.toReal_rpow, toReal_enorm]

/-- A sequence `lp` vector with finite positive exponent defines a
counting-measure `Lᵖ` function. -/
theorem memLp_count_of_memlp_seq_finite
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (f : lp (fun _ : ℤ => ℂ) p) :
    MemLp (f : ℤ → ℂ) p (Measure.count : Measure ℤ) := by
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpTop
    (measurable_of_countable (f : ℤ → ℂ)).aestronglyMeasurable).2
  rw [lintegral_count]
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hsum : Summable (fun k : ℤ => ‖f k‖ ^ p.toReal) :=
    (lp.memℓp f).summable hp
  calc
    ∑' k : ℤ, ‖f k‖ₑ ^ p.toReal =
        ∑' k : ℤ, ENNReal.ofReal (‖f k‖ ^ p.toReal) := by
          apply tsum_congr
          intro k
          have hnorm : ENNReal.ofReal ‖(f : ℤ → ℂ) k‖ =
              ‖(f : ℤ → ℂ) k‖ₑ := by simp
          calc
            _ = ENNReal.ofReal (‖(f : ℤ → ℂ) k‖) ^ p.toReal := by rw [← hnorm]
            _ = _ := ENNReal.ofReal_rpow_of_nonneg
              (norm_nonneg _) hp.le
    _ = ENNReal.ofReal (∑' k : ℤ, ‖f k‖ ^ p.toReal) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun k => Real.rpow_nonneg (norm_nonneg (f k)) _) hsum).symm
    _ < ∞ := ENNReal.ofReal_lt_top

/-- Identify counting-measure `Lᵖ` functions with sequence `lp`, for finite
exponents. -/
noncomputable def countLpToGeneralLp
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) [Fact (1 ≤ p)] :
    Lp ℂ p (Measure.count : Measure ℤ) →ₗ[ℂ] lp (fun _ : ℤ => ℂ) p where
  toFun f := ⟨(f : ℤ → ℂ), memlp_seq_of_memLp_count_finite hp0 hpTop f⟩
  map_add' f g := by
    apply lp.ext
    funext k
    exact ae_count_int_iff_forall.mp (Lp.coeFn_add f g) k
  map_smul' c f := by
    apply lp.ext
    funext k
    exact ae_count_int_iff_forall.mp (Lp.coeFn_smul c f) k

/-- Identify sequence `lp` with counting-measure `Lᵖ`, for finite exponents. -/
noncomputable def generalLpToCountLp
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) [Fact (1 ≤ p)] :
    lp (fun _ : ℤ => ℂ) p →ₗ[ℂ] Lp ℂ p (Measure.count : Measure ℤ) where
  toFun f := (memLp_count_of_memlp_seq_finite hp0 hpTop f).toLp (f : ℤ → ℂ)
  map_add' f g := by
    exact (memLp_count_of_memlp_seq_finite hp0 hpTop f).toLp_add
      (memLp_count_of_memlp_seq_finite hp0 hpTop g)
  map_smul' c f := by
    exact (memLp_count_of_memlp_seq_finite hp0 hpTop f).toLp_const_smul c

/-- The forward bridge keeps the pointwise representative. -/
theorem countLpToGeneralLp_apply
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) [Fact (1 ≤ p)]
    (f : Lp ℂ p (Measure.count : Measure ℤ)) (k : ℤ) :
    countLpToGeneralLp hp0 hpTop f k = f k := rfl

/-- The reverse bridge keeps the pointwise representative at every integer. -/
theorem generalLpToCountLp_apply
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) [Fact (1 ≤ p)]
    (f : lp (fun _ : ℤ => ℂ) p) (k : ℤ) :
    (generalLpToCountLp hp0 hpTop f : ℤ → ℂ) k = f k := by
  change ((memLp_count_of_memlp_seq_finite hp0 hpTop f).toLp
    (f : ℤ → ℂ) : ℤ → ℂ) k = f k
  exact ae_count_int_iff_forall.mp
    (MemLp.coeFn_toLp (memLp_count_of_memlp_seq_finite hp0 hpTop f)) k

/-- The two finite-exponent bridges are inverse on sequence `lp`. -/
theorem countLpToGeneralLp_generalLpToCountLp
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) [Fact (1 ≤ p)]
    (f : lp (fun _ : ℤ => ℂ) p) :
    countLpToGeneralLp hp0 hpTop (generalLpToCountLp hp0 hpTop f) = f := by
  apply lp.ext
  funext k
  rw [countLpToGeneralLp_apply, generalLpToCountLp_apply]

/-- The two finite-exponent bridges are inverse on counting-measure `Lᵖ`. -/
theorem generalLpToCountLp_countLpToGeneralLp
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) [Fact (1 ≤ p)]
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    generalLpToCountLp hp0 hpTop (countLpToGeneralLp hp0 hpTop f) = f := by
  apply Lp.ext
  apply ae_count_int_iff_forall.mpr
  intro k
  rw [generalLpToCountLp_apply, countLpToGeneralLp_apply]

/-- The sequence norm equals the `Lp` norm after the counting-measure bridge. -/
theorem countLpToGeneralLp_norm
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) [Fact (1 ≤ p)]
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    ‖countLpToGeneralLp hp0 hpTop f‖ = ‖f‖ := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hsum : Summable (fun k : ℤ => ‖f k‖ ^ p.toReal) := by
    exact (memℓp_gen_iff hp).1
      (memlp_seq_of_memLp_count_finite hp0 hpTop f)
  have hsumENN : (∑' k : ℤ, ‖f k‖ₑ ^ p.toReal) =
      ENNReal.ofReal (∑' k : ℤ, ‖f k‖ ^ p.toReal) := by
    calc
      ∑' k : ℤ, ‖f k‖ₑ ^ p.toReal =
          ∑' k : ℤ, ENNReal.ofReal (‖f k‖ ^ p.toReal) := by
            apply tsum_congr
            intro k
            have hnorm : ENNReal.ofReal ‖(f : ℤ → ℂ) k‖ =
                ‖(f : ℤ → ℂ) k‖ₑ := by simp
            calc
              _ = ENNReal.ofReal (‖(f : ℤ → ℂ) k‖) ^ p.toReal := by rw [← hnorm]
              _ = _ := ENNReal.ofReal_rpow_of_nonneg
                (norm_nonneg _) hp.le
      _ = ENNReal.ofReal (∑' k : ℤ, ‖f k‖ ^ p.toReal) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun k => Real.rpow_nonneg (norm_nonneg (f k)) _) hsum).symm
  rw [Lp.norm_def,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop
      (measurable_of_countable (f : ℤ → ℂ)).aestronglyMeasurable,
    lintegral_count, hsumENN, ← ENNReal.toReal_rpow]
  rw [lp.norm_eq_tsum_rpow hp (countLpToGeneralLp hp0 hpTop f)]
  rw [ENNReal.toReal_ofReal]
  · congr 1
  · exact tsum_nonneg (fun k : ℤ => Real.rpow_nonneg (norm_nonneg (f k)) _)

/-- The reverse bridge also preserves the finite-exponent norm. -/
theorem generalLpToCountLp_norm
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) [Fact (1 ≤ p)]
    (f : lp (fun _ : ℤ => ℂ) p) :
    ‖generalLpToCountLp hp0 hpTop f‖ = ‖f‖ := by
  rw [← countLpToGeneralLp_norm hp0 hpTop
    (generalLpToCountLp hp0 hpTop f)]
  rw [countLpToGeneralLp_generalLpToCountLp hp0 hpTop]

/-- The `eLpNorm` is the extended norm of the corresponding sequence vector. -/
theorem countLpToGeneralLp_eLpNorm
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) [Fact (1 ≤ p)]
    (f : Lp ℂ p (Measure.count : Measure ℤ)) :
    eLpNorm (f : ℤ → ℂ) p Measure.count =
      ‖countLpToGeneralLp hp0 hpTop f‖ₑ := by
  rw [← Lp.enorm_def]
  calc
    ‖f‖ₑ = ENNReal.ofReal ‖f‖ := by simp
    _ = ENNReal.ofReal ‖countLpToGeneralLp hp0 hpTop f‖ := by
      rw [countLpToGeneralLp_norm]
    _ = ‖countLpToGeneralLp hp0 hpTop f‖ₑ := by simp

end

end FractionalPrimes
