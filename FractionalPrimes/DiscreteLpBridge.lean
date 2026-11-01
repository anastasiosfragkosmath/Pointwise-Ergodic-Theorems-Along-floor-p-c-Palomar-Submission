module

public import FractionalPrimes.Operators
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Counting-measure bridge for discrete `ℓ²`

The Fourier construction in this project currently uses Mathlib's sequence
space `lp`, while the Young inequality uses measure-theoretic `Lp` for
counting measure.  This file supplies the explicit bridge needed to combine
those two faithful models.
-/

@[expose] public section

namespace FractionalPrimes

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

/-- A counting-measure `L²` representative is square summable as a discrete
sequence. -/
theorem meml2_of_memLp_count
    (f : Lp ℂ 2 (Measure.count : Measure ℤ)) :
    Memℓp (f : ℤ → ℂ) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  have hfinite : ∑' n : ℤ, ‖f n‖ₑ ^ (2 : ℝ≥0∞).toReal < ∞ := by
    simpa only [lintegral_count] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2 : ℝ≥0∞)) (f := (f : ℤ → ℂ)) (μ := Measure.count)
        (by norm_num) (by norm_num) (Lp.memLp f)
  have hsum := ENNReal.summable_toReal hfinite.ne
  simpa using hsum

/-- A square-summable discrete sequence is an `L²` function for counting
measure. -/
theorem memLp_count_of_meml2
    (f : lp (fun _ : ℤ => ℂ) 2) :
    MemLp (f : ℤ → ℂ) 2 (Measure.count : Measure ℤ) := by
  rw [memLp_two_iff_integrable_sq_norm
    (measurable_of_countable (f : ℤ → ℂ)).aestronglyMeasurable]
  rw [integrable_count_iff]
  have h := (lp.memℓp f).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa using h

/-- The coordinatewise identification from counting-measure `L²` to the
sequence model, as a complex-linear map. -/
noncomputable def countLpToLp :
    Lp ℂ 2 (Measure.count : Measure ℤ) →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun f := ⟨(f : ℤ → ℂ), meml2_of_memLp_count f⟩
  map_add' f g := by
    apply lp.ext
    funext n
    exact ae_count_int_iff_forall.mp (Lp.coeFn_add f g) n
  map_smul' c f := by
    apply lp.ext
    funext n
    exact ae_count_int_iff_forall.mp (Lp.coeFn_smul c f) n

/-- The coordinatewise bridge preserves the `L²` inner product. -/
theorem countLpToLp_inner (f g : Lp ℂ 2 (Measure.count : Measure ℤ)) :
    inner ℂ (countLpToLp f) (countLpToLp g) = inner ℂ f g := by
  rw [lp.inner_eq_tsum, MeasureTheory.L2.inner_def]
  rw [integral_countable (MeasureTheory.L2.integrable_inner f g)]
  simp only [MeasureTheory.count_real_singleton, one_smul]
  apply tsum_congr
  intro n
  rfl

/-- The counting-measure-to-sequence bridge is an isometry. -/
noncomputable def countLpToLpIsometry :
    Lp ℂ 2 (Measure.count : Measure ℤ) →ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  countLpToLp.isometryOfInner countLpToLp_inner

/-- Exact equality of extended norms across the first bridge direction. -/
theorem enorm_countLpToLp (f : Lp ℂ 2 (Measure.count : Measure ℤ)) :
    ‖countLpToLp f‖ₑ = ‖f‖ₑ :=
  countLpToLpIsometry.enorm_map f

/-- The coordinatewise identification from the sequence model to
counting-measure `L²`, as a complex-linear map. -/
noncomputable def lpToCountLp :
    lp (fun _ : ℤ => ℂ) 2 →ₗ[ℂ] Lp ℂ 2 (Measure.count : Measure ℤ) where
  toFun f := (memLp_count_of_meml2 f).toLp (f : ℤ → ℂ)
  map_add' f g := by
    exact (memLp_count_of_meml2 f).toLp_add (memLp_count_of_meml2 g)
  map_smul' c f := by
    exact (memLp_count_of_meml2 f).toLp_const_smul c

/-- The reverse coordinatewise bridge preserves the `L²` inner product. -/
theorem lpToCountLp_inner (f g : lp (fun _ : ℤ => ℂ) 2) :
    inner ℂ (lpToCountLp f) (lpToCountLp g) = inner ℂ f g := by
  rw [MeasureTheory.L2.inner_def, lp.inner_eq_tsum]
  rw [integral_countable
    (MeasureTheory.L2.integrable_inner (lpToCountLp f) (lpToCountLp g))]
  simp only [MeasureTheory.count_real_singleton, one_smul]
  apply tsum_congr
  intro n
  have hf : (lpToCountLp f : ℤ → ℂ) n = f n := by
    exact ae_count_int_iff_forall.mp
      (MemLp.coeFn_toLp (memLp_count_of_meml2 f)) n
  have hg : (lpToCountLp g : ℤ → ℂ) n = g n := by
    exact ae_count_int_iff_forall.mp
      (MemLp.coeFn_toLp (memLp_count_of_meml2 g)) n
  rw [hf, hg]

/-- The sequence-to-counting-measure bridge is an isometry. -/
noncomputable def lpToCountLpIsometry :
    lp (fun _ : ℤ => ℂ) 2 →ₗᵢ[ℂ] Lp ℂ 2 (Measure.count : Measure ℤ) :=
  lpToCountLp.isometryOfInner lpToCountLp_inner

/-- Exact equality of extended norms across the reverse bridge direction. -/
theorem enorm_lpToCountLp (f : lp (fun _ : ℤ => ℂ) 2) :
    ‖lpToCountLp f‖ₑ = ‖f‖ₑ :=
  lpToCountLpIsometry.enorm_map f

/-- The reverse bridge has exactly the original pointwise sequence
representative. -/
theorem lpToCountLp_apply (f : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    (lpToCountLp f : ℤ → ℂ) n = f n := by
  exact ae_count_int_iff_forall.mp
    (MemLp.coeFn_toLp (memLp_count_of_meml2 f)) n

/-- The forward bridge is definitionally coordinatewise. -/
theorem countLpToLp_apply (f : Lp ℂ 2 (Measure.count : Measure ℤ)) (n : ℤ) :
    countLpToLp f n = f n := rfl

/-- The two bridges are inverse on the sequence model. -/
theorem countLpToLp_lpToCountLp (f : lp (fun _ : ℤ => ℂ) 2) :
    countLpToLp (lpToCountLp f) = f := by
  apply lp.ext
  funext n
  rw [countLpToLp_apply, lpToCountLp_apply]

/-- The two bridges are inverse on the counting-measure `L²` model. -/
theorem lpToCountLp_countLpToLp
    (f : Lp ℂ 2 (Measure.count : Measure ℤ)) :
    lpToCountLp (countLpToLp f) = f := by
  apply Lp.ext
  apply ae_count_int_iff_forall.mpr
  intro n
  rw [lpToCountLp_apply, countLpToLp_apply]

end

end FractionalPrimes
