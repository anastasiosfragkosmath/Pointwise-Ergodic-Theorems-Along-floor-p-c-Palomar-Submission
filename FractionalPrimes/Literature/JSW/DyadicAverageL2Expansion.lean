module

public import FractionalPrimes.Literature.JSW.DyadicAverageAlgebra
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Finite orthogonal expansion for dyadic differences

This module records the finite Pythagorean identity that underlies the
`L²` square-function part of `lj:dyadic-properties`.
-/

@[expose] public section

open MeasureTheory Filter Topology IsUnifLocDoublingMeasure

namespace FractionalPrimes.Literature.JSW

noncomputable section

theorem memLp_dyadicAverage_two_of_memLp {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (m : ℤ) : MemLp (dyadicAverage m f) 2 volume := by
  apply memLp_iff.mpr
  exact (eLpNorm_two_dyadicAverage_le hf m).trans_lt hf.eLpNorm_lt_top

theorem memLp_dyadicDifference_two_of_memLp {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (m : ℤ) : MemLp (dyadicDifference m f) 2 volume := by
  exact (memLp_dyadicAverage_two_of_memLp hf (m - 1)).sub
    (memLp_dyadicAverage_two_of_memLp hf m)

/-- On `L²`, the dyadic averaging operator is linear in its input. -/
theorem dyadicAverage_sub_of_memLp_two {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (m : ℤ) (x : ℝ) :
    dyadicAverage m (f - g) x = dyadicAverage m f x - dyadicAverage m g x := by
  let Q := dyadicInterval m (dyadicIntervalIndex m x)
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hfinite : volume Q ≠ ⊤ := by
    dsimp [Q, dyadicInterval]
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (volume.restrict Q) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hfinite
  have hfQ : Integrable f (volume.restrict Q) :=
    (hf.restrict Q).integrable (by norm_num)
  have hgQ : Integrable g (volume.restrict Q) :=
    (hg.restrict Q).integrable (by norm_num)
  unfold dyadicAverage
  simp only [Pi.sub_apply]
  rw [integral_sub hfQ hgQ]
  simp [smul_sub, Q]

/-- Dyadic averaging is complex-linear on `L²` representatives. -/
theorem dyadicAverage_smul_of_memLp_two {f : ℝ → ℂ}
    (c : ℂ) (hf : MemLp f 2 volume) (m : ℤ) (x : ℝ) :
    dyadicAverage m (c • f) x = c • dyadicAverage m f x := by
  let Q := dyadicInterval m (dyadicIntervalIndex m x)
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hfinite : volume Q ≠ ⊤ := by
    dsimp [Q, dyadicInterval]
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (volume.restrict Q) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hfinite
  have hfQ : Integrable f (volume.restrict Q) :=
    (hf.restrict Q).integrable (by norm_num)
  unfold dyadicAverage
  change ((2 : ℝ) ^ m)⁻¹ •
      (∫ y, c • f y ∂(volume.restrict Q)) =
    c • (((2 : ℝ) ^ m)⁻¹ • ∫ y, f y ∂(volume.restrict Q))
  rw [integral_smul c f]
  exact smul_comm ((2 : ℝ) ^ m)⁻¹ c _

/-- Averaging is an `L²` contraction on differences, by its linearity and
the already established `L²` contraction. -/
theorem eLpNorm_dyadicAverage_sub_le_of_memLp_two {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (m : ℤ) :
    eLpNorm (dyadicAverage m f - dyadicAverage m g) 2 volume ≤
      eLpNorm (f - g) 2 volume := by
  have hfun : dyadicAverage m f - dyadicAverage m g = dyadicAverage m (f - g) := by
    funext x
    exact (dyadicAverage_sub_of_memLp_two hf hg m x).symm
  rw [hfun]
  exact eLpNorm_two_dyadicAverage_le (hf.sub hg) m

/-- The real `L²` norm of an average is controlled by approximation of the
input and the average of the approximant. -/
theorem lpNorm_dyadicAverage_le_of_memLp_two {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (m : ℤ) :
    lpNorm (dyadicAverage m f) 2 volume ≤
      lpNorm (f - g) 2 volume + lpNorm (dyadicAverage m g) 2 volume := by
  have hfg : MemLp (f - g) 2 volume := hf.sub hg
  have hsum : dyadicAverage m f =
      dyadicAverage m (f - g) + dyadicAverage m g := by
    funext x
    have hx := dyadicAverage_sub_of_memLp_two hf hg m x
    simp only [Pi.add_apply]
    rw [hx]
    ring
  rw [hsum]
  calc
    lpNorm (dyadicAverage m (f - g) + dyadicAverage m g) 2 volume ≤
        lpNorm (dyadicAverage m (f - g)) 2 volume +
          lpNorm (dyadicAverage m g) 2 volume :=
      lpNorm_add_le (memLp_dyadicAverage_two_of_memLp hfg m) (by norm_num)
    _ ≤ lpNorm (f - g) 2 volume + lpNorm (dyadicAverage m g) 2 volume := by
      gcongr
      rw [← toReal_eLpNorm, ← toReal_eLpNorm]
      exact ENNReal.toReal_mono
        hfg.eLpNorm_ne_top
        (eLpNorm_two_dyadicAverage_le hfg m)

/-- In `L²`, a finite sum of consecutive dyadic differences is the difference
of its endpoint averages. -/
theorem dyadicDifference_finite_sum_eq_average_difference {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (a : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range n,
        (memLp_dyadicDifference_two_of_memLp hf (a + (k : ℤ) + 1)).toLp
          (dyadicDifference (a + (k : ℤ) + 1) f) =
      (memLp_dyadicAverage_two_of_memLp hf a).toLp (dyadicAverage a f) -
        (memLp_dyadicAverage_two_of_memLp hf (a + n)).toLp
          (dyadicAverage (a + n) f) := by
  let avg : ℤ → Lp ℂ 2 volume := fun m =>
    (memLp_dyadicAverage_two_of_memLp hf m).toLp (dyadicAverage m f)
  let diff : ℤ → Lp ℂ 2 volume := fun m =>
    (memLp_dyadicDifference_two_of_memLp hf m).toLp (dyadicDifference m f)
  have hdiff (m : ℤ) : diff m = avg (m - 1) - avg m := by
    dsimp [diff, avg]
    exact (MemLp.toLp_sub
      (memLp_dyadicAverage_two_of_memLp hf (m - 1))
      (memLp_dyadicAverage_two_of_memLp hf m)).symm
  have htel (n : ℕ) :
      ∑ k ∈ Finset.range n, diff (a + (k : ℤ) + 1) = avg a - avg (a + n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hdiff]
      have hleft : a + (n : ℤ) + 1 - 1 = a + n := by omega
      have hright : a + (n : ℤ) + 1 = a + (n + 1 : ℕ) := by
        push_cast
        omega
      rw [hleft, hright]
      abel
  change ∑ k ∈ Finset.range n, diff (a + (k : ℤ) + 1) = avg a - avg (a + n)
  exact htel n

/-- Every finite family of distinct dyadic differences is orthogonal in `L²`,
so the norm square of their sum is the sum of their norm squares. -/
theorem dyadicDifference_finite_Pythagorean {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (a : ℤ) (n : ℕ) :
    ‖∑ k ∈ Finset.range n,
        (memLp_dyadicDifference_two_of_memLp hf (a + (k : ℤ) + 1)).toLp
          (dyadicDifference (a + (k : ℤ) + 1) f)‖ ^ 2 =
      ∑ k ∈ Finset.range n,
        ‖(memLp_dyadicDifference_two_of_memLp hf (a + (k : ℤ) + 1)).toLp
          (dyadicDifference (a + (k : ℤ) + 1) f)‖ ^ 2 := by
  classical
  let idx : ℕ → ℤ := fun k => a + (k : ℤ) + 1
  let u : ℕ → Lp ℂ 2 volume := fun k =>
    (memLp_dyadicDifference_two_of_memLp hf (idx k)).toLp
      (dyadicDifference (idx k) f)
  change ‖∑ k ∈ Finset.range n, u k‖ ^ 2 =
    ∑ k ∈ Finset.range n, ‖u k‖ ^ 2
  have hidx {i j : ℕ} (hij : i ≠ j) : idx i ≠ idx j := by
    dsimp [idx]
    omega
  have horth {i j : ℕ} (hij : i ≠ j) : inner ℂ (u i) (u j) = 0 := by
    rw [MeasureTheory.L2.inner_def]
    change ∫ x, u j x * star (u i x) ∂volume = 0
    have hzero := dyadicDifference_pairwise_orthogonal hf hf
      (hidx (Ne.symm hij))
    calc
      ∫ x, u j x * star (u i x) ∂volume =
          ∫ x, dyadicDifference (idx j) f x *
            star (dyadicDifference (idx i) f x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [
          (memLp_dyadicDifference_two_of_memLp hf (idx j)).coeFn_toLp,
          (memLp_dyadicDifference_two_of_memLp hf (idx i)).coeFn_toLp] with x hj hi
        simp [u, hj, hi]
      _ = 0 := hzero
  have hsumInner :
      inner ℂ (∑ k ∈ Finset.range n, u k) (∑ k ∈ Finset.range n, u k) =
        ∑ k ∈ Finset.range n, inner ℂ (u k) (u k) := by
    calc
      inner ℂ (∑ k ∈ Finset.range n, u k) (∑ k ∈ Finset.range n, u k) =
          ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range n, inner ℂ (u k) (u j) := by
        calc
          inner ℂ (∑ k ∈ Finset.range n, u k) (∑ k ∈ Finset.range n, u k) =
              ∑ k ∈ Finset.range n, inner ℂ (u k)
                (∑ j ∈ Finset.range n, u j) := by rw [sum_inner]
          _ = ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range n,
                inner ℂ (u k) (u j) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [inner_sum]
      _ = ∑ k ∈ Finset.range n, inner ℂ (u k) (u k) := by
        apply Finset.sum_congr rfl
        intro k hk
        refine Finset.sum_eq_single k ?_ ?_
        · intro j hj hjk
          exact horth (Ne.symm hjk)
        · intro hnot
          exact False.elim (hnot hk)
  calc
    ‖∑ k ∈ Finset.range n, u k‖ ^ 2 =
        (inner ℂ (∑ k ∈ Finset.range n, u k)
          (∑ k ∈ Finset.range n, u k)).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) (∑ k ∈ Finset.range n, u k)).symm
    _ = (∑ k ∈ Finset.range n, inner ℂ (u k) (u k)).re := by rw [hsumInner]
    _ = ∑ k ∈ Finset.range n, ‖u k‖ ^ 2 := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (u k)

/-- The endpoint difference of two dyadic averages has squared norm equal
to the sum of the squared norms of the intervening differences. -/
theorem dyadicAverage_endpoint_Pythagorean {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (a : ℤ) (n : ℕ) :
    ‖(memLp_dyadicAverage_two_of_memLp hf a).toLp (dyadicAverage a f) -
        (memLp_dyadicAverage_two_of_memLp hf (a + n)).toLp
          (dyadicAverage (a + n) f)‖ ^ 2 =
      ∑ k ∈ Finset.range n,
        ‖(memLp_dyadicDifference_two_of_memLp hf (a + (k : ℤ) + 1)).toLp
          (dyadicDifference (a + (k : ℤ) + 1) f)‖ ^ 2 := by
  rw [← dyadicDifference_finite_sum_eq_average_difference hf a n]
  exact dyadicDifference_finite_Pythagorean hf a n

/-- For an integrable input, a coarse dyadic average is bounded everywhere
by the reciprocal cell length times the global `L¹` norm. -/
theorem norm_dyadicAverage_le_inv_scale_mul_integral_norm {f : ℝ → ℂ}
    (hf : Integrable f volume) (m : ℤ) (x : ℝ) :
    ‖dyadicAverage m f x‖ ≤
      ((2 : ℝ) ^ m)⁻¹ * ∫ y, ‖f y‖ ∂volume := by
  let Q := dyadicInterval m (dyadicIntervalIndex m x)
  have hcell := norm_dyadicAverage_le_average_norm (f := f) m x
  have hglobal : ∫ y in Q, ‖f y‖ ∂volume ≤ ∫ y, ‖f y‖ ∂volume := by
    apply MeasureTheory.setIntegral_le_integral hf.norm
    exact Filter.Eventually.of_forall (fun y => norm_nonneg (f y))
  have hscale : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  calc
    ‖dyadicAverage m f x‖ ≤
        ((2 : ℝ) ^ m)⁻¹ * ∫ y in Q, ‖f y‖ ∂volume := by
      simpa [Q] using hcell
    _ ≤ ((2 : ℝ) ^ m)⁻¹ * ∫ y, ‖f y‖ ∂volume :=
      mul_le_mul_of_nonneg_left hglobal (inv_nonneg.mpr hscale.le)

/-- The coarse-scale `L²` energy of an average is bounded by its uniform
bound times its `L¹` mass. -/
theorem integral_sq_dyadicAverage_le_of_integrable {f : ℝ → ℂ}
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) (m : ℤ) :
    ∫ x, ‖dyadicAverage m f x‖ ^ 2 ∂volume ≤
      ((2 : ℝ) ^ m)⁻¹ * (∫ x, ‖f x‖ ∂volume) ^ 2 := by
  let h1 : MemLp f 1 volume := memLp_one_iff_integrable.mpr hf1
  have hE1 : MemLp (dyadicAverage m f) 1 volume := by
    apply memLp_iff.mpr
    exact (eLpNorm_one_dyadicAverage_le h1 m).trans_lt h1.eLpNorm_lt_top
  have hE2 : MemLp (dyadicAverage m f) 2 volume := by
    apply memLp_iff.mpr
    exact (eLpNorm_two_dyadicAverage_le hf2 m).trans_lt hf2.eLpNorm_lt_top
  have hEInt : Integrable (dyadicAverage m f) volume := memLp_one_iff_integrable.mp hE1
  have hEsqInt : Integrable (fun x => ‖dyadicAverage m f x‖ ^ 2) volume :=
    hE2.integrable_norm_pow (by norm_num)
  have hL1 : ∫ x, ‖dyadicAverage m f x‖ ∂volume ≤ ∫ x, ‖f x‖ ∂volume := by
    have hcontract := eLpNorm_one_dyadicAverage_le h1 m
    rw [eLpNorm_one_eq_lintegral_enorm (measurable_dyadicAverage m f).aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm hf1.aestronglyMeasurable] at hcontract
    rw [← ofReal_integral_norm_eq_lintegral_enorm hEInt,
      ← ofReal_integral_norm_eq_lintegral_enorm hf1] at hcontract
    apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => norm_nonneg (f x)))).mp
    exact hcontract
  let C : ℝ := ((2 : ℝ) ^ m)⁻¹ * ∫ x, ‖f x‖ ∂volume
  have hscale : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hC : 0 ≤ C := mul_nonneg (inv_nonneg.mpr hscale.le)
    (integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => norm_nonneg (f x)))
  have hpoint (x : ℝ) : ‖dyadicAverage m f x‖ ≤ C := by
    simpa [C] using norm_dyadicAverage_le_inv_scale_mul_integral_norm hf1 m x
  have hsquare (x : ℝ) : ‖dyadicAverage m f x‖ ^ 2 ≤
      C * ‖dyadicAverage m f x‖ := by
    have hm := mul_le_mul_of_nonneg_right (hpoint x)
      (norm_nonneg (dyadicAverage m f x))
    simpa [pow_two] using hm
  have hmulInt : Integrable (fun x => C * ‖dyadicAverage m f x‖) volume := by
    simpa [mul_comm] using hEInt.norm.const_mul C
  calc
    ∫ x, ‖dyadicAverage m f x‖ ^ 2 ∂volume ≤
        ∫ x, C * ‖dyadicAverage m f x‖ ∂volume :=
      integral_mono_ae hEsqInt hmulInt (Filter.Eventually.of_forall hsquare)
    _ = C * ∫ x, ‖dyadicAverage m f x‖ ∂volume := by
      rw [integral_const_mul]
    _ ≤ C * ∫ x, ‖f x‖ ∂volume := mul_le_mul_of_nonneg_left hL1 hC
    _ = ((2 : ℝ) ^ m)⁻¹ * (∫ x, ‖f x‖ ∂volume) ^ 2 := by
      dsimp [C]
      ring

private theorem tendsto_inv_two_zpow_atTop :
    Tendsto (fun m : ℤ => ((2 : ℝ) ^ m)⁻¹) atTop (𝓝 0) := by
  have htoNat : Tendsto Int.toNat atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro n
    filter_upwards [Filter.eventually_ge_atTop (n : ℤ)] with z hz
    have hz0 : 0 ≤ z := by omega
    have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    have hcast : (n : ℤ) ≤ (z.toNat : ℤ) := by simpa [hzcast] using hz
    exact_mod_cast hcast
  have hpowNat : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hpowInt : Tendsto (fun m : ℤ => (2 : ℝ) ^ m.toNat) atTop atTop :=
    hpowNat.comp htoNat
  have hEq : (fun m : ℤ => ((2 : ℝ) ^ m)⁻¹) =ᶠ[atTop]
      fun m => ((2 : ℝ) ^ m.toNat)⁻¹ := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℤ)] with m hm
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    simp
  exact Tendsto.congr' hEq.symm (tendsto_inv_atTop_zero.comp hpowInt)

/-- For an `L¹ ∩ L²` input, the coarse averages have vanishing `L²` energy. -/
theorem integral_sq_dyadicAverage_tendsto_atTop_zero {f : ℝ → ℂ}
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    Tendsto (fun m : ℤ => ∫ x, ‖dyadicAverage m f x‖ ^ 2 ∂volume)
      atTop (𝓝 0) := by
  have hnonneg (m : ℤ) : 0 ≤ ∫ x, ‖dyadicAverage m f x‖ ^ 2 ∂volume :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hbound (m : ℤ) :
      ∫ x, ‖dyadicAverage m f x‖ ^ 2 ∂volume ≤
        ((2 : ℝ) ^ m)⁻¹ * (∫ x, ‖f x‖ ∂volume) ^ 2 :=
    integral_sq_dyadicAverage_le_of_integrable hf1 hf2 m
  have hboundTendsto : Tendsto
      (fun m : ℤ => ((2 : ℝ) ^ m)⁻¹ * (∫ x, ‖f x‖ ∂volume) ^ 2)
      atTop (𝓝 0) := by
    simpa [mul_comm] using tendsto_inv_two_zpow_atTop.const_mul
      ((∫ x, ‖f x‖ ∂volume) ^ 2)
  refine squeeze_zero' (Filter.Eventually.of_forall hnonneg) ?_ hboundTendsto
  filter_upwards [] with m
  exact hbound m

/-- On the dense class `L¹ ∩ L²`, the coarse averages converge to zero in
the `L²` space. -/
theorem dyadicAverage_toLp_tendsto_atTop_zero_of_integrable {f : ℝ → ℂ}
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    Tendsto (fun m : ℤ =>
      (memLp_dyadicAverage_two_of_memLp hf2 m).toLp (dyadicAverage m f))
      atTop (𝓝 0) := by
  have henergy := integral_sq_dyadicAverage_tendsto_atTop_zero hf1 hf2
  have hroot : Tendsto
      (fun m : ℤ => Real.sqrt (∫ x, ‖dyadicAverage m f x‖ ^ 2 ∂volume))
      atTop (𝓝 0) := by
    simpa using henergy.sqrt
  have hnorm (m : ℤ) :
      ‖(memLp_dyadicAverage_two_of_memLp hf2 m).toLp (dyadicAverage m f)‖ =
        Real.sqrt (∫ x, ‖dyadicAverage m f x‖ ^ 2 ∂volume) := by
    calc
      ‖(memLp_dyadicAverage_two_of_memLp hf2 m).toLp (dyadicAverage m f)‖ =
          ENNReal.toReal (eLpNorm (dyadicAverage m f) 2 volume) :=
        Lp.norm_toLp _ _
      _ = lpNorm (dyadicAverage m f) 2 volume := toReal_eLpNorm
      _ = (∫ x, ‖dyadicAverage m f x‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
        rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
          (measurable_dyadicAverage m f).aestronglyMeasurable]
        norm_num
      _ = Real.sqrt (∫ x, ‖dyadicAverage m f x‖ ^ 2 ∂volume) :=
        (Real.sqrt_eq_rpow _).symm
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact Tendsto.congr' (Filter.Eventually.of_forall fun m => (hnorm m).symm) hroot

/-- The coarse averages converge to zero in `L²` for every `L²` input.
Approximation by continuous compactly supported functions reduces this to
the `L¹ ∩ L²` estimate above. -/
theorem dyadicAverage_lpNorm_tendsto_atTop_zero {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    Tendsto (fun m : ℤ => lpNorm (dyadicAverage m f) 2 volume) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδne : ENNReal.ofReal δ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hδ
  obtain ⟨g, hgSupport, herror, hgContinuous, hgMem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hδne
  have hfg : MemLp (f - g) 2 volume := hf.sub hgMem
  have happrox : lpNorm (f - g) 2 volume ≤ δ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top herror
    rw [toReal_eLpNorm, ENNReal.toReal_ofReal hδ.le] at h
    exact h
  have hgIntegrable : Integrable g volume :=
    hgContinuous.integrable_of_hasCompactSupport hgSupport
  have hGvector := dyadicAverage_toLp_tendsto_atTop_zero_of_integrable
    hgIntegrable hgMem
  have hGnorm : Tendsto
      (fun m : ℤ => ‖(memLp_dyadicAverage_two_of_memLp hgMem m).toLp
        (dyadicAverage m g)‖) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).mp hGvector
  have hGlp : Tendsto
      (fun m : ℤ => lpNorm (dyadicAverage m g) 2 volume) atTop (𝓝 0) := by
    apply Tendsto.congr' (Filter.Eventually.of_forall fun m => ?_) hGnorm
    calc
      ‖(memLp_dyadicAverage_two_of_memLp hgMem m).toLp
          (dyadicAverage m g)‖ =
          ENNReal.toReal (eLpNorm (dyadicAverage m g) 2 volume) := Lp.norm_toLp _ _
      _ = lpNorm (dyadicAverage m g) 2 volume := toReal_eLpNorm
  have hGeventually : ∀ᶠ m : ℤ in atTop,
      lpNorm (dyadicAverage m g) 2 volume < δ := by
    filter_upwards [(Metric.tendsto_nhds.mp hGlp) δ hδ] with m hm
    have hnonneg : 0 ≤ lpNorm (dyadicAverage m g) 2 volume := lpNorm_nonneg
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hm
  filter_upwards [hGeventually] with m hm
  have hnonneg : 0 ≤ lpNorm (dyadicAverage m f) 2 volume := lpNorm_nonneg
  have hlt : lpNorm (dyadicAverage m f) 2 volume < ε := calc
    lpNorm (dyadicAverage m f) 2 volume ≤
        lpNorm (f - g) 2 volume + lpNorm (dyadicAverage m g) 2 volume :=
      lpNorm_dyadicAverage_le_of_memLp_two hf hgMem m
    _ ≤ δ + lpNorm (dyadicAverage m g) 2 volume :=
      add_le_add happrox le_rfl
    _ < δ + δ := by nlinarith [hm]
    _ < ε := by dsimp [δ]; linarith
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hlt

/-- The `L²`-valued coarse averages converge to zero for arbitrary `L²`
inputs. -/
theorem dyadicAverage_toLp_tendsto_atTop_zero {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    Tendsto (fun m : ℤ =>
      (memLp_dyadicAverage_two_of_memLp hf m).toLp (dyadicAverage m f))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm (m : ℤ) :
      ‖(memLp_dyadicAverage_two_of_memLp hf m).toLp (dyadicAverage m f)‖ =
        lpNorm (dyadicAverage m f) 2 volume := by
    calc
      ‖(memLp_dyadicAverage_two_of_memLp hf m).toLp (dyadicAverage m f)‖ =
          ENNReal.toReal (eLpNorm (dyadicAverage m f) 2 volume) := Lp.norm_toLp _ _
      _ = lpNorm (dyadicAverage m f) 2 volume := toReal_eLpNorm
  exact Tendsto.congr' (Filter.Eventually.of_forall fun m => (hnorm m).symm)
    (dyadicAverage_lpNorm_tendsto_atTop_zero hf)

/-- Fine-scale dyadic averages converge uniformly for uniformly continuous
inputs. This is the pointwise estimate used for the compactly supported
density argument in `lj:dyadic-properties`. -/
theorem dyadicAverage_uniform_error_tendsto_atBot_of_uniformContinuous
    {f : ℝ → ℂ} (hf : UniformContinuous f) :
    ∀ ε > 0, ∀ᶠ m : ℤ in atBot,
      ∀ x : ℝ, ‖dyadicAverage m f x - f x‖ ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ :=
    (Metric.uniformContinuous_iff.mp hf) (ε / 2) (by linarith)
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmallEventually : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ^ n < δ := by
    filter_upwards [(Metric.tendsto_nhds.mp hpow) δ hδ] with n hn
    simpa [Real.dist_eq,
      Real.norm_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n)] using hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmallEventually
  have hscaleN : (2 : ℝ) ^ (-(N : ℤ)) = (1 / 2 : ℝ) ^ N := by
    simp [zpow_neg, zpow_natCast, one_div, inv_pow]
  have hsmall : (2 : ℝ) ^ (-(N : ℤ)) < δ := by
    rw [hscaleN]
    exact hN N le_rfl
  have hevent : ∀ᶠ m : ℤ in atBot, m ≤ -(N : ℤ) :=
    eventually_atBot.2 ⟨-(N : ℤ), fun m hm => hm⟩
  filter_upwards [hevent] with m hm x
  have hscale : (2 : ℝ) ^ m < δ := by
    exact (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm).trans_lt hsmall
  have hx : x ∈ dyadicInterval m (dyadicIntervalIndex m x) :=
    mem_dyadicIntervalIndex m x
  have hbound : ∀ y ∈ dyadicInterval m (dyadicIntervalIndex m x),
      ‖f y - f x‖ ≤ ε / 2 := by
    intro y hy
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
  have hloc : LocallyIntegrable f volume := hf.continuous.locallyIntegrable
  have hpoint := norm_dyadicAverage_sub_le_of_cell_bound hloc m x (ε / 2) hbound
  exact hpoint.trans (by linarith)

/-- A compactly supported continuous input and its dyadic average both vanish
outside a fixed one-unit enlargement of the support, for scales at most one. -/
theorem dyadicAverage_eq_zero_of_outside_support_enlargement
    {g : ℝ → ℂ} {a b : ℝ}
    (hgsupp : tsupport g ⊆ Set.Icc a b) {m : ℤ} (hm : m ≤ 0)
    {x : ℝ} (hx : x ∉ Set.Icc (a - 1) (b + 1)) :
    dyadicAverage m g x = 0 ∧ g x = 0 := by
  have hx' : x < a - 1 ∨ b + 1 < x := by
    have hnot : ¬ (a - 1 ≤ x ∧ x ≤ b + 1) := by
      simpa [Set.mem_Icc] using hx
    rcases not_and_or.mp hnot with hleft | hright
    · exact Or.inl (lt_of_not_ge hleft)
    · exact Or.inr (lt_of_not_ge hright)
  have hscale : (2 : ℝ) ^ m ≤ 1 := by
    calc
      (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (0 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
      _ = 1 := by norm_num
  let j := dyadicIntervalIndex m x
  let Q := dyadicInterval m j
  have hxQ : x ∈ Q := by
    simpa [Q, j] using mem_dyadicIntervalIndex m x
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hcellzero : ∀ y ∈ Q, g y = 0 := by
    intro y hy
    have hyQ : y ∈ dyadicInterval m (dyadicIntervalIndex m x) := by
      simpa [Q, j] using hy
    change x ∈ dyadicInterval m (dyadicIntervalIndex m x) at hxQ
    rw [dyadicInterval, Set.mem_Ico] at hxQ hyQ
    have hwidth :
        (((dyadicIntervalIndex m x + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) -
          (dyadicIntervalIndex m x : ℝ) * (2 : ℝ) ^ m = (2 : ℝ) ^ m := by
      push_cast
      ring
    have hyx : y - x < (2 : ℝ) ^ m := by linarith [hyQ.2, hxQ.1]
    have hxy : x - y < (2 : ℝ) ^ m := by linarith [hxQ.2, hyQ.1]
    have hyout : y ∉ tsupport g := by
      intro hySupport
      have hyI : y ∈ Set.Icc a b := hgsupp hySupport
      rcases hx' with hxleft | hxright
      · have : y < x + 1 := by linarith [hyx, hscale]
        exact (not_le_of_gt (by linarith : y < a)) hyI.1
      · have : x - 1 < y := by linarith [hxy, hscale]
        exact (not_le_of_gt (by linarith : b < y)) hyI.2
    apply image_eq_zero_of_notMem_tsupport
    exact hyout
  have hxout : x ∉ tsupport g := by
    intro hxSupport
    have hxI : x ∈ Set.Icc a b := hgsupp hxSupport
    rcases hx' with hxleft | hxright
    · exact (not_le_of_gt (by linarith : x < a)) hxI.1
    · exact (not_le_of_gt (by linarith : b < x)) hxI.2
  have hgx : g x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact hxout
  have hzeroIntegral : (∫ y, g y ∂(volume.restrict Q)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hQ] with y hy
    exact hcellzero y hy
  have hzeroSetIntegral : (∫ y in Q, g y ∂volume) = 0 := by
    change (∫ y, g y ∂(volume.restrict Q)) = 0
    exact hzeroIntegral
  constructor
  · unfold dyadicAverage
    change ((2 : ℝ) ^ m)⁻¹ • (∫ y in Q, g y ∂volume) = 0
    rw [hzeroSetIntegral]
    simp
  · exact hgx

/-- A uniform pointwise error on the one-unit support enlargement gives the
corresponding finite-interval `L²` energy bound. -/
theorem integral_sq_dyadicAverage_sub_le_of_compact_support
    {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hgsupp : tsupport g ⊆ Set.Icc a b) (hgMem : MemLp g 2 volume)
    {m : ℤ} (hm : m ≤ 0) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ x : ℝ, ‖dyadicAverage m g x - g x‖ ≤ ε) :
    ∫ x, ‖dyadicAverage m g x - g x‖ ^ 2 ∂volume ≤
      (b - a + 2) * ε ^ 2 := by
  let K := Set.Icc (a - 1) (b + 1)
  have hKmeas : MeasurableSet K := by
    dsimp [K]
    exact measurableSet_Icc
  have hKfinite : volume K ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hdiffMem : MemLp (dyadicAverage m g - g) 2 volume :=
    (memLp_dyadicAverage_two_of_memLp hgMem m).sub hgMem
  have hdiffInt : Integrable (fun x => ‖dyadicAverage m g x - g x‖ ^ 2) volume :=
    hdiffMem.integrable_norm_pow (by norm_num)
  have hboundInt : Integrable (K.indicator (fun _ : ℝ => ε ^ 2)) volume := by
    have hconst : IntegrableOn (fun _ : ℝ => ε ^ 2) K volume :=
      MeasureTheory.integrableOn_const hKfinite
    exact (integrable_indicator_iff hKmeas).2 hconst
  have hpoint (x : ℝ) : ‖dyadicAverage m g x - g x‖ ^ 2 ≤
      K.indicator (fun _ : ℝ => ε ^ 2) x := by
    by_cases hx : x ∈ K
    · simp [K, hx]
      nlinarith [herr x, norm_nonneg (dyadicAverage m g x - g x)]
    · have hz := dyadicAverage_eq_zero_of_outside_support_enlargement
        hgsupp hm (by simpa [K] using hx)
      simp [K, hx, hz.1, hz.2]
  have hmono : (fun x => ‖dyadicAverage m g x - g x‖ ^ 2) ≤ᵐ[volume]
      (K.indicator (fun _ : ℝ => ε ^ 2)) :=
    Filter.Eventually.of_forall hpoint
  have hmeasure : volume.real K = b - a + 2 := by
    have hab' : a - 1 ≤ b + 1 := by linarith
    calc
      volume.real K = (b + 1) - (a - 1) := by
        simpa [K] using Real.volume_real_Icc_of_le hab'
      _ = b - a + 2 := by ring
  calc
    ∫ x, ‖dyadicAverage m g x - g x‖ ^ 2 ∂volume ≤
        ∫ x, K.indicator (fun _ : ℝ => ε ^ 2) x ∂volume :=
      integral_mono_ae hdiffInt hboundInt hmono
    _ = volume.real K * ε ^ 2 := by
      rw [integral_indicator_const (e := ε ^ 2) hKmeas, smul_eq_mul]
    _ = (b - a + 2) * ε ^ 2 := by rw [hmeasure]

/-- The pointwise support and uniform-error estimate also gives the exact
finite-interval `Lᵖ` power bound for every finite real `p ≥ 1`. -/
theorem integral_rpow_dyadicAverage_sub_le_of_compact_support
    {g : ℝ → ℂ} {a b p : ℝ} (hab : a ≤ b)
    (hgsupp : tsupport g ⊆ Set.Icc a b)
    (hgMem : MemLp g (ENNReal.ofReal p) volume) (hp : 1 ≤ p)
    {m : ℤ} (hm : m ≤ 0) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ x : ℝ, ‖dyadicAverage m g x - g x‖ ≤ ε) :
    ∫ x, ‖dyadicAverage m g x - g x‖ ^ p ∂volume ≤
      (b - a + 2) * ε ^ p := by
  let K := Set.Icc (a - 1) (b + 1)
  have hKmeas : MeasurableSet K := by
    dsimp [K]
    exact measurableSet_Icc
  have hKfinite : volume K ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hp0 : 0 < p := by linarith
  have hq0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hqtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hAvgMem : MemLp (dyadicAverage m g) (ENNReal.ofReal p) volume := by
    apply memLp_iff.mpr
    exact (eLpNorm_finite_dyadicAverage_le hgMem hp m).trans_lt hgMem.eLpNorm_lt_top
  have hdiffMem : MemLp (dyadicAverage m g - g) (ENNReal.ofReal p) volume :=
    hAvgMem.sub hgMem
  have hdiffInt : Integrable (fun x => ‖dyadicAverage m g x - g x‖ ^ p) volume := by
    simpa [htoReal] using hdiffMem.integrable_norm_rpow hq0 hqtop
  have hboundInt : Integrable (K.indicator (fun _ : ℝ => ε ^ p)) volume := by
    have hconst : IntegrableOn (fun _ : ℝ => ε ^ p) K volume :=
      MeasureTheory.integrableOn_const hKfinite
    exact (integrable_indicator_iff hKmeas).2 hconst
  have hpoint (x : ℝ) : ‖dyadicAverage m g x - g x‖ ^ p ≤
      K.indicator (fun _ : ℝ => ε ^ p) x := by
    by_cases hx : x ∈ K
    · simp [K, hx]
      exact Real.rpow_le_rpow (norm_nonneg _) (herr x) (by linarith)
    · have hz := dyadicAverage_eq_zero_of_outside_support_enlargement
        hgsupp hm (by simpa [K] using hx)
      simp [K, hx, hz.1, hz.2, Real.zero_rpow (ne_of_gt hp0)]
  have hmono : (fun x => ‖dyadicAverage m g x - g x‖ ^ p) ≤ᵐ[volume]
      (K.indicator (fun _ : ℝ => ε ^ p)) :=
    Filter.Eventually.of_forall hpoint
  have hmeasure : volume.real K = b - a + 2 := by
    have hab' : a - 1 ≤ b + 1 := by linarith
    calc
      volume.real K = (b + 1) - (a - 1) := by
        simpa [K] using Real.volume_real_Icc_of_le hab'
      _ = b - a + 2 := by ring
  calc
    ∫ x, ‖dyadicAverage m g x - g x‖ ^ p ∂volume ≤
        ∫ x, K.indicator (fun _ : ℝ => ε ^ p) x ∂volume :=
      integral_mono_ae hdiffInt hboundInt hmono
    _ = volume.real K * ε ^ p := by
      rw [integral_indicator_const (e := ε ^ p) hKmeas, smul_eq_mul]
    _ = (b - a + 2) * ε ^ p := by rw [hmeasure]

/-- Fine-scale averages converge strongly in `L²` for continuous compactly
supported inputs, by uniform continuity and a fixed finite enlargement of
their support. -/
theorem dyadicAverage_lpNorm_sub_tendsto_atBot_zero_of_continuous_hasCompactSupport
    {g : ℝ → ℂ} (hg : Continuous g) (hgSupport : HasCompactSupport g)
    (hgMem : MemLp g 2 volume) :
    Tendsto (fun m : ℤ => lpNorm (dyadicAverage m g - g) 2 volume)
      atBot (𝓝 0) := by
  have hcompact : IsCompact (tsupport g) := hgSupport
  rcases hcompact.bddBelow with ⟨a, ha⟩
  rcases hcompact.bddAbove with ⟨b, hb⟩
  let lo := min a b
  let hi := max a b
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; exact min_le_max
  have hgsupp : tsupport g ⊆ Set.Icc lo hi := by
    intro x hx
    exact ⟨(min_le_left a b).trans (ha hx), (hb hx).trans (le_max_right a b)⟩
  let C := hi - lo + 2
  have hC : 0 < C := by dsimp [C]; linarith
  have hCnonneg : 0 ≤ C := le_of_lt hC
  have hUniform : UniformContinuous g :=
    hgSupport.uniformContinuous_of_continuous hg
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let η := δ / (C + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hratio : C * η ^ 2 ≤ δ ^ 2 := by
    dsimp [η]
    have hden : C + 1 ≠ 0 := ne_of_gt (by linarith)
    field_simp [hden]
    nlinarith [sq_nonneg C, sq_nonneg δ]
  have hUevent : ∀ᶠ m : ℤ in atBot,
      ∀ x : ℝ, ‖dyadicAverage m g x - g x‖ ≤ η :=
    dyadicAverage_uniform_error_tendsto_atBot_of_uniformContinuous
      hUniform η hη
  have hmevent : ∀ᶠ m : ℤ in atBot, m ≤ 0 :=
    eventually_atBot.2 ⟨0, fun m hm => hm⟩
  have hdiffMem (m : ℤ) : MemLp (dyadicAverage m g - g) 2 volume :=
    (memLp_dyadicAverage_two_of_memLp hgMem m).sub hgMem
  have hnormFormula (m : ℤ) :
      lpNorm (dyadicAverage m g - g) 2 volume =
        Real.sqrt (∫ x, ‖dyadicAverage m g x - g x‖ ^ 2 ∂volume) := by
    calc
      lpNorm (dyadicAverage m g - g) 2 volume =
          (∫ x, ‖dyadicAverage m g x - g x‖ ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
        rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
          (hdiffMem m).aestronglyMeasurable]
        norm_num
      _ = Real.sqrt (∫ x, ‖dyadicAverage m g x - g x‖ ^ 2 ∂volume) :=
        (Real.sqrt_eq_rpow _).symm
  filter_upwards [hUevent, hmevent] with m herr hm
  have henergy := integral_sq_dyadicAverage_sub_le_of_compact_support
    hlohi hgsupp hgMem hm (le_of_lt hη) herr
  have henergyδ :
      ∫ x, ‖dyadicAverage m g x - g x‖ ^ 2 ∂volume ≤ δ ^ 2 := by
    calc
      ∫ x, ‖dyadicAverage m g x - g x‖ ^ 2 ∂volume ≤ C * η ^ 2 := by
        convert henergy using 1 <;> dsimp [C, lo, hi]
      _ ≤ δ ^ 2 := hratio
  have hnormbound : lpNorm (dyadicAverage m g - g) 2 volume ≤ δ := by
    rw [hnormFormula]
    exact Real.sqrt_le_iff.mpr ⟨le_of_lt hδ, henergyδ⟩
  have hlt : lpNorm (dyadicAverage m g - g) 2 volume < ε := by
    exact hnormbound.trans_lt (by dsimp [δ]; linarith)
  simpa [Real.dist_eq, abs_of_nonneg lpNorm_nonneg] using hlt

/-- Fine-scale averages converge strongly in every finite real `Lᵖ`, `p ≥ 1`,
for continuous compactly supported inputs. -/
theorem dyadicAverage_lpNorm_sub_tendsto_atBot_zero_finite_of_continuous_hasCompactSupport
    {g : ℝ → ℂ} {p : ℝ} (hp : 1 ≤ p) (hg : Continuous g)
    (hgSupport : HasCompactSupport g)
    (hgMem : MemLp g (ENNReal.ofReal p) volume) :
    Tendsto (fun m : ℤ =>
      lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume)
      atBot (𝓝 0) := by
  have hcompact : IsCompact (tsupport g) := hgSupport
  rcases hcompact.bddBelow with ⟨a, ha⟩
  rcases hcompact.bddAbove with ⟨b, hb⟩
  let lo := min a b
  let hi := max a b
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; exact min_le_max
  have hgsupp : tsupport g ⊆ Set.Icc lo hi := by
    intro x hx
    exact ⟨(min_le_left a b).trans (ha hx), (hb hx).trans (le_max_right a b)⟩
  let C := hi - lo + 2
  have hC : 0 < C := by dsimp [C]; linarith
  have hCnonneg : 0 ≤ C := le_of_lt hC
  have hCpow : C ≤ (C + 1) ^ p := by
    have hbase : 1 ≤ C + 1 := by linarith
    calc
      C ≤ C + 1 := by linarith
      _ = (C + 1) ^ 1 := (Real.rpow_one _).symm
      _ ≤ (C + 1) ^ p := Real.rpow_le_rpow_of_exponent_le hbase hp
  have hUniform : UniformContinuous g :=
    hgSupport.uniformContinuous_of_continuous hg
  have hp0 : 0 < p := by linarith
  have hq0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hqtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let η := δ / (C + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hratio : C * η ^ p ≤ δ ^ p := by
    dsimp [η]
    rw [Real.div_rpow hδ.le (by positivity) p]
    have hden : 0 < (C + 1) ^ p := Real.rpow_pos_of_pos (by linarith) p
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).2
    calc
      C * δ ^ p ≤ (C + 1) ^ p * δ ^ p :=
        mul_le_mul_of_nonneg_right hCpow (Real.rpow_nonneg hδ.le p)
      _ = δ ^ p * (C + 1) ^ p := mul_comm _ _
  have hUevent : ∀ᶠ m : ℤ in atBot,
      ∀ x : ℝ, ‖dyadicAverage m g x - g x‖ ≤ η :=
    dyadicAverage_uniform_error_tendsto_atBot_of_uniformContinuous
      hUniform η hη
  have hmevent : ∀ᶠ m : ℤ in atBot, m ≤ 0 :=
    eventually_atBot.2 ⟨0, fun m hm => hm⟩
  have hdiffMem (m : ℤ) :
      MemLp (dyadicAverage m g - g) (ENNReal.ofReal p) volume := by
    have hAvgMem : MemLp (dyadicAverage m g) (ENNReal.ofReal p) volume := by
      apply memLp_iff.mpr
      exact (eLpNorm_finite_dyadicAverage_le hgMem hp m).trans_lt
        hgMem.eLpNorm_lt_top
    exact hAvgMem.sub hgMem
  have hnormFormula (m : ℤ) :
      lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume =
        (∫ x, ‖dyadicAverage m g x - g x‖ ^ p ∂volume) ^ p⁻¹ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal hq0 hqtop
      (hdiffMem m).aestronglyMeasurable]
    simp only [htoReal, Pi.sub_apply]
  filter_upwards [hUevent, hmevent] with m herr hm
  have henergy := integral_rpow_dyadicAverage_sub_le_of_compact_support
    hlohi hgsupp hgMem hp hm (le_of_lt hη) herr
  have henergyδ :
      ∫ x, ‖dyadicAverage m g x - g x‖ ^ p ∂volume ≤ δ ^ p := by
    calc
      ∫ x, ‖dyadicAverage m g x - g x‖ ^ p ∂volume ≤ C * η ^ p := by
        convert henergy using 1 <;> dsimp [C, lo, hi]
      _ ≤ δ ^ p := hratio
  have hnormbound :
      lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume ≤ δ := by
    rw [hnormFormula]
    calc
      (∫ x, ‖dyadicAverage m g x - g x‖ ^ p ∂volume) ^ p⁻¹ ≤
          (δ ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow
          (integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
            Real.rpow_nonneg (norm_nonneg _) p)) henergyδ
          (by positivity)
      _ = δ := by
        rw [← Real.rpow_mul hδ.le, mul_inv_cancel₀ (ne_of_gt hp0), Real.rpow_one]
  have hlt :
      lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume < ε := by
    exact hnormbound.trans_lt (by dsimp [δ]; linarith)
  simpa [Real.dist_eq, abs_of_nonneg lpNorm_nonneg] using hlt

/-- Coarse averages of an integrable finite-`p` input vanish in `Lᵖ` when
`p > 1`; the global `L¹` mass supplies the uniform bound. -/
theorem dyadicAverage_lpNorm_tendsto_atTop_zero_finite_of_integrable
    {g : ℝ → ℂ} {p : ℝ} (hp : 1 < p) (hgInt : Integrable g volume)
    (hgMem : MemLp g (ENNReal.ofReal p) volume) :
    Tendsto (fun m : ℤ => lpNorm (dyadicAverage m g) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hq0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_pos.mpr hp0 |>.ne'
  have hqtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpminus : 0 < p - 1 := by linarith
  let M := ∫ x, ‖g x‖ ∂volume
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => norm_nonneg (g x))
  have hgMem1 : MemLp g 1 volume := memLp_one_iff_integrable.mpr hgInt
  let B : ℤ → ℝ := fun m => ((2 : ℝ) ^ m)⁻¹ * M
  have hBnonneg (m : ℤ) : 0 ≤ B m := by
    dsimp [B]
    exact mul_nonneg (inv_nonneg.mpr (zpow_pos (by norm_num) m).le) hM
  have hAvgMem (m : ℤ) : MemLp (dyadicAverage m g) (ENNReal.ofReal p) volume := by
    apply memLp_iff.mpr
    exact (eLpNorm_finite_dyadicAverage_le hgMem (le_of_lt hp) m).trans_lt
      hgMem.eLpNorm_lt_top
  have hAvgInt (m : ℤ) : Integrable (dyadicAverage m g) volume := by
    have hAvg1 : MemLp (dyadicAverage m g) 1 volume := by
      apply memLp_iff.mpr
      exact (eLpNorm_one_dyadicAverage_le hgMem1 m).trans_lt hgMem1.eLpNorm_lt_top
    exact memLp_one_iff_integrable.mp hAvg1
  have hAvgPowInt (m : ℤ) :
      Integrable (fun x => ‖dyadicAverage m g x‖ ^ p) volume := by
    simpa [htoReal] using (hAvgMem m).integrable_norm_rpow hq0 hqtop
  have hL1 (m : ℤ) :
      ∫ x, ‖dyadicAverage m g x‖ ∂volume ≤ M := by
    have hcontract := eLpNorm_one_dyadicAverage_le hgMem1 m
    rw [eLpNorm_one_eq_lintegral_enorm
      (measurable_dyadicAverage m g).aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm hgInt.aestronglyMeasurable] at hcontract
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hAvgInt m),
      ← ofReal_integral_norm_eq_lintegral_enorm hgInt] at hcontract
    apply (ENNReal.ofReal_le_ofReal_iff hM).mp
    exact hcontract
  have hEnergyBound (m : ℤ) :
      ∫ x, ‖dyadicAverage m g x‖ ^ p ∂volume ≤
        (B m) ^ (p - 1) * M := by
    have hpoint (x : ℝ) : ‖dyadicAverage m g x‖ ^ p ≤
        (B m) ^ (p - 1) * ‖dyadicAverage m g x‖ := by
      let y := ‖dyadicAverage m g x‖
      have hy : 0 ≤ y := norm_nonneg _
      have hyB : y ≤ B m := by
        simpa [B, M, y] using norm_dyadicAverage_le_inv_scale_mul_integral_norm hgInt m x
      have hyPow : y ^ (p - 1) ≤ (B m) ^ (p - 1) :=
        Real.rpow_le_rpow hy hyB (by linarith)
      have hsplit : y ^ p = y ^ (p - 1) * y := by
        calc
          y ^ p = y ^ ((p - 1) + 1) := by congr 1; ring
          _ = y ^ (p - 1) * y ^ (1 : ℝ) :=
            Real.rpow_add_of_nonneg hy (by linarith) (by norm_num)
          _ = y ^ (p - 1) * y := by rw [Real.rpow_one]
      calc
        ‖dyadicAverage m g x‖ ^ p = y ^ p := rfl
        _ = y ^ (p - 1) * y := hsplit
        _ ≤ (B m) ^ (p - 1) * y :=
          mul_le_mul_of_nonneg_right hyPow hy
    have hmajorInt : Integrable
        (fun x => (B m) ^ (p - 1) * ‖dyadicAverage m g x‖) volume := by
      simpa [mul_comm] using (hAvgInt m).norm.const_mul ((B m) ^ (p - 1))
    calc
      ∫ x, ‖dyadicAverage m g x‖ ^ p ∂volume ≤
          ∫ x, (B m) ^ (p - 1) * ‖dyadicAverage m g x‖ ∂volume :=
        integral_mono_ae (hAvgPowInt m) hmajorInt
          (Filter.Eventually.of_forall hpoint)
      _ = (B m) ^ (p - 1) * ∫ x, ‖dyadicAverage m g x‖ ∂volume := by
        rw [integral_const_mul]
      _ ≤ (B m) ^ (p - 1) * M :=
        mul_le_mul_of_nonneg_left (hL1 m)
          (Real.rpow_nonneg (hBnonneg m) (p - 1))
  have hInv : Tendsto (fun m : ℤ => ((2 : ℝ) ^ m)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_two_zpow_atTop
  have hBtendsto : Tendsto B atTop (𝓝 0) := by
    simpa [B, M, mul_comm] using hInv.const_mul M
  have hBpow : Tendsto (fun m : ℤ => (B m) ^ (p - 1)) atTop (𝓝 0) := by
    change Tendsto ((fun x : ℝ => x ^ (p - 1)) ∘ B) atTop (𝓝 0)
    simpa [Real.zero_rpow (ne_of_gt hpminus)] using
      (Real.continuous_rpow_const (le_of_lt hpminus)).continuousAt.tendsto.comp hBtendsto
  have hEnergyTendsto :
      Tendsto (fun m : ℤ => ∫ x, ‖dyadicAverage m g x‖ ^ p ∂volume)
        atTop (𝓝 0) := by
    have hbound : Tendsto (fun m : ℤ => (B m) ^ (p - 1) * M) atTop (𝓝 0) := by
      simpa [mul_comm] using hBpow.const_mul M
    have hnonneg (m : ℤ) :
        0 ≤ ∫ x, ‖dyadicAverage m g x‖ ^ p ∂volume :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (norm_nonneg _) p)
    refine squeeze_zero' (Filter.Eventually.of_forall hnonneg) ?_ hbound
    filter_upwards [] with m
    exact hEnergyBound m
  have hroot : Tendsto (fun y : ℝ => y ^ p⁻¹) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow (ne_of_gt (inv_pos.mpr hp0))] using
      ((Real.continuous_rpow_const (by positivity : 0 ≤ p⁻¹)).continuousAt
        (x := (0 : ℝ))).tendsto
  have hLp : Tendsto
      (fun m : ℤ => (∫ x, ‖dyadicAverage m g x‖ ^ p ∂volume) ^ p⁻¹)
      atTop (𝓝 0) := hroot.comp hEnergyTendsto
  have hnorm (m : ℤ) :
      lpNorm (dyadicAverage m g) (ENNReal.ofReal p) volume =
        (∫ x, ‖dyadicAverage m g x‖ ^ p ∂volume) ^ p⁻¹ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal hq0 hqtop
      (measurable_dyadicAverage m g).aestronglyMeasurable, htoReal]
  exact Tendsto.congr' (Filter.Eventually.of_forall fun m => (hnorm m).symm) hLp

/-- Dyadic averaging is linear on differences of finite-`p` inputs for
`p ≥ 1`. -/
theorem dyadicAverage_sub_of_memLp_finite {f g : ℝ → ℂ} {p : ℝ}
    (hp : 1 ≤ p) (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal p) volume) (m : ℤ) (x : ℝ) :
    dyadicAverage m (f - g) x = dyadicAverage m f x - dyadicAverage m g x := by
  let Q := dyadicInterval m (dyadicIntervalIndex m x)
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hfinite : volume Q ≠ ⊤ := by
    dsimp [Q, dyadicInterval]
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (volume.restrict Q) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hfinite
  have hpq : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hfQ : Integrable f (volume.restrict Q) :=
    (hf.restrict Q).integrable hpq
  have hgQ : Integrable g (volume.restrict Q) :=
    (hg.restrict Q).integrable hpq
  unfold dyadicAverage
  simp only [Pi.sub_apply]
  rw [integral_sub hfQ hgQ]
  simp [smul_sub, Q]

/-- The coarse average of an arbitrary finite-`p` input is bounded by its
approximation error plus the coarse average of the approximant. -/
theorem lpNorm_dyadicAverage_le_of_memLp_finite {f g : ℝ → ℂ} {p : ℝ}
    (hp : 1 ≤ p) (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal p) volume) (m : ℤ) :
    lpNorm (dyadicAverage m f) (ENNReal.ofReal p) volume ≤
      lpNorm (f - g) (ENNReal.ofReal p) volume +
        lpNorm (dyadicAverage m g) (ENNReal.ofReal p) volume := by
  have hpq : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hfg : MemLp (f - g) (ENNReal.ofReal p) volume := hf.sub hg
  have hEfg : MemLp (dyadicAverage m (f - g)) (ENNReal.ofReal p) volume := by
    apply memLp_iff.mpr
    exact (eLpNorm_finite_dyadicAverage_le hfg hp m).trans_lt hfg.eLpNorm_lt_top
  have hEg : MemLp (dyadicAverage m g) (ENNReal.ofReal p) volume := by
    apply memLp_iff.mpr
    exact (eLpNorm_finite_dyadicAverage_le hg hp m).trans_lt hg.eLpNorm_lt_top
  have hidentity : dyadicAverage m f = dyadicAverage m (f - g) + dyadicAverage m g := by
    funext x
    have h := dyadicAverage_sub_of_memLp_finite hp hf hg m x
    simp only [Pi.add_apply]
    rw [h]
    ring
  have hcontract :
      lpNorm (dyadicAverage m (f - g)) (ENNReal.ofReal p) volume ≤
        lpNorm (f - g) (ENNReal.ofReal p) volume := by
    change ENNReal.toReal
        (eLpNorm (dyadicAverage m (f - g)) (ENNReal.ofReal p) volume) ≤
      ENNReal.toReal (eLpNorm (f - g) (ENNReal.ofReal p) volume)
    exact ENNReal.toReal_mono hfg.eLpNorm_ne_top
      (eLpNorm_finite_dyadicAverage_le hfg hp m)
  rw [hidentity]
  calc
    lpNorm (dyadicAverage m (f - g) + dyadicAverage m g) (ENNReal.ofReal p) volume ≤
        lpNorm (dyadicAverage m (f - g)) (ENNReal.ofReal p) volume +
          lpNorm (dyadicAverage m g) (ENNReal.ofReal p) volume :=
      lpNorm_add_le hEfg hpq
    _ ≤ lpNorm (f - g) (ENNReal.ofReal p) volume +
          lpNorm (dyadicAverage m g) (ENNReal.ofReal p) volume := by
      exact add_le_add hcontract le_rfl

/-- Coarse averages converge strongly to zero in every finite real `Lᵖ` with
`p > 1`; density extends the integrable compact-support estimate. -/
theorem dyadicAverage_lpNorm_tendsto_atTop_zero_finite {f : ℝ → ℂ}
    {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto (fun m : ℤ => lpNorm (dyadicAverage m f) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδne : ENNReal.ofReal δ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hδ
  obtain ⟨g, hgSupport, herror, hgContinuous, hgMem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hδne
  have happrox : lpNorm (f - g) (ENNReal.ofReal p) volume ≤ δ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top herror
    rw [toReal_eLpNorm, ENNReal.toReal_ofReal hδ.le] at h
    exact h
  have hgInt : Integrable g volume :=
    hgContinuous.integrable_of_hasCompactSupport hgSupport
  have hG : Tendsto
      (fun m : ℤ => lpNorm (dyadicAverage m g) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) :=
    dyadicAverage_lpNorm_tendsto_atTop_zero_finite_of_integrable hp hgInt hgMem
  have hGevent : ∀ᶠ m : ℤ in atTop,
      lpNorm (dyadicAverage m g) (ENNReal.ofReal p) volume < δ := by
    filter_upwards [(Metric.tendsto_nhds.mp hG) δ hδ] with m hm
    have hnonneg : 0 ≤ lpNorm (dyadicAverage m g) (ENNReal.ofReal p) volume :=
      lpNorm_nonneg
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hm
  filter_upwards [hGevent] with m hm
  have hnonneg : 0 ≤ lpNorm (dyadicAverage m f) (ENNReal.ofReal p) volume :=
    lpNorm_nonneg
  have hlt : lpNorm (dyadicAverage m f) (ENNReal.ofReal p) volume < ε := calc
    lpNorm (dyadicAverage m f) (ENNReal.ofReal p) volume ≤
        lpNorm (f - g) (ENNReal.ofReal p) volume +
          lpNorm (dyadicAverage m g) (ENNReal.ofReal p) volume :=
      lpNorm_dyadicAverage_le_of_memLp_finite (le_of_lt hp) hf hgMem m
    _ ≤ δ + lpNorm (dyadicAverage m g) (ENNReal.ofReal p) volume :=
      add_le_add happrox le_rfl
    _ < δ + δ := by nlinarith
    _ < ε := by dsimp [δ]; linarith
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hlt

/-- The `L²` approximation error after averaging is controlled by the input
approximation error, the averaged approximant error, and the original input
approximation error. -/
theorem lpNorm_dyadicAverage_sub_le_of_memLp_two {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (m : ℤ) :
    lpNorm (dyadicAverage m f - f) 2 volume ≤
      lpNorm (f - g) 2 volume + lpNorm (dyadicAverage m g - g) 2 volume +
        lpNorm (f - g) 2 volume := by
  have hEf : MemLp (dyadicAverage m f) 2 volume :=
    memLp_dyadicAverage_two_of_memLp hf m
  have hEg : MemLp (dyadicAverage m g) 2 volume :=
    memLp_dyadicAverage_two_of_memLp hg m
  have hfg : MemLp (f - g) 2 volume := hf.sub hg
  have hEcontract :
      eLpNorm (dyadicAverage m f - dyadicAverage m g) 2 volume ≤
        eLpNorm (f - g) 2 volume :=
    eLpNorm_dyadicAverage_sub_le_of_memLp_two hf hg m
  have hcontract :
      lpNorm (dyadicAverage m f - dyadicAverage m g) 2 volume ≤
        lpNorm (f - g) 2 volume := by
    change ENNReal.toReal
        (eLpNorm (dyadicAverage m f - dyadicAverage m g) 2 volume) ≤
      ENNReal.toReal (eLpNorm (f - g) 2 volume)
    exact ENNReal.toReal_mono hfg.eLpNorm_ne_top hEcontract
  have hinner :
      lpNorm (dyadicAverage m g - f) 2 volume ≤
        lpNorm (dyadicAverage m g - g) 2 volume + lpNorm (g - f) 2 volume :=
    lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub
      (f := dyadicAverage m g) (g := g) (h := f) hEg hg (by norm_num)
  calc
    lpNorm (dyadicAverage m f - f) 2 volume ≤
        lpNorm (dyadicAverage m f - dyadicAverage m g) 2 volume +
          lpNorm (dyadicAverage m g - f) 2 volume :=
      lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub
        (f := dyadicAverage m f) (g := dyadicAverage m g) (h := f)
        hEf hEg (by norm_num)
    _ ≤ lpNorm (dyadicAverage m f - dyadicAverage m g) 2 volume +
          (lpNorm (dyadicAverage m g - g) 2 volume + lpNorm (g - f) 2 volume) := by
      exact add_le_add le_rfl hinner
    _ ≤ lpNorm (f - g) 2 volume + lpNorm (dyadicAverage m g - g) 2 volume +
          lpNorm (g - f) 2 volume := by
      calc
        lpNorm (dyadicAverage m f - dyadicAverage m g) 2 volume +
            (lpNorm (dyadicAverage m g - g) 2 volume + lpNorm (g - f) 2 volume) =
            (lpNorm (dyadicAverage m f - dyadicAverage m g) 2 volume +
              lpNorm (dyadicAverage m g - g) 2 volume) + lpNorm (g - f) 2 volume := by
          rw [add_assoc]
        _ ≤ (lpNorm (f - g) 2 volume +
              lpNorm (dyadicAverage m g - g) 2 volume) + lpNorm (g - f) 2 volume := by
          nlinarith [hcontract]
        _ = lpNorm (f - g) 2 volume + lpNorm (dyadicAverage m g - g) 2 volume +
            lpNorm (g - f) 2 volume := rfl
    _ = lpNorm (f - g) 2 volume + lpNorm (dyadicAverage m g - g) 2 volume +
          lpNorm (f - g) 2 volume := by
      rw [lpNorm_sub_comm g f 2 volume]

/-- The same three-term `Lᵖ` approximation estimate for every finite real
`p ≥ 1`. -/
theorem lpNorm_dyadicAverage_sub_le_of_memLp_finite {f g : ℝ → ℂ}
    {p : ℝ} (hp : 1 ≤ p) (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal p) volume) (m : ℤ) :
    lpNorm (dyadicAverage m f - f) (ENNReal.ofReal p) volume ≤
      lpNorm (f - g) (ENNReal.ofReal p) volume +
        lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume +
          lpNorm (f - g) (ENNReal.ofReal p) volume := by
  have hpq : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hEf : MemLp (dyadicAverage m f) (ENNReal.ofReal p) volume := by
    apply memLp_iff.mpr
    exact (eLpNorm_finite_dyadicAverage_le hf hp m).trans_lt hf.eLpNorm_lt_top
  have hEg : MemLp (dyadicAverage m g) (ENNReal.ofReal p) volume := by
    apply memLp_iff.mpr
    exact (eLpNorm_finite_dyadicAverage_le hg hp m).trans_lt hg.eLpNorm_lt_top
  have hfg : MemLp (f - g) (ENNReal.ofReal p) volume := hf.sub hg
  have hlinear : dyadicAverage m f - dyadicAverage m g = dyadicAverage m (f - g) := by
    funext x
    exact (dyadicAverage_sub_of_memLp_finite hp hf hg m x).symm
  have hEcontract :
      eLpNorm (dyadicAverage m f - dyadicAverage m g) (ENNReal.ofReal p) volume ≤
        eLpNorm (f - g) (ENNReal.ofReal p) volume := by
    rw [hlinear]
    exact eLpNorm_finite_dyadicAverage_le hfg hp m
  have hcontract :
      lpNorm (dyadicAverage m f - dyadicAverage m g) (ENNReal.ofReal p) volume ≤
        lpNorm (f - g) (ENNReal.ofReal p) volume := by
    change ENNReal.toReal
        (eLpNorm (dyadicAverage m f - dyadicAverage m g) (ENNReal.ofReal p) volume) ≤
      ENNReal.toReal (eLpNorm (f - g) (ENNReal.ofReal p) volume)
    exact ENNReal.toReal_mono hfg.eLpNorm_ne_top
      hEcontract
  have hinner :
      lpNorm (dyadicAverage m g - f) (ENNReal.ofReal p) volume ≤
        lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume +
          lpNorm (g - f) (ENNReal.ofReal p) volume :=
    lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub
      (f := dyadicAverage m g) (g := g) (h := f) hEg hg hpq
  calc
    lpNorm (dyadicAverage m f - f) (ENNReal.ofReal p) volume ≤
        lpNorm (dyadicAverage m f - dyadicAverage m g) (ENNReal.ofReal p) volume +
          lpNorm (dyadicAverage m g - f) (ENNReal.ofReal p) volume :=
      lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub
        (f := dyadicAverage m f) (g := dyadicAverage m g) (h := f) hEf hEg hpq
    _ ≤ lpNorm (dyadicAverage m f - dyadicAverage m g) (ENNReal.ofReal p) volume +
          (lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume +
            lpNorm (g - f) (ENNReal.ofReal p) volume) := by
      exact add_le_add le_rfl hinner
    _ ≤ lpNorm (f - g) (ENNReal.ofReal p) volume +
          lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume +
            lpNorm (g - f) (ENNReal.ofReal p) volume := by
      calc
        lpNorm (dyadicAverage m f - dyadicAverage m g) (ENNReal.ofReal p) volume +
            (lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume +
              lpNorm (g - f) (ENNReal.ofReal p) volume) =
            (lpNorm (dyadicAverage m f - dyadicAverage m g) (ENNReal.ofReal p) volume +
              lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume) +
                lpNorm (g - f) (ENNReal.ofReal p) volume := by rw [add_assoc]
        _ ≤ (lpNorm (f - g) (ENNReal.ofReal p) volume +
              lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume) +
                lpNorm (g - f) (ENNReal.ofReal p) volume := by
          nlinarith [hcontract]
        _ = lpNorm (f - g) (ENNReal.ofReal p) volume +
              lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume +
                lpNorm (g - f) (ENNReal.ofReal p) volume := rfl
    _ = lpNorm (f - g) (ENNReal.ofReal p) volume +
          lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume +
            lpNorm (f - g) (ENNReal.ofReal p) volume := by
      rw [lpNorm_sub_comm g f (ENNReal.ofReal p) volume]

/-- Fine-scale averages converge in every finite real `Lᵖ`, `p ≥ 1`, for
arbitrary `Lᵖ` inputs. Density of continuous compactly supported inputs and
the finite-`p` contraction reduce the assertion to the compact-support case. -/
theorem dyadicAverage_lpNorm_sub_tendsto_atBot_zero_finite {f : ℝ → ℂ}
    {p : ℝ} (hp : 1 ≤ p) (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto (fun m : ℤ =>
      lpNorm (dyadicAverage m f - f) (ENNReal.ofReal p) volume)
      atBot (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδne : ENNReal.ofReal δ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hδ
  obtain ⟨g, hgSupport, herror, hgContinuous, hgMem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hδne
  have happrox : lpNorm (f - g) (ENNReal.ofReal p) volume ≤ δ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top herror
    rw [toReal_eLpNorm, ENNReal.toReal_ofReal hδ.le] at h
    exact h
  have hG : Tendsto
      (fun m : ℤ => lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume)
      atBot (𝓝 0) :=
    dyadicAverage_lpNorm_sub_tendsto_atBot_zero_finite_of_continuous_hasCompactSupport
      hp hgContinuous hgSupport hgMem
  have hGevent : ∀ᶠ m : ℤ in atBot,
      lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume < δ := by
    filter_upwards [(Metric.tendsto_nhds.mp hG) δ hδ] with m hm
    have hnonneg :
        0 ≤ lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume := lpNorm_nonneg
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hm
  filter_upwards [hGevent] with m hm
  have hnonneg :
      0 ≤ lpNorm (dyadicAverage m f - f) (ENNReal.ofReal p) volume := lpNorm_nonneg
  have hlt : lpNorm (dyadicAverage m f - f) (ENNReal.ofReal p) volume < ε := calc
    lpNorm (dyadicAverage m f - f) (ENNReal.ofReal p) volume ≤
        lpNorm (f - g) (ENNReal.ofReal p) volume +
          lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume +
            lpNorm (f - g) (ENNReal.ofReal p) volume :=
      lpNorm_dyadicAverage_sub_le_of_memLp_finite hp hf hgMem m
    _ ≤ δ + lpNorm (dyadicAverage m g - g) (ENNReal.ofReal p) volume + δ := by
      gcongr
    _ < δ + δ + δ := by nlinarith
    _ < ε := by dsimp [δ]; linarith
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hlt

/-- Fine-scale dyadic averages converge strongly in `L²` for every `L²`
input. Density of continuous compactly supported functions and the `L²`
contraction extend the compact-support result. -/
theorem dyadicAverage_lpNorm_sub_tendsto_atBot_zero {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    Tendsto (fun m : ℤ => lpNorm (dyadicAverage m f - f) 2 volume)
      atBot (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδne : ENNReal.ofReal δ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hδ
  obtain ⟨g, hgSupport, herror, hgContinuous, hgMem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hδne
  have happrox : lpNorm (f - g) 2 volume ≤ δ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top herror
    rw [toReal_eLpNorm, ENNReal.toReal_ofReal hδ.le] at h
    exact h
  have hG : Tendsto
      (fun m : ℤ => lpNorm (dyadicAverage m g - g) 2 volume) atBot (𝓝 0) :=
    dyadicAverage_lpNorm_sub_tendsto_atBot_zero_of_continuous_hasCompactSupport
      hgContinuous hgSupport hgMem
  have hGevent : ∀ᶠ m : ℤ in atBot,
      lpNorm (dyadicAverage m g - g) 2 volume < δ := by
    filter_upwards [(Metric.tendsto_nhds.mp hG) δ hδ] with m hm
    have hnonneg : 0 ≤ lpNorm (dyadicAverage m g - g) 2 volume := lpNorm_nonneg
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hm
  filter_upwards [hGevent] with m hm
  have hnonneg : 0 ≤ lpNorm (dyadicAverage m f - f) 2 volume := lpNorm_nonneg
  have hlt : lpNorm (dyadicAverage m f - f) 2 volume < ε := calc
    lpNorm (dyadicAverage m f - f) 2 volume ≤
        lpNorm (f - g) 2 volume + lpNorm (dyadicAverage m g - g) 2 volume +
          lpNorm (f - g) 2 volume :=
      lpNorm_dyadicAverage_sub_le_of_memLp_two hf hgMem m
    _ ≤ δ + lpNorm (dyadicAverage m g - g) 2 volume + δ := by
      gcongr
    _ < δ + δ + δ := by nlinarith
    _ < ε := by dsimp [δ]; linarith
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hlt

private theorem tendsto_dyadicRadius_atBot :
    Tendsto (fun m : ℤ => (2 : ℝ) ^ (m - 1)) atBot (𝓝[>] (0 : ℝ)) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have htoNat : Tendsto (fun m : ℤ => (-m).toNat) atBot atTop := by
    rw [Filter.tendsto_atTop]
    intro n
    filter_upwards [Filter.eventually_atBot.2 ⟨-(n : ℤ), by intro m hm; omega⟩]
      with m hm
    have hmcast : (((-m).toNat : ℕ) : ℤ) = -m :=
      Int.toNat_of_nonneg (by omega)
    have hle : (n : ℤ) ≤ (-m : ℤ) := by omega
    have hleNat : (n : ℤ) ≤ (((-m).toNat : ℕ) : ℤ) := by
      rw [hmcast]
      exact hle
    exact_mod_cast hleNat
  have htoNatPlus : Tendsto (fun m : ℤ => (-m).toNat + 1) atBot atTop := by
    rw [Filter.tendsto_atTop]
    intro n
    filter_upwards [(Filter.tendsto_atTop.1 htoNat) n] with m hm
    omega
  have hpow' : Tendsto (fun m : ℤ => (1 / 2 : ℝ) ^ ((-m).toNat + 1))
      atBot (𝓝 0) := hpow.comp htoNatPlus
  have hEq : (fun m : ℤ => (2 : ℝ) ^ (m - 1)) =ᶠ[atBot]
      fun m => (1 / 2 : ℝ) ^ ((-m).toNat + 1) := by
    filter_upwards [Filter.eventually_atBot.2 ⟨0, fun m hm => hm⟩] with m hm
    have hmcast : (((-m).toNat : ℕ) : ℤ) = -m :=
      Int.toNat_of_nonneg (by omega)
    have hcastplus : (((-m).toNat + 1 : ℕ) : ℤ) = -m + 1 := by
      push_cast
      rw [hmcast]
    have hexp : m - 1 = -(((-m).toNat + 1 : ℕ) : ℤ) := by
      rw [hcastplus]
      omega
    calc
      (2 : ℝ) ^ (m - 1) = (2 : ℝ) ^ (-(((-m).toNat + 1 : ℕ) : ℤ)) := by
        rw [hexp]
      _ = (1 / 2 : ℝ) ^ ((-m).toNat + 1) := by
        rw [zpow_neg, zpow_natCast, one_div_pow]
        simp
  have hzero : Tendsto (fun m : ℤ => (2 : ℝ) ^ (m - 1)) atBot (𝓝 0) :=
    Tendsto.congr' hEq.symm hpow'
  refine tendsto_nhdsWithin_iff.mpr ⟨hzero, ?_⟩
  exact Filter.Eventually.of_forall (fun m => zpow_pos (by norm_num) (m - 1))

private theorem dyadicCell_closedBall_eq_Icc (m j : ℤ) :
    Metric.closedBall
        ((j : ℝ) * (2 : ℝ) ^ m + (2 : ℝ) ^ (m - 1))
        ((2 : ℝ) ^ (m - 1)) =
      Set.Icc ((j : ℝ) * (2 : ℝ) ^ m)
        (((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) := by
  have hdouble : 2 * (2 : ℝ) ^ (m - 1) = (2 : ℝ) ^ m := by
    calc
      2 * (2 : ℝ) ^ (m - 1) = (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (m - 1) := by norm_num
      _ = (2 : ℝ) ^ ((1 : ℤ) + (m - 1)) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = (2 : ℝ) ^ m := by congr 1 <;> omega
  rw [Real.closedBall_eq_Icc]
  congr 1
  · ring
  · calc
      ((j : ℝ) * (2 : ℝ) ^ m + (2 : ℝ) ^ (m - 1)) + (2 : ℝ) ^ (m - 1) =
          (j : ℝ) * (2 : ℝ) ^ m + 2 * (2 : ℝ) ^ (m - 1) := by ring
      _ = (j : ℝ) * (2 : ℝ) ^ m + (2 : ℝ) ^ m := by rw [hdouble]
      _ = (((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) := by push_cast; ring

private theorem dyadicAverage_eq_closedBallAverage (f : ℝ → ℂ) (m : ℤ) (x : ℝ) :
    dyadicAverage m f x =
      ⨍ y in Metric.closedBall
        ((dyadicIntervalIndex m x : ℝ) * (2 : ℝ) ^ m + (2 : ℝ) ^ (m - 1))
        ((2 : ℝ) ^ (m - 1)), f y ∂volume := by
  let j := dyadicIntervalIndex m x
  let s := (2 : ℝ) ^ m
  let r := (2 : ℝ) ^ (m - 1)
  let c := (j : ℝ) * s + r
  have hcell : Metric.closedBall c r =
      Set.Icc ((j : ℝ) * s) (((j + 1 : ℤ) : ℝ) * s) := by
    simpa [c, s, r] using dyadicCell_closedBall_eq_Icc m j
  have hInt : ∫ y in Metric.closedBall c r, f y ∂volume =
      ∫ y in dyadicInterval m j, f y ∂volume := by
    rw [hcell, dyadicInterval]
    exact MeasureTheory.integral_Icc_eq_integral_Ico
  have hdouble : 2 * r = s := by
    dsimp [r, s]
    calc
      2 * (2 : ℝ) ^ (m - 1) = (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (m - 1) := by norm_num
      _ = (2 : ℝ) ^ ((1 : ℤ) + (m - 1)) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = (2 : ℝ) ^ m := by congr 1 <;> omega
  have hvol : volume.real (Metric.closedBall c r) = s := by
    dsimp [r, s]
    rw [Real.volume_real_closedBall (a := c) (r := (2 : ℝ) ^ (m - 1))
      (by positivity)]
    exact hdouble
  calc
    dyadicAverage m f x = s⁻¹ • ∫ y in dyadicInterval m j, f y ∂volume := by
      simp [dyadicAverage, j, s]
    _ = (volume.real (Metric.closedBall c r))⁻¹ •
          ∫ y in Metric.closedBall c r, f y ∂volume := by rw [hvol, hInt]
    _ = ⨍ y in Metric.closedBall c r, f y ∂volume :=
      (MeasureTheory.setAverage_eq volume f (Metric.closedBall c r)).symm

/-- Fine-scale dyadic averages converge almost everywhere to an integrable
input. This is the dyadic specialization of the Vitali-family differentiation
theorem, using the centered closed interval with the same endpoints as the
half-open dyadic cell. -/
theorem dyadicAverage_tendsto_atBot_ae_of_integrable {f : ℝ → ℂ}
    (hf : Integrable f volume) :
    ∀ᵐ x ∂volume, Tendsto (fun m : ℤ => dyadicAverage m f x) atBot (𝓝 (f x)) := by
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average
    (μ := volume) (f := f) hf.locallyIntegrable (1 : ℝ)
  filter_upwards [hdiff] with x hx
  let w : ℤ → ℝ := fun m =>
    (dyadicIntervalIndex m x : ℝ) * (2 : ℝ) ^ m + (2 : ℝ) ^ (m - 1)
  let r : ℤ → ℝ := fun m => (2 : ℝ) ^ (m - 1)
  have hr : Tendsto r atBot (𝓝[>] (0 : ℝ)) := by
    simpa [r] using tendsto_dyadicRadius_atBot
  have hball (m : ℤ) : x ∈ Metric.closedBall (w m) (r m) := by
    have hxcell := mem_dyadicIntervalIndex m x
    rw [dyadicInterval, Set.mem_Ico] at hxcell
    rw [dyadicCell_closedBall_eq_Icc]
    exact ⟨hxcell.1, hxcell.2.le⟩
  have hball_event : ∀ᶠ m : ℤ in atBot,
      x ∈ Metric.closedBall (w m) (1 * r m) := by
    filter_upwards [] with m
    simpa using hball m
  have havg := hx w r hr hball_event
  exact Tendsto.congr' (Filter.Eventually.of_forall fun m =>
    (dyadicAverage_eq_closedBallAverage f m x).symm) havg

noncomputable def dyadicDifferenceL2Vector {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (m : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_dyadicDifference_two_of_memLp hf m).toLp (dyadicDifference m f)

private theorem norm_dyadicAverage_toLp_le {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (m : ℤ) :
    ‖(memLp_dyadicAverage_two_of_memLp hf m).toLp (dyadicAverage m f)‖ ≤
      ‖hf.toLp f‖ := by
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_two_dyadicAverage_le hf m)

set_option maxHeartbeats 1000000 in
/-- Every finite sum of squared dyadic-difference norms is bounded by the
global `L²` norm. The proof embeds the finite index set in the consecutive
interval between its minimum and maximum, then applies the finite
Pythagorean identity and the contraction of the endpoint averages. -/
theorem dyadicDifference_sum_sq_le {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (s : Finset ℤ) :
    ∑ m ∈ s, ‖dyadicDifferenceL2Vector hf m‖ ^ 2 ≤ 4 * ‖hf.toLp f‖ ^ 2 := by
  classical
  by_cases hs : s.Nonempty
  · let lo : ℤ := s.min' hs
    let hi : ℤ := s.max' hs
    let n : ℕ := (hi - lo + 1).toNat
    let idx : ℕ → ℤ := fun k => lo - 1 + (k : ℤ) + 1
    have hlohi : lo ≤ hi := by
      have hlo := Finset.min'_le s (s.max' hs) (Finset.max'_mem s hs)
      dsimp [lo, hi] at hlo ⊢
      exact hlo
    have hpositive : 0 < hi - lo + 1 := by omega
    have hncast : (n : ℤ) = hi - lo + 1 := by
      dsimp [n]
      exact Int.toNat_of_nonneg (by omega)
    have hsubset : s ⊆ Finset.image idx (Finset.range n) := by
      intro m hm
      have hmlo : lo ≤ m := by
        dsimp [lo]
        exact Finset.min'_le s m hm
      have hmhi : m ≤ hi := by
        dsimp [hi]
        exact Finset.le_max' s m hm
      have hmd : 0 ≤ m - lo := by omega
      have hmlt : m - lo < hi - lo + 1 := by omega
      have hcast : (((m - lo).toNat : ℕ) : ℤ) = m - lo :=
        Int.toNat_of_nonneg hmd
      have hklt : (m - lo).toNat < n := by
        dsimp [n]
        exact (Int.toNat_lt_toNat hpositive).2 hmlt
      apply Finset.mem_image.mpr
      refine ⟨(m - lo).toNat, Finset.mem_range.mpr hklt, ?_⟩
      dsimp [idx]
      rw [hcast]
      omega
    have hinj : Set.InjOn idx (↑(Finset.range n)) := by
      intro i hi' j hj' hij
      dsimp [idx] at hij
      omega
    have hpyth := dyadicAverage_endpoint_Pythagorean hf (lo - 1) n
    have hpyth' :
        ‖(memLp_dyadicAverage_two_of_memLp hf (lo - 1)).toLp
              (dyadicAverage (lo - 1) f) -
            (memLp_dyadicAverage_two_of_memLp hf (lo - 1 + n)).toLp
              (dyadicAverage (lo - 1 + n) f)‖ ^ 2 =
          ∑ k ∈ Finset.range n, ‖dyadicDifferenceL2Vector hf (idx k)‖ ^ 2 := by
      simpa [dyadicDifferenceL2Vector, idx] using hpyth
    have hleft := norm_dyadicAverage_toLp_le hf (lo - 1)
    have hright := norm_dyadicAverage_toLp_le hf (lo - 1 + n)
    have hendpoint :
        ‖(memLp_dyadicAverage_two_of_memLp hf (lo - 1)).toLp
              (dyadicAverage (lo - 1) f) -
            (memLp_dyadicAverage_two_of_memLp hf (lo - 1 + n)).toLp
              (dyadicAverage (lo - 1 + n) f)‖ ^ 2 ≤ 4 * ‖hf.toLp f‖ ^ 2 := by
      have hnorm := norm_sub_le
        ((memLp_dyadicAverage_two_of_memLp hf (lo - 1)).toLp
          (dyadicAverage (lo - 1) f))
        ((memLp_dyadicAverage_two_of_memLp hf (lo - 1 + n)).toLp
          (dyadicAverage (lo - 1 + n) f))
      have hsum :
          ‖(memLp_dyadicAverage_two_of_memLp hf (lo - 1)).toLp
                (dyadicAverage (lo - 1) f) -
              (memLp_dyadicAverage_two_of_memLp hf (lo - 1 + n)).toLp
                (dyadicAverage (lo - 1 + n) f)‖ ≤ 2 * ‖hf.toLp f‖ := by
        linarith [add_le_add hleft hright]
      have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hsum
      nlinarith
    calc
      ∑ m ∈ s, ‖dyadicDifferenceL2Vector hf m‖ ^ 2 ≤
          ∑ m ∈ Finset.image idx (Finset.range n),
            ‖dyadicDifferenceL2Vector hf m‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro m hm hnot
        positivity
      _ = ∑ k ∈ Finset.range n, ‖dyadicDifferenceL2Vector hf (idx k)‖ ^ 2 :=
        Finset.sum_image hinj
      _ ≤ 4 * ‖hf.toLp f‖ ^ 2 := by
        rw [← hpyth']
        exact hendpoint
  · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hsempty]

private theorem dyadicDifferenceL2Vector_inner_eq_zero {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) {m n : ℤ} (hmn : m ≠ n) :
    inner ℂ (dyadicDifferenceL2Vector hf m) (dyadicDifferenceL2Vector hf n) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  change ∫ x, dyadicDifferenceL2Vector hf n x *
      star (dyadicDifferenceL2Vector hf m x) ∂volume = 0
  have hzero := dyadicDifference_pairwise_orthogonal hf hf hmn.symm
  calc
    ∫ x, dyadicDifferenceL2Vector hf n x *
        star (dyadicDifferenceL2Vector hf m x) ∂volume =
      ∫ x, dyadicDifference n f x * star (dyadicDifference m f x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [
          (memLp_dyadicDifference_two_of_memLp hf n).coeFn_toLp,
          (memLp_dyadicDifference_two_of_memLp hf m).coeFn_toLp] with x hn hm
        simp [dyadicDifferenceL2Vector, hn, hm]
    _ = 0 := hzero

theorem dyadicDifferenceL2_square_summable {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    Summable (fun m : ℤ => ‖dyadicDifferenceL2Vector hf m‖ ^ 2) := by
  apply summable_of_sum_le (f := fun m : ℤ =>
    ‖dyadicDifferenceL2Vector hf m‖ ^ 2)
  · intro m
    positivity
  · intro s
    exact dyadicDifference_sum_sq_le hf s

theorem dyadicDifferenceL2Vector_summable {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    Summable (fun m : ℤ => dyadicDifferenceL2Vector hf m) := by
  classical
  let V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) := fun m =>
    ℂ ∙ dyadicDifferenceL2Vector hf m
  let v : (m : ℤ) → V m := fun m =>
    ⟨dyadicDifferenceL2Vector hf m,
      Submodule.mem_span_singleton_self (dyadicDifferenceL2Vector hf m)⟩
  have hpair : Pairwise (fun m n : ℤ => V m ⟂ V n) := by
    intro m n hmn
    rw [Submodule.isOrtho_iff_inner_eq]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [inner_smul_left, inner_smul_right,
      dyadicDifferenceL2Vector_inner_eq_zero hf hmn]
  have hfamily : OrthogonalFamily ℂ (fun m => (V m : Type _))
      (fun m => (V m).subtypeₗᵢ) := OrthogonalFamily.of_pairwise hpair
  have hnorm : Summable (fun m : ℤ => ‖v m‖ ^ 2) := by
    simpa [v] using dyadicDifferenceL2_square_summable hf
  have hsum := (hfamily.summable_iff_norm_sq_summable v).2 hnorm
  exact hsum.congr fun m => rfl

theorem dyadicDifferenceL2Vector_finset_Pythagorean {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (s : Finset ℤ) :
    ‖∑ m ∈ s, dyadicDifferenceL2Vector hf m‖ ^ 2 =
      ∑ m ∈ s, ‖dyadicDifferenceL2Vector hf m‖ ^ 2 := by
  classical
  let V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) := fun m =>
    ℂ ∙ dyadicDifferenceL2Vector hf m
  let v : (m : ℤ) → V m := fun m =>
    ⟨dyadicDifferenceL2Vector hf m,
      Submodule.mem_span_singleton_self (dyadicDifferenceL2Vector hf m)⟩
  have hpair : Pairwise (fun m n : ℤ => V m ⟂ V n) := by
    intro m n hmn
    rw [Submodule.isOrtho_iff_inner_eq]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [inner_smul_left, inner_smul_right,
      dyadicDifferenceL2Vector_inner_eq_zero hf hmn]
  have hfamily : OrthogonalFamily ℂ (fun m => (V m : Type _))
      (fun m => (V m).subtypeₗᵢ) := OrthogonalFamily.of_pairwise hpair
  simpa [v] using hfamily.norm_sum v s

theorem dyadicAverage_toLp_tendsto_atBot {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    Tendsto (fun m : ℤ =>
      (memLp_dyadicAverage_two_of_memLp hf m).toLp (dyadicAverage m f))
      atBot (𝓝 (hf.toLp f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm (m : ℤ) :
      ‖(memLp_dyadicAverage_two_of_memLp hf m).toLp (dyadicAverage m f) -
          hf.toLp f‖ = lpNorm (dyadicAverage m f - f) 2 volume := by
    rw [← MemLp.toLp_sub (memLp_dyadicAverage_two_of_memLp hf m) hf]
    calc
      ‖(MemLp.sub (memLp_dyadicAverage_two_of_memLp hf m) hf).toLp
          (dyadicAverage m f - f)‖ =
          ENNReal.toReal (eLpNorm (dyadicAverage m f - f) 2 volume) := Lp.norm_toLp _ _
      _ = lpNorm (dyadicAverage m f - f) 2 volume := toReal_eLpNorm
  exact Tendsto.congr' (Filter.Eventually.of_forall fun m => (hnorm m).symm)
    (dyadicAverage_lpNorm_sub_tendsto_atBot_zero hf)

/-- The first `2N+1` terms of Mathlib's enumeration of `ℤ` are exactly
the symmetric integer interval `[-N,N]`. -/
theorem intEquivNat_oddRange_image (N : ℕ) :
    Finset.image Equiv.intEquivNat.symm (Finset.range (2 * N + 1)) =
      Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  classical
  ext z
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨k, hklt, hz⟩
    by_cases hodd : k.bodd = true
    · have hkdecomp : 1 + 2 * k.div2 = k := by
        simpa [hodd] using Nat.bodd_add_div2 k
      have hd : k.div2 < N := by omega
      have hdc : (k.div2 : ℤ) < N := by exact_mod_cast hd
      have hzeq : z = -((k.div2 : ℤ) + 1) := by
        simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat, hodd] at hz
        omega
      omega
    · have hkdecomp : 0 + 2 * k.div2 = k := by
        simpa [hodd] using Nat.bodd_add_div2 k
      have hd : k.div2 ≤ N := by omega
      have hdc : (k.div2 : ℤ) ≤ N := by exact_mod_cast hd
      have hzeq : z = (k.div2 : ℤ) := by
        simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat, hodd] at hz
        omega
      omega
  · intro hz
    rcases z with z | z
    · have hzN : z ≤ N := Int.ofNat_le.mp hz.2
      refine ⟨2 * z, ?_, ?_⟩
      · omega
      · simpa [Equiv.intEquivNat, Equiv.intEquivNatSumNat]
    · have h : -(N : ℤ) ≤ -((z : ℤ) + 1) := by simpa [Int.negSucc_eq] using hz.1
      have hN : ((z : ℤ) + 1) ≤ N := by linarith
      have hzN : z + 1 ≤ N := by
        apply Int.ofNat_le.mp
        simpa using hN
      refine ⟨2 * z + 1, ?_, ?_⟩
      · omega
      · simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat]

/-- Translating a natural interval to `ℤ` gives the corresponding symmetric
integer interval. -/
theorem intShift_oddRange_image (N : ℕ) :
    Finset.image (fun k : ℕ => -(N : ℤ) + (k : ℤ))
        (Finset.range (2 * N + 1)) = Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  classical
  ext z
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨k, hklt, rfl⟩
    have hkcast : (k : ℤ) < 2 * (N : ℤ) + 1 := by exact_mod_cast hklt
    omega
  · intro hz
    let k := (z + (N : ℤ)).toNat
    have hnonneg : 0 ≤ z + (N : ℤ) := by omega
    have hcast : (k : ℤ) = z + (N : ℤ) := by
      dsimp [k]
      exact Int.toNat_of_nonneg hnonneg
    have hlt : z + (N : ℤ) < 2 * (N : ℤ) + 1 := by omega
    have hklt : k < 2 * N + 1 := by
      dsimp [k]
      exact (Int.toNat_lt_toNat (by omega : 0 < 2 * (N : ℤ) + 1)).2 hlt
    refine ⟨k, hklt, ?_⟩
    dsimp [k]
    rw [hcast]
    omega

/-- The dyadic differences sum unconditionally in `L²` to the original
function. Symmetric finite partial sums telescope to the fine average minus
the coarse average; these converge to `f` and `0`, respectively. -/
theorem dyadicDifferenceL2Vector_hasSum {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    HasSum (fun m : ℤ => dyadicDifferenceL2Vector hf m) (hf.toLp f) := by
  classical
  let e : ℕ ≃ ℤ := Equiv.intEquivNat.symm
  let g : ℕ → Lp ℂ 2 volume := fun k => dyadicDifferenceL2Vector hf (e k)
  let avg : ℤ → Lp ℂ 2 volume := fun m =>
    (memLp_dyadicAverage_two_of_memLp hf m).toLp (dyadicAverage m f)
  have hvecSum : Summable (fun m : ℤ => dyadicDifferenceL2Vector hf m) :=
    dyadicDifferenceL2Vector_summable hf
  have hnatSum : HasSum g (∑' m : ℤ, dyadicDifferenceL2Vector hf m) := by
    change HasSum ((fun m : ℤ => dyadicDifferenceL2Vector hf m) ∘ e) _
    exact e.hasSum_iff.mpr hvecSum.hasSum
  have hpartial := hnatSum.tendsto_sum_nat
  have hindexOdd : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro n
    filter_upwards [Filter.eventually_ge_atTop n] with N hN
    omega
  have hseriesPartial : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1), g k)
      atTop (𝓝 (∑' m : ℤ, dyadicDifferenceL2Vector hf m)) :=
    hpartial.comp hindexOdd
  have hindexFine : Tendsto (fun N : ℕ => -(N : ℤ) - 1) atTop atBot := by
    have hneg : Tendsto (fun N : ℕ => -(N : ℤ)) atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
    simpa [sub_eq_add_neg] using
      Filter.tendsto_atBot_add_const_right atTop (-1 : ℤ) hneg
  have hfine := (dyadicAverage_toLp_tendsto_atBot hf).comp hindexFine
  have hcoarse := (dyadicAverage_toLp_tendsto_atTop_zero hf).comp
    tendsto_natCast_atTop_atTop
  have hlimit : Tendsto (fun N : ℕ => avg (-(N : ℤ) - 1) - avg (N : ℤ))
      atTop (𝓝 (hf.toLp f)) := by
    simpa [avg] using hfine.sub hcoarse
  have htel (N : ℕ) :
      ∑ k ∈ Finset.range (2 * N + 1),
          dyadicDifferenceL2Vector hf (-(N : ℤ) + (k : ℤ)) =
        avg (-(N : ℤ) - 1) - avg (N : ℤ) := by
    dsimp [avg]
    convert (dyadicDifference_finite_sum_eq_average_difference hf
        (-(N : ℤ) - 1) (2 * N + 1)) using 1
    · apply Finset.sum_congr rfl
      intro k hk
      simp only [dyadicDifferenceL2Vector]
      congr 1
      funext x
      congr 1
      omega
    · have hidx : (-(N : ℤ) - 1 + ((2 * N + 1 : ℕ) : ℤ)) = (N : ℤ) := by
        push_cast
        omega
      rw [hidx]
  have hsumEnum (N : ℕ) :
      ∑ k ∈ Finset.range (2 * N + 1), g k =
        ∑ k ∈ Finset.range (2 * N + 1),
          dyadicDifferenceL2Vector hf (-(N : ℤ) + (k : ℤ)) := by
    have heinj : Set.InjOn Equiv.intEquivNat.symm
        (↑(Finset.range (2 * N + 1))) := by
      intro i hi j hj hij
      exact Equiv.intEquivNat.symm.injective hij
    have hsinj : Set.InjOn (fun k : ℕ => -(N : ℤ) + (k : ℤ))
        (↑(Finset.range (2 * N + 1))) := by
      intro i hi j hj hij
      dsimp at hij
      omega
    calc
      ∑ k ∈ Finset.range (2 * N + 1), g k =
          ∑ m ∈ Finset.image Equiv.intEquivNat.symm
              (Finset.range (2 * N + 1)), dyadicDifferenceL2Vector hf m := by
        dsimp [g]
        exact (Finset.sum_image heinj).symm
      _ = ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            dyadicDifferenceL2Vector hf m := by
        rw [intEquivNat_oddRange_image]
      _ = ∑ m ∈ Finset.image (fun k : ℕ => -(N : ℤ) + (k : ℤ))
              (Finset.range (2 * N + 1)), dyadicDifferenceL2Vector hf m := by
        rw [← intShift_oddRange_image]
      _ = ∑ k ∈ Finset.range (2 * N + 1),
            dyadicDifferenceL2Vector hf (-(N : ℤ) + (k : ℤ)) :=
        Finset.sum_image hsinj
  have hseqEq : (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1), g k) =ᶠ[atTop]
      (fun N : ℕ => avg (-(N : ℤ) - 1) - avg (N : ℤ)) :=
    Filter.Eventually.of_forall fun N => (hsumEnum N).trans (htel N)
  have hseriesEndpoint := hseriesPartial.congr' hseqEq
  have hsum_eq : (∑' m : ℤ, dyadicDifferenceL2Vector hf m) = hf.toLp f :=
    tendsto_nhds_unique hseriesEndpoint hlimit
  exact hvecSum.hasSum_iff.mpr hsum_eq

/-- Parseval's identity for the dyadic differences in `L²`. -/
theorem dyadicDifferenceL2Vector_parseval {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    HasSum (fun m : ℤ => ‖dyadicDifferenceL2Vector hf m‖ ^ 2)
      (‖hf.toLp f‖ ^ 2) := by
  classical
  let e : ℕ ≃ ℤ := Equiv.intEquivNat.symm
  let u : ℤ → Lp ℂ 2 volume := fun m => dyadicDifferenceL2Vector hf m
  let q : ℤ → ℝ := fun m => ‖u m‖ ^ 2
  have hsquare : Summable q := by
    simpa [q, u] using dyadicDifferenceL2_square_summable hf
  have hsqNat : HasSum (fun n : ℕ => q (e n)) (∑' m : ℤ, q m) := by
    change HasSum ((fun m : ℤ => q m) ∘ e) _
    exact e.hasSum_iff.mpr hsquare.hasSum
  have hindexOdd : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro n
    filter_upwards [Filter.eventually_ge_atTop n] with N hN
    omega
  have hsqPartial : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1), q (e k))
      atTop (𝓝 (∑' m : ℤ, q m)) :=
    hsqNat.tendsto_sum_nat.comp hindexOdd
  have hvecNat : HasSum (fun n : ℕ => u (e n)) (hf.toLp f) := by
    change HasSum ((fun m : ℤ => u m) ∘ e) _
    exact e.hasSum_iff.mpr (dyadicDifferenceL2Vector_hasSum hf)
  have hvecPartial := hvecNat.tendsto_sum_nat
  have hfinite (n : ℕ) :
      ‖∑ k ∈ Finset.range n, u (e k)‖ ^ 2 =
        ∑ k ∈ Finset.range n, ‖u (e k)‖ ^ 2 := by
    have hinj : Set.InjOn e (↑(Finset.range n)) := by
      intro i hi j hj hij
      exact e.injective hij
    have hP := dyadicDifferenceL2Vector_finset_Pythagorean hf
      (Finset.image e (Finset.range n))
    simpa only [Finset.sum_image hinj] using hP
  have hsqNorm : Tendsto
      (fun N : ℕ => ‖∑ k ∈ Finset.range (2 * N + 1), u (e k)‖ ^ 2)
      atTop (𝓝 (‖hf.toLp f‖ ^ 2)) :=
    hvecPartial.norm.pow 2 |>.comp hindexOdd
  have hEq : (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1), q (e k)) =ᶠ[atTop]
      (fun N : ℕ => ‖∑ k ∈ Finset.range (2 * N + 1), u (e k)‖ ^ 2) :=
    Filter.Eventually.of_forall fun N => (hfinite (2 * N + 1)).symm
  have hsumEq : (∑' m : ℤ, q m) = ‖hf.toLp f‖ ^ 2 :=
    tendsto_nhds_unique (hsqPartial.congr' hEq) hsqNorm
  simpa [q, u] using hsquare.hasSum_iff.mpr hsumEq

/-- The individual assertions in the approved `lj:dyadic-properties`
lemma, stated together so downstream arguments can use the complete
dyadic-average package. -/
structure DyadicAveragePropertyStatements : Prop where
  finite_contraction : ∀ {f : ℝ → ℂ} {p : ℝ}
      (hf : MemLp f (ENNReal.ofReal p) volume) (hp : 1 ≤ p) (m : ℤ),
      eLpNorm (dyadicAverage m f) (ENNReal.ofReal p) volume ≤
        eLpNorm f (ENNReal.ofReal p) volume
  essSup_contraction : ∀ {f : ℝ → ℂ}
      (hf : LocallyIntegrable f volume) (m : ℤ),
      eLpNormEssSup (dyadicAverage m f) volume ≤ eLpNormEssSup f volume
  self_adjoint : ∀ {f g : ℝ → ℂ}
      (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (m : ℤ),
      ∫ x, dyadicAverage m f x * star (g x) ∂volume =
        ∫ x, f x * star (dyadicAverage m g x) ∂volume
  l2_mem : ∀ {f : ℝ → ℂ} (hf : MemLp f 2 volume) (m : ℤ),
      MemLp (dyadicAverage m f) 2 volume
  l2_sub : ∀ {f g : ℝ → ℂ}
      (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (m : ℤ) (x : ℝ),
      dyadicAverage m (f - g) x =
        dyadicAverage m f x - dyadicAverage m g x
  l2_smul : ∀ {f : ℝ → ℂ} (c : ℂ)
      (hf : MemLp f 2 volume) (m : ℤ) (x : ℝ),
      dyadicAverage m (c • f) x = c • dyadicAverage m f x
  nested_composition : ∀ {f : ℝ → ℂ}
      (hf : LocallyIntegrable f volume) (m j : ℤ) (x : ℝ),
      dyadicAverage m (dyadicAverage j f) x =
        dyadicAverage (max m j) f x
  fine_finite_Lp_convergence : ∀ {f : ℝ → ℂ} {p : ℝ}
      (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) volume),
      Tendsto (fun m : ℤ =>
        lpNorm (dyadicAverage m f - f) (ENNReal.ofReal p) volume)
        atBot (𝓝 0)
  coarse_finite_Lp_convergence : ∀ {f : ℝ → ℂ} {p : ℝ}
      (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) volume),
      Tendsto (fun m : ℤ =>
        lpNorm (dyadicAverage m f) (ENNReal.ofReal p) volume)
        atTop (𝓝 0)
  fine_ae_convergence : ∀ {f : ℝ → ℂ} (hf : Integrable f volume),
      ∀ᵐ x ∂volume,
        Tendsto (fun m : ℤ => dyadicAverage m f x) atBot (𝓝 (f x))
  l2_expansion : ∀ {f : ℝ → ℂ} (hf : MemLp f 2 volume),
      HasSum (fun m : ℤ => dyadicDifferenceL2Vector hf m) (hf.toLp f)
  l2_parseval : ∀ {f : ℝ → ℂ} (hf : MemLp f 2 volume),
      HasSum (fun m : ℤ => ‖dyadicDifferenceL2Vector hf m‖ ^ 2)
        (‖hf.toLp f‖ ^ 2)
  fine_cell_constancy : ∀ (m j : ℤ) (f : ℝ → ℂ) {x y : ℝ},
      x ∈ dyadicInterval (m - 1) j → y ∈ dyadicInterval (m - 1) j →
        dyadicDifference m f x = dyadicDifference m f y
  coarse_cell_cancellation : ∀ {f : ℝ → ℂ}
      (hf : LocallyIntegrable f volume) (m j : ℤ),
      ∫ x in dyadicInterval m j, dyadicDifference m f x ∂volume = 0

/-- Dyadic averages are contractive, self-adjoint projections with the
nested-scale identity and the fine/coarse convergence, orthogonal expansion,
Parseval identity, and cell properties of `lj:dyadic-properties`. -/
theorem dyadicAverageProperties : DyadicAveragePropertyStatements := by
  constructor
  · exact fun hf hp m => eLpNorm_finite_dyadicAverage_le hf hp m
  · exact fun hf m => eLpNormEssSup_dyadicAverage_le hf m
  · exact fun hf hg m => dyadicAverage_selfAdjoint hf hg m
  · exact fun hf m => memLp_dyadicAverage_two_of_memLp hf m
  · exact fun hf hg m x => dyadicAverage_sub_of_memLp_two hf hg m x
  · exact fun c hf m x => dyadicAverage_smul_of_memLp_two c hf m x
  · exact fun hf m j x => dyadicAverage_comp hf x
  · exact fun hp hf => dyadicAverage_lpNorm_sub_tendsto_atBot_zero_finite
      (le_of_lt hp) hf
  · exact fun hp hf => dyadicAverage_lpNorm_tendsto_atTop_zero_finite hp hf
  · exact fun hf => dyadicAverage_tendsto_atBot_ae_of_integrable hf
  · exact fun hf => dyadicDifferenceL2Vector_hasSum hf
  · exact fun hf => dyadicDifferenceL2Vector_parseval hf
  · intro m j f x y hx hy
    exact dyadicDifference_eq_of_mem_same_fine_cell m j f hx hy
  · exact fun hf m j => dyadicDifference_integral_eq_zero hf m j

#print axioms dyadicDifference_finite_Pythagorean
#print axioms dyadicAverage_endpoint_Pythagorean
#print axioms dyadicDifference_sum_sq_le
#print axioms dyadicDifferenceL2_square_summable
#print axioms dyadicDifferenceL2Vector_summable
#print axioms dyadicDifferenceL2Vector_finset_Pythagorean
#print axioms dyadicAverage_toLp_tendsto_atBot
#print axioms dyadicDifferenceL2Vector_hasSum
#print axioms dyadicDifferenceL2Vector_parseval
#print axioms integral_sq_dyadicAverage_tendsto_atTop_zero
#print axioms dyadicAverage_lpNorm_tendsto_atTop_zero
#print axioms dyadicAverage_toLp_tendsto_atTop_zero
#print axioms dyadicAverage_uniform_error_tendsto_atBot_of_uniformContinuous
#print axioms dyadicAverage_lpNorm_sub_tendsto_atBot_zero_of_continuous_hasCompactSupport
#print axioms dyadicAverage_lpNorm_sub_tendsto_atBot_zero
#print axioms dyadicAverage_lpNorm_sub_tendsto_atBot_zero_finite
#print axioms dyadicAverage_lpNorm_tendsto_atTop_zero_finite_of_integrable
#print axioms dyadicAverage_lpNorm_tendsto_atTop_zero_finite
#print axioms dyadicAverage_tendsto_atBot_ae_of_integrable
#print axioms dyadicAverageProperties

end

end FractionalPrimes.Literature.JSW

end
