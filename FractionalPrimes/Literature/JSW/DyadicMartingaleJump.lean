module

public import FractionalPrimes.Literature.JSW.PredictableTransformBound
public import FractionalPrimes.Literature.JSW.FiniteSignSquareLpBound
public import FractionalPrimes.Literature.Variation.GreedyStopRunExistence
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Dyadic martingale jumps

This file follows `lj:martingale-jump` in `expanded-blueprint.tex:3858–3898`
and the final Astra source `blueprint-sources 2/literature-expansion/sections/jsw.tex:569–609`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open FractionalPrimes.Literature.Variation

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The coordinate signs represented by the recursive finite product
`jswSignSpace`. -/
def jswSignCoordinate : (n : ℕ) → jswSignSpace n → Fin n → ℝ
  | 0, _, i => Fin.elim0 i
  | n + 1, (b, ω), i =>
      Fin.cases (jswSign b) (fun j => jswSignCoordinate n ω j) i

theorem jswSignSum_eq_sum_signCoordinate (n : ℕ) (ω : jswSignSpace n)
    (z : Fin n → ℂ) :
    jswSignSum n ω z = ∑ i, (jswSignCoordinate n ω i : ℂ) * z i := by
  induction n with
  | zero => simp [jswSignSum, jswSignCoordinate]
  | succ n ih =>
      cases ω with
      | mk b ω =>
          rw [jswSignSum]
          simp [jswSignCoordinate, Fin.sum_univ_succ, ih]

theorem jswSignCoordinate_abs_eq_one (n : ℕ) (ω : jswSignSpace n)
    (i : Fin n) : |jswSignCoordinate n ω i| = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases ω with
      | mk b ω =>
          cases i using Fin.cases with
          | zero => cases b <;> simp [jswSignCoordinate, jswSign]
          | succ i => exact ih ω i

/-- Group a finite sequence by a block-label map. -/
def jswGroupedBlocks {M : ℕ} (κ : Fin M → Fin (M + 1))
    (a : Fin M → ℂ) : Fin (M + 1) → ℂ :=
  fun i => ∑ t : Fin M, if κ t = i then a t else 0

/-- Signing grouped block increments is the same as assigning each original
increment the sign of its block. -/
theorem jswSignSum_groupedBlocks {M : ℕ} (ω : jswSignSpace (M + 1))
    (κ : Fin M → Fin (M + 1)) (a : Fin M → ℂ) :
    jswSignSum (M + 1) ω (jswGroupedBlocks κ a) =
      ∑ t : Fin M, (jswSignCoordinate (M + 1) ω (κ t) : ℂ) * a t := by
  classical
  rw [jswSignSum_eq_sum_signCoordinate]
  simp_rw [jswGroupedBlocks, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [eq_comm, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem dyadicInterval_parent_subset_jump (m j : ℤ) :
    dyadicInterval m j ⊆ dyadicInterval (m + 1) (j / 2) := by
  have hchildren := dyadicInterval_eq_two_children (m + 1) (j / 2)
  have hchildren' : dyadicInterval (m + 1) (j / 2) =
      dyadicInterval m (2 * (j / 2)) ∪ dyadicInterval m (2 * (j / 2) + 1) := by
    simpa only [show (m + 1) - 1 = m by omega] using hchildren
  rcases Int.emod_two_eq_zero_or_one j with heven | hodd
  · have hindex : j = 2 * (j / 2) := by omega
    intro x hx
    rw [hchildren']
    left
    rw [hindex] at hx
    exact hx
  · have hindex : j = 2 * (j / 2) + 1 := by omega
    intro x hx
    rw [hchildren']
    right
    rw [hindex] at hx
    exact hx

private theorem dyadicInterval_ancestor_subset_jump (m j : ℤ) (k : ℕ) :
    dyadicInterval m j ⊆
      dyadicInterval (m + (k : ℤ)) (dyadicIntervalAncestor k j) := by
  induction k generalizing m j with
  | zero => simp [dyadicIntervalAncestor]
  | succ k ih =>
      calc
        dyadicInterval m j ⊆ dyadicInterval (m + 1) (j / 2) :=
          dyadicInterval_parent_subset_jump m j
        _ ⊆ dyadicInterval ((m + 1) + (k : ℤ))
            (dyadicIntervalAncestor k (j / 2)) := ih (m := m + 1) (j := j / 2)
        _ = dyadicInterval (m + ((k + 1 : ℕ) : ℤ))
            (dyadicIntervalAncestor (k + 1) j) := by
          simp only [dyadicIntervalAncestor]
          congr 1
          omega

/-- Averages at any coarser scale agree on a finer dyadic cell. -/
theorem dyadicAverage_eq_on_finer_cell {r s j : ℤ} {f : ℝ → ℂ}
    (hrs : r ≤ s) {x y : ℝ}
    (hx : x ∈ dyadicInterval r j) (hy : y ∈ dyadicInterval r j) :
    dyadicAverage s f x = dyadicAverage s f y := by
  let d : ℕ := (s - r).toNat
  have hd : (d : ℤ) = s - r := by
    dsimp [d]
    exact Int.toNat_of_nonneg (by omega)
  have hscale : r + (d : ℤ) = s := by omega
  have hsub : dyadicInterval r j ⊆
      dyadicInterval s (dyadicIntervalAncestor d j) := by
    simpa [hscale] using dyadicInterval_ancestor_subset_jump r j d
  exact dyadicAverage_eq_of_mem_same_cell s (dyadicIntervalAncestor d j) f
    (hsub hx) (hsub hy)

theorem dyadicAverage_eq_of_ae_eq_jump {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) (m : ℤ) (x : ℝ) :
    dyadicAverage m f x = dyadicAverage m g x := by
  let Q := dyadicInterval m (dyadicIntervalIndex m x)
  have hfgQ : f =ᵐ[volume.restrict Q] g := ae_restrict_of_ae hfg
  change ((2 : ℝ) ^ m)⁻¹ • ∫ y in Q, f y ∂volume =
    ((2 : ℝ) ^ m)⁻¹ • ∫ y in Q, g y ∂volume
  rw [integral_congr_ae hfgQ]

private theorem dyadicAverage_add_of_memLp_finite_jump {f g : ℝ → ℂ}
    {p : ℝ} (hp : 1 ≤ p) (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal p) volume) (m : ℤ) (x : ℝ) :
    dyadicAverage m (f + g) x = dyadicAverage m f x + dyadicAverage m g x := by
  have h := dyadicAverage_sub_of_memLp_finite hp (hf.add hg) hg m x
  have h' : dyadicAverage m f x =
      dyadicAverage m (f + g) x - dyadicAverage m g x := by
    simpa only [Pi.add_apply, Pi.sub_apply, add_sub_cancel_right] using h
  calc
    dyadicAverage m (f + g) x =
        (dyadicAverage m (f + g) x - dyadicAverage m g x) +
          dyadicAverage m g x := by abel
    _ = dyadicAverage m f x + dyadicAverage m g x := by rw [h']

private theorem dyadicAverage_smul_of_memLp_finite_jump {f : ℝ → ℂ}
    {p : ℝ} (hp : 1 ≤ p) (hf : MemLp f (ENNReal.ofReal p) volume)
    (c : ℂ) (m : ℤ) (x : ℝ) :
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
  have hpq : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hfQ : Integrable f (volume.restrict Q) :=
    (hf.restrict Q).integrable hpq
  unfold dyadicAverage
  change ((2 : ℝ) ^ m)⁻¹ •
      ∫ y, c * f y ∂(volume.restrict Q) =
    c • (((2 : ℝ) ^ m)⁻¹ • ∫ y, f y ∂(volume.restrict Q))
  rw [integral_const_mul]
  exact smul_comm ((2 : ℝ) ^ m)⁻¹ c _

/-- The pointwise dyadic average induces a complex-linear contraction on every
finite `Lᵖ`, `p>1`. -/
def dyadicAverageLpCLM {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (m : ℤ) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let avg (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :=
    (show MemLp (dyadicAverage m (f : ℝ → ℂ)) (ENNReal.ofReal p) volume from by
      apply memLp_iff.mpr
      exact (eLpNorm_finite_dyadicAverage_le (Lp.memLp f) hp.le m).trans_lt
        (Lp.memLp f).eLpNorm_lt_top).toLp (dyadicAverage m (f : ℝ → ℂ))
  let L : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := {
    toFun := avg
    map_add' := by
      intro f g
      apply Lp.ext
      have hleft := (show MemLp (dyadicAverage m ((f + g : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ))
          (ENNReal.ofReal p) volume from by
          apply memLp_iff.mpr
          exact (eLpNorm_finite_dyadicAverage_le (Lp.memLp (f + g)) hp.le m).trans_lt
            (Lp.memLp (f + g)).eLpNorm_lt_top).coeFn_toLp
      have hf := (show MemLp (dyadicAverage m (f : ℝ → ℂ))
          (ENNReal.ofReal p) volume from by
          apply memLp_iff.mpr
          exact (eLpNorm_finite_dyadicAverage_le (Lp.memLp f) hp.le m).trans_lt
            (Lp.memLp f).eLpNorm_lt_top).coeFn_toLp
      have hg := (show MemLp (dyadicAverage m (g : ℝ → ℂ))
          (ENNReal.ofReal p) volume from by
          apply memLp_iff.mpr
          exact (eLpNorm_finite_dyadicAverage_le (Lp.memLp g) hp.le m).trans_lt
            (Lp.memLp g).eLpNorm_lt_top).coeFn_toLp
      have hout := Lp.coeFn_add (avg f) (avg g)
      have hinput : ((f + g : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) =ᵐ[volume]
          fun x => (f : ℝ → ℂ) x + (g : ℝ → ℂ) x := Lp.coeFn_add f g
      have havg : dyadicAverage m ((f + g : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) =ᵐ[volume]
          fun x => dyadicAverage m (f : ℝ → ℂ) x + dyadicAverage m (g : ℝ → ℂ) x := by
        filter_upwards [] with x
        calc
          dyadicAverage m ((f + g : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) x =
              dyadicAverage m (fun y => (f : ℝ → ℂ) y + (g : ℝ → ℂ) y) x :=
            dyadicAverage_eq_of_ae_eq_jump hinput m x
          _ = dyadicAverage m (f : ℝ → ℂ) x + dyadicAverage m (g : ℝ → ℂ) x :=
            dyadicAverage_add_of_memLp_finite_jump hp.le (Lp.memLp f) (Lp.memLp g) m x
      filter_upwards [hleft, hf, hg, hout, havg] with x hleft hf hg hout havg
      calc
        (avg (f + g) : ℝ → ℂ) x =
            dyadicAverage m ((f + g : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) x := hleft
        _ = dyadicAverage m (f : ℝ → ℂ) x + dyadicAverage m (g : ℝ → ℂ) x := havg
        _ = (avg f + avg g) x := by rw [← hf, ← hg]; exact hout.symm
    map_smul' := by
      intro c f
      apply Lp.ext
      have hleft := (show MemLp (dyadicAverage m ((c • f : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ))
          (ENNReal.ofReal p) volume from by
          apply memLp_iff.mpr
          exact (eLpNorm_finite_dyadicAverage_le (Lp.memLp (c • f)) hp.le m).trans_lt
            (Lp.memLp (c • f)).eLpNorm_lt_top).coeFn_toLp
      have hf := (show MemLp (dyadicAverage m (f : ℝ → ℂ))
          (ENNReal.ofReal p) volume from by
          apply memLp_iff.mpr
          exact (eLpNorm_finite_dyadicAverage_le (Lp.memLp f) hp.le m).trans_lt
            (Lp.memLp f).eLpNorm_lt_top).coeFn_toLp
      have hout := Lp.coeFn_smul c (avg f)
      have hinput : ((c • f : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) =ᵐ[volume]
          fun x => c * (f : ℝ → ℂ) x := by
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simpa [smul_eq_mul] using hx
      have havg : dyadicAverage m ((c • f : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) =ᵐ[volume]
          fun x => c * dyadicAverage m (f : ℝ → ℂ) x := by
        filter_upwards [] with x
        calc
          dyadicAverage m ((c • f : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) x =
              dyadicAverage m (fun y => c * (f : ℝ → ℂ) y) x :=
            dyadicAverage_eq_of_ae_eq_jump hinput m x
          _ = c * dyadicAverage m (f : ℝ → ℂ) x :=
            dyadicAverage_smul_of_memLp_finite_jump hp.le (Lp.memLp f) c m x
      filter_upwards [hleft, hf, hout, havg] with x hleft hf hout havg
      calc
        (avg (c • f) : ℝ → ℂ) x =
            dyadicAverage m ((c • f : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) x := hleft
        _ = c * dyadicAverage m (f : ℝ → ℂ) x := havg
        _ = c * (avg f : ℝ → ℂ) x := by rw [← hf]
        _ = (c • avg f) x := by simpa [smul_eq_mul] using hout.symm
  }
  exact L.mkContinuous 1 (by
    intro f
    have h := eLpNorm_finite_dyadicAverage_le (Lp.memLp f) hp.le m
    change ‖avg f‖ ≤ 1 * ‖f‖
    dsimp [avg]
    rw [Lp.norm_toLp, Lp.norm_def]
    simpa using ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top h)

theorem memLp_mul_of_abs_le_one_finite {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] {f : ℝ → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) volume) (v : ℝ → ℝ)
    (hv : Measurable v) (hvBound : ∀ x, |v x| ≤ 1) :
    MemLp (fun x => (v x : ℂ) * f x) (ENNReal.ofReal p) volume := by
  apply hf.of_le
  · have hvm : Measurable (fun x => (v x : ℂ)) := by fun_prop
    exact hvm.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · filter_upwards [] with x
    rw [norm_mul, Complex.norm_real]
    simpa [Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right (hvBound x) (norm_nonneg (f x))

/-- Multiplication by a measurable real coefficient of absolute value at
most one is a complex-linear contraction on finite `Lᵖ`. -/
def dyadicRealMultiplierLpCLM {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (v : ℝ → ℝ) (hv : Measurable v) (hvBound : ∀ x, |v x| ≤ 1) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  let mul (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :=
    (memLp_mul_of_abs_le_one_finite (Lp.memLp f) v hv hvBound).toLp
      (fun x => (v x : ℂ) * (f : ℝ → ℂ) x)
  let L : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := {
    toFun := mul
    map_add' := by
      intro f g
      apply Lp.ext
      have hleft := (memLp_mul_of_abs_le_one_finite
        (Lp.memLp (f + g)) v hv hvBound).coeFn_toLp
      have hf := (memLp_mul_of_abs_le_one_finite (Lp.memLp f) v hv hvBound).coeFn_toLp
      have hg := (memLp_mul_of_abs_le_one_finite (Lp.memLp g) v hv hvBound).coeFn_toLp
      have hout := Lp.coeFn_add (mul f) (mul g)
      have hinput := Lp.coeFn_add f g
      filter_upwards [hleft, hf, hg, hout, hinput] with x hleft hf hg hout hinput
      have hinput' : ((f + g : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) x =
          (f : ℝ → ℂ) x + (g : ℝ → ℂ) x := by
        simpa only [Pi.add_apply] using hinput
      calc
        (mul (f + g) : ℝ → ℂ) x =
            (v x : ℂ) * ((f + g : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) x := hleft
        _ = (v x : ℂ) * ((f : ℝ → ℂ) x + (g : ℝ → ℂ) x) := by rw [hinput']
        _ = (v x : ℂ) * (f : ℝ → ℂ) x + (v x : ℂ) * (g : ℝ → ℂ) x := by ring
        _ = (mul f + mul g) x := by rw [← hf, ← hg]; exact hout.symm
    map_smul' := by
      intro c f
      apply Lp.ext
      have hleft := (memLp_mul_of_abs_le_one_finite
        (Lp.memLp (c • f)) v hv hvBound).coeFn_toLp
      have hf := (memLp_mul_of_abs_le_one_finite (Lp.memLp f) v hv hvBound).coeFn_toLp
      have hout := Lp.coeFn_smul c (mul f)
      have hinput : ((c • f : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) =ᵐ[volume]
          fun x => c * (f : ℝ → ℂ) x := by
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simpa [smul_eq_mul] using hx
      filter_upwards [hleft, hf, hout, hinput] with x hleft hf hout hinput
      calc
        (mul (c • f) : ℝ → ℂ) x =
            (v x : ℂ) * ((c • f : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) x := hleft
        _ = (v x : ℂ) * (c * (f : ℝ → ℂ) x) := by rw [hinput]
        _ = c * ((v x : ℂ) * (f : ℝ → ℂ) x) := by ring
        _ = (c • mul f) x := by rw [← hf]; exact hout.symm
  }
  exact L.mkContinuous 1 (by
    intro f
    let hmul := memLp_mul_of_abs_le_one_finite (Lp.memLp f) v hv hvBound
    have hpoint : ∀ x, ‖(v x : ℂ) * (f : ℝ → ℂ) x‖ ≤ ‖(f : ℝ → ℂ) x‖ := by
      intro x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        |v x| * ‖(f : ℝ → ℂ) x‖ ≤ 1 * ‖(f : ℝ → ℂ) x‖ :=
          mul_le_mul_of_nonneg_right (hvBound x) (norm_nonneg _)
        _ = ‖(f : ℝ → ℂ) x‖ := by ring
    have heLp : eLpNorm (fun x => (v x : ℂ) * (f : ℝ → ℂ) x)
        (ENNReal.ofReal p) volume ≤ eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) volume :=
      eLpNorm_mono_ae hmul.aestronglyMeasurable
        (Filter.Eventually.of_forall hpoint)
    change ‖mul f‖ ≤ 1 * ‖f‖
    calc
      ‖mul f‖ = ENNReal.toReal
          (eLpNorm (fun x => (v x : ℂ) * (f : ℝ → ℂ) x)
            (ENNReal.ofReal p) volume) := by
        dsimp [mul]
        rw [Lp.norm_toLp]
      _ ≤ ENNReal.toReal (eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) volume) :=
        ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top heLp
      _ = 1 * ‖f‖ := by rw [Lp.norm_def]; simp)

theorem dyadicAverageLpCLM_coeFn {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (m : ℤ)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    (dyadicAverageLpCLM hp m f : ℝ → ℂ) =ᵐ[volume]
      dyadicAverage m (f : ℝ → ℂ) := by
  change ((show MemLp (dyadicAverage m (f : ℝ → ℂ)) (ENNReal.ofReal p) volume from by
      apply memLp_iff.mpr
      exact (eLpNorm_finite_dyadicAverage_le (Lp.memLp f) hp.le m).trans_lt
        (Lp.memLp f).eLpNorm_lt_top).toLp (dyadicAverage m (f : ℝ → ℂ)) : ℝ → ℂ) =ᵐ[volume] _
  exact (show MemLp (dyadicAverage m (f : ℝ → ℂ)) (ENNReal.ofReal p) volume from by
      apply memLp_iff.mpr
      exact (eLpNorm_finite_dyadicAverage_le (Lp.memLp f) hp.le m).trans_lt
        (Lp.memLp f).eLpNorm_lt_top).coeFn_toLp

theorem dyadicRealMultiplierLpCLM_coeFn {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (v : ℝ → ℝ) (hv : Measurable v)
    (hvBound : ∀ x, |v x| ≤ 1)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    (dyadicRealMultiplierLpCLM v hv hvBound f : ℝ → ℂ) =ᵐ[volume]
      fun x => (v x : ℂ) * (f : ℝ → ℂ) x := by
  change ((memLp_mul_of_abs_le_one_finite (Lp.memLp f) v hv hvBound).toLp
    (fun x => (v x : ℂ) * (f : ℝ → ℂ) x) : ℝ → ℂ) =ᵐ[volume] _
  exact (memLp_mul_of_abs_le_one_finite (Lp.memLp f) v hv hvBound).coeFn_toLp

/-- One predictable martingale difference as a continuous complex-linear
operator on finite `Lᵖ`. -/
def dyadicPredictableTermLpCLM {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (n : ℤ) (v : ℝ → ℝ)
    (hv : ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v x = v y)
    (hvBound : ∀ x, |v x| ≤ 1) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
  (dyadicRealMultiplierLpCLM v
    (measurable_of_constantOn_dyadicInterval hv) hvBound).comp
      (dyadicAverageLpCLM hp (-n) - dyadicAverageLpCLM hp (1 - n))

theorem dyadicPredictableTermLpCLM_coeFn {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (n : ℤ)
    (v : ℝ → ℝ) (hv : ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v x = v y)
    (hvBound : ∀ x, |v x| ≤ 1)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    (dyadicPredictableTermLpCLM hp n v hv hvBound f : ℝ → ℂ) =ᵐ[volume]
      fun x => (v x : ℂ) * dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
  have hmul := dyadicRealMultiplierLpCLM_coeFn v
    (measurable_of_constantOn_dyadicInterval hv) hvBound
    ((dyadicAverageLpCLM hp (-n) - dyadicAverageLpCLM hp (1 - n)) f)
  have hleft := dyadicAverageLpCLM_coeFn hp (-n) f
  have hright := dyadicAverageLpCLM_coeFn hp (1 - n) f
  have hsub := Lp.coeFn_sub
    (dyadicAverageLpCLM hp (-n) f) (dyadicAverageLpCLM hp (1 - n) f)
  filter_upwards [hmul, hsub, hleft, hright] with x hmul hsub hleft hright
  change (dyadicRealMultiplierLpCLM v
    (measurable_of_constantOn_dyadicInterval hv) hvBound
    ((dyadicAverageLpCLM hp (-n) - dyadicAverageLpCLM hp (1 - n)) f) : ℝ → ℂ) x = _
  rw [hmul]
  change (v x : ℂ) *
      ((dyadicAverageLpCLM hp (-n) f - dyadicAverageLpCLM hp (1 - n) f :
        Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ) x = _
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hleft, hright]
  unfold dyadicMartingaleDifference dyadicIncreasingAverage
  rw [show -(n - 1) = 1 - n by omega]

/-- The finite predictable martingale transform on `Lᵖ`, assembled from the
dyadic average and multiplier operators. -/
def dyadicPredictableTransformLpCLM {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (F : Finset ℤ) (v : ℤ → ℝ → ℝ)
    (hv : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n ∈ F, ∀ x, |v n x| ≤ 1) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  let vF := dyadicPredictableFamily F v
  exact ∑ n ∈ F, dyadicPredictableTermLpCLM hp n (vF n)
    (dyadicPredictableFamily_predictable F v hv n)
    (dyadicPredictableFamily_bound F v hvBound n)

theorem dyadicPredictableTransformLpCLM_coeFn {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (F : Finset ℤ)
    (v : ℤ → ℝ → ℝ)
    (hv : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n ∈ F, ∀ x, |v n x| ≤ 1)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    (dyadicPredictableTransformLpCLM hp F v hv hvBound f : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ n ∈ F, (v n x : ℂ) * dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
  classical
  let vF := dyadicPredictableFamily F v
  have hsum : dyadicPredictableTransformLpCLM hp F v hv hvBound f =
      ∑ n ∈ F, dyadicPredictableTermLpCLM hp n (vF n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) f := by
    simp [dyadicPredictableTransformLpCLM, vF, Finset.sum_apply]
  rw [hsum]
  have hterms : ∀ n ∈ F, ∀ᵐ x ∂volume,
      (dyadicPredictableTermLpCLM hp n (dyadicPredictableFamily F v n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) f : ℝ → ℂ) x =
        (v n x : ℂ) * dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
    intro n hn
    filter_upwards [dyadicPredictableTermLpCLM_coeFn hp n
      (dyadicPredictableFamily F v n)
      (dyadicPredictableFamily_predictable F v hv n)
      (dyadicPredictableFamily_bound F v hvBound n) f] with x hx
    simpa [dyadicPredictableFamily, hn] using hx
  have hall : ∀ᵐ x ∂volume, ∀ n ∈ F,
      (dyadicPredictableTermLpCLM hp n (dyadicPredictableFamily F v n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) f : ℝ → ℂ) x =
        (v n x : ℂ) * dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
    rw [Finset.eventually_all]
    exact hterms
  have hcoe := Lp.coeFn_finsetSum F (fun n =>
    dyadicPredictableTermLpCLM hp n (dyadicPredictableFamily F v n)
      (dyadicPredictableFamily_predictable F v hv n)
      (dyadicPredictableFamily_bound F v hvBound n) f)
  filter_upwards [hcoe, hall] with x hcoe hx
  calc
    (∑ n ∈ F, dyadicPredictableTermLpCLM hp n (vF n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) f :
        Lp ℂ (ENNReal.ofReal p) volume) x =
        ∑ n ∈ F, (dyadicPredictableTermLpCLM hp n (vF n)
          (dyadicPredictableFamily_predictable F v hv n)
          (dyadicPredictableFamily_bound F v hvBound n) f : ℝ → ℂ) x := by
      simpa only [Finset.sum_apply] using hcoe
    _ = ∑ n ∈ F, (v n x : ℂ) * dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hx n hn

/-- On the common `Lᵖ ∩ L²` domain, the finite `Lᵖ` transform is the
ordinary finite `L²` predictable transform. -/
theorem dyadicPredictableTransformLpCLM_agrees_l2 {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (F : Finset ℤ)
    (v : ℤ → ℝ → ℝ)
    (hv : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n ∈ F, ∀ x, |v n x| ≤ 1)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (hf₂ : MemLp (f : ℝ → ℂ) 2 volume) :
    (dyadicPredictableTransformLpCLM hp F v hv hvBound f : ℝ → ℂ) =ᵐ[volume]
      (dyadicPredictableTransformL2 F v hv hvBound
        (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) := by
  classical
  let vF := dyadicPredictableFamily F v
  have hterms : ∀ n ∈ F, ∀ᵐ x ∂volume,
      (dyadicPredictableTermLpCLM hp n (vF n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) f : ℝ → ℂ) x =
      (dyadicPredictableTermL2 (Lp.memLp (hf₂.toLp (f : ℝ → ℂ))) n (vF n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) : ℝ → ℂ) x := by
    intro n hn
    have hpTerm := dyadicPredictableTermLpCLM_coeFn hp n (vF n)
      (dyadicPredictableFamily_predictable F v hv n)
      (dyadicPredictableFamily_bound F v hvBound n) f
    have h2Term := (memLp_dyadicPredictableTerm_two
      (Lp.memLp (hf₂.toLp (f : ℝ → ℂ))) n (vF n)
      (measurable_of_constantOn_dyadicInterval
        (dyadicPredictableFamily_predictable F v hv n))
      (dyadicPredictableFamily_bound F v hvBound n)).coeFn_toLp
    have hdiff : dyadicMartingaleDifference n (hf₂.toLp (f : ℝ → ℂ) : ℝ → ℂ) =ᵐ[volume]
        dyadicMartingaleDifference n (f : ℝ → ℂ) := by
      filter_upwards [] with x
      unfold dyadicMartingaleDifference dyadicIncreasingAverage
      rw [dyadicAverage_eq_of_ae_eq_jump hf₂.coeFn_toLp (-n) x,
        dyadicAverage_eq_of_ae_eq_jump hf₂.coeFn_toLp (-(n - 1)) x]
    filter_upwards [hpTerm, h2Term, hdiff] with x hpTerm h2Term hdiff
    have hfamily : vF n x = v n x := by
      simp [vF, dyadicPredictableFamily, hn]
    calc
      (dyadicPredictableTermLpCLM hp n (vF n)
          (dyadicPredictableFamily_predictable F v hv n)
          (dyadicPredictableFamily_bound F v hvBound n) f : ℝ → ℂ) x =
          (vF n x : ℂ) * dyadicMartingaleDifference n (f : ℝ → ℂ) x := hpTerm
      _ = (vF n x : ℂ) *
          dyadicMartingaleDifference n (hf₂.toLp (f : ℝ → ℂ) : ℝ → ℂ) x := by
            rw [hdiff]
      _ = (dyadicPredictableTermL2 (Lp.memLp (hf₂.toLp (f : ℝ → ℂ))) n (vF n)
          (dyadicPredictableFamily_predictable F v hv n)
          (dyadicPredictableFamily_bound F v hvBound n) : ℝ → ℂ) x := by
            simpa only [dyadicPredictableTermL2] using h2Term.symm
  have htermsAll : ∀ᵐ x ∂volume, ∀ n ∈ F,
      (dyadicPredictableTermLpCLM hp n (vF n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) f : ℝ → ℂ) x =
      (dyadicPredictableTermL2 (Lp.memLp (hf₂.toLp (f : ℝ → ℂ))) n (vF n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) : ℝ → ℂ) x := by
    rw [Finset.eventually_all]
    exact hterms
  have hpSum := Lp.coeFn_fun_finsetSum F (fun n =>
    dyadicPredictableTermLpCLM hp n (vF n)
      (dyadicPredictableFamily_predictable F v hv n)
      (dyadicPredictableFamily_bound F v hvBound n) f)
  have h2Sum := Lp.coeFn_fun_finsetSum F (fun n =>
    dyadicPredictableTermL2 (Lp.memLp (hf₂.toLp (f : ℝ → ℂ))) n (vF n)
      (dyadicPredictableFamily_predictable F v hv n)
      (dyadicPredictableFamily_bound F v hvBound n))
  have hLpSumIdent : dyadicPredictableTransformLpCLM hp F v hv hvBound f =
      ∑ n ∈ F, dyadicPredictableTermLpCLM hp n (vF n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) f := by
    simp [dyadicPredictableTransformLpCLM, vF]
  have hL2Ident := dyadicPredictableTransformL2_eq_sum F v hv hvBound
    (hf₂.toLp (f : ℝ → ℂ))
  have hL2IdentAE :
      (dyadicPredictableTransformL2 F v hv hvBound
        (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) =ᵐ[volume]
        fun x => ∑ n ∈ F,
          (dyadicPredictableTermL2 (Lp.memLp (hf₂.toLp (f : ℝ → ℂ))) n (vF n)
            (dyadicPredictableFamily_predictable F v hv n)
            (dyadicPredictableFamily_bound F v hvBound n) : ℝ → ℂ) x := by
    rw [hL2Ident]
    simpa [vF, Finset.sum_apply] using h2Sum
  filter_upwards [htermsAll, hpSum, h2Sum, hL2IdentAE] with
      x htermsAll hpSum h2Sum hL2IdentAE
  calc
    (dyadicPredictableTransformLpCLM hp F v hv hvBound f : ℝ → ℂ) x =
      (∑ n ∈ F, dyadicPredictableTermLpCLM hp n (vF n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) f : Lp ℂ (ENNReal.ofReal p) volume) x := by
          rw [hLpSumIdent]
    _ = ∑ n ∈ F, (dyadicPredictableTermLpCLM hp n (vF n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) f : ℝ → ℂ) x := by
          exact hpSum
    _ = ∑ n ∈ F, (dyadicPredictableTermL2 (Lp.memLp (hf₂.toLp (f : ℝ → ℂ))) n (vF n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) : ℝ → ℂ) x := by
          apply Finset.sum_congr rfl
          intro n hn
          exact htermsAll n hn
    _ = (∑ n ∈ F, dyadicPredictableTermL2 (Lp.memLp (hf₂.toLp (f : ℝ → ℂ))) n (vF n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) : Lp ℂ 2 volume) x := by
          exact h2Sum.symm
    _ = (dyadicPredictableTransformL2 F v hv hvBound
          (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) x := by
          calc
            (∑ n ∈ F, dyadicPredictableTermL2 (Lp.memLp (hf₂.toLp (f : ℝ → ℂ))) n (vF n)
                (dyadicPredictableFamily_predictable F v hv n)
                (dyadicPredictableFamily_bound F v hvBound n) : Lp ℂ 2 volume) x =
              ∑ n ∈ F, (dyadicPredictableTermL2 (Lp.memLp (hf₂.toLp (f : ℝ → ℂ))) n (vF n)
                (dyadicPredictableFamily_predictable F v hv n)
              (dyadicPredictableFamily_bound F v hvBound n) : ℝ → ℂ) x := h2Sum
            _ = (dyadicPredictableTransformL2 F v hv hvBound
                (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ) x := hL2IdentAE.symm

/-- The concrete finite `Lᵖ` transform on an interval of scales inherits
the exact `K_p` bound from the paper's predictable-transform theorem. -/
theorem dyadicPredictableTransformLpCLM_interval_bound {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (L N : ℤ) (hLN : L < N)
    (v : ℤ → ℝ → ℝ)
    (hv : ∀ n, L < n → n ≤ N → ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n, L < n → n ≤ N → ∀ x, |v n x| ≤ 1)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    ‖dyadicPredictableTransformLpCLM hp (Finset.Ioc L N) v
        (fun n hn => by
          rcases Finset.mem_Ioc.mp hn with ⟨hLn, hnN⟩
          exact hv n hLn hnN)
        (fun n hn => by
          rcases Finset.mem_Ioc.mp hn with ⟨hLn, hnN⟩
          exact hvBound n hLn hnN) f‖ ≤
      weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖ := by
  classical
  obtain ⟨U, hUnorm, hUagree⟩ :=
    predictableTransformBound L N hLN v hv hvBound p hp
  let F := Finset.Ioc L N
  have hvF : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y := by
    intro n hn j x y hx hy
    rcases Finset.mem_Ioc.mp hn with ⟨hLn, hnN⟩
    exact hv n hLn hnN j hx hy
  have hvBoundF : ∀ n ∈ F, ∀ x, |v n x| ≤ 1 := by
    intro n hn x
    rcases Finset.mem_Ioc.mp hn with ⟨hLn, hnN⟩
    exact hvBound n hLn hnN x
  let T := dyadicPredictableTransformL2 F v hvF hvBoundF
  let V : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    (dyadicPredictableTransformLpCLM hp F v hvF hvBoundF).restrictScalars ℝ
  have hVagree : ∀ (g : Lp ℂ (ENNReal.ofReal p) volume)
      (hg₂ : MemLp (g : ℝ → ℂ) 2 volume),
      (V g : ℝ → ℂ) =ᵐ[volume]
        (T (hg₂.toLp (g : ℝ → ℂ)) : ℝ → ℂ) := by
    intro g hg₂
    exact dyadicPredictableTransformLpCLM_agrees_l2 hp F v hvF hvBoundF g hg₂
  have hUV : U = V :=
    lpContinuousOperator_eq_of_agree_on_l2 ENNReal.ofReal_ne_top T U V hUagree hVagree
  have hbound : ‖V f‖ ≤ weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖ := by
    rw [← hUV]
    exact hUnorm f
  simpa [V, F] using hbound

/-- Choose a greedy stop run for a finite sequence, retaining its stop count
and all first-crossing/exhaustion certificates. -/
noncomputable def greedyStopRunChoice
    {I : Type*} [LinearOrder I] [Fintype I] [Nonempty I]
    (u : I → ℂ) (threshold : ℝ) (hthreshold : 0 < threshold) :
    Σ G : ℕ, GreedyStopRun u threshold G := by
  classical
  let hex := exists_greedyStopRun u threshold hthreshold
  exact ⟨Classical.choose hex, Classical.choice (Classical.choose_spec hex)⟩

/-- The prefix greedy-stop count cannot exceed the number of increments seen
so far. -/
def greedyPrefixStopCount (u : ℕ → ℂ) (threshold : ℝ)
    (hthreshold : 0 < threshold) (t : ℕ) : ℕ :=
  (greedyStopRunChoice (I := Fin (t + 1)) (fun i => u i.val)
    threshold hthreshold).1

theorem greedyPrefixStopCount_le (u : ℕ → ℂ) (threshold : ℝ)
    (hthreshold : 0 < threshold) (t : ℕ) :
    greedyPrefixStopCount u threshold hthreshold t ≤ t := by
  classical
  let choice := greedyStopRunChoice (I := Fin (t + 1))
    (fun i => u i.val) threshold hthreshold
  have hcard' : Fintype.card (Fin (choice.1 + 1)) ≤ Fintype.card (Fin (t + 1)) :=
    Fintype.card_le_of_injective choice.2.point choice.2.strict.injective
  have hcard : choice.1 + 1 ≤ Fintype.card (Fin (t + 1)) := by
    simpa using hcard'
  change choice.1 ≤ t
  simpa using hcard

/-- The independent sign attached to the greedy block active after the
prefix through time `t`. -/
def greedyPrefixSignedCoefficient {M : ℕ} (u : ℕ → ℂ) (threshold : ℝ)
    (hthreshold : 0 < threshold) (ω : jswSignSpace (M + 1)) (t : Fin M) : ℝ :=
  let G := greedyPrefixStopCount u threshold hthreshold t.val
  jswSignCoordinate (M + 1) ω ⟨G, by
    have hG := greedyPrefixStopCount_le u threshold hthreshold t.val
    omega⟩

theorem greedyPrefixSignedCoefficient_abs_eq_one {M : ℕ} (u : ℕ → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (ω : jswSignSpace (M + 1)) (t : Fin M) :
    |greedyPrefixSignedCoefficient u threshold hthreshold ω t| = 1 := by
  simp only [greedyPrefixSignedCoefficient]
  exact jswSignCoordinate_abs_eq_one _ _ _


end

end FractionalPrimes.Literature.JSW

end
