module

public import FractionalPrimes.Literature.JSW.PredictableTransformL2
public import FractionalPrimes.Literature.JSW.DyadicWeakCZSupport
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# The full predictable dyadic-transform bound

This file follows `lj:martingale-transform` in
`expanded-blueprint.tex:3824–3859` and Astra
`blueprint-sources 2/literature-expansion/sections/jsw.tex:536–564`.
The checked L² orthogonality core is imported from
`PredictableTransformL2.lean`; this file constructs the L² operator and
supplies the off-support hypothesis needed by the weak-CZ extension.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

private theorem dyadicAverage_eq_of_ae_eq {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) (m : ℤ) (x : ℝ) :
    dyadicAverage m f x = dyadicAverage m g x := by
  let Q := dyadicInterval m (dyadicIntervalIndex m x)
  have hfgQ : f =ᵐ[volume.restrict Q] g := ae_restrict_of_ae hfg
  change ((2 : ℝ) ^ m)⁻¹ • ∫ y in Q, f y ∂volume =
    ((2 : ℝ) ^ m)⁻¹ • ∫ y in Q, g y ∂volume
  rw [integral_congr_ae hfgQ]

private theorem dyadicAverage_add_of_memLp_two {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (m : ℤ) (x : ℝ) :
    dyadicAverage m (fun y => f y + g y) x =
      dyadicAverage m f x + dyadicAverage m g x := by
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
  change ((2 : ℝ) ^ m)⁻¹ •
      ∫ y, (f y + g y) ∂(volume.restrict Q) =
    ((2 : ℝ) ^ m)⁻¹ • ∫ y, f y ∂(volume.restrict Q) +
      ((2 : ℝ) ^ m)⁻¹ • ∫ y, g y ∂(volume.restrict Q)
  rw [integral_add hfQ hgQ, smul_add]

private theorem dyadicAverage_smulReal_of_memLp_two {c : ℝ} {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (m : ℤ) (x : ℝ) :
    dyadicAverage m (fun y => (c : ℂ) * f y) x =
      (c : ℂ) * dyadicAverage m f x := by
  have h := dyadicAverage_smul_of_memLp_two (c := (c : ℂ)) hf m x
  convert h using 1 <;> simp [Pi.smul_apply, smul_eq_mul]

/-- The dyadic averaging projection as a bounded real-linear operator on
`L²(ℝ;ℂ)`. -/
def dyadicAverageL2CLM (m : ℤ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] Lp ℂ 2 (volume : Measure ℝ) := by
  let avg (f : Lp ℂ 2 (volume : Measure ℝ)) :=
    (memLp_dyadicAverage_two_of_memLp (Lp.memLp f) m).toLp
      (dyadicAverage m (f : ℝ → ℂ))
  let L : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℝ]
      Lp ℂ 2 (volume : Measure ℝ) := {
    toFun := avg
    map_add' := by
      intro f g
      apply Lp.ext
      have hleft :=
        (memLp_dyadicAverage_two_of_memLp (Lp.memLp (f + g)) m).coeFn_toLp
      have hf :=
        (memLp_dyadicAverage_two_of_memLp (Lp.memLp f) m).coeFn_toLp
      have hg :=
        (memLp_dyadicAverage_two_of_memLp (Lp.memLp g) m).coeFn_toLp
      have hout := Lp.coeFn_add
        ((memLp_dyadicAverage_two_of_memLp (Lp.memLp f) m).toLp
          (dyadicAverage m (f : ℝ → ℂ)))
        ((memLp_dyadicAverage_two_of_memLp (Lp.memLp g) m).toLp
          (dyadicAverage m (g : ℝ → ℂ)))
      have hinput : ((f + g : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
          fun x => (f : ℝ → ℂ) x + (g : ℝ → ℂ) x := Lp.coeFn_add f g
      have havg : dyadicAverage m ((f + g : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
          fun x => dyadicAverage m (f : ℝ → ℂ) x +
            dyadicAverage m (g : ℝ → ℂ) x := by
        filter_upwards [] with x
        calc
          dyadicAverage m ((f + g : Lp ℂ 2 volume) : ℝ → ℂ) x =
              dyadicAverage m (fun y => (f : ℝ → ℂ) y +
                (g : ℝ → ℂ) y) x :=
            dyadicAverage_eq_of_ae_eq hinput m x
          _ = dyadicAverage m (f : ℝ → ℂ) x +
                dyadicAverage m (g : ℝ → ℂ) x :=
            dyadicAverage_add_of_memLp_two (Lp.memLp f) (Lp.memLp g) m x
      filter_upwards [hleft, hf, hg, hout, havg] with x hleft hf' hg' hout havg
      calc
        (avg (f + g) : ℝ → ℂ) x = dyadicAverage m (f + g : Lp ℂ 2 volume) x := hleft
        _ = dyadicAverage m (f : ℝ → ℂ) x +
            dyadicAverage m (g : ℝ → ℂ) x := havg
        _ = (avg f + avg g) x := by
          rw [← hf', ← hg']
          exact hout.symm
    map_smul' := by
      intro c f
      apply Lp.ext
      have hleft :=
        (memLp_dyadicAverage_two_of_memLp (Lp.memLp (c • f)) m).coeFn_toLp
      have hf :=
        (memLp_dyadicAverage_two_of_memLp (Lp.memLp f) m).coeFn_toLp
      have hout := Lp.coeFn_smul c
        ((memLp_dyadicAverage_two_of_memLp (Lp.memLp f) m).toLp
          (dyadicAverage m (f : ℝ → ℂ)))
      have hinput : ((c • f : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
          fun x => (c : ℂ) * (f : ℝ → ℂ) x := by
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simpa [smul_eq_mul] using hx
      have havg : dyadicAverage m ((c • f : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
          fun x => (c : ℂ) * dyadicAverage m (f : ℝ → ℂ) x := by
        filter_upwards [] with x
        calc
          dyadicAverage m ((c • f : Lp ℂ 2 volume) : ℝ → ℂ) x =
              dyadicAverage m (fun y => (c : ℂ) * (f : ℝ → ℂ) y) x :=
            dyadicAverage_eq_of_ae_eq hinput m x
          _ = (c : ℂ) * dyadicAverage m (f : ℝ → ℂ) x :=
            dyadicAverage_smulReal_of_memLp_two (Lp.memLp f) m x
      filter_upwards [hleft, hf, hout, havg] with x hleft hf' hout havg
      calc
        (avg (c • f) : ℝ → ℂ) x = dyadicAverage m (c • f : Lp ℂ 2 volume) x := hleft
        _ = (c : ℂ) * dyadicAverage m (f : ℝ → ℂ) x := havg
        _ = (c : ℂ) * (avg f : ℝ → ℂ) x := by rw [← hf']
        _ = (c • avg f) x := by
          simpa [avg, smul_eq_mul] using hout.symm
  }
  exact L.mkContinuous 1 (by
    intro f
    have h := eLpNorm_two_dyadicAverage_le (Lp.memLp f) m
    change ‖avg f‖ ≤ 1 * ‖f‖
    dsimp [avg]
    rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_def]
    simpa using ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top h)

def dyadicRealMultiplierL2CLM (v : ℝ → ℝ)
    (hv : Measurable v) (hvBound : ∀ x, |v x| ≤ 1) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] Lp ℂ 2 (volume : Measure ℝ) := by
  let mul (f : Lp ℂ 2 (volume : Measure ℝ)) :=
    (memLp_mul_of_abs_le_one (Lp.memLp f) v hv hvBound).toLp
      (fun x => (v x : ℂ) * (f : ℝ → ℂ) x)
  let L : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℝ]
      Lp ℂ 2 (volume : Measure ℝ) := {
    toFun := mul
    map_add' := by
      intro f g
      apply Lp.ext
      have hleft := (memLp_mul_of_abs_le_one
        (Lp.memLp (f + g)) v hv hvBound).coeFn_toLp
      have hf := (memLp_mul_of_abs_le_one (Lp.memLp f) v hv hvBound).coeFn_toLp
      have hg := (memLp_mul_of_abs_le_one (Lp.memLp g) v hv hvBound).coeFn_toLp
      have hout := Lp.coeFn_add (mul f) (mul g)
      have hinput := Lp.coeFn_add f g
      filter_upwards [hleft, hf, hg, hout, hinput] with x hleft hf hg hout hinput
      have hinput' : ((f + g : Lp ℂ 2 volume) : ℝ → ℂ) x =
          (f : ℝ → ℂ) x + (g : ℝ → ℂ) x := by
        simpa only [Pi.add_apply] using hinput
      calc
        (mul (f + g) : ℝ → ℂ) x = (v x : ℂ) * ((f + g : Lp ℂ 2 volume) : ℝ → ℂ) x := hleft
        _ = (v x : ℂ) * ((f : ℝ → ℂ) x + (g : ℝ → ℂ) x) := by rw [hinput']
        _ = (v x : ℂ) * (f : ℝ → ℂ) x + (v x : ℂ) * (g : ℝ → ℂ) x := by ring
        _ = (mul f + mul g) x := by rw [← hf, ← hg]; exact hout.symm
    map_smul' := by
      intro c f
      apply Lp.ext
      have hleft := (memLp_mul_of_abs_le_one
        (Lp.memLp (c • f)) v hv hvBound).coeFn_toLp
      have hf := (memLp_mul_of_abs_le_one (Lp.memLp f) v hv hvBound).coeFn_toLp
      have hout := Lp.coeFn_smul c (mul f)
      have hinput : ((c • f : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
          fun x => (c : ℂ) * (f : ℝ → ℂ) x := by
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simpa [smul_eq_mul] using hx
      filter_upwards [hleft, hf, hout, hinput] with x hleft hf hout hinput
      calc
        (mul (c • f) : ℝ → ℂ) x = (v x : ℂ) * ((c • f : Lp ℂ 2 volume) : ℝ → ℂ) x := hleft
        _ = (v x : ℂ) * ((c : ℂ) * (f : ℝ → ℂ) x) := by rw [hinput]
        _ = (c : ℂ) * ((v x : ℂ) * (f : ℝ → ℂ) x) := by ring
        _ = (c • mul f) x := by rw [← hf]; exact hout.symm
  }
  exact L.mkContinuous 1 (by
    intro f
    let hmul := memLp_mul_of_abs_le_one (Lp.memLp f) v hv hvBound
    have hpoint : ∀ x, ‖(v x : ℂ) * (f : ℝ → ℂ) x‖ ≤ ‖(f : ℝ → ℂ) x‖ := by
      intro x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        |v x| * ‖(f : ℝ → ℂ) x‖ ≤ 1 * ‖(f : ℝ → ℂ) x‖ :=
          mul_le_mul_of_nonneg_right (hvBound x) (norm_nonneg _)
        _ = ‖(f : ℝ → ℂ) x‖ := by ring
    have heLp : eLpNorm (fun x => (v x : ℂ) * (f : ℝ → ℂ) x)
        2 volume ≤ eLpNorm (f : ℝ → ℂ) 2 volume :=
      eLpNorm_mono_ae hmul.aestronglyMeasurable
        (Filter.Eventually.of_forall hpoint)
    change ‖mul f‖ ≤ 1 * ‖f‖
    calc
      ‖mul f‖ = ENNReal.toReal
          (eLpNorm (fun x => (v x : ℂ) * (f : ℝ → ℂ) x) 2 volume) := by
        dsimp [mul]
        rw [MeasureTheory.Lp.norm_toLp]
      _ ≤ ENNReal.toReal (eLpNorm (f : ℝ → ℂ) 2 volume) :=
        ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top heLp
      _ = 1 * ‖f‖ := by rw [MeasureTheory.Lp.norm_def]; simp)

private theorem dyadicRealMultiplierL2CLM_coeFn (v : ℝ → ℝ)
    (hv : Measurable v) (hvBound : ∀ x, |v x| ≤ 1)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (dyadicRealMultiplierL2CLM v hv hvBound f : ℝ → ℂ) =ᵐ[volume]
      fun x => (v x : ℂ) * (f : ℝ → ℂ) x := by
  change ((memLp_mul_of_abs_le_one (Lp.memLp f) v hv hvBound).toLp
    (fun x => (v x : ℂ) * (f : ℝ → ℂ) x) : ℝ → ℂ) =ᵐ[volume] _
  exact (memLp_mul_of_abs_le_one (Lp.memLp f) v hv hvBound).coeFn_toLp

def dyadicMartingaleDifferenceL2CLM (n : ℤ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] Lp ℂ 2 (volume : Measure ℝ) :=
  dyadicAverageL2CLM (-n) - dyadicAverageL2CLM (1 - n)

private theorem dyadicAverageL2CLM_coeFn (m : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (dyadicAverageL2CLM m f : ℝ → ℂ) =ᵐ[volume]
      dyadicAverage m (f : ℝ → ℂ) := by
  change ((memLp_dyadicAverage_two_of_memLp (Lp.memLp f) m).toLp
    (dyadicAverage m (f : ℝ → ℂ)) : ℝ → ℂ) =ᵐ[volume] _
  exact (memLp_dyadicAverage_two_of_memLp (Lp.memLp f) m).coeFn_toLp

private theorem dyadicMartingaleDifferenceL2CLM_coeFn (n : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (dyadicMartingaleDifferenceL2CLM n f : ℝ → ℂ) =ᵐ[volume]
      dyadicMartingaleDifference n (f : ℝ → ℂ) := by
  have hsub := Lp.coeFn_sub
    (dyadicAverageL2CLM (-n) f) (dyadicAverageL2CLM (1 - n) f)
  have hleft := dyadicAverageL2CLM_coeFn (-n) f
  have hright := dyadicAverageL2CLM_coeFn (1 - n) f
  filter_upwards [hsub, hleft, hright] with x hsub hleft hright
  calc
    (dyadicMartingaleDifferenceL2CLM n f : ℝ → ℂ) x =
        (dyadicAverageL2CLM (-n) f : ℝ → ℂ) x -
          (dyadicAverageL2CLM (1 - n) f : ℝ → ℂ) x := hsub
    _ = dyadicAverage (-n) (f : ℝ → ℂ) x -
        dyadicAverage (1 - n) (f : ℝ → ℂ) x := by rw [hleft, hright]
    _ = dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
      unfold dyadicMartingaleDifference dyadicIncreasingAverage
      rw [show -(n - 1) = 1 - n by omega]

def dyadicPredictableTermL2CLM (n : ℤ) (v : ℝ → ℝ)
    (hv : Measurable v) (_hvPredictable : ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v x = v y)
    (hvBound : ∀ x, |v x| ≤ 1) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] Lp ℂ 2 (volume : Measure ℝ) :=
  (dyadicRealMultiplierL2CLM v hv hvBound).comp
    (dyadicMartingaleDifferenceL2CLM n)

private theorem dyadicPredictableTermL2CLM_coeFn (n : ℤ) (v : ℝ → ℝ)
    (hv : Measurable v) (hvPredictable : ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v x = v y)
    (hvBound : ∀ x, |v x| ≤ 1) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (dyadicPredictableTermL2CLM n v hv hvPredictable hvBound f : ℝ → ℂ) =ᵐ[volume]
      fun x => (v x : ℂ) * dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
  have hmult := dyadicRealMultiplierL2CLM_coeFn v hv hvBound
    (dyadicMartingaleDifferenceL2CLM n f)
  have hdiff := dyadicMartingaleDifferenceL2CLM_coeFn n f
  filter_upwards [hmult, hdiff] with x hmult hdiff
  change (dyadicRealMultiplierL2CLM v hv hvBound
    (dyadicMartingaleDifferenceL2CLM n f) : ℝ → ℂ) x = _
  rw [hmult, hdiff]

private theorem dyadicPredictableTermL2CLM_eq_toLp (n : ℤ) (v : ℝ → ℝ)
    (hv : Measurable v) (hvPredictable : ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v x = v y)
    (hvBound : ∀ x, |v x| ≤ 1) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    dyadicPredictableTermL2CLM n v hv hvPredictable hvBound f =
      dyadicPredictableTermL2 (Lp.memLp f) n v hvPredictable hvBound := by
  apply Lp.ext
  have hleft := dyadicPredictableTermL2CLM_coeFn n v hv hvPredictable hvBound f
  have hright := (memLp_dyadicPredictableTerm_two (Lp.memLp f) n v hv hvBound).coeFn_toLp
  filter_upwards [hleft, hright] with x hleft hright
  calc
    (dyadicPredictableTermL2CLM n v hv hvPredictable hvBound f : ℝ → ℂ) x =
        (v x : ℂ) * dyadicMartingaleDifference n (f : ℝ → ℂ) x := hleft
    _ = (dyadicPredictableTermL2 (Lp.memLp f) n v hvPredictable hvBound : ℝ → ℂ) x :=
      hright.symm

def dyadicPredictableFamily (F : Finset ℤ) (v : ℤ → ℝ → ℝ) :
    ℤ → ℝ → ℝ := fun n => if n ∈ F then v n else 0

theorem dyadicPredictableFamily_predictable (F : Finset ℤ)
    (v : ℤ → ℝ → ℝ)
    (hv : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y) :
    ∀ n j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j →
        dyadicPredictableFamily F v n x = dyadicPredictableFamily F v n y := by
  intro n j x y hx hy
  by_cases hn : n ∈ F
  · simpa [dyadicPredictableFamily, hn] using hv n hn j hx hy
  · simp [dyadicPredictableFamily, hn]

theorem dyadicPredictableFamily_bound (F : Finset ℤ)
    (v : ℤ → ℝ → ℝ) (hv : ∀ n ∈ F, ∀ x, |v n x| ≤ 1) :
    ∀ n x, |dyadicPredictableFamily F v n x| ≤ 1 := by
  intro n x
  by_cases hn : n ∈ F
  · simpa [dyadicPredictableFamily, hn] using hv n hn x
  · simp [dyadicPredictableFamily, hn]

def dyadicPredictableTransformL2CLM (F : Finset ℤ)
    (v : ℤ → ℝ → ℝ)
    (hv : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n ∈ F, ∀ x, |v n x| ≤ 1) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] Lp ℂ 2 (volume : Measure ℝ) := by
  let vF := dyadicPredictableFamily F v
  letI hvF := dyadicPredictableFamily_predictable F v hv
  letI hbF := dyadicPredictableFamily_bound F v hvBound
  exact ∑ n ∈ F, dyadicPredictableTermL2CLM n (vF n)
    (measurable_of_constantOn_dyadicInterval (hvF n)) (hvF n) (hbF n)

private theorem dyadicPredictableTransformL2CLM_eq_termSum (F : Finset ℤ)
    (v : ℤ → ℝ → ℝ)
    (hv : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n ∈ F, ∀ x, |v n x| ≤ 1)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    dyadicPredictableTransformL2CLM F v hv hvBound f =
      ∑ n ∈ F, dyadicPredictableTermL2
        (Lp.memLp f) n (dyadicPredictableFamily F v n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) := by
  classical
  let vF := dyadicPredictableFamily F v
  have hsum : dyadicPredictableTransformL2CLM F v hv hvBound f =
      ∑ n ∈ F, dyadicPredictableTermL2CLM n (vF n)
        (measurable_of_constantOn_dyadicInterval
          (dyadicPredictableFamily_predictable F v hv n))
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) f := by
    simp [dyadicPredictableTransformL2CLM, vF, ContinuousLinearMap.sum_apply]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro n hn
  exact dyadicPredictableTermL2CLM_eq_toLp n (vF n)
    (measurable_of_constantOn_dyadicInterval
      (dyadicPredictableFamily_predictable F v hv n))
    (dyadicPredictableFamily_predictable F v hv n)
    (dyadicPredictableFamily_bound F v hvBound n) f

private theorem dyadicPredictableTransformL2CLM_norm_le (F : Finset ℤ)
    (v : ℤ → ℝ → ℝ)
    (hv : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n ∈ F, ∀ x, |v n x| ≤ 1)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖dyadicPredictableTransformL2CLM F v hv hvBound f‖ ≤ ‖f‖ := by
  have hsum := dyadicPredictableTransformL2CLM_eq_termSum F v hv hvBound f
  rw [hsum]
  have hnorm := dyadicPredictableTransformL2_norm_le (Lp.memLp f)
    (dyadicPredictableFamily F v)
    (dyadicPredictableFamily_predictable F v hv)
    (dyadicPredictableFamily_bound F v hvBound) F
  have htoLp : (Lp.memLp f).toLp (f : ℝ → ℂ) = f := by
    apply Lp.ext
    exact (Lp.memLp f).coeFn_toLp
  rw [htoLp] at hnorm
  exact hnorm

private theorem dyadicInterval_parent_subset_transform (m j : ℤ) :
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

private theorem dyadicInterval_ancestor_subset_transform
    (m j : ℤ) (k : ℕ) :
    dyadicInterval m j ⊆
      dyadicInterval (m + (k : ℤ)) (dyadicIntervalAncestor k j) := by
  induction k generalizing m j with
  | zero => simp [dyadicIntervalAncestor]
  | succ k ih =>
      calc
        dyadicInterval m j ⊆ dyadicInterval (m + 1) (j / 2) :=
          dyadicInterval_parent_subset_transform m j
        _ ⊆ dyadicInterval ((m + 1) + (k : ℤ))
            (dyadicIntervalAncestor k (j / 2)) := ih (m := m + 1) (j := j / 2)
        _ = dyadicInterval (m + ((k + 1 : ℕ) : ℤ))
            (dyadicIntervalAncestor (k + 1) j) := by
          simp only [dyadicIntervalAncestor]
          congr 1
          omega

private theorem dyadicInterval_inter_same_scale_index_transform
    {m j k : ℤ}
    (h : (dyadicInterval m j ∩ dyadicInterval m k).Nonempty) : j = k := by
  obtain ⟨x, hxj, hxk⟩ := h
  calc
    j = dyadicIntervalIndex m x :=
      (dyadicIntervalIndex_eq_of_mem hxj).symm
    _ = k := dyadicIntervalIndex_eq_of_mem hxk

private theorem dyadicInterval_nested_transform
    {m r j k : ℤ}
    (h : (dyadicInterval m j ∩ dyadicInterval r k).Nonempty) :
    dyadicInterval m j ⊆ dyadicInterval r k ∨
      dyadicInterval r k ⊆ dyadicInterval m j := by
  rcases le_total m r with hmr | hrm
  · let d : ℕ := (r - m).toNat
    have hd : (d : ℤ) = r - m := by
      dsimp [d]
      exact Int.toNat_of_nonneg (by omega)
    have hscale : m + (d : ℤ) = r := by omega
    have hsub : dyadicInterval m j ⊆
        dyadicInterval r (dyadicIntervalAncestor d j) := by
      simpa [hscale] using dyadicInterval_ancestor_subset_transform m j d
    obtain ⟨x, hxj, hxk⟩ := h
    have hinter :
        (dyadicInterval r (dyadicIntervalAncestor d j) ∩ dyadicInterval r k).Nonempty :=
      ⟨x, hsub hxj, hxk⟩
    have hindex := dyadicInterval_inter_same_scale_index_transform hinter
    rw [hindex] at hsub
    exact Or.inl hsub
  · let d : ℕ := (m - r).toNat
    have hd : (d : ℤ) = m - r := by
      dsimp [d]
      exact Int.toNat_of_nonneg (by omega)
    have hscale : r + (d : ℤ) = m := by omega
    have hsub : dyadicInterval r k ⊆
        dyadicInterval m (dyadicIntervalAncestor d k) := by
      simpa [hscale] using dyadicInterval_ancestor_subset_transform r k d
    obtain ⟨x, hxj, hxk⟩ := h
    have hinter :
        (dyadicInterval m (dyadicIntervalAncestor d k) ∩ dyadicInterval m j).Nonempty :=
      ⟨x, hsub hxk, hxj⟩
    have hindex := dyadicInterval_inter_same_scale_index_transform hinter
    rw [hindex] at hsub
    exact Or.inr hsub

private theorem dyadicInterval_subset_ninefold_transform (m j : ℤ) :
    dyadicInterval m j ⊆ dyadicNinefoldInterval m j := by
  intro x hx
  rw [dyadicInterval, Set.mem_Ico] at hx
  rw [dyadicNinefoldInterval, Set.mem_Ico]
  have hscale : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  constructor
  · have hleft : ((j - 4 : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : j - 4 ≤ j)
    exact (mul_le_mul_of_nonneg_right hleft hscale.le).trans hx.1
  · have hright : ((j + 1 : ℤ) : ℝ) ≤ ((j + 5 : ℤ) : ℝ) := by
      exact_mod_cast (by omega : j + 1 ≤ j + 5)
    exact lt_of_lt_of_le hx.2 (mul_le_mul_of_nonneg_right hright hscale.le)

private theorem dyadicAverage_eq_zero_of_meanZero_supported
    {u : ℝ → ℂ} (hmean : ∫ x, u x ∂volume = 0)
    (m j : ℤ) (hsupport : ∀ x, x ∉ dyadicInterval m j → u x = 0)
    (a : ℤ) {x : ℝ} (hx : x ∉ dyadicInterval m j) :
    dyadicAverage a u x = 0 := by
  let Q := dyadicInterval m j
  let R := dyadicInterval a (dyadicIntervalIndex a x)
  have hxR : x ∈ R := by
    exact mem_dyadicIntervalIndex a x
  have hQmeas : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hRmeas : MeasurableSet R := by
    dsimp [R, dyadicInterval]
    exact measurableSet_Ico
  have hsetIntegral_eq_of_subset (hQR : Q ⊆ R) :
      (∫ y in R, u y ∂volume) = ∫ y, u y ∂volume := by
    rw [← integral_indicator hRmeas]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ R
    · simp [Set.indicator, hy]
    · have hyQ : y ∉ Q := fun hyQ => hy (hQR hyQ)
      simp [Set.indicator, hy, hsupport y hyQ]
  have hsetIntegral_eq_zero (hdisj : Disjoint Q R) :
      (∫ y in R, u y ∂volume) = 0 := by
    rw [← integral_indicator hRmeas]
    have hae : R.indicator u =ᵐ[volume] (0 : ℝ → ℂ) := by
      filter_upwards [] with y
      by_cases hy : y ∈ R
      · have hyQ : y ∉ Q := by
          intro hyQ
          exact Set.disjoint_left.mp hdisj hyQ hy
        simp [Set.indicator, hy, hsupport y hyQ]
      · simp [Set.indicator, hy]
    rw [integral_congr_ae hae]
    simp
  by_cases hinter : (Q ∩ R).Nonempty
  · rcases dyadicInterval_nested_transform hinter with hQR | hRQ
    · have hRI : (∫ y in R, u y ∂volume) = 0 := by
        rw [hsetIntegral_eq_of_subset hQR, hmean]
      change ((2 : ℝ) ^ a)⁻¹ • ∫ y in R, u y ∂volume = 0
      rw [hRI]
      simp
    · have hxQ : x ∈ Q := hRQ hxR
      exact (hx hxQ).elim
  · have hdisj : Disjoint Q R := Set.disjoint_left.mpr (by
      intro y hyQ hyR
      exact hinter ⟨y, hyQ, hyR⟩)
    have hRI := hsetIntegral_eq_zero hdisj
    change ((2 : ℝ) ^ a)⁻¹ • ∫ y in R, u y ∂volume = 0
    rw [hRI]
    simp

private theorem dyadicMartingaleDifference_eq_zero_of_meanZero_supported
    {u : ℝ → ℂ} (hmean : ∫ x, u x ∂volume = 0)
    (m j n : ℤ) (hsupport : ∀ x, x ∉ dyadicInterval m j → u x = 0)
    {x : ℝ} (hx : x ∉ dyadicInterval m j) :
    dyadicMartingaleDifference n u x = 0 := by
  unfold dyadicMartingaleDifference dyadicIncreasingAverage
  rw [dyadicAverage_eq_zero_of_meanZero_supported hmean m j hsupport (-n) hx,
    dyadicAverage_eq_zero_of_meanZero_supported hmean m j hsupport (-(n - 1)) hx]
  simp

private theorem innerReal_complex_eq_re_mul_star (z w : ℂ) :
    inner ℝ z w = Complex.re (z * star w) := by
  rw [Complex.inner]
  change (w * star z).re = (z * star w).re
  calc
    (w * star z).re = (star (w * star z)).re := by simp
    _ = (star w * z).re := by simp [map_mul]
    _ = (z * star w).re := by congr 1 <;> ring

private theorem dyadicAverage_realInner_selfAdjoint {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (m : ℤ) :
    ∫ x, inner ℝ (dyadicAverage m f x) (g x) ∂volume =
      ∫ x, inner ℝ (f x) (dyadicAverage m g x) ∂volume := by
  have hfE : MemLp (dyadicAverage m f) 2 volume :=
    memLp_dyadicAverage_two_of_memLp hf m
  have hgE : MemLp (dyadicAverage m g) 2 volume :=
    memLp_dyadicAverage_two_of_memLp hg m
  have hleftInt : Integrable
      (fun x : ℝ => dyadicAverage m f x * star (g x)) volume :=
    MemLp.integrable_mul hfE hg.star
  have hrightInt : Integrable
      (fun x : ℝ => f x * star (dyadicAverage m g x)) volume :=
    MemLp.integrable_mul hf hgE.star
  have hcomplex := dyadicAverage_selfAdjoint hf hg m
  calc
    ∫ x, inner ℝ (dyadicAverage m f x) (g x) ∂volume =
        ∫ x, Complex.re (dyadicAverage m f x * star (g x)) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact innerReal_complex_eq_re_mul_star _ _
    _ = Complex.re (∫ x, dyadicAverage m f x * star (g x) ∂volume) :=
      integral_re hleftInt
    _ = Complex.re (∫ x, f x * star (dyadicAverage m g x) ∂volume) :=
      congrArg Complex.re hcomplex
    _ = ∫ x, Complex.re (f x * star (dyadicAverage m g x)) ∂volume :=
      (integral_re hrightInt).symm
    _ = ∫ x, inner ℝ (f x) (dyadicAverage m g x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (innerReal_complex_eq_re_mul_star _ _).symm

private theorem dyadicAverageL2CLM_selfAdjoint
    (m : ℤ) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℝ (dyadicAverageL2CLM m f) g =
      inner ℝ f (dyadicAverageL2CLM m g) := by
  letI : InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  have hf := dyadicAverageL2CLM_coeFn m f
  have hg := dyadicAverageL2CLM_coeFn m g
  calc
    inner ℝ (dyadicAverageL2CLM m f) g =
        ∫ x, inner ℝ ((dyadicAverageL2CLM m f : Lp ℂ 2 volume) x)
          ((g : Lp ℂ 2 volume) x) ∂volume := MeasureTheory.L2.inner_def _ _
    _ = ∫ x, inner ℝ (dyadicAverage m (f : ℝ → ℂ) x)
          ((g : ℝ → ℂ) x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
    _ = ∫ x, inner ℝ ((f : ℝ → ℂ) x)
          (dyadicAverage m (g : ℝ → ℂ) x) ∂volume :=
      dyadicAverage_realInner_selfAdjoint (Lp.memLp f) (Lp.memLp g) m
    _ = inner ℝ f (dyadicAverageL2CLM m g) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]

private theorem dyadicMartingaleDifferenceL2CLM_selfAdjoint
    (n : ℤ) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℝ (dyadicMartingaleDifferenceL2CLM n f) g =
      inner ℝ f (dyadicMartingaleDifferenceL2CLM n g) := by
  letI : InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  change inner ℝ (dyadicAverageL2CLM (-n) f - dyadicAverageL2CLM (1 - n) f) g =
    inner ℝ f (dyadicAverageL2CLM (-n) g - dyadicAverageL2CLM (1 - n) g)
  rw [inner_sub_left, inner_sub_right,
    dyadicAverageL2CLM_selfAdjoint (-n) f g,
    dyadicAverageL2CLM_selfAdjoint (1 - n) f g]

private theorem dyadicRealMultiplierL2CLM_selfAdjoint (v : ℝ → ℝ)
    (hv : Measurable v) (hvBound : ∀ x, |v x| ≤ 1)
    (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℝ (dyadicRealMultiplierL2CLM v hv hvBound f) g =
      inner ℝ f (dyadicRealMultiplierL2CLM v hv hvBound g) := by
  letI : InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  have hmf := dyadicRealMultiplierL2CLM_coeFn v hv hvBound f
  have hmg := dyadicRealMultiplierL2CLM_coeFn v hv hvBound g
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hmf, hmg] with x hmf hmg
  rw [hmf, hmg]
  change inner ℝ (v x • (f : ℝ → ℂ) x) ((g : ℝ → ℂ) x) =
    inner ℝ ((f : ℝ → ℂ) x) (v x • (g : ℝ → ℂ) x)
  simp [inner_smul_left, inner_smul_right]
  <;> ring

private theorem dyadicMartingaleDifferenceL2CLM_commute_multiplier
    (n : ℤ) (v : ℝ → ℝ) (hv : Measurable v)
    (hvPredictable : ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v x = v y)
    (hvBound : ∀ x, |v x| ≤ 1) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    dyadicMartingaleDifferenceL2CLM n (dyadicRealMultiplierL2CLM v hv hvBound g) =
      dyadicRealMultiplierL2CLM v hv hvBound (dyadicMartingaleDifferenceL2CLM n g) := by
  apply Lp.ext
  have hMAE := dyadicRealMultiplierL2CLM_coeFn v hv hvBound g
  have hDleft := dyadicMartingaleDifferenceL2CLM_coeFn n
    (dyadicRealMultiplierL2CLM v hv hvBound g)
  have hDg := dyadicMartingaleDifferenceL2CLM_coeFn n g
  have hMdelta := dyadicRealMultiplierL2CLM_coeFn v hv hvBound
    (dyadicMartingaleDifferenceL2CLM n g)
  filter_upwards [hMAE, hDleft, hDg, hMdelta] with x hMx hDleft hDg hMdelta
  calc
    (dyadicMartingaleDifferenceL2CLM n
        (dyadicRealMultiplierL2CLM v hv hvBound g) : ℝ → ℂ) x =
        dyadicMartingaleDifference n
          (dyadicRealMultiplierL2CLM v hv hvBound g : ℝ → ℂ) x := hDleft
    _ = dyadicMartingaleDifference n
        (fun y => (v y : ℂ) * (g : ℝ → ℂ) y) x := by
      unfold dyadicMartingaleDifference dyadicIncreasingAverage
      rw [dyadicAverage_eq_of_ae_eq hMAE (-n) x,
        dyadicAverage_eq_of_ae_eq hMAE (-(n - 1)) x]
    _ = (v x : ℂ) * dyadicMartingaleDifference n (g : ℝ → ℂ) x :=
      dyadicMartingaleDifference_mul_of_predictable (Lp.memLp g) n v hvPredictable x
    _ = (dyadicRealMultiplierL2CLM v hv hvBound
        (dyadicMartingaleDifferenceL2CLM n g) : ℝ → ℂ) x := by
      rw [← hDg]
      exact hMdelta.symm

private theorem dyadicPredictableTermL2CLM_selfAdjoint
    (n : ℤ) (v : ℝ → ℝ) (hv : Measurable v)
    (hvPredictable : ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v x = v y)
    (hvBound : ∀ x, |v x| ≤ 1) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℝ (dyadicPredictableTermL2CLM n v hv hvPredictable hvBound f) g =
      inner ℝ f (dyadicPredictableTermL2CLM n v hv hvPredictable hvBound g) := by
  letI : InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  change inner ℝ
      (dyadicRealMultiplierL2CLM v hv hvBound (dyadicMartingaleDifferenceL2CLM n f)) g =
    inner ℝ f
      (dyadicRealMultiplierL2CLM v hv hvBound (dyadicMartingaleDifferenceL2CLM n g))
  calc
    inner ℝ
        (dyadicRealMultiplierL2CLM v hv hvBound (dyadicMartingaleDifferenceL2CLM n f)) g =
      inner ℝ (dyadicMartingaleDifferenceL2CLM n f)
        (dyadicRealMultiplierL2CLM v hv hvBound g) :=
      dyadicRealMultiplierL2CLM_selfAdjoint v hv hvBound
        (dyadicMartingaleDifferenceL2CLM n f) g
    _ = inner ℝ f
        (dyadicMartingaleDifferenceL2CLM n
          (dyadicRealMultiplierL2CLM v hv hvBound g)) :=
      dyadicMartingaleDifferenceL2CLM_selfAdjoint n f
        (dyadicRealMultiplierL2CLM v hv hvBound g)
    _ = inner ℝ f
        (dyadicRealMultiplierL2CLM v hv hvBound (dyadicMartingaleDifferenceL2CLM n g)) := by
      rw [dyadicMartingaleDifferenceL2CLM_commute_multiplier n v hv hvPredictable
        hvBound g]

private theorem dyadicPredictableTransformL2CLM_selfAdjoint_pairing
    (F : Finset ℤ) (v : ℤ → ℝ → ℝ)
    (hv : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n ∈ F, ∀ x, |v n x| ≤ 1)
    (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℝ (dyadicPredictableTransformL2CLM F v hv hvBound f) g =
      inner ℝ f (dyadicPredictableTransformL2CLM F v hv hvBound g) := by
  classical
  letI : InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  let vF := dyadicPredictableFamily F v
  let hvF := dyadicPredictableFamily_predictable F v hv
  let hbF := dyadicPredictableFamily_bound F v hvBound
  have hbasef : dyadicPredictableTransformL2CLM F v hv hvBound f =
      ∑ n ∈ F, dyadicPredictableTermL2CLM n (vF n)
        (measurable_of_constantOn_dyadicInterval (hvF n)) (hvF n) (hbF n) f := by
    simp [dyadicPredictableTransformL2CLM, vF]
  have hbaseg : dyadicPredictableTransformL2CLM F v hv hvBound g =
      ∑ n ∈ F, dyadicPredictableTermL2CLM n (vF n)
        (measurable_of_constantOn_dyadicInterval (hvF n)) (hvF n) (hbF n) g := by
    simp [dyadicPredictableTransformL2CLM, vF]
  rw [hbasef, hbaseg, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact dyadicPredictableTermL2CLM_selfAdjoint n (vF n)
    (measurable_of_constantOn_dyadicInterval (hvF n)) (hvF n) (hbF n) f g

private theorem dyadicPredictableTransformL2CLM_ae_zero_off_ninefold
    (F : Finset ℤ) (v : ℤ → ℝ → ℝ)
    (hv : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n ∈ F, ∀ x, |v n x| ≤ 1)
    {u : ℝ → ℂ} (hu₂ : MemLp u 2 volume)
    (hmean : ∫ x, u x ∂volume = 0) (m j : ℤ)
    (hsupport : ∀ x, x ∉ dyadicInterval m j → u x = 0) :
    (dyadicPredictableTransformL2CLM F v hv hvBound (hu₂.toLp u) : ℝ → ℂ) =ᵐ[
      volume.restrict (dyadicNinefoldInterval m j)ᶜ] (0 : ℝ → ℂ) := by
  classical
  let vF := dyadicPredictableFamily F v
  let hvF := dyadicPredictableFamily_predictable F v hv
  let hbF := dyadicPredictableFamily_bound F v hvBound
  let f : Lp ℂ 2 (volume : Measure ℝ) := hu₂.toLp u
  have hfu : (f : ℝ → ℂ) =ᵐ[volume] u := by
    exact hu₂.coeFn_toLp
  have hsumCoe :
      (dyadicPredictableTransformL2CLM F v hv hvBound f : ℝ → ℂ) =ᵐ[volume]
        fun x => ∑ n ∈ F, (vF n x : ℂ) *
          dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
    have hbase : dyadicPredictableTransformL2CLM F v hv hvBound f =
        ∑ n ∈ F, dyadicPredictableTermL2CLM n (vF n)
          (measurable_of_constantOn_dyadicInterval (hvF n)) (hvF n) (hbF n) f := by
      simp [dyadicPredictableTransformL2CLM, vF, hvF, hbF]
    rw [hbase]
    calc
      (↑(∑ n ∈ F, dyadicPredictableTermL2CLM n (vF n)
          (measurable_of_constantOn_dyadicInterval (hvF n)) (hvF n) (hbF n) f) :
            ℝ → ℂ) =ᵐ[volume]
          fun x => ∑ n ∈ F,
            (dyadicPredictableTermL2CLM n (vF n)
              (measurable_of_constantOn_dyadicInterval (hvF n)) (hvF n) (hbF n) f :
                ℝ → ℂ) x :=
        Lp.coeFn_fun_finsetSum F (fun n => dyadicPredictableTermL2CLM n (vF n)
          (measurable_of_constantOn_dyadicInterval (hvF n)) (hvF n) (hbF n) f)
      _ =ᵐ[volume] fun x => ∑ n ∈ F, (vF n x : ℂ) *
          dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
        have hsumFn :
            (∑ n ∈ F, fun x : ℝ =>
              (dyadicPredictableTermL2CLM n (vF n)
                (measurable_of_constantOn_dyadicInterval (hvF n)) (hvF n) (hbF n) f :
                  ℝ → ℂ) x) =ᵐ[volume]
              ∑ n ∈ F, fun x : ℝ => (vF n x : ℂ) *
                dyadicMartingaleDifference n (f : ℝ → ℂ) x := by
          exact eventuallyEq_sum (s := F) fun n hn =>
            dyadicPredictableTermL2CLM_coeFn n (vF n)
              (measurable_of_constantOn_dyadicInterval (hvF n)) (hvF n) (hbF n) f
        filter_upwards [hsumFn] with x hx
        simpa only [Finset.sum_apply] using hx
  have hQsub : dyadicInterval m j ⊆ dyadicNinefoldInterval m j :=
    dyadicInterval_subset_ninefold_transform m j
  have hsumZero : ∀ x, x ∈ (dyadicNinefoldInterval m j)ᶜ →
      (∑ n ∈ F, (vF n x : ℂ) *
          dyadicMartingaleDifference n (f : ℝ → ℂ) x) = 0 := by
    intro x hx
    have hxQ : x ∉ dyadicInterval m j := fun hxQ => hx (hQsub hxQ)
    have hdiff : ∀ n : ℤ,
        dyadicMartingaleDifference n (f : ℝ → ℂ) x = 0 := by
      intro n
      have hdf : dyadicMartingaleDifference n (f : ℝ → ℂ) x =
          dyadicMartingaleDifference n u x := by
        unfold dyadicMartingaleDifference dyadicIncreasingAverage
        rw [dyadicAverage_eq_of_ae_eq hfu (-n) x,
          dyadicAverage_eq_of_ae_eq hfu (-(n - 1)) x]
      rw [hdf]
      exact dyadicMartingaleDifference_eq_zero_of_meanZero_supported
        hmean m j n hsupport hxQ
    apply Finset.sum_eq_zero
    intro n hn
    rw [hdiff n]
    simp
  have hzero : (dyadicPredictableTransformL2CLM F v hv hvBound f : ℝ → ℂ) =ᵐ[
      volume.restrict (dyadicNinefoldInterval m j)ᶜ] (0 : ℝ → ℂ) := by
    apply (ae_restrict_iff' (measurableSet_Ico.compl)).2
    filter_upwards [hsumCoe] with x hsumx
    intro hx
    calc
      (dyadicPredictableTransformL2CLM F v hv hvBound f : ℝ → ℂ) x =
          ∑ n ∈ F, (vF n x : ℂ) *
            dyadicMartingaleDifference n (f : ℝ → ℂ) x := hsumx
      _ = 0 := hsumZero x hx
  filter_upwards [hzero] with x hx
  simpa using hx

private theorem dyadicPredictableTransformL2CLM_offSupport
    (F : Finset ℤ) (v : ℤ → ℝ → ℝ)
    (hv : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n ∈ F, ∀ x, |v n x| ≤ 1) :
    weakCZOffSupportBound (dyadicPredictableTransformL2CLM F v hv hvBound) 0 := by
  intro u m j hu₁ hu₂ hmean hsupport
  let E := (dyadicNinefoldInterval m j)ᶜ
  let output := dyadicPredictableTransformL2CLM F v hv hvBound (hu₂.toLp u)
  have hzero : (output : ℝ → ℂ) =ᵐ[volume.restrict E] (0 : ℝ → ℂ) := by
    simpa [E, output] using
      dyadicPredictableTransformL2CLM_ae_zero_off_ninefold F v hv hvBound
        hu₂ hmean m j hsupport
  have hNorm : (fun x : ℝ => ‖(output : ℝ → ℂ) x‖) =ᵐ[
      volume.restrict E] (0 : ℝ → ℝ) := by
    filter_upwards [hzero] with x hx
    simp [hx]
  have hInt : Integrable (fun x : ℝ => ‖(output : ℝ → ℂ) x‖)
      (volume.restrict E) := by
    exact (integrable_zero ℝ ℝ (volume.restrict E)).congr hNorm.symm
  have hIntegral : (∫ x in E, ‖(output : ℝ → ℂ) x‖ ∂volume) = 0 := by
    change ∫ x, ‖(output : ℝ → ℂ) x‖ ∂(volume.restrict E) = 0
    rw [integral_congr_ae hNorm]
    simp
  refine ⟨hInt, ?_⟩
  change (∫ x in E, ‖(output : ℝ → ℂ) x‖ ∂volume) ≤
    0 * ∫ x, ‖u x‖ ∂volume
  rw [hIntegral]
  simp

/-- The finite predictable martingale transform on `L²`. The coefficient
functions are constant on the `P_{n-1}` cells and bounded by one. -/
def dyadicPredictableTransformL2 (F : Finset ℤ) (v : ℤ → ℝ → ℝ)
    (hv : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n ∈ F, ∀ x, |v n x| ≤ 1) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] Lp ℂ 2 (volume : Measure ℝ) :=
  dyadicPredictableTransformL2CLM F v hv hvBound

/-- On `L²`, the operator is the exact finite sum of the predictable terms. -/
theorem dyadicPredictableTransformL2_eq_sum (F : Finset ℤ) (v : ℤ → ℝ → ℝ)
    (hv : ∀ n ∈ F, ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n ∈ F, ∀ x, |v n x| ≤ 1)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    dyadicPredictableTransformL2 F v hv hvBound f =
      ∑ n ∈ F, dyadicPredictableTermL2 (Lp.memLp f) n
        (dyadicPredictableFamily F v n)
        (dyadicPredictableFamily_predictable F v hv n)
        (dyadicPredictableFamily_bound F v hvBound n) := by
  classical
  change dyadicPredictableTransformL2CLM F v hv hvBound f = _
  exact dyadicPredictableTransformL2CLM_eq_termSum F v hv hvBound f

/-- The paper's exact predictable-transform estimate: for every `1<p<∞`,
the finite transform over `L<n≤N` has a bounded `Lᵖ` extension with the
source constant `𝔠_p(1,0)`. Its restriction to `Lᵖ∩L²` is the finite `L²`
transform, so the extension is uniquely determined by the displayed finite
sum and density. -/
theorem predictableTransformBound (L N : ℤ) (hLN : L < N)
    (v : ℤ → ℝ → ℝ)
    (hv : ∀ n, L < n → n ≤ N → ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j → y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n, L < n → n ≤ N → ∀ x, |v n x| ≤ 1)
    (p : ℝ) (hp₁ : 1 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    ∃ U : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
        Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      (∀ f, ‖U f‖ ≤ weakTypeFromOffSupportStrongConstant p 1 0 * ‖f‖) ∧
      (∀ (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
        (hf₂ : MemLp (f : ℝ → ℂ) 2 volume),
        (U f : ℝ → ℂ) =ᵐ[volume]
          (dyadicPredictableTransformL2 (Finset.Ioc L N) v
            (fun n hn => by
              rcases Finset.mem_Ioc.mp hn with ⟨hLn, hnN⟩
              exact hv n hLn hnN)
            (fun n hn => by
              rcases Finset.mem_Ioc.mp hn with ⟨hLn, hnN⟩
              exact hvBound n hLn hnN)
            (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ)) := by
  classical
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
  have hTnorm : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound (by norm_num)
    intro f
    simpa [T, dyadicPredictableTransformL2] using
      dyadicPredictableTransformL2CLM_norm_le F v hvF hvBoundF f
  have hOff : weakCZOffSupportBound T 0 := by
    simpa [T, dyadicPredictableTransformL2] using
      dyadicPredictableTransformL2CLM_offSupport F v hvF hvBoundF
  have hPair : ∀ (f : Lp ℂ 2 (volume : Measure ℝ))
      (g : Lp ℂ 2 (volume : Measure ℝ)),
      (∫ x, inner ℝ ((T f : Lp ℂ 2 volume) x) (g x) ∂volume) =
        ∫ x, inner ℝ (f x) ((T g : Lp ℂ 2 volume) x) ∂volume := by
    letI : InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure ℝ)) :=
      MeasureTheory.L2.innerProductSpace
    intro f g
    calc
      ∫ x, inner ℝ ((T f : Lp ℂ 2 volume) x) (g x) ∂volume =
          inner ℝ (T f) g := (MeasureTheory.L2.inner_def _ _).symm
      _ = inner ℝ f (T g) :=
        by simpa [T, dyadicPredictableTransformL2] using
          dyadicPredictableTransformL2CLM_selfAdjoint_pairing F v hvF hvBoundF f g
      _ = ∫ x, inner ℝ (f x) ((T g : Lp ℂ 2 volume) x) ∂volume :=
        MeasureTheory.L2.inner_def _ _
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
  exact weakTypeFromOffSupport_extension_agrees_on_Lp_inter_L2
    T hTnorm hOff T hPair hTnorm hOff p hp₁

/-- At `p=2`, the source constant specializes exactly to one. -/
theorem predictableTransformStrongConstant_two :
    weakTypeFromOffSupportStrongConstant 2 1 0 = 1 := by
  simp [weakTypeFromOffSupportStrongConstant]

/-- A continuous `Lᵖ` extension agreeing with a fixed `L²` operator on every
input in `Lᵖ∩L²` is unique. Schwartz functions are dense in finite `Lᵖ` and
belong to `L²`, so agreement on the common domain determines the operator. -/
theorem lpContinuousOperator_eq_of_agree_on_l2
    {P : ENNReal} [Fact (1 ≤ P)] (hP : P ≠ ⊤)
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] Lp ℂ 2 (volume : Measure ℝ))
    (U V : Lp ℂ P (volume : Measure ℝ) →L[ℝ] Lp ℂ P (volume : Measure ℝ))
    (hU : ∀ (f : Lp ℂ P volume)
      (hf₂ : MemLp (f : ℝ → ℂ) 2 volume),
      (U f : ℝ → ℂ) =ᵐ[volume]
        (T (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ))
    (hV : ∀ (f : Lp ℂ P volume)
      (hf₂ : MemLp (f : ℝ → ℂ) 2 volume),
      (V f : ℝ → ℂ) =ᵐ[volume]
        (T (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ)) :
    U = V := by
  let e : SchwartzMap ℝ ℂ →L[ℝ] Lp ℂ P (volume : Measure ℝ) :=
    SchwartzMap.toLpCLM ℝ ℂ P (volume : Measure ℝ)
  have hdense : DenseRange e := by
    exact SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) hP
  have heq : (fun g : SchwartzMap ℝ ℂ => U (e g)) =
      (fun g : SchwartzMap ℝ ℂ => V (e g)) := by
    funext g
    have hcoe : (e g : ℝ → ℂ) =ᵐ[volume] (g : ℝ → ℂ) := by
      change (g.toLp P volume : ℝ → ℂ) =ᵐ[volume] (g : ℝ → ℂ)
      exact g.coeFn_toLp P volume
    have hg₂ : MemLp (e g : ℝ → ℂ) 2 volume :=
      (memLp_congr_ae hcoe).mpr (g.memLp 2 volume)
    have hUg := hU (e g) hg₂
    have hVg := hV (e g) hg₂
    apply Lp.ext
    filter_upwards [hUg, hVg] with x hUx hVx
    exact hUx.trans hVx.symm
  have hfun : (U : Lp ℂ P (volume : Measure ℝ) → Lp ℂ P (volume : Measure ℝ)) = V :=
    hdense.equalizer U.continuous V.continuous heq
  exact ContinuousLinearMap.ext (fun f => congrFun hfun f)

/-- Reuse the checked atom-support fact for the smooth/dyadic comparison. -/
theorem dyadicAverage_meanZeroAtom_zero_off
    {u : ℝ → ℂ} (hmean : ∫ x, u x ∂volume = 0)
    (m j : ℤ) (hsupport : ∀ x, x ∉ dyadicInterval m j → u x = 0)
    (a : ℤ) {x : ℝ} (hx : x ∉ dyadicInterval m j) :
    dyadicAverage a u x = 0 :=
  dyadicAverage_eq_zero_of_meanZero_supported hmean m j hsupport a hx

/-- The checked half-open dyadic cell lies inside its ninefold enlargement. -/
theorem dyadicInterval_subset_ninefold (m j : ℤ) :
    dyadicInterval m j ⊆ dyadicNinefoldInterval m j :=
  dyadicInterval_subset_ninefold_transform m j

#print axioms dyadicAverage_meanZeroAtom_zero_off
#print axioms dyadicInterval_subset_ninefold

end

end FractionalPrimes.Literature.JSW

end
