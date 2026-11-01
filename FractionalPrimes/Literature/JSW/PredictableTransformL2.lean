module

public import FractionalPrimes.Literature.JSW.DyadicAverageL2Expansion
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The L² core of predictable dyadic transforms

This module isolates the orthogonality argument used in the `L²` part of
`lj:martingale-transform`.  It does not assert the missing full `Lᵖ`
martingale-transform theorem.
-/

@[expose] public section

open MeasureTheory

namespace FractionalPrimes.Literature.JSW

noncomputable section

private theorem dyadicInterval_leftEndpoint_mem_local (m j : ℤ) :
    (j : ℝ) * (2 : ℝ) ^ m ∈ dyadicInterval m j := by
  rw [dyadicInterval, Set.mem_Ico]
  constructor
  · exact le_rfl
  · have hpos : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
    push_cast
    nlinarith [hpos]

/-- A real function constant on every half-open dyadic cell is measurable. -/
theorem measurable_of_constantOn_dyadicInterval {m : ℤ} {v : ℝ → ℝ}
    (hv : ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval m j → y ∈ dyadicInterval m j → v x = v y) :
    Measurable v := by
  classical
  let c : ℤ → ℝ := fun j => v ((j : ℝ) * (2 : ℝ) ^ m)
  have hrepr : v = fun x => c (dyadicIntervalIndex m x) := by
    funext x
    dsimp [c]
    exact hv (dyadicIntervalIndex m x)
      (mem_dyadicIntervalIndex m x)
      (dyadicInterval_leftEndpoint_mem_local m (dyadicIntervalIndex m x))
  rw [hrepr]
  exact (Measurable.of_discrete (f := c)).comp
    (Int.measurable_floor.comp (by fun_prop))

private theorem dyadicInterval_parent_subset_local (m j : ℤ) :
    dyadicInterval m j ⊆ dyadicInterval (m + 1) (j / 2) := by
  have hmod : j % 2 = 0 ∨ j % 2 = 1 := Int.emod_two_eq_zero_or_one j
  have hlen : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hscale : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 := by
    rw [show m + 1 = m + (1 : ℤ) by rfl, zpow_add₀ (by norm_num), zpow_one]
  have hdecomp : j % 2 + 2 * (j / 2) = j := Int.emod_add_mul_ediv j 2
  rcases hmod with hmod | hmod
  · have hji : (j : ℝ) = 2 * ((j / 2 : ℤ) : ℝ) := by
      have h := hdecomp
      rw [hmod] at h
      exact_mod_cast (by omega : j = 2 * (j / 2))
    intro x hx
    simp only [dyadicInterval, Set.mem_Ico] at hx ⊢
    rw [hscale]
    constructor
    · nlinarith [hx.1]
    · have hupper : ((j + 1 : ℤ) : ℝ) =
          2 * ((j / 2 : ℤ) : ℝ) + 1 := by rw [Int.cast_add, Int.cast_one, hji]
      rw [hupper] at hx
      have hcmp :
          (2 * ((j / 2 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ m ≤
            (((j / 2 + 1 : ℤ) : ℝ)) * ((2 : ℝ) ^ m * 2) := by
        rw [Int.cast_add, Int.cast_one]
        calc
          _ = (((j / 2 : ℤ) : ℝ) + 1) * ((2 : ℝ) ^ m * 2) - (2 : ℝ) ^ m := by ring
          _ ≤ _ := by linarith [hlen]
      exact lt_of_lt_of_le hx.2 hcmp
  · have hji : (j : ℝ) = 2 * ((j / 2 : ℤ) : ℝ) + 1 := by
      have h := hdecomp
      rw [hmod] at h
      exact_mod_cast (by omega : j = 2 * (j / 2) + 1)
    intro x hx
    simp only [dyadicInterval, Set.mem_Ico] at hx ⊢
    rw [hscale]
    constructor
    · nlinarith [hx.1]
    · have hupper : ((j + 1 : ℤ) : ℝ) =
          2 * ((j / 2 : ℤ) : ℝ) + 2 := by rw [Int.cast_add, Int.cast_one, hji]; ring
      rw [hupper] at hx
      calc
        x < (2 * ((j / 2 : ℤ) : ℝ) + 2) * (2 : ℝ) ^ m := hx.2
        _ = ((j / 2 + 1 : ℤ) : ℝ) * ((2 : ℝ) ^ m * 2) := by
          rw [Int.cast_add, Int.cast_one]
          ring

/-- Averaging commutes with multiplication by a real function that is
constant on the averaging cell. -/
theorem dyadicAverage_mul_of_constantOn_cell {m : ℤ} {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (v : ℝ → ℝ)
    (hv : ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval m j → y ∈ dyadicInterval m j → v x = v y)
    (x : ℝ) :
    dyadicAverage m (fun y => (v y : ℂ) * f y) x =
      (v x : ℂ) * dyadicAverage m f x := by
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
  have hvQ : ∀ y ∈ Q, v y = v x := by
    intro y hy
    have hx : x ∈ dyadicInterval m (dyadicIntervalIndex m x) :=
      mem_dyadicIntervalIndex m x
    have hy' : y ∈ dyadicInterval m (dyadicIntervalIndex m x) := by
      simpa [Q] using hy
    exact hv (dyadicIntervalIndex m x) hy' hx
  unfold dyadicAverage
  change ((2 : ℝ) ^ m)⁻¹ •
      ∫ y in Q, (v y : ℂ) * f y ∂volume =
    (v x : ℂ) * (((2 : ℝ) ^ m)⁻¹ •
      ∫ y in Q, f y ∂volume)
  have hint :
      ∫ y in Q, (v y : ℂ) * f y ∂volume =
        ∫ y in Q, (v x : ℂ) * f y ∂volume := by
    apply MeasureTheory.setIntegral_congr_fun hQ
    exact fun y hy => by rw [hvQ y hy]
  rw [hint]
  change ((2 : ℝ) ^ m)⁻¹ •
      ∫ y, (v x : ℂ) * f y ∂(volume.restrict Q) =
    (v x : ℂ) * (((2 : ℝ) ^ m)⁻¹ •
      ∫ y, f y ∂(volume.restrict Q))
  rw [integral_const_mul]
  exact smul_comm ((2 : ℝ) ^ m)⁻¹ (v x : ℂ) _

/-- A bounded measurable real multiplier preserves `L²` and does not increase
the `L²` norm. -/
theorem memLp_mul_of_abs_le_one {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (v : ℝ → ℝ)
    (hv : Measurable v) (hvBound : ∀ x, |v x| ≤ 1) :
    MemLp (fun x => (v x : ℂ) * f x) 2 volume := by
  apply hf.of_le
  · have hvm : Measurable (fun x => (v x : ℂ)) := by fun_prop
    exact hvm.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · filter_upwards [] with x
    rw [norm_mul, Complex.norm_real]
    simpa [Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right (hvBound x) (norm_nonneg (f x))

private theorem constantOn_fine_cells_of_constantOn_parent_cells
    {m : ℤ} {v : ℝ → ℝ}
    (hv : ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval m j → y ∈ dyadicInterval m j → v x = v y) :
    ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (m - 1) j →
      y ∈ dyadicInterval (m - 1) j → v x = v y := by
  intro j x y hx hy
  have hxParent := dyadicInterval_parent_subset_local (m - 1) j hx
  have hyParent := dyadicInterval_parent_subset_local (m - 1) j hy
  have hscale : m - 1 + 1 = m := by omega
  have hxParent' : x ∈ dyadicInterval m (j / 2) := by
    simpa [hscale] using hxParent
  have hyParent' : y ∈ dyadicInterval m (j / 2) := by
    simpa [hscale] using hyParent
  exact hv (j / 2) hxParent' hyParent'

/-- Multiplication by a `P_{n-1}`-measurable real function commutes with
the `n`th dyadic martingale difference. -/
theorem dyadicMartingaleDifference_mul_of_predictable {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (n : ℤ) (v : ℝ → ℝ)
    (hv : ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j →
      y ∈ dyadicInterval (1 - n) j → v x = v y)
    (x : ℝ) :
    dyadicMartingaleDifference n (fun y => (v y : ℂ) * f y) x =
      (v x : ℂ) * dyadicMartingaleDifference n f x := by
  have hFineConst : ∀ j : ℤ, ∀ ⦃y z : ℝ⦄,
      y ∈ dyadicInterval ((1 - n) - 1) j →
      z ∈ dyadicInterval ((1 - n) - 1) j → v y = v z :=
    constantOn_fine_cells_of_constantOn_parent_cells hv
  have hFine := dyadicAverage_mul_of_constantOn_cell
    (m := (1 - n) - 1) hf v hFineConst x
  have hCoarse := dyadicAverage_mul_of_constantOn_cell
    (m := 1 - n) hf v hv x
  have hFineScale : (1 - n) - 1 = -n := by omega
  have hCoarseScale : -(n - 1) = 1 - n := by omega
  unfold dyadicMartingaleDifference dyadicIncreasingAverage
  rw [hFineScale] at hFine
  rw [hCoarseScale]
  rw [hFine, hCoarse]
  ring

/-- The increasing-filtration increment `d_n` is the decreasing-scale
difference `Δ_{1-n}` under the approved sign convention. -/
theorem dyadicMartingaleDifference_eq_dyadicDifference
    (n : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    dyadicMartingaleDifference n f x = dyadicDifference (1 - n) f x := by
  unfold dyadicMartingaleDifference dyadicIncreasingAverage dyadicDifference
  rw [show (1 - n) - 1 = -n by omega,
    show 1 - n = -(n - 1) by omega]

/-- The `n`th predictable term belongs to `L²` whenever the coefficient is
measurable and bounded by one. -/
theorem memLp_dyadicPredictableTerm_two {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (n : ℤ) (v : ℝ → ℝ)
    (hv : Measurable v) (hvBound : ∀ x, |v x| ≤ 1) :
    MemLp (fun x => (v x : ℂ) * dyadicMartingaleDifference n f x)
      2 volume := by
  have hdelta : MemLp (dyadicMartingaleDifference n f) 2 volume := by
    apply (memLp_congr_ae (Filter.Eventually.of_forall fun x =>
      dyadicMartingaleDifference_eq_dyadicDifference n f x)).2
    exact memLp_dyadicDifference_two_of_memLp hf (1 - n)
  exact memLp_mul_of_abs_le_one hdelta v hv hvBound

/-- A predictable coefficient bounded by one does not increase the norm of
its dyadic martingale-difference term. -/
theorem dyadicPredictableTerm_norm_le {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (n : ℤ) (v : ℝ → ℝ)
    (hv : Measurable v) (hvBound : ∀ x, |v x| ≤ 1) :
    ‖(memLp_dyadicPredictableTerm_two hf n v hv hvBound).toLp
        (fun x => (v x : ℂ) * dyadicMartingaleDifference n f x)‖ ≤
      ‖dyadicDifferenceL2Vector hf (1 - n)‖ := by
  let ht := memLp_dyadicPredictableTerm_two hf n v hv hvBound
  let hd := memLp_dyadicDifference_two_of_memLp hf (1 - n)
  have hpoint (x : ℝ) :
      ‖(v x : ℂ) * dyadicMartingaleDifference n f x‖ ≤
        ‖dyadicDifference (1 - n) f x‖ := by
    rw [dyadicMartingaleDifference_eq_dyadicDifference]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |v x| * ‖dyadicDifference (1 - n) f x‖ ≤
          1 * ‖dyadicDifference (1 - n) f x‖ :=
            mul_le_mul_of_nonneg_right (hvBound x) (norm_nonneg _)
      _ = ‖dyadicDifference (1 - n) f x‖ := by ring
  have henorm :
      eLpNorm (fun x => (v x : ℂ) * dyadicMartingaleDifference n f x)
          2 volume ≤ eLpNorm (dyadicDifference (1 - n) f) 2 volume :=
    eLpNorm_mono_ae ht.aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  calc
    ‖ht.toLp (fun x => (v x : ℂ) * dyadicMartingaleDifference n f x)‖ =
        (eLpNorm (fun x => (v x : ℂ) * dyadicMartingaleDifference n f x)
          2 volume).toReal := by rw [MeasureTheory.Lp.norm_toLp]
    _ ≤ (eLpNorm (dyadicDifference (1 - n) f) 2 volume).toReal :=
      ENNReal.toReal_mono hd.eLpNorm_ne_top henorm
    _ = ‖dyadicDifferenceL2Vector hf (1 - n)‖ := by
      rw [dyadicDifferenceL2Vector, MeasureTheory.Lp.norm_toLp]

/-- The `L²` representative of one predictable dyadic transform term. -/
noncomputable def dyadicPredictableTermL2 {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (n : ℤ) (v : ℝ → ℝ)
    (hv : ∀ j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j →
      y ∈ dyadicInterval (1 - n) j → v x = v y)
    (hvBound : ∀ x, |v x| ≤ 1) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_dyadicPredictableTerm_two hf n v
    (measurable_of_constantOn_dyadicInterval hv) hvBound).toLp
      (fun x => (v x : ℂ) * dyadicMartingaleDifference n f x)

/-- Distinct predictable dyadic transform terms remain orthogonal in `L²`.
The identity `d_n(v_n f)=v_n d_n f` reduces this to orthogonality of
dyadic differences, allowing the input to vary with the scale. -/
theorem dyadicPredictableTerm_inner_eq_zero {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (v : ℤ → ℝ → ℝ)
    (hv : ∀ n j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j →
      y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n x, |v n x| ≤ 1) {m n : ℤ} (hmn : m ≠ n) :
    inner ℂ (dyadicPredictableTermL2 hf n (v n) (hv n) (hvBound n))
      (dyadicPredictableTermL2 hf m (v m) (hv m) (hvBound m)) = 0 := by
  let w : ℤ → ℝ → ℂ := fun k x => (v k x : ℂ) * f x
  have hw (k : ℤ) : MemLp (w k) 2 volume := by
    dsimp [w]
    exact memLp_mul_of_abs_le_one hf (v k)
      (measurable_of_constantOn_dyadicInterval (hv k)) (hvBound k)
  have hrepr (k : ℤ) (x : ℝ) :
      dyadicDifference (1 - k) (w k) x =
        (v k x : ℂ) * dyadicMartingaleDifference k f x := by
    calc
      dyadicDifference (1 - k) (w k) x =
          dyadicMartingaleDifference k (w k) x :=
        (dyadicMartingaleDifference_eq_dyadicDifference k (w k) x).symm
      _ = (v k x : ℂ) * dyadicMartingaleDifference k f x :=
        dyadicMartingaleDifference_mul_of_predictable hf k (v k) (hv k) x
  rw [MeasureTheory.L2.inner_def]
  change ∫ x,
      dyadicPredictableTermL2 hf m (v m) (hv m) (hvBound m) x *
        star (dyadicPredictableTermL2 hf n (v n) (hv n) (hvBound n) x)
        ∂volume = 0
  have hzero : ∫ x, dyadicDifference (1 - m) (w m) x *
      star (dyadicDifference (1 - n) (w n) x) ∂volume = 0 := by
    apply dyadicDifference_pairwise_orthogonal (hw m) (hw n)
    omega
  calc
    ∫ x,
        dyadicPredictableTermL2 hf m (v m) (hv m) (hvBound m) x *
          star (dyadicPredictableTermL2 hf n (v n) (hv n) (hvBound n) x)
          ∂volume =
      ∫ x, dyadicDifference (1 - m) (w m) x *
          star (dyadicDifference (1 - n) (w n) x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [
          (memLp_dyadicPredictableTerm_two hf m (v m)
            (measurable_of_constantOn_dyadicInterval (hv m))
            (hvBound m)).coeFn_toLp,
          (memLp_dyadicPredictableTerm_two hf n (v n)
            (measurable_of_constantOn_dyadicInterval (hv n))
            (hvBound n)).coeFn_toLp] with x hm hn
        simp only [dyadicPredictableTermL2, hm, hn]
        rw [← hrepr m x, ← hrepr n x]
    _ = 0 := hzero

/-- The finite predictable transform is an `L²` contraction. This is the
orthogonal part of the source's martingale-transform estimate; the full
`Lᵖ` theorem still requires the separate weak-CZ argument. -/
theorem dyadicPredictableTransformL2_norm_le {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (v : ℤ → ℝ → ℝ)
    (hv : ∀ n j : ℤ, ∀ ⦃x y : ℝ⦄,
      x ∈ dyadicInterval (1 - n) j →
      y ∈ dyadicInterval (1 - n) j → v n x = v n y)
    (hvBound : ∀ n x, |v n x| ≤ 1) (s : Finset ℤ) :
    ‖∑ n ∈ s,
        dyadicPredictableTermL2 hf n (v n) (hv n) (hvBound n)‖ ≤
      ‖hf.toLp f‖ := by
  classical
  let U : ℤ → Lp ℂ 2 (volume : Measure ℝ) := fun n =>
    dyadicPredictableTermL2 hf n (v n) (hv n) (hvBound n)
  have hinner {m n : ℤ} (hmn : m ≠ n) : inner ℂ (U m) (U n) = 0 := by
    simpa [U] using
      (dyadicPredictableTerm_inner_eq_zero hf v hv hvBound
        (m := n) (n := m) hmn.symm)
  let V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) := fun n => ℂ ∙ U n
  let u : (n : ℤ) → V n := fun n =>
    ⟨U n, Submodule.mem_span_singleton_self (U n)⟩
  have hpair : Pairwise (fun m n : ℤ => V m ⟂ V n) := by
    intro m n hmn
    rw [Submodule.isOrtho_iff_inner_eq]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [inner_smul_left, inner_smul_right, hinner hmn]
  have hfamily : OrthogonalFamily ℂ (fun n => (V n : Type _))
      (fun n => (V n).subtypeₗᵢ) := OrthogonalFamily.of_pairwise hpair
  have hpyth :
      ‖∑ n ∈ s, U n‖ ^ 2 = ∑ n ∈ s, ‖U n‖ ^ 2 := by
    simpa [U, u] using hfamily.norm_sum u s
  have hterm (n : ℤ) :
      ‖U n‖ ≤ ‖dyadicDifferenceL2Vector hf (1 - n)‖ := by
    simpa [U, dyadicPredictableTermL2] using
      (dyadicPredictableTerm_norm_le hf n (v n)
        (measurable_of_constantOn_dyadicInterval (hv n)) (hvBound n))
  let q : ℤ → ℝ := fun m => ‖dyadicDifferenceL2Vector hf m‖ ^ 2
  have hmap : Set.InjOn (fun n : ℤ => 1 - n) (↑s : Set ℤ) := by
    intro m hm n hn hmn
    exact (sub_right_inj).mp hmn
  have hparseval := dyadicDifferenceL2Vector_parseval hf
  have hsquared : ‖∑ n ∈ s, U n‖ ^ 2 ≤ ‖hf.toLp f‖ ^ 2 := by
    rw [hpyth]
    calc
      ∑ n ∈ s, ‖U n‖ ^ 2 ≤ ∑ n ∈ s, q (1 - n) := by
        apply Finset.sum_le_sum
        intro n hn
        have h := hterm n
        dsimp [q]
        exact (sq_le_sq₀ (norm_nonneg (U n))
          (norm_nonneg (dyadicDifferenceL2Vector hf (1 - n)))).2 h
      _ = ∑ m ∈ Finset.image (fun n : ℤ => 1 - n) s, q m := by
        symm
        exact Finset.sum_image hmap
      _ ≤ ∑' m : ℤ, q m :=
        hparseval.summable.sum_le_tsum _ (by intro m hm; positivity)
      _ = ‖hf.toLp f‖ ^ 2 := hparseval.tsum_eq
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsquared

end

end FractionalPrimes.Literature.JSW

#print axioms FractionalPrimes.Literature.JSW.dyadicPredictableTerm_norm_le
#print axioms FractionalPrimes.Literature.JSW.dyadicPredictableTerm_inner_eq_zero
#print axioms FractionalPrimes.Literature.JSW.dyadicPredictableTransformL2_norm_le

end
