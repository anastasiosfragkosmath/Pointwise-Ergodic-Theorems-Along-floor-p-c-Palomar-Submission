module

public import FractionalPrimes.Literature.JSW.DyadicAverageL2Expansion
public import FractionalPrimes.Literature.JSW.MaximalBounds

/-!
# Finite-vector dyadic averages

This module begins the finite-vector averaging input needed by the dyadic
Calderón–Zygmund decomposition.
-/

@[expose] public section

open MeasureTheory Filter Topology IsUnifLocDoublingMeasure

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The half-open dyadic-cell average of a real normed-space-valued function. -/
def dyadicVectorAverage {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (m : ℤ) (f : ℝ → H) (x : ℝ) : H :=
  ((2 : ℝ) ^ m)⁻¹ •
    ∫ y in dyadicInterval m (dyadicIntervalIndex m x), f y ∂volume

/-- The average size of a vector input on a specified dyadic cell. -/
def dyadicVectorNormCellAverage {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (m j : ℤ) : ℝ :=
  (∫ x in dyadicInterval m j, ‖f x‖ ∂volume) / (2 : ℝ) ^ m

/-- The vector average on a specified dyadic cell. -/
def dyadicVectorCellAverage {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (m j : ℤ) : H :=
  ((2 : ℝ) ^ m)⁻¹ • ∫ x in dyadicInterval m j, f x ∂volume

/-- The mean-zero vector bad piece on one dyadic cell. -/
def dyadicVectorBadPiece {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (m j : ℤ) : ℝ → H :=
  (dyadicInterval m j).indicator
    (fun x => f x - dyadicVectorCellAverage f m j)

private theorem dyadicInterval_volume_vector (m j : ℤ) :
    volume (dyadicInterval m j) = ENNReal.ofReal ((2 : ℝ) ^ m) := by
  rw [dyadicInterval, Real.volume_Ico]
  congr 1
  push_cast
  ring

/-- A vector bad piece vanishes outside its defining dyadic cell. -/
theorem dyadicVectorBadPiece_eq_zero_of_not_mem {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (m j : ℤ) {x : ℝ}
    (hx : x ∉ dyadicInterval m j) :
    dyadicVectorBadPiece f m j x = 0 := by
  simp [dyadicVectorBadPiece, hx]

/-- A vector bad piece is integrable when the original input is. -/
theorem integrable_dyadicVectorBadPiece {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} (hf : Integrable f volume) (m j : ℤ) :
    Integrable (dyadicVectorBadPiece f m j) volume := by
  let Q := dyadicInterval m j
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hfinite : volume Q ≠ ⊤ := by
    rw [dyadicInterval_volume_vector]
    exact ENNReal.ofReal_ne_top
  have hfQ : IntegrableOn f Q volume := hf.integrableOn
  have hcQ : IntegrableOn (fun _ : ℝ => dyadicVectorCellAverage f m j)
      Q volume := by
    exact MeasureTheory.integrableOn_const hfinite
  have hdiffQ : IntegrableOn (fun x : ℝ => f x - dyadicVectorCellAverage f m j)
      Q volume := hfQ.sub hcQ
  have hpiece := hdiffQ.integrable_indicator hQ
  simpa [dyadicVectorBadPiece, Q] using hpiece

/-- The average vector on a cell is bounded by the average of the input norm. -/
theorem norm_dyadicVectorCellAverage_le_normCellAverage {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (f : ℝ → H) (m j : ℤ) :
    ‖dyadicVectorCellAverage f m j‖ ≤ dyadicVectorNormCellAverage f m j := by
  let s := (2 : ℝ) ^ m
  have hs : 0 < s := by dsimp [s]; exact zpow_pos (by norm_num) m
  have hinv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  change ‖s⁻¹ • ∫ x in dyadicInterval m j, f x ∂volume‖ ≤ _
  calc
    ‖s⁻¹ • ∫ x in dyadicInterval m j, f x ∂volume‖ =
        s⁻¹ * ‖∫ x in dyadicInterval m j, f x ∂volume‖ := by
      rw [norm_smul, Real.norm_of_nonneg hinv]
    _ ≤ s⁻¹ * ∫ x in dyadicInterval m j, ‖f x‖ ∂volume :=
      mul_le_mul_of_nonneg_left
        (MeasureTheory.norm_integral_le_integral_norm f) hinv
    _ = dyadicVectorNormCellAverage f m j := by
      simp [s, dyadicVectorNormCellAverage, div_eq_mul_inv, mul_comm]

/-- The `L¹` norm of one mean-zero bad piece is at most twice the input mass
on its cell. -/
theorem integral_norm_dyadicVectorBadPiece_le_two {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} (hf : Integrable f volume) (m j : ℤ) :
    ∫ x, ‖dyadicVectorBadPiece f m j x‖ ∂volume ≤
      2 * ∫ x in dyadicInterval m j, ‖f x‖ ∂volume := by
  let Q := dyadicInterval m j
  let c := dyadicVectorCellAverage f m j
  let s := (2 : ℝ) ^ m
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hs : 0 < s := by dsimp [s]; exact zpow_pos (by norm_num) m
  have hfinite : volume Q ≠ ⊤ := by
    rw [dyadicInterval_volume_vector]
    exact ENNReal.ofReal_ne_top
  have hfQ : Integrable f (volume.restrict Q) := by
    change IntegrableOn f Q volume
    exact hf.integrableOn
  have hcQ : Integrable (fun _ : ℝ => c) (volume.restrict Q) := by
    change IntegrableOn (fun _ : ℝ => c) Q volume
    exact MeasureTheory.integrableOn_const hfinite
  have hdiffQ : Integrable (fun x : ℝ => f x - c) (volume.restrict Q) :=
    hfQ.sub hcQ
  have hnormEq : (fun x : ℝ => ‖dyadicVectorBadPiece f m j x‖) =
      Q.indicator (fun x => ‖f x - c‖) := by
    funext x
    by_cases hx : x ∈ Q <;> simp [dyadicVectorBadPiece, Q, c, hx]
  have htriangle :
      ∫ x in Q, ‖f x - c‖ ∂volume ≤
        (∫ x in Q, ‖f x‖ ∂volume) + ∫ x in Q, ‖c‖ ∂volume := by
    have hnormF : Integrable (fun x : ℝ => ‖f x‖) (volume.restrict Q) := hfQ.norm
    have hnormC : Integrable (fun _ : ℝ => ‖c‖) (volume.restrict Q) := hcQ.norm
    have hnormDiff : Integrable (fun x : ℝ => ‖f x - c‖)
        (volume.restrict Q) := hdiffQ.norm
    have hpoint : (fun x : ℝ => ‖f x - c‖) ≤ᵐ[volume.restrict Q]
        (fun x => ‖f x‖ + ‖c‖) := by
      filter_upwards [] with x
      exact norm_sub_le (f x) c
    have hmono := integral_mono_ae hnormDiff (hnormF.add hnormC) hpoint
    change (∫ x in Q, ‖f x - c‖ ∂volume) ≤
      ∫ x in Q, (‖f x‖ + ‖c‖) ∂volume at hmono
    rw [integral_add hnormF hnormC] at hmono
    exact hmono
  have hconstInt : (∫ x in Q, ‖c‖ ∂volume) = s * ‖c‖ := by
    rw [MeasureTheory.setIntegral_const, show volume.real Q = s by
      dsimp [Q, s]
      exact dyadicInterval_volume_real m j]
    simp [smul_eq_mul]
  have hcBound : ‖c‖ ≤ (∫ x in Q, ‖f x‖ ∂volume) / s := by
    change ‖dyadicVectorCellAverage f m j‖ ≤ _
    simpa [dyadicVectorNormCellAverage, s] using
      norm_dyadicVectorCellAverage_le_normCellAverage f m j
  have hconstLe : (∫ x in Q, ‖c‖ ∂volume) ≤
      ∫ x in Q, ‖f x‖ ∂volume := by
    rw [hconstInt]
    calc
      s * ‖c‖ ≤ s * ((∫ x in Q, ‖f x‖ ∂volume) / s) :=
        mul_le_mul_of_nonneg_left hcBound hs.le
      _ = ∫ x in Q, ‖f x‖ ∂volume := by
        field_simp [ne_of_gt hs]
  calc
    ∫ x, ‖dyadicVectorBadPiece f m j x‖ ∂volume =
        ∫ x in Q, ‖f x - c‖ ∂volume := by
      rw [hnormEq, integral_indicator hQ]
    _ ≤ (∫ x in Q, ‖f x‖ ∂volume) + ∫ x in Q, ‖c‖ ∂volume := htriangle
    _ ≤ 2 * ∫ x in Q, ‖f x‖ ∂volume := by linarith [hconstLe]

/-- Every vector bad piece has integral zero on the line. -/
theorem integral_dyadicVectorBadPiece_eq_zero {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} (hf : Integrable f volume) (m j : ℤ) :
    ∫ x, dyadicVectorBadPiece f m j x ∂volume = 0 := by
  let Q := dyadicInterval m j
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hscale : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hvolume : volume Q = ENNReal.ofReal ((2 : ℝ) ^ m) := by
    exact dyadicInterval_volume_vector m j
  have hfinite : volume Q ≠ ⊤ := by
    rw [hvolume]
    exact ENNReal.ofReal_ne_top
  have hfQ : Integrable (fun x : ℝ => f x) (volume.restrict Q) := by
    change IntegrableOn f Q volume
    exact hf.integrableOn
  have hconst : Integrable (fun _ : ℝ => dyadicVectorCellAverage f m j)
      (volume.restrict Q) := by
    change IntegrableOn (fun _ : ℝ => dyadicVectorCellAverage f m j) Q volume
    exact MeasureTheory.integrableOn_const hfinite
  have hset :
      ∫ x in Q, f x - dyadicVectorCellAverage f m j ∂volume =
        (∫ x in Q, f x ∂volume) - volume.real Q •
          dyadicVectorCellAverage f m j := by
    rw [integral_sub hfQ hconst, MeasureTheory.setIntegral_const]
  have hvol : volume.real Q = (2 : ℝ) ^ m := by
    simpa [Q] using dyadicInterval_volume_real m j
  rw [dyadicVectorBadPiece, integral_indicator hQ, hset, hvol]
  rw [dyadicVectorCellAverage, smul_smul]
  rw [mul_inv_cancel₀ (ne_of_gt hscale), one_smul, sub_self]

/-- A cell whose average size exceeds `λ` has length bounded by the total
`L¹` norm divided by `λ`. -/
theorem dyadicVectorNormCellAverage_scale_lt {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t)
    (m j : ℤ)
    (hbad : t < dyadicVectorNormCellAverage f m j) :
    (2 : ℝ) ^ m < (∫ x, ‖f x‖ ∂volume) / t := by
  have hscale : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hlocal : t * (2 : ℝ) ^ m <
      ∫ x in dyadicInterval m j, ‖f x‖ ∂volume :=
    (lt_div_iff₀ hscale).mp hbad
  have hlocal' : (2 : ℝ) ^ m * t <
      ∫ x in dyadicInterval m j, ‖f x‖ ∂volume := by
    nlinarith [hlocal]
  have htotal :
      (∫ x in dyadicInterval m j, ‖f x‖ ∂volume) ≤ ∫ x, ‖f x‖ ∂volume := by
    apply setIntegral_le_integral hf.norm
    filter_upwards with x
    exact norm_nonneg (f x)
  apply (lt_div_iff₀ ht).2
  exact lt_of_lt_of_le hlocal' htotal

private theorem dyadicInterval_parent_subset_vector (m j : ℤ) :
    dyadicInterval m j ⊆ dyadicInterval (m + 1) (j / 2) := by
  have hmod : j % 2 = 0 ∨ j % 2 = 1 := Int.emod_two_eq_zero_or_one j
  have hchildren :
      dyadicInterval (m + 1) (j / 2) =
        dyadicInterval m (2 * (j / 2)) ∪
          dyadicInterval m (2 * (j / 2) + 1) := by
    simpa only [show (m + 1) - 1 = m by omega] using
      dyadicInterval_eq_two_children (m + 1) (j / 2)
  rcases hmod with hmod | hmod
  · have hji : j = 2 * (j / 2) := by omega
    intro x hx
    rw [hchildren]
    left
    rw [hji] at hx
    exact hx
  · have hji : j = 2 * (j / 2) + 1 := by omega
    intro x hx
    rw [hchildren]
    right
    rw [hji] at hx
    exact hx

def dyadicIntervalAncestor : ℕ → ℤ → ℤ
  | 0, j => j
  | n + 1, j => dyadicIntervalAncestor n (j / 2)

private theorem dyadicIntervalAncestor_succ_parent (n : ℕ) (j : ℤ) :
    dyadicIntervalAncestor (n + 1) j =
      dyadicIntervalAncestor n j / 2 := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
      change dyadicIntervalAncestor (n + 1) (j / 2) =
        dyadicIntervalAncestor (n + 1) j / 2
      rw [ih (j / 2), dyadicIntervalAncestor]

private theorem dyadicIntervalAncestor_add (a b : ℕ) (j : ℤ) :
    dyadicIntervalAncestor a (dyadicIntervalAncestor b j) =
      dyadicIntervalAncestor (a + b) j := by
  induction a generalizing b j with
  | zero => simp [dyadicIntervalAncestor]
  | succ a ih =>
      change dyadicIntervalAncestor a
        (dyadicIntervalAncestor b j / 2) =
          dyadicIntervalAncestor (a + 1 + b) j
      rw [← dyadicIntervalAncestor_succ_parent b j]
      rw [ih]
      congr 1
      omega

private theorem dyadicInterval_ancestor_subset_vector (m j : ℤ) (n : ℕ) :
    dyadicInterval m j ⊆
      dyadicInterval (m + n) (dyadicIntervalAncestor n j) := by
  induction n generalizing m j with
  | zero => simp [dyadicIntervalAncestor]
  | succ n ih =>
      calc
        dyadicInterval m j ⊆ dyadicInterval (m + 1) (j / 2) :=
          dyadicInterval_parent_subset_vector m j
        _ ⊆ dyadicInterval ((m + 1) + n)
              (dyadicIntervalAncestor n (j / 2)) :=
          ih (m := m + 1) (j := j / 2)
        _ = dyadicInterval (m + (n + 1))
              (dyadicIntervalAncestor (n + 1) j) := by
          simp [dyadicIntervalAncestor, add_comm, add_left_comm]

private theorem dyadicInterval_subset_scale_le_vector {m n j k : ℤ}
    (hsub : dyadicInterval m j ⊆ dyadicInterval n k) : m ≤ n := by
  have hvol : ENNReal.ofReal ((2 : ℝ) ^ m) ≤ ENNReal.ofReal ((2 : ℝ) ^ n) := by
    rw [← dyadicInterval_volume_vector m j, ← dyadicInterval_volume_vector n k]
    exact measure_mono hsub
  have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ n :=
    (ENNReal.ofReal_le_ofReal_iff (le_of_lt (zpow_pos (by norm_num) n))).mp hvol
  by_contra hmn
  have hnm : n < m := by omega
  have hstrict : (2 : ℝ) ^ n < (2 : ℝ) ^ m :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) hnm
  linarith

private theorem dyadicInterval_index_eq_of_inter_vector
    (m j k : ℤ)
    (h : (dyadicInterval m j ∩ dyadicInterval m k).Nonempty) : j = k := by
  obtain ⟨x, hxj, hxk⟩ := h
  have hlen : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  rw [dyadicInterval, Set.mem_Ico] at hxj hxk
  simp only [Int.cast_add, Int.cast_one] at hxj hxk
  have hjk : (j : ℝ) < (k : ℝ) + 1 := by
    by_contra h
    have hle : (k : ℝ) + 1 ≤ (j : ℝ) := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hle hlen.le
    linarith [hxj.1, hxk.2]
  have hkj : (k : ℝ) < (j : ℝ) + 1 := by
    by_contra h
    have hle : (j : ℝ) + 1 ≤ (k : ℝ) := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hle hlen.le
    linarith [hxk.1, hxj.2]
  have hjk' : j < k + 1 := by exact_mod_cast hjk
  have hkj' : k < j + 1 := by exact_mod_cast hkj
  omega

private theorem dyadicInterval_nested_of_inter_vector
    {m n j k : ℤ}
    (hinter : (dyadicInterval m j ∩ dyadicInterval n k).Nonempty) :
    dyadicInterval m j ⊆ dyadicInterval n k ∨
      dyadicInterval n k ⊆ dyadicInterval m j := by
  rcases le_total m n with hmn | hnm
  · let d : ℕ := (n - m).toNat
    have hdiff : (d : ℤ) = n - m := by
      dsimp [d]
      exact Int.toNat_of_nonneg (by omega)
    have hscale : m + (d : ℤ) = n := by omega
    have hsub : dyadicInterval m j ⊆
        dyadicInterval n (dyadicIntervalAncestor d j) := by
      simpa [hscale] using dyadicInterval_ancestor_subset_vector m j d
    obtain ⟨x, hxj, hxk⟩ := hinter
    have hancestorInter :
        (dyadicInterval n (dyadicIntervalAncestor d j) ∩
          dyadicInterval n k).Nonempty := ⟨x, hsub hxj, hxk⟩
    have hindex := dyadicInterval_index_eq_of_inter_vector n
      (dyadicIntervalAncestor d j) k hancestorInter
    rw [hindex] at hsub
    exact Or.inl hsub
  · let d : ℕ := (m - n).toNat
    have hdiff : (d : ℤ) = m - n := by
      dsimp [d]
      exact Int.toNat_of_nonneg (by omega)
    have hscale : n + (d : ℤ) = m := by omega
    have hsub : dyadicInterval n k ⊆
        dyadicInterval m (dyadicIntervalAncestor d k) := by
      simpa [hscale] using dyadicInterval_ancestor_subset_vector n k d
    obtain ⟨x, hxj, hxk⟩ := hinter
    have hancestorInter :
        (dyadicInterval m (dyadicIntervalAncestor d k) ∩
          dyadicInterval m j).Nonempty := ⟨x, hsub hxk, hxj⟩
    have hindex := dyadicInterval_index_eq_of_inter_vector m
      (dyadicIntervalAncestor d k) j hancestorInter
    rw [hindex] at hsub
    exact Or.inr hsub

/-- The set of dyadic cells on which the average of `‖f‖` is above `t`,
with every strictly coarser ancestor below the cutoff. -/
def dyadicVectorMaximalBadCells {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (t : ℝ) : Set (ℤ × ℤ) :=
  {q | t < dyadicVectorNormCellAverage f q.1 q.2 ∧
    ∀ n : ℕ, 0 < n →
      ¬ t < dyadicVectorNormCellAverage f
        (q.1 + (n : ℤ)) (dyadicIntervalAncestor n q.2)}

/-- The measurable union of all selected maximal bad cells. -/
def dyadicVectorMaximalBadRegion {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (t : ℝ) : Set ℝ :=
  ⋃ q : dyadicVectorMaximalBadCells f t,
    dyadicInterval q.1.1 q.1.2

theorem measurableSet_dyadicVectorMaximalBadRegion {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (t : ℝ) :
    MeasurableSet (dyadicVectorMaximalBadRegion f t) := by
  classical
  let S := dyadicVectorMaximalBadCells f t
  have hScount : S.Countable := Set.countable_univ.mono (Set.subset_univ S)
  letI : Countable S := hScount.to_subtype
  apply MeasurableSet.iUnion
  intro q
  rw [dyadicInterval]
  exact measurableSet_Ico

/-- On a maximal bad cell, the vector average is bounded by twice the
cutoff, using the cutoff bound on its parent. -/
theorem dyadicVectorMaximalBadCell_average_le_two {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} {t : ℝ} {q : ℤ × ℤ}
    (hf : Integrable f volume)
    (hq : q ∈ dyadicVectorMaximalBadCells f t) :
    ‖dyadicVectorCellAverage f q.1 q.2‖ ≤ 2 * t := by
  change t < dyadicVectorNormCellAverage f q.1 q.2 ∧ _ at hq
  let Q := dyadicInterval q.1 q.2
  let P := dyadicInterval (q.1 + 1) (q.2 / 2)
  let s := (2 : ℝ) ^ q.1
  have hs : 0 < s := by dsimp [s]; exact zpow_pos (by norm_num) q.1
  have hpow : (2 : ℝ) ^ (q.1 + 1) = 2 * s := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    dsimp [s]
    ring
  have hparentAvg : dyadicVectorNormCellAverage f (q.1 + 1) (q.2 / 2) ≤ t := by
    have hnot := hq.2 1 (by omega)
    simpa [dyadicIntervalAncestor] using (le_of_not_gt hnot)
  have hparentPos : 0 < (2 : ℝ) ^ (q.1 + 1) := zpow_pos (by norm_num) _
  have hparentMass' :
      (∫ x in P, ‖f x‖ ∂volume) ≤ t * (2 : ℝ) ^ (q.1 + 1) :=
    (div_le_iff₀ hparentPos).mp
      (by simpa [dyadicVectorNormCellAverage, P] using hparentAvg)
  have hparentMass :
      (∫ x in P, ‖f x‖ ∂volume) ≤ t * (2 * s) := by
    simpa [hpow] using hparentMass'
  have hparentInt : IntegrableOn (fun x : ℝ => ‖f x‖) P volume :=
    hf.norm.integrableOn
  have hsubset : Q ⊆ P := by
    dsimp [Q, P]
    exact dyadicInterval_parent_subset_vector q.1 q.2
  have hmass :
      (∫ x in Q, ‖f x‖ ∂volume) ≤ ∫ x in P, ‖f x‖ ∂volume :=
    MeasureTheory.setIntegral_mono_set hparentInt
      (Filter.Eventually.of_forall fun x => norm_nonneg (f x))
      (Filter.Eventually.of_forall fun x hx => hsubset hx)
  have hchildAvg :
      dyadicVectorNormCellAverage f q.1 q.2 ≤ 2 * t := by
    apply (div_le_iff₀ hs).2
    calc
      (∫ x in Q, ‖f x‖ ∂volume) ≤ ∫ x in P, ‖f x‖ ∂volume := hmass
      _ ≤ t * (2 * s) := hparentMass
      _ = (2 * t) * s := by ring
  calc
    ‖dyadicVectorCellAverage f q.1 q.2‖ ≤
        dyadicVectorNormCellAverage f q.1 q.2 :=
      norm_dyadicVectorCellAverage_le_normCellAverage f q.1 q.2
    _ ≤ 2 * t := hchildAvg

/-- Choose the selected maximal bad cell containing a point in the bad
region. -/
noncomputable def dyadicVectorMaximalCellAt {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (t : ℝ) {x : ℝ}
    (hx : x ∈ dyadicVectorMaximalBadRegion f t) :
    dyadicVectorMaximalBadCells f t := by
  classical
  have hex : ∃ q : dyadicVectorMaximalBadCells f t,
      x ∈ dyadicInterval q.1.1 q.1.2 := by
    simpa [dyadicVectorMaximalBadRegion] using hx
  exact Classical.choose hex

theorem dyadicVectorMaximalCellAt_mem {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (t : ℝ) {x : ℝ}
    (hx : x ∈ dyadicVectorMaximalBadRegion f t) :
    x ∈ dyadicInterval (dyadicVectorMaximalCellAt f t hx).1.1
      (dyadicVectorMaximalCellAt f t hx).1.2 := by
  classical
  have hex : ∃ q : dyadicVectorMaximalBadCells f t,
      x ∈ dyadicInterval q.1.1 q.1.2 := by
    simpa [dyadicVectorMaximalBadRegion] using hx
  exact Classical.choose_spec hex

/-- The selected vector average on the unique bad cell containing `x`, with
zero assigned outside the bad region. -/
noncomputable def dyadicVectorBadAverageAt {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (t : ℝ) (x : ℝ) : H := by
  classical
  exact if hx : x ∈ dyadicVectorMaximalBadRegion f t then
    dyadicVectorCellAverage f
      (dyadicVectorMaximalCellAt f t hx).1.1
      (dyadicVectorMaximalCellAt f t hx).1.2
  else 0

theorem norm_dyadicVectorBadAverageAt_le_two {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    ‖dyadicVectorBadAverageAt f t x‖ ≤ 2 * t := by
  classical
  by_cases hx : x ∈ dyadicVectorMaximalBadRegion f t
  · rw [dyadicVectorBadAverageAt, dif_pos hx]
    exact dyadicVectorMaximalBadCell_average_le_two hf
      (dyadicVectorMaximalCellAt f t hx).2
  · rw [dyadicVectorBadAverageAt, dif_neg hx]
    simp
    linarith

/-- The vector good part equals the original input off the bad region and
the selected cell average on each bad cell. -/
noncomputable def dyadicVectorGoodPart {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (t : ℝ) (x : ℝ) : H := by
  classical
  exact if x ∈ dyadicVectorMaximalBadRegion f t then
    dyadicVectorBadAverageAt f t x
  else f x

private def dyadicVectorNormAsComplex {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] (f : ℝ → H) : ℝ → ℂ :=
  fun x => (‖f x‖ : ℂ)

private theorem integrable_dyadicVectorNormAsComplex {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} (hf : Integrable f volume) :
    Integrable (dyadicVectorNormAsComplex f) volume := by
  have hnormLp : MemLp (fun x => ‖f x‖) 1 volume :=
    memLp_one_iff_integrable.mpr hf.norm
  have hcomplexLp : MemLp (dyadicVectorNormAsComplex f) 1 volume := by
    change MemLp (fun x => ((‖f x‖ : ℝ) : ℂ)) 1 volume
    exact hnormLp.ofReal
  exact memLp_one_iff_integrable.mp hcomplexLp

private theorem dyadicInterval_lower_mem_vector (m j : ℤ) :
    (j : ℝ) * (2 : ℝ) ^ m ∈ dyadicInterval m j := by
  rw [dyadicInterval, Set.mem_Ico]
  constructor
  · exact le_rfl
  · have hs : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
    have hlen : (((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m) -
        (j : ℝ) * (2 : ℝ) ^ m = (2 : ℝ) ^ m := by
      push_cast
      ring
    linarith

private theorem dyadicVectorMaximalBadCells_subset_eq
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} {t : ℝ} {q r : ℤ × ℤ}
    (hq : q ∈ dyadicVectorMaximalBadCells f t)
    (hr : r ∈ dyadicVectorMaximalBadCells f t)
    (hsub : dyadicInterval q.1 q.2 ⊆ dyadicInterval r.1 r.2) : q = r := by
  change t < dyadicVectorNormCellAverage f q.1 q.2 ∧ _ at hq
  change t < dyadicVectorNormCellAverage f r.1 r.2 ∧ _ at hr
  have hscale : q.1 ≤ r.1 := dyadicInterval_subset_scale_le_vector hsub
  by_cases heq : q.1 = r.1
  · have hxq := dyadicInterval_lower_mem_vector q.1 q.2
    have hxr := hsub hxq
    have hinter : (dyadicInterval r.1 q.2 ∩ dyadicInterval r.1 r.2).Nonempty := by
      exact ⟨(q.2 : ℝ) * (2 : ℝ) ^ q.1,
        by simpa [heq, mul_comm] using hxq,
        by simpa [heq] using hxr⟩
    have hindex := dyadicInterval_index_eq_of_inter_vector r.1 q.2 r.2 hinter
    exact Prod.ext heq hindex
  · have hlt : q.1 < r.1 := by omega
    let d : ℕ := (r.1 - q.1).toNat
    have hdiff : (d : ℤ) = r.1 - q.1 := by
      dsimp [d]
      exact Int.toNat_of_nonneg (by omega)
    have hscale' : q.1 + (d : ℤ) = r.1 := by omega
    have hancsub : dyadicInterval q.1 q.2 ⊆
        dyadicInterval r.1 (dyadicIntervalAncestor d q.2) := by
      simpa [hscale'] using dyadicInterval_ancestor_subset_vector q.1 q.2 d
    have hxq := dyadicInterval_lower_mem_vector q.1 q.2
    have hxr := hsub hxq
    have hxanc := hancsub hxq
    have hinter :
        (dyadicInterval r.1 (dyadicIntervalAncestor d q.2) ∩
          dyadicInterval r.1 r.2).Nonempty :=
      ⟨(q.2 : ℝ) * (2 : ℝ) ^ q.1, by simpa [hscale'] using hxanc,
        by simpa [hscale'] using hxr⟩
    have hindex := dyadicInterval_index_eq_of_inter_vector r.1
      (dyadicIntervalAncestor d q.2) r.2 hinter
    have hdpos : 0 < d := by
      dsimp [d]
      omega
    have hbad : t < dyadicVectorNormCellAverage f
        (q.1 + (d : ℤ)) (dyadicIntervalAncestor d q.2) := by
      rw [hscale', hindex]
      exact hr.1
    exact False.elim (hq.2 d hdpos hbad)

theorem dyadicVectorMaximalBadCells_pairwiseDisjoint
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (t : ℝ) :
    Set.PairwiseDisjoint (dyadicVectorMaximalBadCells f t)
      (fun q => dyadicInterval q.1 q.2) := by
  intro q hq r hr hne
  apply Set.disjoint_iff_inter_eq_empty.mpr
  by_contra hnonempty
  obtain ⟨x, hxq, hxr⟩ := Set.nonempty_iff_ne_empty.mpr hnonempty
  rcases dyadicInterval_nested_of_inter_vector ⟨x, hxq, hxr⟩ with hqr | hrq
  · exact hne (dyadicVectorMaximalBadCells_subset_eq hq hr hqr)
  · exact hne.symm (dyadicVectorMaximalBadCells_subset_eq hr hq hrq)

private theorem dyadicVectorMaximalBadCells_value_eq_of_mem
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} {t x : ℝ}
    {q r : dyadicVectorMaximalBadCells f t}
    (hq : x ∈ dyadicInterval q.1.1 q.1.2)
    (hr : x ∈ dyadicInterval r.1.1 r.1.2) : q = r := by
  rcases dyadicInterval_nested_of_inter_vector ⟨x, hq, hr⟩ with hqr | hrq
  · exact Subtype.ext (dyadicVectorMaximalBadCells_subset_eq q.2 r.2 hqr)
  · exact (Subtype.ext (dyadicVectorMaximalBadCells_subset_eq r.2 q.2 hrq)).symm

/-- The selected-cell average is measurable: the maximal bad intervals form a
countable measurable partition of the bad region, and the value is zero on
its complement. -/
theorem measurable_dyadicVectorBadAverageAt {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H]
    (f : ℝ → H) (t : ℝ) :
    Measurable (dyadicVectorBadAverageAt f t) := by
  classical
  let E := dyadicVectorMaximalBadRegion f t
  let S := dyadicVectorMaximalBadCells f t
  have hScount : S.Countable := Set.countable_univ.mono (Set.subset_univ S)
  letI : Countable S := hScount.to_subtype
  let Q : Option S → Set ℝ := fun i =>
    match i with
    | none => Eᶜ
    | some q => dyadicInterval q.1.1 q.1.2
  let c : (i : Option S) → {x : ℝ // x ∈ Q i} → H := fun i _ =>
    match i with
    | none => 0
    | some q => dyadicVectorCellAverage f q.1.1 q.1.2
  have hcover : ⋃ i, Q i = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x ∈ E
    · have hx' : x ∈ ⋃ q : S, dyadicInterval q.1.1 q.1.2 := by
        simpa [E, dyadicVectorMaximalBadRegion, S] using hx
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx'
      exact ⟨some q, by simpa [Q] using hq⟩
    · exact ⟨none, by simpa [Q] using hx⟩
  have hQ : ∀ i, MeasurableSet (Q i) := by
    intro i
    cases i with
    | none => exact (measurableSet_dyadicVectorMaximalBadRegion f t).compl
    | some q =>
        dsimp [Q, dyadicInterval]
        exact measurableSet_Ico
  have hcompat : ∀ i j x (hxi : x ∈ Q i) (hxj : x ∈ Q j),
      c i ⟨x, hxi⟩ = c j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some r =>
            have hxE : x ∈ E := by
              change x ∈ dyadicVectorMaximalBadRegion f t
              exact Set.mem_iUnion.mpr ⟨r, by simpa [Q] using hxj⟩
            exact (hxi hxE).elim
    | some q =>
        cases j with
        | none =>
            have hxE : x ∈ E := by
              change x ∈ dyadicVectorMaximalBadRegion f t
              exact Set.mem_iUnion.mpr ⟨q, by simpa [Q] using hxi⟩
            exact (hxj hxE).elim
        | some r =>
            have hqr : q = r := by
              apply dyadicVectorMaximalBadCells_value_eq_of_mem
                (by simpa [Q] using hxi) (by simpa [Q] using hxj)
            subst r
            rfl
  have hc : ∀ i, Measurable (c i) := by
    intro i
    cases i <;> exact measurable_const
  have hglued : Measurable (Set.liftCover Q c hcompat hcover) :=
    measurable_liftCover Q hQ c hc hcompat hcover
  have heq : dyadicVectorBadAverageAt f t =
      Set.liftCover Q c hcompat hcover := by
    funext x
    by_cases hx : x ∈ E
    · have hx' : x ∈ ⋃ q : S, dyadicInterval q.1.1 q.1.2 := by
        simpa [E, dyadicVectorMaximalBadRegion, S] using hx
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx'
      have hchosen : dyadicVectorMaximalCellAt f t hx = q := by
        apply dyadicVectorMaximalBadCells_value_eq_of_mem
          (dyadicVectorMaximalCellAt_mem f t hx) hq
      rw [dyadicVectorBadAverageAt, dif_pos hx]
      rw [Set.liftCover_of_mem (i := some q) (by simpa [Q] using hq)]
      simp [c, hchosen]
    · rw [dyadicVectorBadAverageAt, dif_neg hx]
      rw [Set.liftCover_of_mem (i := none) (by simpa [Q] using hx)]
  rw [heq]
  exact hglued

theorem dyadicVectorBadAverageAt_eq_cellAverage_of_mem
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (t : ℝ) {q : ℤ × ℤ} (hq : q ∈ dyadicVectorMaximalBadCells f t)
    {x : ℝ} (hx : x ∈ dyadicInterval q.1 q.2) :
    dyadicVectorBadAverageAt f t x = dyadicVectorCellAverage f q.1 q.2 := by
  have hxE : x ∈ dyadicVectorMaximalBadRegion f t :=
    Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hx⟩
  have hchosen : dyadicVectorMaximalCellAt f t hxE = ⟨q, hq⟩ := by
    apply dyadicVectorMaximalBadCells_value_eq_of_mem
      (dyadicVectorMaximalCellAt_mem f t hxE) hx
  rw [dyadicVectorBadAverageAt, dif_pos hxE, hchosen]

theorem dyadicVectorGoodPart_eq_cellAverage_of_mem
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (t : ℝ) {q : ℤ × ℤ} (hq : q ∈ dyadicVectorMaximalBadCells f t)
    {x : ℝ} (hx : x ∈ dyadicInterval q.1 q.2) :
    dyadicVectorGoodPart f t x = dyadicVectorCellAverage f q.1 q.2 := by
  have hxE : x ∈ dyadicVectorMaximalBadRegion f t :=
    Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hx⟩
  rw [dyadicVectorGoodPart, if_pos hxE]
  exact dyadicVectorBadAverageAt_eq_cellAverage_of_mem f t hq hx

private theorem tendsto_dyadicAncestorScale_atTop (m : ℤ) :
    Tendsto (fun k : ℕ => (2 : ℝ) ^ (m + (k : ℤ))) atTop atTop := by
  have hpow : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hscale : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hmul : Tendsto (fun k : ℕ => (2 : ℝ) ^ m * (2 : ℝ) ^ k) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hscale).2 hpow
  have hEq : (fun k : ℕ => (2 : ℝ) ^ (m + (k : ℤ))) =ᶠ[atTop]
      fun k => (2 : ℝ) ^ m * (2 : ℝ) ^ k := by
    filter_upwards [] with k
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  exact Tendsto.congr' hEq.symm hmul

/-- Every bad dyadic cell has a largest bad ancestor along its unique parent
chain. The selected ancestor's own parent has average at most the cutoff. -/
theorem exists_maximal_bad_dyadicVector_ancestor {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t)
    (m j : ℤ) (hbad : t < dyadicVectorNormCellAverage f m j) :
    ∃ k : ℕ,
      dyadicInterval m j ⊆
        dyadicInterval (m + (k : ℤ)) (dyadicIntervalAncestor k j) ∧
      t < dyadicVectorNormCellAverage f (m + (k : ℤ))
        (dyadicIntervalAncestor k j) ∧
      dyadicVectorNormCellAverage f (m + ((k + 1 : ℕ) : ℤ))
        (dyadicIntervalAncestor (k + 1) j) ≤ t ∧
      ∀ l : ℕ, 0 < l →
        ¬ t < dyadicVectorNormCellAverage f
          (m + ((k + l : ℕ) : ℤ)) (dyadicIntervalAncestor (k + l) j) := by
  classical
  let A : Set ℕ := {k | t < dyadicVectorNormCellAverage f (m + (k : ℤ))
    (dyadicIntervalAncestor k j)}
  have hzero : (0 : ℕ) ∈ A := by
    simpa [A, dyadicIntervalAncestor] using hbad
  let C : ℝ := (∫ x, ‖f x‖ ∂volume) / t
  have htail : ∀ᶠ k : ℕ in atTop, C ≤ (2 : ℝ) ^ (m + (k : ℤ)) := by
    have hscale := tendsto_dyadicAncestorScale_atTop m
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      ((Filter.tendsto_atTop.1 hscale) C)
    filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with k hk
    simpa [C] using hk
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 htail
  have hA_bdd : BddAbove A := by
    refine ⟨N, ?_⟩
    intro k hk
    by_contra hNk
    have hNk' : N ≤ k := by omega
    have hlarge : C ≤ (2 : ℝ) ^ (m + (k : ℤ)) := hN k hNk'
    have hbadScale : (2 : ℝ) ^ (m + (k : ℤ)) < C := by
      simpa [C] using dyadicVectorNormCellAverage_scale_lt hf ht
        (m + (k : ℤ)) (dyadicIntervalAncestor k j) hk
    exact (not_lt_of_ge hlarge) hbadScale
  have hA_finite : A.Finite := Set.finite_iff_bddAbove.mpr hA_bdd
  let AF : Finset ℕ := hA_finite.toFinset
  have hAF_nonempty : AF.Nonempty := by
    refine ⟨0, ?_⟩
    exact hA_finite.mem_toFinset.mpr hzero
  let k : ℕ := AF.max' hAF_nonempty
  have hkA : k ∈ A := by
    dsimp [k]
    exact hA_finite.mem_toFinset.mp (Finset.max'_mem AF hAF_nonempty)
  have hmax : ∀ l ∈ A, l ≤ k := by
    intro l hl
    dsimp [k]
    exact AF.le_max' l (hA_finite.mem_toFinset.mpr hl)
  have hparentBad : ¬ t < dyadicVectorNormCellAverage f
      (m + ((k + 1 : ℕ) : ℤ)) (dyadicIntervalAncestor (k + 1) j) := by
    intro hparent
    have hkone : k + 1 ∈ A := hparent
    have hkbound := hmax (k + 1) hkone
    omega
  have hfuture : ∀ l : ℕ, 0 < l →
      ¬ t < dyadicVectorNormCellAverage f
        (m + ((k + l : ℕ) : ℤ)) (dyadicIntervalAncestor (k + l) j) := by
    intro l hl hbadFuture
    have hfutureA : k + l ∈ A := by
      simpa [A] using hbadFuture
    have hbound := hmax (k + l) hfutureA
    omega
  refine ⟨k, dyadicInterval_ancestor_subset_vector m j k, hkA,
    le_of_not_gt hparentBad, hfuture⟩

/-- Every bad cell lies in a globally maximal bad dyadic cell. -/
theorem dyadicVectorMaximalBadCells_cover_bad
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t)
    {m j : ℤ} (hbad : t < dyadicVectorNormCellAverage f m j) :
    ∃ q ∈ dyadicVectorMaximalBadCells f t,
      dyadicInterval m j ⊆ dyadicInterval q.1 q.2 := by
  obtain ⟨k, hsub, hkbad, _, hfuture⟩ :=
    exists_maximal_bad_dyadicVector_ancestor hf ht m j hbad
  refine ⟨(m + (k : ℤ), dyadicIntervalAncestor k j), ?_, hsub⟩
  change t < dyadicVectorNormCellAverage f
      (m + (k : ℤ)) (dyadicIntervalAncestor k j) ∧ _
  constructor
  · exact hkbad
  · intro n hn
    change ¬ t < dyadicVectorNormCellAverage f
      (m + (k : ℤ) + (n : ℤ))
      (dyadicIntervalAncestor n (dyadicIntervalAncestor k j))
    have hscale : m + (k : ℤ) + (n : ℤ) =
        m + ((k + n : ℕ) : ℤ) := by
      push_cast
      omega
    rw [hscale, dyadicIntervalAncestor_add, Nat.add_comm n k]
    exact hfuture n hn

/-- The union of the globally maximal bad vector-norm cells obeys the
constant-one dyadic weak `(1,1)` estimate. -/
theorem dyadicVectorMaximalBadCells_measure_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t) :
    volume (⋃ q : dyadicVectorMaximalBadCells f t,
      dyadicInterval q.1.1 q.1.2) ≤
        ENNReal.ofReal ((∫ x, ‖f x‖ ∂volume) / t) := by
  classical
  let g : ℝ → ℂ := dyadicVectorNormAsComplex f
  have hg : Integrable g volume := integrable_dyadicVectorNormAsComplex hf
  have hnormEq (x : ℝ) : ‖g x‖ = ‖f x‖ := by
    rw [show g x = (‖f x‖ : ℂ) by rfl, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg (f x))]
  have hnormFun : (fun x : ℝ => ‖g x‖) = fun x => ‖f x‖ := funext hnormEq
  have havgEq (m j : ℤ) :
      dyadicMaximalAverage g m j = dyadicVectorNormCellAverage f m j := by
    simp only [dyadicMaximalAverage, dyadicVectorNormCellAverage]
    rw [hnormFun]
  have hsubset :
      (⋃ q : dyadicVectorMaximalBadCells f t,
        dyadicInterval q.1.1 q.1.2) ⊆
      {x : ℝ | ENNReal.ofReal t < dyadicMaximal g x} := by
    intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    have hbad : t < dyadicMaximalAverage g q.1.1 q.1.2 := by
      rw [havgEq]
      exact q.2.1
    have hterm : ENNReal.ofReal t <
        (if x ∈ dyadicInterval q.1.1 q.1.2 then
          ENNReal.ofReal (dyadicMaximalAverage g q.1.1 q.1.2) else 0) := by
      rw [if_pos hxq]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans ht hbad)).mpr hbad
    have hle :
        (if x ∈ dyadicInterval q.1.1 q.1.2 then
          ENNReal.ofReal (dyadicMaximalAverage g q.1.1 q.1.2) else 0) ≤
            dyadicMaximal g x := by
      unfold dyadicMaximal
      exact le_iSup_of_le q.1 le_rfl
    exact lt_of_lt_of_le hterm hle
  have hweak := dyadicMaximal_weakType_one hg t ht
  rw [hnormFun] at hweak
  exact (measure_mono hsubset).trans hweak

/-- The sum of the lengths of the disjoint maximal bad cells is bounded by
the vector `L¹` norm divided by the cutoff. -/
theorem dyadicVectorMaximalBadCells_sum_length_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t) :
    (∑' q : dyadicVectorMaximalBadCells f t,
      ENNReal.ofReal ((2 : ℝ) ^ q.1.1)) ≤
        ENNReal.ofReal ((∫ x, ‖f x‖ ∂volume) / t) := by
  classical
  let S := dyadicVectorMaximalBadCells f t
  have hScount : S.Countable := Set.countable_univ.mono (Set.subset_univ S)
  letI : Countable S := hScount.to_subtype
  have hdisj : Pairwise (fun q r : S =>
      Disjoint (dyadicInterval q.1.1 q.1.2)
        (dyadicInterval r.1.1 r.1.2)) := by
    intro q r hne
    have hval : q.1 ≠ r.1 := by
      intro heq
      exact hne (Subtype.ext heq)
    exact dyadicVectorMaximalBadCells_pairwiseDisjoint f t q.2 r.2 hval
  have hmeas : ∀ q : S, MeasurableSet (dyadicInterval q.1.1 q.1.2) := by
    intro q
    rw [dyadicInterval]
    exact measurableSet_Ico
  have hvolume :
      (∑' q : S, ENNReal.ofReal ((2 : ℝ) ^ q.1.1)) =
        volume (⋃ q : S, dyadicInterval q.1.1 q.1.2) := by
    symm
    rw [measure_iUnion hdisj hmeas]
    simp_rw [dyadicInterval_volume_vector]
  calc
    (∑' q : S, ENNReal.ofReal ((2 : ℝ) ^ q.1.1)) =
        volume (⋃ q : S, dyadicInterval q.1.1 q.1.2) := hvolume
    _ ≤ ENNReal.ofReal ((∫ x, ‖f x‖ ∂volume) / t) :=
      dyadicVectorMaximalBadCells_measure_le hf ht

/-- The sum of the `L¹` masses of the selected disjoint cells is at most the
total `L¹` mass. -/
theorem dyadicVectorMaximalBadCells_sum_integral_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} :
    (∑' q : dyadicVectorMaximalBadCells f t,
      ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume) ≤
        ∫ x, ‖f x‖ ∂volume := by
  classical
  let S := dyadicVectorMaximalBadCells f t
  have hScount : S.Countable := Set.countable_univ.mono (Set.subset_univ S)
  letI : Countable S := hScount.to_subtype
  have hdisj : Pairwise (fun q r : S =>
      Disjoint (dyadicInterval q.1.1 q.1.2)
        (dyadicInterval r.1.1 r.1.2)) := by
    intro q r hne
    have hval : q.1 ≠ r.1 := by
      intro heq
      exact hne (Subtype.ext heq)
    exact dyadicVectorMaximalBadCells_pairwiseDisjoint f t q.2 r.2 hval
  have hmeas : ∀ q : S, MeasurableSet (dyadicInterval q.1.1 q.1.2) := by
    intro q
    rw [dyadicInterval]
    exact measurableSet_Ico
  have hfi : IntegrableOn (fun x : ℝ => ‖f x‖)
      (⋃ q : S, dyadicInterval q.1.1 q.1.2) volume := hf.norm.integrableOn
  have hintUnion :
      (∫ x in ⋃ q : S, dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume) =
        ∑' q : S, ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume :=
    integral_iUnion hmeas hdisj hfi
  calc
    (∑' q : S, ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume) =
        ∫ x in ⋃ q : S, dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume :=
      hintUnion.symm
    _ ≤ ∫ x, ‖f x‖ ∂volume := by
      apply setIntegral_le_integral hf.norm
      filter_upwards [] with x
      exact norm_nonneg (f x)

/-- A vector dyadic average is constant on every cell at its scale. -/
theorem dyadicVectorAverage_eq_of_mem_same_cell {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (m j : ℤ) (f : ℝ → H) {x y : ℝ}
    (hx : x ∈ dyadicInterval m j) (hy : y ∈ dyadicInterval m j) :
    dyadicVectorAverage m f x = dyadicVectorAverage m f y := by
  have hxi : dyadicIntervalIndex m x = j := dyadicIntervalIndex_eq_of_mem hx
  have hyi : dyadicIntervalIndex m y = j := dyadicIntervalIndex_eq_of_mem hy
  simp [dyadicVectorAverage, hxi, hyi]

/-- The norm of a vector dyadic average is bounded by the average of the
input norm on the cell. -/
theorem norm_dyadicVectorAverage_le_average_norm {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (m : ℤ) (f : ℝ → H) (x : ℝ) :
    ‖dyadicVectorAverage m f x‖ ≤
      ((2 : ℝ) ^ m)⁻¹ *
        ∫ y in dyadicInterval m (dyadicIntervalIndex m x), ‖f y‖ ∂volume := by
  have hs : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hinv : 0 ≤ ((2 : ℝ) ^ m)⁻¹ := inv_nonneg.mpr hs.le
  change ‖((2 : ℝ) ^ m)⁻¹ •
      ∫ y in dyadicInterval m (dyadicIntervalIndex m x), f y ∂volume‖ ≤ _
  calc
    _ = ‖((2 : ℝ) ^ m)⁻¹‖ *
        ‖∫ y in dyadicInterval m (dyadicIntervalIndex m x), f y ∂volume‖ :=
          norm_smul _ _
    _ = ((2 : ℝ) ^ m)⁻¹ *
        ‖∫ y in dyadicInterval m (dyadicIntervalIndex m x), f y ∂volume‖ := by
          rw [Real.norm_of_nonneg hinv]
    _ ≤ ((2 : ℝ) ^ m)⁻¹ *
        ∫ y in dyadicInterval m (dyadicIntervalIndex m x), ‖f y‖ ∂volume :=
      mul_le_mul_of_nonneg_left
        (MeasureTheory.norm_integral_le_integral_norm (μ :=
          volume.restrict (dyadicInterval m (dyadicIntervalIndex m x))) f) hinv

private theorem tendsto_dyadicRadius_atBot_vector :
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

private theorem dyadicCell_closedBall_eq_Icc_vector (m j : ℤ) :
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

private theorem dyadicVectorAverage_eq_closedBallAverage {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) (m : ℤ) (x : ℝ) :
    dyadicVectorAverage m f x =
      ⨍ y in Metric.closedBall
        ((dyadicIntervalIndex m x : ℝ) * (2 : ℝ) ^ m + (2 : ℝ) ^ (m - 1))
        ((2 : ℝ) ^ (m - 1)), f y ∂volume := by
  let j := dyadicIntervalIndex m x
  let s := (2 : ℝ) ^ m
  let r := (2 : ℝ) ^ (m - 1)
  let c := (j : ℝ) * s + r
  have hcell : Metric.closedBall c r =
      Set.Icc ((j : ℝ) * s) (((j + 1 : ℤ) : ℝ) * s) := by
    simpa [c, s, r] using dyadicCell_closedBall_eq_Icc_vector m j
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
    dyadicVectorAverage m f x = s⁻¹ •
        ∫ y in dyadicInterval m j, f y ∂volume := by
      simp [dyadicVectorAverage, j, s]
    _ = (volume.real (Metric.closedBall c r))⁻¹ •
          ∫ y in Metric.closedBall c r, f y ∂volume := by rw [hvol, hInt]
    _ = ⨍ y in Metric.closedBall c r, f y ∂volume :=
      (MeasureTheory.setAverage_eq volume f (Metric.closedBall c r)).symm

/-- Fine-scale vector dyadic averages converge almost everywhere to every
integrable input. This is the dyadic specialization of Mathlib's
normed-space Vitali differentiation theorem. -/
theorem dyadicVectorAverage_tendsto_atBot_ae_of_integrable {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} (hf : Integrable f volume) :
    ∀ᵐ x ∂volume,
      Tendsto (fun m : ℤ => dyadicVectorAverage m f x) atBot (𝓝 (f x)) := by
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average
    (μ := volume) (f := f) hf.locallyIntegrable (1 : ℝ)
  filter_upwards [hdiff] with x hx
  let w : ℤ → ℝ := fun m =>
    (dyadicIntervalIndex m x : ℝ) * (2 : ℝ) ^ m + (2 : ℝ) ^ (m - 1)
  let r : ℤ → ℝ := fun m => (2 : ℝ) ^ (m - 1)
  have hr : Tendsto r atBot (𝓝[>] (0 : ℝ)) := by
    simpa [r] using tendsto_dyadicRadius_atBot_vector
  have hball (m : ℤ) : x ∈ Metric.closedBall (w m) (r m) := by
    have hxcell := mem_dyadicIntervalIndex m x
    rw [dyadicInterval, Set.mem_Ico] at hxcell
    rw [dyadicCell_closedBall_eq_Icc_vector]
    exact ⟨hxcell.1, hxcell.2.le⟩
  have hball_event : ∀ᶠ m : ℤ in atBot,
      x ∈ Metric.closedBall (w m) (1 * r m) := by
    filter_upwards [] with m
    simpa using hball m
  have havg := hx w r hr hball_event
  exact Tendsto.congr' (Filter.Eventually.of_forall fun m =>
    (dyadicVectorAverage_eq_closedBallAverage f m x).symm) havg

private theorem dyadicVectorNorm_le_of_not_mem_badRegion_of_tendsto
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} {t x : ℝ}
    (hf : Integrable f volume) (ht : 0 < t)
    (hx : x ∉ dyadicVectorMaximalBadRegion f t)
    (hlim : Tendsto
      (fun m : ℤ => dyadicVectorAverage m (fun y : ℝ => ‖f y‖) x)
      atBot (𝓝 (‖f x‖))) :
    ‖f x‖ ≤ t := by
  have hbound : ∀ m : ℤ,
      dyadicVectorAverage m (fun y : ℝ => ‖f y‖) x ≤ t := by
    intro m
    have hcell :
        dyadicVectorNormCellAverage f m (dyadicIntervalIndex m x) ≤ t := by
      by_contra h
      have hbad : t < dyadicVectorNormCellAverage f m (dyadicIntervalIndex m x) :=
        lt_of_not_ge h
      obtain ⟨q, hq, hsub⟩ :=
        dyadicVectorMaximalBadCells_cover_bad hf ht hbad
      have hxcell : x ∈ dyadicInterval m (dyadicIntervalIndex m x) :=
        mem_dyadicIntervalIndex m x
      have hxq : x ∈ dyadicInterval q.1 q.2 := hsub hxcell
      exact hx (Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hxq⟩)
    have havg : dyadicVectorAverage m (fun y : ℝ => ‖f y‖) x =
        dyadicVectorNormCellAverage f m (dyadicIntervalIndex m x) := by
      simp [dyadicVectorAverage, dyadicVectorNormCellAverage,
        div_eq_mul_inv, smul_eq_mul, mul_comm]
    rw [havg]
    exact hcell
  by_contra h
  have hlt : t < ‖f x‖ := lt_of_not_ge h
  have hEventually : ∀ᶠ m : ℤ in atBot,
      t < dyadicVectorAverage m (fun y : ℝ => ‖f y‖) x :=
    hlim.eventually (Ioi_mem_nhds hlt)
  have hAlways : ∀ᶠ m : ℤ in atBot,
      dyadicVectorAverage m (fun y : ℝ => ‖f y‖) x ≤ t :=
    Filter.Eventually.of_forall hbound
  obtain ⟨m, hm₁, hm₂⟩ := hEventually.and hAlways |>.exists
  exact (not_lt_of_ge hm₂) hm₁

/-- Outside the selected bad cells, differentiation bounds the original
vector norm by the cutoff almost everywhere. -/
theorem dyadicVectorNorm_le_of_not_mem_badRegion_ae {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂volume, x ∉ dyadicVectorMaximalBadRegion f t → ‖f x‖ ≤ t := by
  have hnorm : Integrable (fun x : ℝ => ‖f x‖) volume := hf.norm
  have hdiff :=
    dyadicVectorAverage_tendsto_atBot_ae_of_integrable hnorm
  filter_upwards [hdiff] with x hx
  intro hxout
  exact dyadicVectorNorm_le_of_not_mem_badRegion_of_tendsto hf ht
    hxout hx

theorem dyadicVectorGoodPart_norm_le_two_ae {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂volume, ‖dyadicVectorGoodPart f t x‖ ≤ 2 * t := by
  classical
  have hout := dyadicVectorNorm_le_of_not_mem_badRegion_ae hf ht
  filter_upwards [hout] with x hxout
  by_cases hx : x ∈ dyadicVectorMaximalBadRegion f t
  · simpa [dyadicVectorGoodPart, hx] using
      norm_dyadicVectorBadAverageAt_le_two hf ht x
  · simpa [dyadicVectorGoodPart, hx] using show ‖f x‖ ≤ 2 * t from by
      calc
        ‖f x‖ ≤ t := hxout hx
        _ ≤ 2 * t := by linarith

/-- The vector good part remains integrable: it equals the input off a set of
finite measure and has the checked uniform bound on that set. -/
theorem dyadicVectorGoodPart_integrable {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [TopologicalSpace.PseudoMetrizableSpace H]
    [SecondCountableTopology H] [OpensMeasurableSpace H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t) :
    Integrable (dyadicVectorGoodPart f t) volume := by
  classical
  let E := dyadicVectorMaximalBadRegion f t
  have hEmeas : MeasurableSet E := measurableSet_dyadicVectorMaximalBadRegion f t
  have hEmass : volume E ≤
      ENNReal.ofReal ((∫ x, ‖f x‖ ∂volume) / t) := by
    simpa [E, dyadicVectorMaximalBadRegion] using
      dyadicVectorMaximalBadCells_measure_le hf ht
  have hEfinite : volume E ≠ ⊤ := ne_of_lt <|
    lt_of_le_of_lt hEmass (ENNReal.ofReal_lt_top)
  have hconstOn : IntegrableOn (fun _ : ℝ => 2 * t) E volume :=
    integrableOn_const hEfinite
  have hconst : Integrable (E.indicator (fun _ : ℝ => 2 * t)) volume :=
    hconstOn.integrable_indicator hEmeas
  have hdom : Integrable
      (fun x => ‖f x‖ + E.indicator (fun _ : ℝ => 2 * t) x) volume :=
    hf.norm.add hconst
  have hbadAES : AEStronglyMeasurable[Real.measurableSpace]
      (dyadicVectorBadAverageAt f t)
      (volume : Measure[Real.measureSpace.toMeasurableSpace] ℝ) :=
    (measurable_dyadicVectorBadAverageAt f t).aestronglyMeasurable
      (μ := (volume : Measure[Real.measureSpace.toMeasurableSpace] ℝ))
  have hgoodAES : AEStronglyMeasurable (dyadicVectorGoodPart f t) volume := by
    have hp : AEStronglyMeasurable (E.piecewise
        (dyadicVectorBadAverageAt f t) f) volume :=
      AEStronglyMeasurable.piecewise (μ := volume) hEmeas.nullMeasurableSet
        hbadAES.restrict hf.aestronglyMeasurable.restrict
    have heq : E.piecewise (dyadicVectorBadAverageAt f t) f =
        dyadicVectorGoodPart f t := by
      funext x
      by_cases hx : x ∈ E <;>
        simp [E, dyadicVectorGoodPart, Set.piecewise, hx]
    exact hp.congr (Filter.Eventually.of_forall fun x => congrFun heq x)
  apply hdom.mono' hgoodAES
  filter_upwards [dyadicVectorGoodPart_norm_le_two_ae hf ht] with x hx
  by_cases hxE : x ∈ E
  · have hnonneg : 0 ≤ ‖f x‖ := norm_nonneg _
    have hright : 2 * t ≤ ‖f x‖ + 2 * t := by linarith
    simpa [E, Set.indicator, hxE] using hx.trans hright
  · simp [dyadicVectorGoodPart, E, Set.indicator, hxE]

/-- The dyadic good part has no larger `L¹` norm than the original input. -/
theorem integral_norm_dyadicVectorGoodPart_le {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [TopologicalSpace.PseudoMetrizableSpace H]
    [SecondCountableTopology H] [OpensMeasurableSpace H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t) :
    ∫ x, ‖dyadicVectorGoodPart f t x‖ ∂volume ≤ ∫ x, ‖f x‖ ∂volume := by
  classical
  let S := dyadicVectorMaximalBadCells f t
  let E := dyadicVectorMaximalBadRegion f t
  have hScount : S.Countable := Set.countable_univ.mono (Set.subset_univ S)
  letI : Countable S := hScount.to_subtype
  have hQmeas : ∀ q : S, MeasurableSet (dyadicInterval q.1.1 q.1.2) := by
    intro q
    rw [dyadicInterval]
    exact measurableSet_Ico
  have hdisj : Pairwise (fun q r : S =>
      Disjoint (dyadicInterval q.1.1 q.1.2)
        (dyadicInterval r.1.1 r.1.2)) := by
    intro q r hne
    have hval : q.1 ≠ r.1 := by
      intro heq
      exact hne (Subtype.ext heq)
    exact dyadicVectorMaximalBadCells_pairwiseDisjoint f t q.2 r.2 hval
  have hEeq : E = ⋃ q : S, dyadicInterval q.1.1 q.1.2 := by
    rfl
  have hgood : Integrable (dyadicVectorGoodPart f t) volume :=
    dyadicVectorGoodPart_integrable hf ht
  have hgoodNorm : Integrable (fun x => ‖dyadicVectorGoodPart f t x‖) volume :=
    hgood.norm
  have hsumGood : ∫ x in E, ‖dyadicVectorGoodPart f t x‖ ∂volume =
      ∑' q : S, ∫ x in dyadicInterval q.1.1 q.1.2,
        ‖dyadicVectorGoodPart f t x‖ ∂volume := by
    rw [hEeq]
    exact integral_iUnion hQmeas hdisj hgoodNorm.integrableOn
  have hhasF : HasSum
      (fun q : S => ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume)
      (∫ x in ⋃ q : S, dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume) :=
    hasSum_integral_iUnion hQmeas hdisj hf.norm.integrableOn
  have hhasGood : HasSum
      (fun q : S => ∫ x in dyadicInterval q.1.1 q.1.2,
        ‖dyadicVectorGoodPart f t x‖ ∂volume)
      (∫ x in ⋃ q : S, dyadicInterval q.1.1 q.1.2,
        ‖dyadicVectorGoodPart f t x‖ ∂volume) :=
    hasSum_integral_iUnion hQmeas hdisj hgoodNorm.integrableOn
  have hcell (q : S) :
      ∫ x in dyadicInterval q.1.1 q.1.2,
        ‖dyadicVectorGoodPart f t x‖ ∂volume ≤
      ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume := by
    let m := q.1.1
    let j := q.1.2
    let Q := dyadicInterval m j
    let s := (2 : ℝ) ^ m
    let c := dyadicVectorCellAverage f m j
    have hQ : MeasurableSet Q := by dsimp [Q, dyadicInterval]; exact measurableSet_Ico
    have hs : 0 < s := by dsimp [s]; exact zpow_pos (by norm_num) m
    have hconst :
        ∫ x in Q, ‖dyadicVectorGoodPart f t x‖ ∂volume =
          s * ‖c‖ := by
      calc
        _ = ∫ x in Q, (fun _ : ℝ => ‖c‖) x ∂volume := by
          apply setIntegral_congr_fun hQ
          intro x hx
          change ‖dyadicVectorGoodPart f t x‖ = ‖c‖
          exact congrArg (fun z : H => ‖z‖)
            (dyadicVectorGoodPart_eq_cellAverage_of_mem f t
              (q := q.1) q.2 hx)
        _ = volume.real Q * ‖c‖ := by
          rw [setIntegral_const, smul_eq_mul]
        _ = s * ‖c‖ := by
          rw [show volume.real Q = s by
            simpa [Q, s, m, j] using dyadicInterval_volume_real m j]
    have hnorm : ‖c‖ ≤ dyadicVectorNormCellAverage f m j :=
      norm_dyadicVectorCellAverage_le_normCellAverage f m j
    have hle : s * ‖c‖ ≤ s * dyadicVectorNormCellAverage f m j :=
      mul_le_mul_of_nonneg_left hnorm hs.le
    have hscale : s * dyadicVectorNormCellAverage f m j =
        ∫ x in Q, ‖f x‖ ∂volume := by
      change s * ((∫ x in Q, ‖f x‖ ∂volume) / s) = _
      rw [div_eq_mul_inv]
      calc
        s * ((∫ x in Q, ‖f x‖ ∂volume) * s⁻¹) =
            (s * s⁻¹) * (∫ x in Q, ‖f x‖ ∂volume) := by ring
        _ = ∫ x in Q, ‖f x‖ ∂volume := by
          rw [mul_inv_cancel₀ (ne_of_gt hs), one_mul]
    simpa [Q, c, m, j] using hconst ▸ hle.trans_eq hscale
  have htsum :
      (∑' q : S, ∫ x in dyadicInterval q.1.1 q.1.2,
        ‖dyadicVectorGoodPart f t x‖ ∂volume) ≤
      ∑' q : S, ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume :=
    hhasGood.summable.tsum_le_tsum hcell hhasF.summable
  have hEmeas : MeasurableSet E := measurableSet_dyadicVectorMaximalBadRegion f t
  have hcompl : ∫ x in Eᶜ, ‖dyadicVectorGoodPart f t x‖ ∂volume =
      ∫ x in Eᶜ, ‖f x‖ ∂volume := by
    apply setIntegral_congr_fun hEmeas.compl
    intro x hx
    have hx' : x ∉ E := by simpa using hx
    simp [dyadicVectorGoodPart, E, hx']
  have hsumF :
      (∑' q : S, ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume) =
        ∫ x in E, ‖f x‖ ∂volume := by
    rw [hEeq]
    exact (integral_iUnion hQmeas hdisj hf.norm.integrableOn).symm
  calc
    ∫ x, ‖dyadicVectorGoodPart f t x‖ ∂volume =
        (∫ x in E, ‖dyadicVectorGoodPart f t x‖ ∂volume) +
          ∫ x in Eᶜ, ‖dyadicVectorGoodPart f t x‖ ∂volume :=
      (integral_add_compl hEmeas hgoodNorm).symm
    _ = (∫ x in E, ‖dyadicVectorGoodPart f t x‖ ∂volume) +
          ∫ x in Eᶜ, ‖f x‖ ∂volume := by rw [hcompl]
    _ = (∑' q : S, ∫ x in dyadicInterval q.1.1 q.1.2,
          ‖dyadicVectorGoodPart f t x‖ ∂volume) +
          ∫ x in Eᶜ, ‖f x‖ ∂volume := by rw [hsumGood]
    _ ≤ (∑' q : S, ∫ x in dyadicInterval q.1.1 q.1.2,
          ‖f x‖ ∂volume) + ∫ x in Eᶜ, ‖f x‖ ∂volume :=
        add_le_add htsum le_rfl
    _ = (∫ x in E, ‖f x‖ ∂volume) + ∫ x in Eᶜ, ‖f x‖ ∂volume := by
      rw [hsumF]
    _ = ∫ x, ‖f x‖ ∂volume := integral_add_compl hEmeas hf.norm

/-- The dyadic good part has squared `L²` norm at most
`2 t ‖f‖₁`, using its pointwise `2t` bound and the exact `L¹` estimate. -/
theorem integral_norm_sq_dyadicVectorGoodPart_le {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [TopologicalSpace.PseudoMetrizableSpace H]
    [SecondCountableTopology H] [OpensMeasurableSpace H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} (ht : 0 < t) :
    ∫ x, ‖dyadicVectorGoodPart f t x‖ ^ 2 ∂volume ≤
      2 * t * ∫ x, ‖f x‖ ∂volume := by
  have hgood : Integrable (dyadicVectorGoodPart f t) volume :=
    dyadicVectorGoodPart_integrable hf ht
  have hgoodNorm : Integrable (fun x => ‖dyadicVectorGoodPart f t x‖) volume :=
    hgood.norm
  have hsqAES : AEStronglyMeasurable
      (fun x => ‖dyadicVectorGoodPart f t x‖ ^ 2) volume :=
    hgoodNorm.aestronglyMeasurable.pow 2
  have hdom : Integrable
      (fun x => (2 * t) * ‖dyadicVectorGoodPart f t x‖) volume :=
    hgoodNorm.const_mul (2 * t)
  have hsq : Integrable
      (fun x => ‖dyadicVectorGoodPart f t x‖ ^ 2) volume := by
    apply hdom.mono' hsqAES
    filter_upwards [dyadicVectorGoodPart_norm_le_two_ae hf ht] with x hx
    have hnonneg : 0 ≤ ‖dyadicVectorGoodPart f t x‖ := norm_nonneg _
    have hle : ‖dyadicVectorGoodPart f t x‖ ^ 2 ≤
        (2 * t) * ‖dyadicVectorGoodPart f t x‖ := by nlinarith
    calc
      ‖‖dyadicVectorGoodPart f t x‖ ^ 2‖ =
          ‖dyadicVectorGoodPart f t x‖ ^ 2 :=
        Real.norm_of_nonneg (sq_nonneg _)
      _ ≤ (2 * t) * ‖dyadicVectorGoodPart f t x‖ := hle
  have hmono :
      ∫ x, ‖dyadicVectorGoodPart f t x‖ ^ 2 ∂volume ≤
        ∫ x, (2 * t) * ‖dyadicVectorGoodPart f t x‖ ∂volume := by
    apply integral_mono_ae hsq hdom
    filter_upwards [dyadicVectorGoodPart_norm_le_two_ae hf ht] with x hx
    have hnonneg : 0 ≤ ‖dyadicVectorGoodPart f t x‖ := norm_nonneg _
    nlinarith
  calc
    ∫ x, ‖dyadicVectorGoodPart f t x‖ ^ 2 ∂volume ≤
        ∫ x, (2 * t) * ‖dyadicVectorGoodPart f t x‖ ∂volume := hmono
    _ = (2 * t) * ∫ x, ‖dyadicVectorGoodPart f t x‖ ∂volume := by
      rw [integral_const_mul]
    _ ≤ (2 * t) * ∫ x, ‖f x‖ ∂volume := by
      apply mul_le_mul_of_nonneg_left
        (integral_norm_dyadicVectorGoodPart_le hf ht)
      positivity

/-- The scalar series of `L¹` norms of the selected vector bad pieces is
summable. This is the direct countable-cell reduction needed for convergence
of the bad series in `L¹`. -/
theorem dyadicVectorBadPieces_l1_summable {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} :
    Summable (fun q : dyadicVectorMaximalBadCells f t =>
      ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume) := by
  classical
  let S := dyadicVectorMaximalBadCells f t
  have hScount : S.Countable := Set.countable_univ.mono (Set.subset_univ S)
  letI : Countable S := hScount.to_subtype
  have hQmeas : ∀ q : S, MeasurableSet (dyadicInterval q.1.1 q.1.2) := by
    intro q
    rw [dyadicInterval]
    exact measurableSet_Ico
  have hdisj : Pairwise (fun q r : S =>
      Disjoint (dyadicInterval q.1.1 q.1.2)
        (dyadicInterval r.1.1 r.1.2)) := by
    intro q r hne
    have hval : q.1 ≠ r.1 := by
      intro heq
      exact hne (Subtype.ext heq)
    exact dyadicVectorMaximalBadCells_pairwiseDisjoint f t q.2 r.2 hval
  have hmass : Summable (fun q : S =>
      ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume) := by
    exact (hasSum_integral_iUnion hQmeas hdisj hf.norm.integrableOn).summable
  have htwice := hmass.mul_left (2 : ℝ)
  apply Summable.of_nonneg_of_le
  · intro q
    exact integral_nonneg (fun x => norm_nonneg _)
  · intro q
    exact integral_norm_dyadicVectorBadPiece_le_two hf q.1.1 q.1.2
  · exact htwice

/-- The total `L¹` mass of the countable vector bad series is at most twice
the input `L¹` norm. -/
theorem dyadicVectorBadPieces_l1_tsum_le_two {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} :
    (∑' q : dyadicVectorMaximalBadCells f t,
      ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume) ≤
        2 * ∫ x, ‖f x‖ ∂volume := by
  classical
  let S := dyadicVectorMaximalBadCells f t
  have hScount : S.Countable := Set.countable_univ.mono (Set.subset_univ S)
  letI : Countable S := hScount.to_subtype
  have hQmeas : ∀ q : S, MeasurableSet (dyadicInterval q.1.1 q.1.2) := by
    intro q
    rw [dyadicInterval]
    exact measurableSet_Ico
  have hdisj : Pairwise (fun q r : S =>
      Disjoint (dyadicInterval q.1.1 q.1.2)
        (dyadicInterval r.1.1 r.1.2)) := by
    intro q r hne
    have hval : q.1 ≠ r.1 := by
      intro heq
      exact hne (Subtype.ext heq)
    exact dyadicVectorMaximalBadCells_pairwiseDisjoint f t q.2 r.2 hval
  have hmass : Summable (fun q : S =>
      ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume) := by
    exact (hasSum_integral_iUnion hQmeas hdisj hf.norm.integrableOn).summable
  have hbad := dyadicVectorBadPieces_l1_summable hf (t := t)
  have hcell (q : S) :
      ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume ≤
        2 * ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume :=
    integral_norm_dyadicVectorBadPiece_le_two hf q.1.1 q.1.2
  calc
    (∑' q : S, ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ∂volume) ≤
        ∑' q : S, 2 * ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume :=
      hbad.tsum_le_tsum hcell (hmass.mul_left (2 : ℝ))
    _ = 2 * ∑' q : S,
          ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ∂volume :=
      hmass.tsum_mul_left 2
    _ ≤ 2 * ∫ x, ‖f x‖ ∂volume := by
      apply mul_le_mul_of_nonneg_left
        (dyadicVectorMaximalBadCells_sum_integral_le hf)
      norm_num

/-- The selected bad pieces form a convergent series in the Bochner `L¹`
space. -/
theorem dyadicVectorBadPieces_l1_summableLp {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} (hf : Integrable f volume) {t : ℝ} :
    Summable (fun q : dyadicVectorMaximalBadCells f t =>
      (integrable_dyadicVectorBadPiece hf q.1.1 q.1.2).toL1
        (dyadicVectorBadPiece f q.1.1 q.1.2)) := by
  apply Summable.of_norm
  convert dyadicVectorBadPieces_l1_summable hf (t := t) using 1
  ext q
  exact L1.norm_of_fun_eq_integral_norm
    (integrable_dyadicVectorBadPiece hf q.1.1 q.1.2)

end

end FractionalPrimes.Literature.JSW

#print axioms FractionalPrimes.Literature.JSW.norm_dyadicVectorAverage_le_average_norm
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorNormCellAverage_scale_lt
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorMaximalBadCells_pairwiseDisjoint
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorMaximalBadCells_cover_bad
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorMaximalBadCells_measure_le
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorMaximalBadCells_sum_length_le
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorMaximalBadCells_sum_integral_le
#print axioms FractionalPrimes.Literature.JSW.exists_maximal_bad_dyadicVector_ancestor
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorAverage_tendsto_atBot_ae_of_integrable
#print axioms FractionalPrimes.Literature.JSW.integrable_dyadicVectorBadPiece
#print axioms FractionalPrimes.Literature.JSW.norm_dyadicVectorCellAverage_le_normCellAverage
#print axioms FractionalPrimes.Literature.JSW.integral_norm_dyadicVectorBadPiece_le_two
#print axioms FractionalPrimes.Literature.JSW.integral_dyadicVectorBadPiece_eq_zero
#print axioms FractionalPrimes.Literature.JSW.measurableSet_dyadicVectorMaximalBadRegion
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorMaximalBadCell_average_le_two
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorNorm_le_of_not_mem_badRegion_ae
#print axioms FractionalPrimes.Literature.JSW.norm_dyadicVectorBadAverageAt_le_two
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorGoodPart_norm_le_two_ae
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorBadPieces_l1_summable
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorBadPieces_l1_tsum_le_two
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorBadPieces_l1_summableLp

end
