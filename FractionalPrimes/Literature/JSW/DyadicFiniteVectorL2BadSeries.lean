module

public import FractionalPrimes.Literature.JSW.DyadicFiniteVectorAverage
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# L² bounds for the finite-vector dyadic bad pieces

This module develops the square-integrability estimate needed to pass from
the disjoint dyadic bad pieces to their `L²` sum.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace FractionalPrimes.Literature.JSW

noncomputable section

private theorem l2_norm_sq_eq_integral_norm_sq {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℝ →₂[volume] H) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂volume := by
  calc
    ‖u‖ ^ 2 = ⟪u, u⟫_ℝ := by simp [inner_self_eq_norm_sq_to_K]
    _ = ∫ x, ⟪u x, u x⟫_ℝ ∂volume := L2.inner_def u u
    _ = ∫ x, ‖u x‖ ^ 2 ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [inner_self_eq_norm_sq_to_K]

/-- On one dyadic cell, subtracting its vector average is an orthogonal
projection error in `L²`; its squared integral is no larger than the input's
squared integral on that cell. -/
theorem integral_norm_sq_dyadicVectorBadPiece_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {f : ℝ → H}
    (hf : Integrable f volume) (hf₂ : MemLp f 2 volume) (m j : ℤ) :
    ∫ x, ‖dyadicVectorBadPiece f m j x‖ ^ 2 ∂volume ≤
      ∫ x in dyadicInterval m j, ‖f x‖ ^ 2 ∂volume := by
  let Q := dyadicInterval m j
  let s := (2 : ℝ) ^ m
  let c := dyadicVectorCellAverage f m j
  have hs : 0 < s := by dsimp [s]; exact zpow_pos (by norm_num) m
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hfinite : volume Q ≠ ⊤ := by
    have hlt : volume Q < ⊤ := by
      dsimp [Q, dyadicInterval]
      exact measure_Ico_lt_top
    exact ne_of_lt hlt
  have hfQ : Integrable (fun x : ℝ => f x) (volume.restrict Q) := by
    change IntegrableOn f Q volume
    exact hf.integrableOn
  have hfsq : Integrable (fun x : ℝ => ‖f x‖ ^ 2) volume :=
    hf₂.integrable_norm_pow (by norm_num)
  have hfsqQ : Integrable (fun x : ℝ => ‖f x‖ ^ 2)
      (volume.restrict Q) := hfsq.integrableOn
  have hcQ : Integrable (fun _ : ℝ => c) (volume.restrict Q) := by
    change IntegrableOn (fun _ : ℝ => c) Q volume
    exact MeasureTheory.integrableOn_const hfinite
  have hdiffQ : Integrable (fun x : ℝ => f x - c) (volume.restrict Q) :=
    hfQ.sub hcQ
  have hcrossQ : Integrable (fun x : ℝ => ⟪f x, c⟫_ℝ)
      (volume.restrict Q) := hfQ.inner_const c
  have hcSqQ : Integrable (fun _ : ℝ => ‖c‖ ^ 2) (volume.restrict Q) := by
    change IntegrableOn (fun _ : ℝ => ‖c‖ ^ 2) Q volume
    exact MeasureTheory.integrableOn_const hfinite
  have hdiffSqQ : Integrable (fun x : ℝ => ‖f x - c‖ ^ 2)
      (volume.restrict Q) := by
    have hdom : Integrable
        (fun x : ℝ => 2 * ‖f x‖ ^ 2 + 2 * ‖c‖ ^ 2)
        (volume.restrict Q) := (hfsqQ.const_mul 2).add (hcSqQ.const_mul 2)
    apply hdom.mono'
      ((hdiffQ.aestronglyMeasurable.norm.pow 2))
    filter_upwards [] with x
    have hsub := norm_sub_le (f x) c
    change ‖‖f x - c‖ ^ 2‖ ≤ _
    have hsq : ‖f x - c‖ ^ 2 ≤ (‖f x‖ + ‖c‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hsub
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [hsq, sq_nonneg (‖f x‖ - ‖c‖)]
  have hmean : (∫ x in Q, f x ∂volume) = s • c := by
    dsimp [c, dyadicVectorCellAverage, s]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
  have hcross :
      ∫ x in Q, ⟪f x, c⟫_ℝ ∂volume = s * ‖c‖ ^ 2 := by
    calc
      ∫ x in Q, ⟪f x, c⟫_ℝ ∂volume =
          ∫ x in Q, ⟪c, f x⟫_ℝ ∂volume := by
        apply setIntegral_congr_fun hQ
        intro x hx
        exact real_inner_comm _ _
      _ = ⟪c, ∫ x in Q, f x ∂volume⟫_ℝ := integral_inner hfQ c
      _ = ⟪c, s • c⟫_ℝ := by rw [hmean]
      _ = s * ‖c‖ ^ 2 := by
        simp [inner_smul_right, inner_self_eq_norm_sq_to_K]
  have hconst : ∫ x in Q, (fun _ : ℝ => ‖c‖ ^ 2) x ∂volume =
      s * ‖c‖ ^ 2 := by
    rw [setIntegral_const, show volume.real Q = s by
      simpa [Q, s] using dyadicInterval_volume_real m j]
    simp [smul_eq_mul]
  have hExpanded :
      ∫ x in Q, ‖f x - c‖ ^ 2 ∂volume =
        (∫ x in Q, ‖f x‖ ^ 2 ∂volume) -
          2 * (∫ x in Q, ⟪f x, c⟫_ℝ ∂volume) +
            ∫ x in Q, (fun _ : ℝ => ‖c‖ ^ 2) x ∂volume := by
    calc
      ∫ x in Q, ‖f x - c‖ ^ 2 ∂volume =
          ∫ x in Q, (‖f x‖ ^ 2 - 2 * ⟪f x, c⟫_ℝ + ‖c‖ ^ 2) ∂volume := by
        apply setIntegral_congr_fun hQ
        intro x hx
        exact norm_sub_sq_real (f x) c
      _ = (∫ x in Q, ‖f x‖ ^ 2 ∂volume) -
            2 * (∫ x in Q, ⟪f x, c⟫_ℝ ∂volume) +
              ∫ x in Q, (fun _ : ℝ => ‖c‖ ^ 2) x ∂volume := by
        calc
          ∫ x in Q, (‖f x‖ ^ 2 - 2 * ⟪f x, c⟫_ℝ + ‖c‖ ^ 2) ∂volume =
              (∫ x in Q, ‖f x‖ ^ 2 - 2 * ⟪f x, c⟫_ℝ ∂volume) +
                ∫ x in Q, (fun _ : ℝ => ‖c‖ ^ 2) x ∂volume :=
            integral_add (hfsqQ.sub (hcrossQ.const_mul 2)) hcSqQ
          _ = (∫ x in Q, ‖f x‖ ^ 2 ∂volume) -
                2 * (∫ x in Q, ⟪f x, c⟫_ℝ ∂volume) +
                  ∫ x in Q, (fun _ : ℝ => ‖c‖ ^ 2) x ∂volume := by
            rw [integral_sub hfsqQ (hcrossQ.const_mul 2), integral_const_mul]
  have hlocal :
      ∫ x in Q, ‖f x - c‖ ^ 2 ∂volume ≤ ∫ x in Q, ‖f x‖ ^ 2 ∂volume := by
    rw [hExpanded, hcross, hconst]
    have hnonneg : 0 ≤ s * ‖c‖ ^ 2 := mul_nonneg hs.le (sq_nonneg _)
    nlinarith
  have hnormEq :
      (fun x : ℝ => ‖dyadicVectorBadPiece f m j x‖ ^ 2) =
        Q.indicator (fun x => ‖f x - c‖ ^ 2) := by
    funext x
    by_cases hx : x ∈ Q <;>
      simp [dyadicVectorBadPiece, Q, c, hx]
  rw [hnormEq, integral_indicator hQ]
  simpa [Q] using hlocal

/-- A vector bad piece belongs to `L²` whenever the original input does. -/
theorem memLp_dyadicVectorBadPiece_two {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} (hf : Integrable f volume) (hf₂ : MemLp f 2 volume)
    (m j : ℤ) : MemLp (dyadicVectorBadPiece f m j) 2 volume := by
  let Q := dyadicInterval m j
  let c := dyadicVectorCellAverage f m j
  have hQ : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hfinite : volume Q ≠ ⊤ := by
    have hlt : volume Q < ⊤ := by
      dsimp [Q, dyadicInterval]
      exact measure_Ico_lt_top
    exact ne_of_lt hlt
  have hfsq : Integrable (fun x : ℝ => ‖f x‖ ^ 2) volume :=
    hf₂.integrable_norm_pow (by norm_num)
  have hfsqQ : Integrable (fun x : ℝ => ‖f x‖ ^ 2)
      (volume.restrict Q) := hfsq.integrableOn
  have hcSqQ : Integrable (fun _ : ℝ => ‖c‖ ^ 2) (volume.restrict Q) := by
    change IntegrableOn (fun _ : ℝ => ‖c‖ ^ 2) Q volume
    exact MeasureTheory.integrableOn_const hfinite
  have hdomQ : Integrable (fun x : ℝ =>
      2 * ‖f x‖ ^ 2 + 2 * ‖c‖ ^ 2) (volume.restrict Q) :=
    (hfsqQ.const_mul 2).add (hcSqQ.const_mul 2)
  have hdom : Integrable
      (Q.indicator (fun x : ℝ => 2 * ‖f x‖ ^ 2 + 2 * ‖c‖ ^ 2)) volume := by
    change IntegrableOn (fun x : ℝ =>
      2 * ‖f x‖ ^ 2 + 2 * ‖c‖ ^ 2) Q volume at hdomQ
    exact hdomQ.integrable_indicator hQ
  have hbadAES : AEStronglyMeasurable (dyadicVectorBadPiece f m j) volume :=
    (integrable_dyadicVectorBadPiece hf m j).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hbadAES).2
  apply hdom.mono' (hbadAES.norm.pow 2)
  filter_upwards [] with x
  by_cases hx : x ∈ Q
  · have hsub := norm_sub_le (f x) c
    have hsq : ‖f x - c‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖c‖ ^ 2 := by
      have hsq' : ‖f x - c‖ ^ 2 ≤ (‖f x‖ + ‖c‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hsub
      nlinarith [hsq', sq_nonneg (‖f x‖ - ‖c‖)]
    simpa [dyadicVectorBadPiece, Q, hx,
      Real.norm_of_nonneg (sq_nonneg _)] using hsq
  · simp [dyadicVectorBadPiece, Q, hx]

/-- The selected bad pieces form a convergent series in vector-valued `L²`.
Their supports are disjoint, so square summability of their norms suffices. -/
theorem dyadicVectorBadPieces_l2_summable {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} (hf : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {t : ℝ} :
    Summable (fun q : dyadicVectorMaximalBadCells f t =>
      (memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
        (dyadicVectorBadPiece f q.1.1 q.1.2)) := by
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
  have hfsq : Integrable (fun x : ℝ => ‖f x‖ ^ 2) volume :=
    hf₂.integrable_norm_pow (by norm_num)
  have hmass : Summable (fun q : S =>
      ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ^ 2 ∂volume) := by
    exact (hasSum_integral_iUnion hQmeas hdisj hfsq.integrableOn).summable
  let b : S → ℝ →₂[volume] H := fun q =>
    (memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
      (dyadicVectorBadPiece f q.1.1 q.1.2)
  have hbound (q : S) :
      ‖b q‖ ^ 2 ≤ ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ^ 2 ∂volume := by
    calc
      ‖b q‖ ^ 2 = ∫ x, ‖b q x‖ ^ 2 ∂volume :=
        l2_norm_sq_eq_integral_norm_sq (b q)
      _ = ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ^ 2 ∂volume := by
        apply integral_congr_ae
        filter_upwards [
          (memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).coeFn_toLp]
          with x hx
        rw [hx]
      _ ≤ ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ^ 2 ∂volume :=
        integral_norm_sq_dyadicVectorBadPiece_le hf hf₂ q.1.1 q.1.2
  have hsq : Summable (fun q : S => ‖b q‖ ^ 2) := by
    apply Summable.of_nonneg_of_le
    · intro q
      exact sq_nonneg _
    · exact hbound
    · exact hmass
  let U : S → Submodule ℝ (ℝ →₂[volume] H) := fun q =>
    Submodule.span ℝ ({b q} : Set (ℝ →₂[volume] H))
  let V : (q : S) → U q →ₗᵢ[ℝ] (ℝ →₂[volume] H) := fun q =>
    (U q).subtypeₗᵢ
  have horth : OrthogonalFamily ℝ (fun q : S => U q)
      (fun q => (U q).subtypeₗᵢ) := by
    apply OrthogonalFamily.of_pairwise
    intro q r hne
    have hval : q.1 ≠ r.1 := by
      intro heq
      exact hne (Subtype.ext heq)
    have hcellDisj : Disjoint (dyadicInterval q.1.1 q.1.2)
        (dyadicInterval r.1.1 r.1.2) :=
      dyadicVectorMaximalBadCells_pairwiseDisjoint f t q.2 r.2 hval
    have hqRep : b q =ᵐ[volume]
        fun x => dyadicVectorBadPiece f q.1.1 q.1.2 x :=
      (memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).coeFn_toLp
    have hrRep : b r =ᵐ[volume]
        fun x => dyadicVectorBadPiece f r.1.1 r.1.2 x :=
      (memLp_dyadicVectorBadPiece_two hf hf₂ r.1.1 r.1.2).coeFn_toLp
    have hzero :
        ⟪b q, b r⟫_ℝ = 0 := by
      rw [L2.inner_def]
      have hAE : (fun x => ⟪b q x, b r x⟫_ℝ) =ᵐ[volume] 0 := by
        filter_upwards [hqRep, hrRep] with x hxq hxr
        rw [hxq, hxr]
        by_cases hxin : x ∈ dyadicInterval q.1.1 q.1.2
        · have hxout : x ∉ dyadicInterval r.1.1 r.1.2 := by
            intro hxout
            exact Set.disjoint_left.mp hcellDisj hxin hxout
          rw [dyadicVectorBadPiece_eq_zero_of_not_mem f _ _ hxout]
          simp
        · rw [dyadicVectorBadPiece_eq_zero_of_not_mem f _ _ hxin]
          simp
      calc
        ∫ x, ⟪b q x, b r x⟫_ℝ ∂volume = ∫ x, (0 : ℝ) ∂volume :=
          integral_congr_ae hAE
        _ = 0 := by simp
    apply Submodule.isOrtho_iff_inner_eq.mpr
    intro u hu v hv
    rw [Submodule.mem_span_singleton] at hu hv
    obtain ⟨a, rfl⟩ := hu
    obtain ⟨d, rfl⟩ := hv
    simp [inner_smul_left, inner_smul_right, hzero]
  let u : (q : S) → U q := fun q =>
    ⟨b q, Submodule.mem_span_singleton_self (b q)⟩
  have hsum : Summable (fun q : S => V q (u q)) := by
    apply (horth.summable_iff_norm_sq_summable u).2
    simpa [u] using hsq
  simpa [U, V, u] using hsum

/-- The total squared `L²` norm of the disjoint bad pieces is bounded by the
source-exact constant `4` times the input's squared `L²` norm. -/
theorem dyadicVectorBadPieces_l2_norm_sq_tsum_le_four {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} (hf : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {t : ℝ} :
    (∑' q : dyadicVectorMaximalBadCells f t,
      ‖(memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
          (dyadicVectorBadPiece f q.1.1 q.1.2)‖ ^ 2) ≤
        4 * ∫ x, ‖f x‖ ^ 2 ∂volume := by
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
  have hfsq : Integrable (fun x : ℝ => ‖f x‖ ^ 2) volume :=
    hf₂.integrable_norm_pow (by norm_num)
  have hmassSum :
      (∑' q : S, ∫ x in dyadicInterval q.1.1 q.1.2,
          ‖f x‖ ^ 2 ∂volume) =
        ∫ x in ⋃ q : S, dyadicInterval q.1.1 q.1.2,
          ‖f x‖ ^ 2 ∂volume := by
    rw [integral_iUnion hQmeas hdisj hfsq.integrableOn]
  have hmassLe :
      (∑' q : S, ∫ x in dyadicInterval q.1.1 q.1.2,
          ‖f x‖ ^ 2 ∂volume) ≤ ∫ x, ‖f x‖ ^ 2 ∂volume := by
    rw [hmassSum]
    apply setIntegral_le_integral hfsq
    filter_upwards [] with x
    exact sq_nonneg _
  have hmassSummable : Summable (fun q : S =>
      ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ^ 2 ∂volume) := by
    exact (hasSum_integral_iUnion hQmeas hdisj hfsq.integrableOn).summable
  have hcell (q : S) :
      ‖(memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
          (dyadicVectorBadPiece f q.1.1 q.1.2)‖ ^ 2 ≤
        ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ^ 2 ∂volume := by
    calc
      _ = ∫ x, ‖(memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
          (dyadicVectorBadPiece f q.1.1 q.1.2) x‖ ^ 2 ∂volume :=
        l2_norm_sq_eq_integral_norm_sq _
      _ = ∫ x, ‖dyadicVectorBadPiece f q.1.1 q.1.2 x‖ ^ 2 ∂volume := by
        apply integral_congr_ae
        filter_upwards [
          (memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).coeFn_toLp]
          with x hx
        rw [hx]
      _ ≤ ∫ x in dyadicInterval q.1.1 q.1.2, ‖f x‖ ^ 2 ∂volume :=
        integral_norm_sq_dyadicVectorBadPiece_le hf hf₂ q.1.1 q.1.2
  have hsquareSummable : Summable (fun q : S =>
      ‖(memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
          (dyadicVectorBadPiece f q.1.1 q.1.2)‖ ^ 2) := by
    apply Summable.of_nonneg_of_le
    · intro q
      exact sq_nonneg _
    · exact hcell
    · exact hmassSummable
  calc
    (∑' q : S,
      ‖(memLp_dyadicVectorBadPiece_two hf hf₂ q.1.1 q.1.2).toLp
          (dyadicVectorBadPiece f q.1.1 q.1.2)‖ ^ 2) ≤
        ∑' q : S, ∫ x in dyadicInterval q.1.1 q.1.2,
          ‖f x‖ ^ 2 ∂volume :=
      hsquareSummable.tsum_le_tsum hcell hmassSummable
    _ ≤ ∫ x, ‖f x‖ ^ 2 ∂volume := hmassLe
    _ ≤ 4 * ∫ x, ‖f x‖ ^ 2 ∂volume := by
      have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂volume :=
        integral_nonneg (fun x => sq_nonneg _)
      nlinarith

/-- The input is the good part plus the pointwise sum of the selected bad
pieces. At each point at most one selected cell contributes. -/
theorem dyadicVectorGoodPart_add_badPieces_eq {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} {t : ℝ} (x : ℝ) :
    f x = dyadicVectorGoodPart f t x +
      ∑' q : dyadicVectorMaximalBadCells f t,
        dyadicVectorBadPiece f q.1.1 q.1.2 x := by
  classical
  let S := dyadicVectorMaximalBadCells f t
  let E := dyadicVectorMaximalBadRegion f t
  by_cases hxE : x ∈ E
  · have hex : ∃ q : S, x ∈ dyadicInterval q.1.1 q.1.2 := by
      simpa [E, S, dyadicVectorMaximalBadRegion] using hxE
    obtain ⟨q, hxq⟩ := hex
    have hzero (r : S) (hr : r ≠ q) :
        dyadicVectorBadPiece f r.1.1 r.1.2 x = 0 := by
      apply dyadicVectorBadPiece_eq_zero_of_not_mem
      intro hxr
      have hval : r.1 ≠ q.1 := by
        intro heq
        exact hr (Subtype.ext heq)
      have hdisj := dyadicVectorMaximalBadCells_pairwiseDisjoint
        f t r.2 q.2 hval
      exact Set.disjoint_left.mp hdisj hxr hxq
    rw [tsum_eq_single q hzero]
    have hgood := dyadicVectorGoodPart_eq_cellAverage_of_mem
      (f := f) (t := t) (q := q.1) q.2 hxq
    rw [hgood]
    dsimp [dyadicVectorBadPiece]
    simp [hxq]
  · have hzero (q : S) :
        dyadicVectorBadPiece f q.1.1 q.1.2 x = 0 := by
      apply dyadicVectorBadPiece_eq_zero_of_not_mem
      intro hxq
      exact hxE (Set.mem_iUnion.mpr ⟨q, hxq⟩)
    have htsum :
        (∑' q : S, dyadicVectorBadPiece f q.1.1 q.1.2 x) = 0 := by
      simp [hzero]
    change f x = dyadicVectorGoodPart f t x +
      ∑' q : S, dyadicVectorBadPiece f q.1.1 q.1.2 x
    rw [htsum]
    simp [dyadicVectorGoodPart, E, hxE]

end

end FractionalPrimes.Literature.JSW

#print axioms FractionalPrimes.Literature.JSW.integral_norm_sq_dyadicVectorBadPiece_le
#print axioms FractionalPrimes.Literature.JSW.memLp_dyadicVectorBadPiece_two
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorBadPieces_l2_summable
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorBadPieces_l2_norm_sq_tsum_le_four
#print axioms FractionalPrimes.Literature.JSW.dyadicVectorGoodPart_add_badPieces_eq

end
