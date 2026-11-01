module

public import FractionalPrimes.Literature.JSW.Conventions
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Cancellation and positivity splitting

The arbitrary finite measure is convolved with the fixed cutoff from
`lj:conventions`. This file develops the exact measure splitting used in
`lj:measure-splitting`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Convolution ContDiff

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The cutoff convolution `φ * σ`, written with the real convolution
convention of Mathlib. -/
def measureSplittingPsi (σ : Measure ℝ) : ℝ → ℝ :=
  (fun _ : ℝ => (1 : ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, σ] φ

/-- The signed cancellation measure `σ - ψ(x) dx`. -/
def measureSplittingNu (σ : Measure ℝ) [IsFiniteMeasure σ] : SignedMeasure ℝ :=
  σ.toSignedMeasure - volume.withDensityᵥ (measureSplittingPsi σ)

/-- Fourier--Stieltjes transform of a positive measure in the JSW phase convention. -/
def measureSplittingFourier (μ : Measure ℝ) (ξ : ℝ) : ℂ :=
  ∫ x, Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) ∂μ

/-- Fourier--Stieltjes transform of a real signed measure in the JSW convention. -/
def measureSplittingNuFourier (σ : Measure ℝ) [IsFiniteMeasure σ] (ξ : ℝ) : ℂ :=
  ∫ᵛ x, Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) ∂<•(measureSplittingNu σ)

/-- Fourier transform of the smoothed density. -/
def measureSplittingPsiFourier (σ : Measure ℝ) (ξ : ℝ) : ℂ :=
  jswFourier (fun x => (measureSplittingPsi σ x : ℂ)) ξ

theorem measureSplittingPsi_nonneg (σ : Measure ℝ) [IsFiniteMeasure σ]
    (x : ℝ) : 0 ≤ measureSplittingPsi σ x := by
  unfold measureSplittingPsi
  apply integral_nonneg
  intro y
  exact mul_nonneg (by norm_num) (phi_nonneg (x - y))

theorem measureSplittingPsi_integral (σ : Measure ℝ) [IsProbabilityMeasure σ] :
    ∫ x, measureSplittingPsi σ x ∂volume = 1 := by
  unfold measureSplittingPsi
  rw [MeasureTheory.integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ)
    (integrable_const (1 : ℝ))
    (phi_contDiff.continuous.integrable_of_hasCompactSupport phi_hasCompactSupport)]
  simp [integral_phi]

private theorem phi_eq_zero_of_not_mem_Icc {x : ℝ}
    (hx : x ∉ Set.Icc (-(1 : ℝ)) 1) : φ x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx'
  exact hx (tsupport_phi_subset hx')

theorem measureSplittingPsi_eq_zero_of_not_mem_Icc (σ : Measure ℝ)
    [IsFiniteMeasure σ] (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {x : ℝ} (hx : x ∉ Set.Icc (-(2 : ℝ)) 2) : measureSplittingPsi σ x = 0 := by
  unfold measureSplittingPsi
  apply integral_eq_zero_of_ae
  filter_upwards [Measure.support_mem_ae (μ := σ)] with y hy
  have hyI : y ∈ Set.Icc (-(1 : ℝ)) 1 := hσ hy
  have hxy : x - y ∉ Set.Icc (-(1 : ℝ)) 1 := by
    intro h
    rcases Set.mem_Icc.mp hyI with ⟨hylo, hyhi⟩
    rcases Set.mem_Icc.mp h with ⟨hlo, hhi⟩
    apply hx
    constructor <;> nlinarith
  simp [phi_eq_zero_of_not_mem_Icc hxy]

theorem measureSplittingPsi_tsupport_subset (σ : Measure ℝ)
    [IsFiniteMeasure σ] (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    tsupport (measureSplittingPsi σ) ⊆ Set.Icc (-(2 : ℝ)) 2 := by
  apply closure_minimal
  · intro x hx
    change measureSplittingPsi σ x ≠ 0 at hx
    by_contra hnot
    exact hx (measureSplittingPsi_eq_zero_of_not_mem_Icc σ hσ hnot)
  · exact isClosed_Icc

private theorem iteratedDeriv_phi_hasCompactSupport (n : ℕ) :
    HasCompactSupport (iteratedDeriv n φ) := by
  induction n with
  | zero => simpa using phi_hasCompactSupport
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

private theorem iteratedDeriv_phi_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (phi_contDiff.continuous_iteratedDeriv n (by simp)).bounded_above_of_compact_support
      (iteratedDeriv_phi_hasCompactSupport n)
  refine ⟨C, le_trans (norm_nonneg _) (hC 0), hC⟩

private theorem integrable_iteratedDeriv_phi_translate (σ : Measure ℝ)
    [IsFiniteMeasure σ] (n : ℕ) (x : ℝ) :
    Integrable (fun y => iteratedDeriv n φ (x - y)) σ := by
  obtain ⟨C, hC, hbound⟩ := iteratedDeriv_phi_bound n
  refine (integrable_const ‖C‖).mono' ?_ ?_
  · exact (phi_contDiff.continuous_iteratedDeriv n (by simp)).comp
      (continuous_const.sub continuous_id) |>.aestronglyMeasurable
  · filter_upwards [] with y
    calc
      ‖iteratedDeriv n φ (x - y)‖ ≤ C := hbound _
      _ ≤ ‖C‖ := le_abs_self _

private theorem integral_iteratedDeriv_phi_hasDerivAt (σ : Measure ℝ)
    [IsFiniteMeasure σ] (n : ℕ) (x : ℝ) :
    HasDerivAt (fun z => ∫ y, iteratedDeriv n φ (z - y) ∂σ)
      (∫ y, iteratedDeriv (n + 1) φ (x - y) ∂σ) x := by
  obtain ⟨C, hC, hbound⟩ := iteratedDeriv_phi_bound (n + 1)
  let F : ℝ → ℝ → ℝ := fun z y => iteratedDeriv n φ (z - y)
  let F' : ℝ → ℝ → ℝ := fun z y => iteratedDeriv (n + 1) φ (z - y)
  have hF_meas : ∀ᶠ z in nhds x, AEStronglyMeasurable (F z) σ :=
    Filter.Eventually.of_forall fun z =>
      ((phi_contDiff.continuous_iteratedDeriv n (by simp)).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hF_int : Integrable (F x) σ := by
    simpa [F] using integrable_iteratedDeriv_phi_translate σ n x
  have hF'_meas : AEStronglyMeasurable (F' x) σ :=
    ((phi_contDiff.continuous_iteratedDeriv (n + 1) (by simp)).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂σ, ∀ z ∈ Set.univ, ‖F' z y‖ ≤ C := by
    filter_upwards [] with y z hz
    change ‖iteratedDeriv (n + 1) φ (z - y)‖ ≤ C
    exact hbound _
  have hC_integrable : Integrable (fun _ : ℝ => C) σ := integrable_const C
  have h_diff : ∀ᵐ y ∂σ, ∀ z ∈ Set.univ,
      HasDerivAt (F · y) (F' z y) z := by
    filter_upwards [] with y z hz
    change HasDerivAt (fun w => iteratedDeriv n φ (w - y))
      (iteratedDeriv (n + 1) φ (z - y)) z
    have hiter : DifferentiableAt ℝ (iteratedDeriv n φ) (z - y) :=
      ((phi_contDiff.differentiable_iteratedDeriv n
        (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))).differentiableAt)
    have hcomp := hiter.hasDerivAt.comp z ((hasDerivAt_id z).sub_const y)
    convert hcomp using 1
    · rfl
    · simp [iteratedDeriv_succ]
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := σ) (s := Set.univ) (x₀ := x) (F := F) (F' := F') (bound := fun _ => C)
    univ_mem hF_meas hF_int hF'_meas h_bound hC_integrable h_diff
  simpa [F, F'] using hresult.2

theorem measureSplittingPsi_iteratedDeriv_eq_integral (σ : Measure ℝ)
    [IsFiniteMeasure σ] (n : ℕ) (x : ℝ) :
    iteratedDeriv n (measureSplittingPsi σ) x =
      ∫ y, iteratedDeriv n φ (x - y) ∂σ := by
    induction n generalizing x with
  | zero =>
      change (∫ y, (1 : ℝ) * φ (x - y) ∂σ) = ∫ y, φ (x - y) ∂σ
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hi : iteratedDeriv n (measureSplittingPsi σ) =
          fun z => ∫ y, iteratedDeriv n φ (z - y) ∂σ := funext ih
      rw [hi]
      exact (integral_iteratedDeriv_phi_hasDerivAt σ n x).deriv

theorem measureSplittingPsi_contDiff (σ : Measure ℝ) [IsFiniteMeasure σ] :
    ContDiff ℝ (WithTop.some (⊤ : ℕ∞)) (measureSplittingPsi σ) := by
  apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
  intro n hn x
  rw [show iteratedDeriv n (measureSplittingPsi σ) =
      fun z => ∫ y, iteratedDeriv n φ (z - y) ∂σ from
    funext (measureSplittingPsi_iteratedDeriv_eq_integral σ n)]
  exact (integral_iteratedDeriv_phi_hasDerivAt σ n x).differentiableAt

theorem measureSplittingPsi_integrable (σ : Measure ℝ) [IsFiniteMeasure σ]
    (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    Integrable (measureSplittingPsi σ) volume := by
  have hcompact : HasCompactSupport (measureSplittingPsi σ) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    exact (subset_tsupport _).trans (measureSplittingPsi_tsupport_subset σ hσ)
  exact (measureSplittingPsi_contDiff σ).continuous.integrable_of_hasCompactSupport hcompact

private theorem continuous_norm_le_lpNorm_top {g : ℝ → ℝ}
    (hg : Continuous g) (hmem : MemLp g ∞ volume) (x : ℝ) :
    ‖g x‖ ≤ lpNorm g ∞ volume := by
  by_contra hnot
  have hlt : lpNorm g ∞ volume < ‖g x‖ := lt_of_not_ge hnot
  let c : ℝ := (lpNorm g ∞ volume + ‖g x‖) / 2
  have hlt' : lpNorm g ∞ volume < |g x| := by simpa using hlt
  have hc₁ : lpNorm g ∞ volume < c := by
    dsimp [c]
    linarith [hlt']
  have hc₂ : c < ‖g x‖ := by
    dsimp [c]
    linarith
  have hopen : IsOpen {y : ℝ | c < ‖g y‖} := isOpen_lt continuous_const hg.norm
  have hpos : 0 < volume {y : ℝ | c < ‖g y‖} :=
    IsOpen.measure_pos hopen (μ := volume) ⟨x, hc₂⟩
  have hlow : {y : ℝ | ‖g y‖ ≤ lpNorm g ∞ volume} ∈ ae volume :=
    ae_le_lpNorm_exponent_top hmem
  have hnull : volume {y : ℝ | lpNorm g ∞ volume < ‖g y‖} = 0 := by
    have h := mem_ae_iff.mp hlow
    simpa [Set.compl_setOf, not_le, Real.norm_eq_abs] using h
  have hsub : {y : ℝ | c < ‖g y‖} ⊆
      {y : ℝ | lpNorm g ∞ volume < ‖g y‖} := by
    intro y hy
    exact lt_trans hc₁ hy
  exact hpos.ne' (measure_mono_null hsub hnull)

theorem measureSplittingPsi_iteratedDeriv_pointwise_bound (σ : Measure ℝ)
    [IsProbabilityMeasure σ] (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (measureSplittingPsi σ) x‖ ≤
      lpNorm (iteratedDeriv n φ) ∞ volume := by
  let g : ℝ → ℝ := iteratedDeriv n φ
  have hcont : Continuous g := phi_contDiff.continuous_iteratedDeriv n
    (by exact_mod_cast (ENat.natCast_lt_top n).le)
  obtain ⟨C, hC, hbound⟩ := iteratedDeriv_phi_bound n
  have hmem : MemLp g ∞ volume := by
    apply memLp_top_of_bound hcont.aestronglyMeasurable C
    filter_upwards [] with y
    simpa [g] using hbound y
  rw [measureSplittingPsi_iteratedDeriv_eq_integral σ n x]
  calc
    ‖∫ y, g (x - y) ∂σ‖ ≤ ∫ y, ‖g (x - y)‖ ∂σ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, lpNorm g ∞ volume ∂σ := by
      apply integral_mono_ae
      · exact (integrable_iteratedDeriv_phi_translate σ n x).norm
      · exact integrable_const _
      · filter_upwards [] with y
        exact continuous_norm_le_lpNorm_top hcont hmem (x - y)
    _ = lpNorm g ∞ volume := by
      rw [integral_const]
      simp [Measure.real, IsProbabilityMeasure.measure_univ]

private theorem iteratedDeriv_phi_tsupport_subset (n : ℕ) :
    tsupport (iteratedDeriv n φ) ⊆ Set.Icc (-(1 : ℝ)) 1 := by
  rw [iteratedDeriv_eq_equiv_comp]
  have hcomp : tsupport
      ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) ℝ).symm ∘
        iteratedFDeriv ℝ n φ) ⊆ tsupport (iteratedFDeriv ℝ n φ) :=
    tsupport_comp_subset (map_zero _) _
  exact hcomp.trans ((tsupport_iteratedFDeriv_subset n).trans tsupport_phi_subset)

private theorem iteratedDeriv_phi_eq_zero_of_not_mem_Icc {n : ℕ} {x : ℝ}
    (hx : x ∉ Set.Icc (-(1 : ℝ)) 1) : iteratedDeriv n φ x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx'
  exact hx (iteratedDeriv_phi_tsupport_subset n hx')

/-- The positive convolution majorant for the absolute value of a cutoff
derivative. -/
def measureSplittingDerivativeMajorant (σ : Measure ℝ) (n : ℕ) : ℝ → ℝ :=
  (fun _ : ℝ => (1 : ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, σ]
    (fun x => ‖iteratedDeriv n φ x‖)

private theorem measureSplittingDerivativeMajorant_eq_zero_of_not_mem_Icc
    (σ : Measure ℝ) [IsFiniteMeasure σ] (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (n : ℕ) {x : ℝ} (hx : x ∉ Set.Icc (-(2 : ℝ)) 2) :
    measureSplittingDerivativeMajorant σ n x = 0 := by
  unfold measureSplittingDerivativeMajorant
  apply integral_eq_zero_of_ae
  filter_upwards [Measure.support_mem_ae (μ := σ)] with y hy
  have hyI : y ∈ Set.Icc (-(1 : ℝ)) 1 := hσ hy
  have hxy : x - y ∉ Set.Icc (-(1 : ℝ)) 1 := by
    intro h
    rcases Set.mem_Icc.mp hyI with ⟨hylo, hyhi⟩
    rcases Set.mem_Icc.mp h with ⟨hlo, hhi⟩
    apply hx
    constructor <;> nlinarith
  simp [iteratedDeriv_phi_eq_zero_of_not_mem_Icc hxy]

private theorem measureSplittingDerivativeMajorant_tsupport_subset
    (σ : Measure ℝ) [IsFiniteMeasure σ] (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (n : ℕ) :
    tsupport (measureSplittingDerivativeMajorant σ n) ⊆ Set.Icc (-(2 : ℝ)) 2 := by
  apply closure_minimal
  · intro x hx
    change measureSplittingDerivativeMajorant σ n x ≠ 0 at hx
    by_contra hnot
    exact hx (measureSplittingDerivativeMajorant_eq_zero_of_not_mem_Icc σ hσ n hnot)
  · exact isClosed_Icc

private theorem measureSplittingDerivativeMajorant_continuous
    (σ : Measure ℝ) [IsFiniteMeasure σ] (n : ℕ) :
    Continuous (measureSplittingDerivativeMajorant σ n) := by
  have hg : Continuous (fun x => ‖iteratedDeriv n φ x‖) :=
    (phi_contDiff.continuous_iteratedDeriv n
      (by exact_mod_cast (ENat.natCast_lt_top n).le)).norm
  have hgb : BddAbove (Set.range fun x => ‖‖iteratedDeriv n φ x‖‖) := by
    simpa using
      hg.bddAbove_range_of_hasCompactSupport
        (iteratedDeriv_phi_hasCompactSupport n).norm
  have hfg : Integrable (fun _ : ℝ => (1 : ℝ)) σ := integrable_const 1
  simpa [measureSplittingDerivativeMajorant] using
    hgb.continuous_convolution_right_of_integrable (L := ContinuousLinearMap.mul ℝ ℝ)
      hfg hg

private theorem measureSplittingDerivativeMajorant_integrable
    (σ : Measure ℝ) [IsFiniteMeasure σ] (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (n : ℕ) : Integrable (measureSplittingDerivativeMajorant σ n) volume := by
  have hcompact : HasCompactSupport (measureSplittingDerivativeMajorant σ n) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    exact (subset_tsupport _).trans
      (measureSplittingDerivativeMajorant_tsupport_subset σ hσ n)
  exact (measureSplittingDerivativeMajorant_continuous σ n).integrable_of_hasCompactSupport
    hcompact

private theorem iteratedDeriv_psi_hasCompactSupport (σ : Measure ℝ)
    [IsFiniteMeasure σ] (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n (measureSplittingPsi σ)) := by
  induction n with
  | zero =>
      apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      exact (subset_tsupport _).trans (measureSplittingPsi_tsupport_subset σ hσ)
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

theorem measureSplittingPsi_iteratedDeriv_lpNorm_top_le (σ : Measure ℝ)
    [IsProbabilityMeasure σ] (n : ℕ) :
    lpNorm (iteratedDeriv n (measureSplittingPsi σ)) ∞ volume ≤
      lpNorm (iteratedDeriv n φ) ∞ volume := by
  let g : ℝ → ℝ := iteratedDeriv n (measureSplittingPsi σ)
  let C : ℝ := lpNorm (iteratedDeriv n φ) ∞ volume
  have hcont : Continuous g := (measureSplittingPsi_contDiff σ).continuous_iteratedDeriv n
    (by exact_mod_cast (ENat.natCast_lt_top n).le)
  have hpoint : ∀ x, ‖g x‖ ≤ C := by
    intro x
    simpa [g, C] using measureSplittingPsi_iteratedDeriv_pointwise_bound σ n x
  have hmem : MemLp g ∞ volume :=
    memLp_top_of_bound hcont.aestronglyMeasurable C (ae_of_all volume hpoint)
  rw [lpNorm_exponent_top_eq_essSup hmem]
  exact essSup_le_of_ae_le C (ae_of_all volume hpoint)
    (Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
      (Filter.Frequently.of_forall fun x => norm_nonneg (g x)))

private theorem measureSplittingDerivativeMajorant_integral (σ : Measure ℝ)
    [IsProbabilityMeasure σ] (n : ℕ) :
    ∫ x, measureSplittingDerivativeMajorant σ n x ∂volume =
      ∫ x, ‖iteratedDeriv n φ x‖ ∂volume := by
  unfold measureSplittingDerivativeMajorant
  rw [MeasureTheory.integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ)
    (integrable_const (1 : ℝ))
    ((phi_contDiff.continuous_iteratedDeriv n
      (by exact_mod_cast (ENat.natCast_lt_top n).le)).norm.integrable_of_hasCompactSupport
      (iteratedDeriv_phi_hasCompactSupport n).norm)]
  simp [Measure.real, IsProbabilityMeasure.measure_univ]

theorem measureSplittingPsi_iteratedDeriv_lpNorm_one_le (σ : Measure ℝ)
    [IsProbabilityMeasure σ]
    (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (n : ℕ) :
    lpNorm (iteratedDeriv n (measureSplittingPsi σ)) 1 volume ≤
      lpNorm (iteratedDeriv n φ) 1 volume := by
  have hpsi : AEStronglyMeasurable (iteratedDeriv n (measureSplittingPsi σ)) volume :=
    ((measureSplittingPsi_contDiff σ).continuous_iteratedDeriv n
      (by exact_mod_cast (ENat.natCast_lt_top n).le)).aestronglyMeasurable
  have hphi : AEStronglyMeasurable (iteratedDeriv n φ) volume :=
    (phi_contDiff.continuous_iteratedDeriv n
      (by exact_mod_cast (ENat.natCast_lt_top n).le)).aestronglyMeasurable
  rw [lpNorm_one_eq_integral_norm hpsi, lpNorm_one_eq_integral_norm hphi]
  calc
    ∫ x, ‖iteratedDeriv n (measureSplittingPsi σ) x‖ ∂volume ≤
        ∫ x, measureSplittingDerivativeMajorant σ n x ∂volume := by
      apply integral_mono
      · exact (measureSplittingPsi_contDiff σ).continuous_iteratedDeriv n
          (by exact_mod_cast (ENat.natCast_lt_top n).le) |>.integrable_of_hasCompactSupport
          (iteratedDeriv_psi_hasCompactSupport σ hσ n) |>.norm
      · exact measureSplittingDerivativeMajorant_integrable σ hσ n
      · intro x
        change ‖iteratedDeriv n (measureSplittingPsi σ) x‖ ≤
          measureSplittingDerivativeMajorant σ n x
        rw [measureSplittingPsi_iteratedDeriv_eq_integral σ n x]
        unfold measureSplittingDerivativeMajorant
        simp only [convolution_def, ContinuousLinearMap.mul_apply', one_mul]
        exact norm_integral_le_integral_norm
          (fun y : ℝ => iteratedDeriv n φ (x - y))
    _ = ∫ x, ‖iteratedDeriv n φ x‖ ∂volume :=
      measureSplittingDerivativeMajorant_integral σ n

theorem measureSplittingNu_mass (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    measureSplittingNu σ Set.univ = 0 := by
  unfold measureSplittingNu
  rw [sub_apply, Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
    withDensityᵥ_apply (measureSplittingPsi_integrable σ hσ) MeasurableSet.univ]
  simp [Measure.real, measureSplittingPsi_integral σ]

private theorem measureSplittingDensityVariation_mass (σ : Measure ℝ)
    [IsProbabilityMeasure σ]
    (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    (volume.withDensityᵥ (measureSplittingPsi σ)).variation Set.univ = 1 := by
  have hψint : Integrable (measureSplittingPsi σ) volume :=
    measureSplittingPsi_integrable σ hσ
  have hψnonneg : ∀ x, 0 ≤ measureSplittingPsi σ x :=
    measureSplittingPsi_nonneg σ
  have hden : (fun x => ‖measureSplittingPsi σ x‖ₑ) =
      fun x => ENNReal.ofReal (measureSplittingPsi σ x) := by
    funext x
    exact Real.enorm_eq_ofReal (hψnonneg x)
  rw [Measure.variation_withDensityᵥ hψint, hden,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hψint (ae_of_all volume hψnonneg),
    measureSplittingPsi_integral σ]
  norm_num

theorem measureSplittingNu_totalVariation_le (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    (measureSplittingNu σ).totalVariation.real Set.univ ≤ 2 := by
  have hvariation : (measureSplittingNu σ).variation ≤
      σ + (volume.withDensityᵥ (measureSplittingPsi σ)).variation := by
    simpa [measureSplittingNu, Measure.variation_toSignedMeasure] using
      (VectorMeasure.variation_sub_le (μ := σ.toSignedMeasure)
        (ν := volume.withDensityᵥ (measureSplittingPsi σ)))
  have h_univ := (Measure.le_iff.mp hvariation) Set.univ MeasurableSet.univ
  have hfinite : (σ + (volume.withDensityᵥ (measureSplittingPsi σ)).variation)
      Set.univ ≠ (⊤ : ℝ≥0∞) := by
    rw [Measure.add_apply, IsProbabilityMeasure.measure_univ,
      measureSplittingDensityVariation_mass σ hσ]
    norm_num
  have hreal := ENNReal.toReal_mono hfinite h_univ
  have hreal' : (measureSplittingNu σ).variation.real Set.univ ≤
      (σ + (volume.withDensityᵥ (measureSplittingPsi σ)).variation).real Set.univ := by
    simpa [Measure.real] using hreal
  have hsum : (σ + (volume.withDensityᵥ (measureSplittingPsi σ)).variation).real
      Set.univ = 2 := by
    rw [measureReal_add_apply
      (by simp [IsProbabilityMeasure.measure_univ])
      (by rw [measureSplittingDensityVariation_mass σ hσ]; norm_num)]
    simp [Measure.real, IsProbabilityMeasure.measure_univ,
      measureSplittingDensityVariation_mass σ hσ]
    <;> norm_num
  have hbound := hreal'.trans_eq hsum
  simpa [SignedMeasure.totalVariation_eq_variation] using hbound

private theorem measureSplittingPhase_add (u y ξ : ℝ) :
    Complex.exp (↑(-2 * Real.pi * (u + y) * ξ) * Complex.I) =
      Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) *
        Complex.exp (↑(-2 * Real.pi * u * ξ) * Complex.I) := by
  have harg : (↑(-2 * Real.pi * (u + y) * ξ) : ℂ) * Complex.I =
      ↑(-2 * Real.pi * y * ξ) * Complex.I + ↑(-2 * Real.pi * u * ξ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add]

private theorem measureSplittingPsiFourier_eq (σ : Measure ℝ)
    [IsFiniteMeasure σ] (ξ : ℝ) :
    measureSplittingPsiFourier σ ξ =
      measureSplittingFourier σ ξ * jswFourier (fun x => (φ x : ℂ)) ξ := by
  let phase : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I)
  have hphi : Integrable (fun x : ℝ => (φ x : ℂ)) volume :=
    (phi_contDiff.continuous.integrable_of_hasCompactSupport phi_hasCompactSupport).ofReal
  have hphiC : Continuous (fun x : ℝ => (φ x : ℂ)) :=
    Complex.continuous_ofReal.comp phi_contDiff.continuous
  have hprod : Integrable
      (fun z : ℝ × ℝ => (φ (z.1 - z.2) : ℂ)) (volume.prod σ) := by
    apply (integrable_prod_iff'
      ((hphiC.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)).mpr
    constructor
    · filter_upwards with y
      exact hphi.comp_sub_right y
    · have he : (fun y : ℝ => ∫ x : ℝ, ‖(φ (x - y) : ℂ)‖ ∂volume) =
          fun _ => ∫ x, ‖(φ x : ℂ)‖ ∂volume := by
        funext y
        exact integral_sub_right_eq_self (fun x : ℝ => ‖(φ x : ℂ)‖) y
      change Integrable (fun y : ℝ => ∫ x : ℝ, ‖(φ (x-y) : ℂ)‖ ∂volume) σ
      rw [he]
      exact integrable_const _
  have hjoint : Integrable
      (fun z : ℝ × ℝ => phase z.1 * (φ (z.1 - z.2) : ℂ)) (volume.prod σ) := by
    have hphase : Continuous phase := by
      dsimp [phase]
      fun_prop
    apply hprod.norm.mono'
    · exact (hphase.comp continuous_fst).mul
        (hphiC.comp (continuous_fst.sub continuous_snd)) |>.aestronglyMeasurable
    · filter_upwards with z
      simp [phase, Complex.norm_exp]
  have hFourier : jswFourier (fun x => (φ x : ℂ)) ξ =
      ∫ u : ℝ, phase u * (φ u : ℂ) ∂volume := by
    rw [jswFourier_eq_integral]
  have hswap :
      (∫ x : ℝ, phase x * (∫ y, (φ (x-y) : ℂ) ∂σ) ∂volume) =
        ∫ y : ℝ, ∫ x : ℝ, phase x * (φ (x-y) : ℂ) ∂volume ∂σ := by
    calc
      _ = ∫ x : ℝ, ∫ y : ℝ, phase x * (φ (x-y) : ℂ) ∂σ ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        exact (integral_const_mul (phase x)
          (fun y : ℝ => (φ (x-y) : ℂ))).symm
      _ = ∫ y : ℝ, ∫ x : ℝ, phase x * (φ (x-y) : ℂ) ∂volume ∂σ := by
        simpa using integral_integral_swap hjoint
  have hshift (y : ℝ) :
      (∫ x : ℝ, phase x * (φ (x-y) : ℂ) ∂volume) =
        phase y * jswFourier (fun x => (φ x : ℂ)) ξ := by
    calc
      _ = ∫ u : ℝ, phase (u+y) * (φ u : ℂ) ∂volume := by
        simpa only [sub_add_cancel] using
          (integral_sub_right_eq_self
            (fun u : ℝ => phase (u+y) * (φ u : ℂ)) y)
      _ = ∫ u : ℝ, phase y * (phase u * (φ u : ℂ)) ∂volume := by
        apply integral_congr_ae
        filter_upwards with u
        simp only [phase, measureSplittingPhase_add]
        ring
      _ = phase y * ∫ u : ℝ, phase u * (φ u : ℂ) ∂volume :=
        integral_const_mul _ _
      _ = phase y * jswFourier (fun x => (φ x : ℂ)) ξ := by rw [hFourier]
  rw [measureSplittingPsiFourier, jswFourier_eq_integral]
  change (∫ x : ℝ, phase x * (measureSplittingPsi σ x : ℂ) ∂volume) = _
  calc
    _ = ∫ x : ℝ, phase x * (∫ y, (φ (x-y) : ℂ) ∂σ) ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      rw [show (measureSplittingPsi σ x : ℂ) = ∫ y, (φ (x-y) : ℂ) ∂σ by
        calc
          (measureSplittingPsi σ x : ℂ) =
              ((∫ y, φ (x-y) ∂σ : ℝ)) := by
                simpa [iteratedDeriv_zero] using
                  (measureSplittingPsi_iteratedDeriv_eq_integral σ 0 x)
          _ = ∫ y, (φ (x-y) : ℂ) ∂σ :=
            (integral_complex_ofReal (f := fun y : ℝ => φ (x-y)) (μ := σ)).symm]
    _ = ∫ y : ℝ, ∫ x : ℝ, phase x * (φ (x-y) : ℂ) ∂volume ∂σ := hswap
    _ = ∫ y : ℝ, phase y * jswFourier (fun x => (φ x : ℂ)) ξ ∂σ := by
      apply integral_congr_ae
      filter_upwards with y
      exact hshift y
    _ = measureSplittingFourier σ ξ * jswFourier (fun x => (φ x : ℂ)) ξ := by
      rw [measureSplittingFourier, integral_mul_const]

private theorem measureSplittingDensity_eq_toSignedMeasure (σ : Measure ℝ)
    [IsProbabilityMeasure σ]
    (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    ∃ hμ : IsFiniteMeasure
        (volume.withDensity (fun x => ENNReal.ofReal (measureSplittingPsi σ x))),
      volume.withDensityᵥ (measureSplittingPsi σ) =
        @Measure.toSignedMeasure ℝ _
          (volume.withDensity (fun x => ENNReal.ofReal (measureSplittingPsi σ x))) hμ := by
  let d : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (measureSplittingPsi σ x)
  have hψint : Integrable (measureSplittingPsi σ) volume :=
    measureSplittingPsi_integrable σ hσ
  have hψnonneg : ∀ x, 0 ≤ measureSplittingPsi σ x :=
    measureSplittingPsi_nonneg σ
  have hdmeas : AEMeasurable d volume := by
    exact (ENNReal.continuous_ofReal.comp
      (measureSplittingPsi_contDiff σ).continuous).aemeasurable
  have hlin : (∫⁻ x, d x ∂volume) =
      ENNReal.ofReal (∫ x, measureSplittingPsi σ x ∂volume) := by
    simpa [d] using (ofReal_integral_eq_lintegral_ofReal hψint
      (ae_of_all volume hψnonneg)).symm
  have hfinite : (∫⁻ x, d x ∂volume) ≠ (⊤ : ℝ≥0∞) := by
    rw [hlin, measureSplittingPsi_integral σ]
    norm_num
  have hpoint : (fun x => (d x).toReal) =ᵐ[volume] measureSplittingPsi σ := by
    filter_upwards [] with x
    simp [d, ENNReal.toReal_ofReal (hψnonneg x)]
  let hμ : IsFiniteMeasure (volume.withDensity d) := isFiniteMeasure_withDensity hfinite
  refine ⟨hμ, ?_⟩
  letI : IsFiniteMeasure (volume.withDensity d) := hμ
  calc
    volume.withDensityᵥ (measureSplittingPsi σ) =
        volume.withDensityᵥ (fun x => (d x).toReal) :=
      (WithDensityᵥEq.congr_ae hpoint).symm
    _ = (volume.withDensity d).toSignedMeasure := withDensityᵥ_toReal hdmeas hfinite

private theorem measureSplittingDensityFourier_eq (σ : Measure ℝ)
    [IsProbabilityMeasure σ]
    (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (ξ : ℝ) :
    (∫ᵛ x, Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I)
      ∂<•(volume.withDensityᵥ (measureSplittingPsi σ))) = measureSplittingPsiFourier σ ξ := by
  let d : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (measureSplittingPsi σ x)
  let phase : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I)
  have hψnonneg : ∀ x, 0 ≤ measureSplittingPsi σ x := measureSplittingPsi_nonneg σ
  have hdmeas : Measurable d :=
    ENNReal.continuous_ofReal.comp (measureSplittingPsi_contDiff σ).continuous |>.measurable
  have htop : ∀ᵐ x ∂volume, d x < (⊤ : ℝ≥0∞) := by
    filter_upwards [] with x
    exact ENNReal.ofReal_lt_top
  obtain ⟨hμ, hrho⟩ := measureSplittingDensity_eq_toSignedMeasure σ hσ
  letI : IsFiniteMeasure (volume.withDensity d) := hμ
  rw [hrho,
    VectorMeasure.integral_toSignedMeasure,
    integral_withDensity_eq_integral_toReal_smul hdmeas htop]
  rw [measureSplittingPsiFourier, jswFourier_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [d, phase, ENNReal.toReal_ofReal (hψnonneg x), smul_eq_mul, mul_comm]

theorem measureSplittingNuFourier_eq (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (ξ : ℝ) :
    measureSplittingNuFourier σ ξ =
      (1 - jswFourier (fun x => (φ x : ℂ)) ξ) * measureSplittingFourier σ ξ := by
  let phase : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I)
  have hphaseCont : Continuous phase := by
    dsimp [phase]
    fun_prop
  have hphaseBound : ∀ x, ‖phase x‖ ≤ 1 := by
    intro x
    simp [phase, Complex.norm_exp]
  haveI : IsFiniteMeasure (σ.toSignedMeasure).variation := by
    rw [Measure.variation_toSignedMeasure]
    infer_instance
  have hσint : (σ.toSignedMeasure).Integrable phase :=
    Integrable.of_bound hphaseCont.aestronglyMeasurable 1
      (ae_of_all _ hphaseBound)
  haveI : IsFiniteMeasure (volume.withDensityᵥ (measureSplittingPsi σ)).variation := by
    refine ⟨?_⟩
    rw [measureSplittingDensityVariation_mass σ hσ]
    norm_num
  have hρint : (volume.withDensityᵥ (measureSplittingPsi σ)).Integrable phase :=
    Integrable.of_bound hphaseCont.aestronglyMeasurable 1
      (ae_of_all _ hphaseBound)
  calc
    measureSplittingNuFourier σ ξ =
        (∫ᵛ x, phase x ∂<•(σ.toSignedMeasure)) -
          (∫ᵛ x, phase x ∂<•(volume.withDensityᵥ (measureSplittingPsi σ))) := by
      rw [measureSplittingNuFourier, measureSplittingNu,
        VectorMeasure.integral_sub_vectorMeasure hσint hρint]
    _ = measureSplittingFourier σ ξ - measureSplittingPsiFourier σ ξ := by
      rw [VectorMeasure.integral_toSignedMeasure,
        measureSplittingDensityFourier_eq σ hσ ξ, measureSplittingFourier]
    _ = (1 - jswFourier (fun x => (φ x : ℂ)) ξ) * measureSplittingFourier σ ξ := by
      rw [measureSplittingPsiFourier_eq σ ξ]
      ring

private theorem measureSplittingPhase_sub_one_bound (x ξ : ℝ) :
    ‖Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) - 1‖ ≤
      2 * Real.pi * |x * ξ| := by
  let t : ℝ := 2 * Real.pi * (x * ξ)
  have harg : (↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I =
      Complex.I * ↑(-t) := by
    dsimp [t]
    push_cast
    ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  calc
    ‖2 * Real.sin (-t / 2)‖ ≤ |t| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        2 * |Real.sin (-t / 2)| ≤ 2 * |-t / 2| :=
          mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
        _ = |t| := by rw [abs_div, abs_neg]; ring
    _ = 2 * Real.pi * |x * ξ| := by
      dsimp [t]
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

private theorem measureSplittingPhiFourier_small (ξ : ℝ) :
    ‖1 - jswFourier (fun x => (φ x : ℂ)) ξ‖ ≤ 2 * Real.pi * |ξ| := by
  let phase : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I)
  have hphiR : Integrable φ volume :=
    phi_contDiff.continuous.integrable_of_hasCompactSupport phi_hasCompactSupport
  have hphiC : Integrable (fun x : ℝ => (φ x : ℂ)) volume := hphiR.ofReal
  have hphiC_cont : Continuous (fun x : ℝ => (φ x : ℂ)) :=
    Complex.continuous_ofReal.comp phi_contDiff.continuous
  have hphaseCont : Continuous phase := by
    dsimp [phase]
    fun_prop
  have hphaseBound : ∀ x, ‖phase x‖ ≤ 1 := by
    intro x
    simp [phase, Complex.norm_exp]
  have hphasePhi : Integrable (fun x : ℝ => phase x * (φ x : ℂ)) volume := by
    apply hphiC.norm.mono'
    · exact (hphaseCont.mul hphiC_cont).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hphaseBound x) (norm_nonneg (φ x : ℂ))
  have hdiffBound : ∀ x, ‖1 - phase x‖ ≤ 2 := by
    intro x
    calc
      ‖1 - phase x‖ ≤ ‖(1 : ℂ)‖ + ‖phase x‖ := norm_sub_le _ _
      _ ≤ 2 := by
        calc
          ‖(1 : ℂ)‖ + ‖phase x‖ ≤ 1 + 1 := add_le_add (by simp) (hphaseBound x)
          _ = 2 := by norm_num
  have hdiffPhi : Integrable (fun x : ℝ => (1 - phase x) * (φ x : ℂ)) volume := by
    apply (hphiC.norm.const_mul 2).mono'
    · exact ((continuous_const.sub hphaseCont).mul hphiC_cont).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hdiffBound x) (norm_nonneg (φ x : ℂ))
  have hmass : ∫ x, (φ x : ℂ) ∂volume = 1 := by
    rw [integral_complex_ofReal, integral_phi]
    norm_num
  have hidentity :
      1 - jswFourier (fun x => (φ x : ℂ)) ξ =
        ∫ x, (1 - phase x) * (φ x : ℂ) ∂volume := by
    calc
      _ = (∫ x, (φ x : ℂ) ∂volume) -
          ∫ x, phase x * (φ x : ℂ) ∂volume := by
        rw [hmass, jswFourier_eq_integral]
      _ = ∫ x, (φ x : ℂ) - phase x * (φ x : ℂ) ∂volume :=
        (integral_sub hphiC hphasePhi).symm
      _ = ∫ x, (1 - phase x) * (φ x : ℂ) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
  rw [hidentity]
  calc
    ‖∫ x, (1 - phase x) * (φ x : ℂ) ∂volume‖ ≤
        ∫ x, ‖(1 - phase x) * (φ x : ℂ)‖ ∂volume := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (2 * Real.pi * |ξ|) * φ x ∂volume := by
      apply integral_mono
      · exact hdiffPhi.norm
      · exact hphiR.const_mul (2 * Real.pi * |ξ|)
      · intro x
        change ‖(1 - phase x) * (φ x : ℂ)‖ ≤
          (2 * Real.pi * |ξ|) * φ x
        have hnormφ : ‖(φ x : ℂ)‖ = φ x := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (phi_nonneg x)]
        have hpoint : ‖(1 - phase x) * (φ x : ℂ)‖ = ‖1 - phase x‖ * φ x := by
          rw [norm_mul, hnormφ]
        rw [hpoint]
        by_cases hzero : φ x = 0
        · simp [hzero]
        · have hxI : x ∈ Set.Icc (-(1 : ℝ)) 1 :=
            tsupport_phi_subset (subset_tsupport _ hzero)
          have hxabs : |x| ≤ 1 := by
            apply abs_le.mpr
            exact ⟨by linarith [hxI.1], hxI.2⟩
          have hprod : |x * ξ| ≤ |ξ| := by
            rw [abs_mul]
            nlinarith [abs_nonneg ξ]
          have hphaseDiff : ‖1 - phase x‖ ≤ 2 * Real.pi * |x * ξ| := by
            rw [show 1 - phase x = -(phase x - 1) by ring, norm_neg]
            exact measureSplittingPhase_sub_one_bound x ξ
          calc
            ‖1 - phase x‖ * φ x ≤ (2 * Real.pi * |x * ξ|) * φ x :=
              mul_le_mul_of_nonneg_right hphaseDiff (phi_nonneg x)
            _ ≤ (2 * Real.pi * |ξ|) * φ x := by
              apply mul_le_mul_of_nonneg_right _ (phi_nonneg x)
              exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 2 * Real.pi * |ξ| := by
      rw [integral_const_mul, integral_phi]
      ring

private theorem measureSplittingPhiFourier_norm_le (ξ : ℝ) :
    ‖jswFourier (fun x => (φ x : ℂ)) ξ‖ ≤ 1 := by
  let phase : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I)
  have hphiR : Integrable φ volume :=
    phi_contDiff.continuous.integrable_of_hasCompactSupport phi_hasCompactSupport
  have hphiC : Integrable (fun x : ℝ => (φ x : ℂ)) volume := hphiR.ofReal
  have hphiC_cont : Continuous (fun x : ℝ => (φ x : ℂ)) :=
    Complex.continuous_ofReal.comp phi_contDiff.continuous
  have hphaseCont : Continuous phase := by
    dsimp [phase]
    fun_prop
  have hphasePhi : Integrable (fun x : ℝ => phase x * (φ x : ℂ)) volume := by
    apply hphiC.norm.mono'
    · exact (hphaseCont.mul hphiC_cont).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul]
      simp [phase, Complex.norm_exp]
  rw [jswFourier_eq_integral]
  calc
    ‖∫ x, phase x * (φ x : ℂ) ∂volume‖ ≤
        ∫ x, ‖phase x * (φ x : ℂ)‖ ∂volume := norm_integral_le_integral_norm _
    _ = 1 := by
      have hintegrand : (fun x : ℝ => ‖phase x * (φ x : ℂ)‖) = fun x => φ x := by
        funext x
        simp [phase, Complex.norm_exp, Real.norm_eq_abs, abs_of_nonneg (phi_nonneg x)]
      rw [hintegrand, integral_phi]

private theorem measureSplittingFourier_norm_le (σ : Measure ℝ)
    [IsProbabilityMeasure σ] (ξ : ℝ) : ‖measureSplittingFourier σ ξ‖ ≤ 1 := by
  let phase : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I)
  rw [measureSplittingFourier]
  calc
    ‖∫ x, phase x ∂σ‖ ≤ ∫ x, ‖phase x‖ ∂σ := norm_integral_le_integral_norm _
    _ = 1 := by
      simp [phase, Complex.norm_exp, IsProbabilityMeasure.measure_univ]

theorem measureSplittingNuFourier_decay_bound (σ : Measure ℝ)
    [IsProbabilityMeasure σ]
    (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (β : ℝ) (hβ : 0 < β) (D : ℝ)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β))
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖measureSplittingNuFourier σ ξ‖ ≤
      (2 * Real.pi + 2 * |D|) * min |ξ| (|ξ| ^ (-β)) := by
  have habs : 0 < |ξ| := abs_pos.mpr hξ
  have hpow : 0 < |ξ| ^ (-β) := Real.rpow_pos_of_pos habs (-β)
  have hσnorm : ‖measureSplittingFourier σ ξ‖ ≤ 1 :=
    measureSplittingFourier_norm_le σ ξ
  have hφnorm : ‖jswFourier (fun x => (φ x : ℂ)) ξ‖ ≤ 1 :=
    measureSplittingPhiFourier_norm_le ξ
  have hsmall : ‖1 - jswFourier (fun x => (φ x : ℂ)) ξ‖ ≤
      2 * Real.pi * |ξ| := measureSplittingPhiFourier_small ξ
  have hlarge : ‖1 - jswFourier (fun x => (φ x : ℂ)) ξ‖ ≤ 2 := by
    calc
      ‖1 - jswFourier (fun x => (φ x : ℂ)) ξ‖ ≤
          ‖(1 : ℂ)‖ + ‖jswFourier (fun x => (φ x : ℂ)) ξ‖ := norm_sub_le _ _
      _ ≤ 2 := by
        calc
          ‖(1 : ℂ)‖ + ‖jswFourier (fun x => (φ x : ℂ)) ξ‖ ≤ 1 + 1 :=
            add_le_add (by simp) hφnorm
          _ = 2 := by norm_num
  have hσdecay := hdecay ξ hξ
  have hDnonneg : 0 ≤ D := by
    have hprod : 0 ≤ D * |ξ| ^ (-β) := le_trans (norm_nonneg _) hσdecay
    by_contra hD
    have hDneg : D < 0 := lt_of_not_ge hD
    exact (not_lt_of_ge hprod) (mul_neg_of_neg_of_pos hDneg hpow)
  rw [measureSplittingNuFourier_eq σ hσ ξ]
  rw [norm_mul]
  by_cases hlow : |ξ| ≤ 1
  · have hpowone : 1 ≤ |ξ| ^ (-β) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos habs hlow (neg_nonpos.mpr hβ.le)
    have hmin : min |ξ| (|ξ| ^ (-β)) = |ξ| := min_eq_left (le_trans hlow hpowone)
    rw [hmin]
    calc
      ‖1 - jswFourier (fun x => (φ x : ℂ)) ξ‖ *
          ‖measureSplittingFourier σ ξ‖ ≤
          (2 * Real.pi * |ξ|) * 1 := by
        exact mul_le_mul hsmall hσnorm (norm_nonneg _) (by positivity)
      _ = 2 * Real.pi * |ξ| := by ring
      _ ≤ (2 * Real.pi + 2 * |D|) * |ξ| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg ξ)
        nlinarith [abs_nonneg D, Real.pi_pos]
  · have hξgt : 1 < |ξ| := lt_of_not_ge hlow
    have hpowone : |ξ| ^ (-β) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hξgt.le (neg_nonpos.mpr hβ.le)
    have hmin : min |ξ| (|ξ| ^ (-β)) = |ξ| ^ (-β) :=
      min_eq_right (le_trans hpowone hξgt.le)
    rw [hmin]
    calc
      ‖1 - jswFourier (fun x => (φ x : ℂ)) ξ‖ *
          ‖measureSplittingFourier σ ξ‖ ≤
          2 * ‖measureSplittingFourier σ ξ‖ :=
            mul_le_mul_of_nonneg_right hlarge (norm_nonneg _)
      _ ≤ 2 * (D * |ξ| ^ (-β)) :=
            mul_le_mul_of_nonneg_left hσdecay (by norm_num)
      _ = (2 * D) * |ξ| ^ (-β) := by ring
      _ ≤ (2 * Real.pi + 2 * |D|) * |ξ| ^ (-β) := by
        apply mul_le_mul_of_nonneg_right _ hpow.le
        rw [abs_of_nonneg hDnonneg]
        nlinarith [Real.pi_pos]

theorem measureSplittingSupport_map_neg (σ : Measure ℝ)
    (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) :
    (Measure.map Neg.neg σ).support ⊆ Set.Icc (-(1 : ℝ)) 1 := by
  intro x hx
  have hxopen : ∀ U, x ∈ U → IsOpen U → 0 < (Measure.map Neg.neg σ) U := by
    rw [Measure.support_eq_forall_isOpen] at hx
    exact hx
  have hxpre : -x ∈ σ.support := by
    rw [Measure.support_eq_forall_isOpen]
    intro U hU hUopen
    have hpreopen : IsOpen (Neg.neg ⁻¹' U) := hUopen.preimage continuous_neg
    have hxpre : x ∈ Neg.neg ⁻¹' U := by simpa using hU
    have hpos := hxopen (Neg.neg ⁻¹' U) hxpre hpreopen
    rw [Measure.map_apply (by fun_prop) hpreopen.measurableSet] at hpos
    simpa using hpos
  have hbound := hσ hxpre
  rcases Set.mem_Icc.mp hbound with ⟨hlo, hhi⟩
  constructor <;> linarith

theorem measureSplittingFourier_map_neg (σ : Measure ℝ) (ξ : ℝ) :
    measureSplittingFourier (Measure.map Neg.neg σ) ξ =
      measureSplittingFourier σ (-ξ) := by
  rw [measureSplittingFourier, measureSplittingFourier]
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  congr 1
  congr 1
  ring_nf

/-- The conclusions of the cancellation and positivity splitting for one
probability measure, with the exact constants and norms from `lj:measure-splitting`. -/
structure MeasureSplittingBounds (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (β D : ℝ) : Prop where
  psi_nonneg : ∀ x, 0 ≤ measureSplittingPsi σ x
  psi_integral : ∫ x, measureSplittingPsi σ x ∂volume = 1
  psi_tsupport : tsupport (measureSplittingPsi σ) ⊆ Set.Icc (-(2 : ℝ)) 2
  psi_iteratedDeriv_lpNorm_one : ∀ n,
    lpNorm (iteratedDeriv n (measureSplittingPsi σ)) 1 volume ≤
      lpNorm (iteratedDeriv n φ) 1 volume
  psi_iteratedDeriv_lpNorm_top : ∀ n,
    lpNorm (iteratedDeriv n (measureSplittingPsi σ)) ∞ volume ≤
      lpNorm (iteratedDeriv n φ) ∞ volume
  nu_mass : measureSplittingNu σ Set.univ = 0
  nu_totalVariation : (measureSplittingNu σ).totalVariation.real Set.univ ≤ 2
  nu_fourier_identity : ∀ ξ,
    measureSplittingNuFourier σ ξ =
      (1 - jswFourier (fun x => (φ x : ℂ)) ξ) * measureSplittingFourier σ ξ
  nu_fourier_decay : ∀ {ξ}, ξ ≠ 0 →
    ‖measureSplittingNuFourier σ ξ‖ ≤
      (2 * Real.pi + 2 * |D|) * min |ξ| (|ξ| ^ (-β))

private theorem measureSplittingBounds_of_hypotheses (σ : Measure ℝ)
    [IsProbabilityMeasure σ] (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (β : ℝ) (hβ : 0 < β) (D : ℝ)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β)) :
    MeasureSplittingBounds σ β D where
  psi_nonneg := measureSplittingPsi_nonneg σ
  psi_integral := measureSplittingPsi_integral σ
  psi_tsupport := measureSplittingPsi_tsupport_subset σ hσ
  psi_iteratedDeriv_lpNorm_one := measureSplittingPsi_iteratedDeriv_lpNorm_one_le σ hσ
  psi_iteratedDeriv_lpNorm_top := measureSplittingPsi_iteratedDeriv_lpNorm_top_le σ
  nu_mass := measureSplittingNu_mass σ hσ
  nu_totalVariation := measureSplittingNu_totalVariation_le σ hσ
  nu_fourier_identity := measureSplittingNuFourier_eq σ hσ
  nu_fourier_decay := fun {ξ} hξ =>
    measureSplittingNuFourier_decay_bound σ hσ β hβ D hdecay hξ

/-- Cancellation and positivity splitting for a compactly supported
probability measure. The second component states the same bounds for the
reflected probability measure. -/
theorem measureSplitting (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hσ : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (β : ℝ) (hβ : 0 < β) (D : ℝ)
    (hdecay : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σ ξ‖ ≤ D * |ξ| ^ (-β)) :
    MeasureSplittingBounds σ β D ∧
      MeasureSplittingBounds (Measure.map Neg.neg σ) β D := by
  let σref : Measure ℝ := Measure.map Neg.neg σ
  have hσref : σref.support ⊆ Set.Icc (-(1 : ℝ)) 1 := by
    change (Measure.map Neg.neg σ).support ⊆ Set.Icc (-(1 : ℝ)) 1
    exact measureSplittingSupport_map_neg σ hσ
  have hdecayref : ∀ ξ, ξ ≠ 0 →
      ‖measureSplittingFourier σref ξ‖ ≤ D * |ξ| ^ (-β) := by
    intro ξ hξ
    rw [show σref = Measure.map Neg.neg σ by rfl,
      measureSplittingFourier_map_neg]
    simpa [abs_neg] using hdecay (-ξ) (by simpa using hξ)
  have hmain : MeasureSplittingBounds σ β D :=
    measureSplittingBounds_of_hypotheses σ hσ β hβ D hdecay
  have href : MeasureSplittingBounds σref β D := by
    haveI : IsProbabilityMeasure σref := inferInstance
    exact measureSplittingBounds_of_hypotheses σref hσref β hβ D hdecayref
  exact ⟨hmain, by simpa only [σref] using href⟩

end

end FractionalPrimes.Literature.JSW

end

#print axioms FractionalPrimes.Literature.JSW.measureSplittingNuFourier_decay_bound
#print axioms FractionalPrimes.Literature.JSW.measureSplitting
