module
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import FractionalPrimes.Literature.Reciprocal.TwistedMobiusRectangle
public import FractionalPrimes.Literature.LongArithmetic.ReciprocalSeriesTransfer
public import FractionalPrimes.Literature.Uniformity.LogAbsorption
@[expose] public section

noncomputable section

namespace FractionalPrimes.Literature.Reciprocal

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.LongArithmetic
open Set
open scoped Interval

/-- An analytic-on-a-closed-set hypothesis supplies the open neighbourhood
and `C¹` data required by `reciprocalSeriesTransfer`. The neighbourhood is
the open locus on which the same function is analytic. -/
theorem analyticOnNhd_open_contDiffOn_adapter
    {f : ℂ → ℂ} {K : Set ℂ} (hf : AnalyticOnNhd ℂ f K) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℂ 1 f U := by
  let U : Set ℂ := {z | AnalyticAt ℂ f z}
  refine ⟨U, ?_, ?_, ?_⟩
  · exact isOpen_analyticAt ℂ f
  · intro z hz
    exact hf z hz
  · exact (show AnalyticOnNhd ℂ f U from fun z hz => hz).contDiffOn_of_completeSpace

/-- The explicit threshold from `lu:elementary-growth`, packaged as a lower
bound on the variable `w` rather than on `log w`. -/
noncomputable def prefixLogAbsorptionThreshold (a b K : ℝ) : ℝ :=
  Real.exp ((2 / a) * Real.log (K * logAbsorptionM a b))

private theorem prefix_log_absorption_of_threshold {a b K w : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hK : 1 ≤ K)
    (hw : prefixLogAbsorptionThreshold a b K ≤ w) :
    K * (Real.log w) ^ b ≤ w ^ a := by
  have hM : 1 ≤ logAbsorptionM a b := one_le_logAbsorptionM
  have hKM : 1 ≤ K * logAbsorptionM a b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hM)]
  have hlogKM : 0 ≤ Real.log (K * logAbsorptionM a b) :=
    Real.log_nonneg hKM
  have hthreshold_nonneg :
      0 ≤ (2 / a) * Real.log (K * logAbsorptionM a b) := by positivity
  have hw0 : 1 ≤ prefixLogAbsorptionThreshold a b K := by
    rw [prefixLogAbsorptionThreshold]
    exact Real.one_le_exp_iff.mpr hthreshold_nonneg
  have hw1 : 1 ≤ w := hw0.trans hw
  have hlarge :
      (2 / a) * Real.log (K * logAbsorptionM a b) ≤ Real.log w := by
    calc
      (2 / a) * Real.log (K * logAbsorptionM a b) =
          Real.log (prefixLogAbsorptionThreshold a b K) := by
        rw [prefixLogAbsorptionThreshold, Real.log_exp]
      _ ≤ Real.log w := Real.log_le_log (by positivity) hw
  exact log_absorption_bound ha hb hK hw1 hlarge

private theorem prefix_scaled_linear_absorption {c K t w scale : ℝ}
    (hscale : 0 ≤ scale) (hcK : c ≤ scale * K) (ht : 0 ≤ t)
    (hKt : K * t ≤ w) : c * t ≤ scale * w := by
  calc
    c * t ≤ (scale * K) * t := mul_le_mul_of_nonneg_right hcK ht
    _ = scale * (K * t) := by ring
    _ ≤ scale * w := mul_le_mul_of_nonneg_left hKt hscale

private theorem prefix_scaled_power_absorption {c K θ w scale : ℝ}
    (hscale : 0 ≤ scale) (hcK : c ≤ scale * K) (hW : 1 ≤ w)
    (hlogW : 0 ≤ Real.log w)
    (hKlog : K * Real.log w ≤ w ^ (1 - θ)) :
    c * w ^ θ * Real.log w ≤ scale * w := by
  have hpow : 0 ≤ w ^ θ := Real.rpow_nonneg (by linarith : 0 ≤ w) _
  calc
    c * w ^ θ * Real.log w = c * (w ^ θ * Real.log w) := by ring
    _ ≤ (scale * K) * (w ^ θ * Real.log w) :=
      mul_le_mul_of_nonneg_right hcK (mul_nonneg hpow hlogW)
    _ = scale * w ^ θ * (K * Real.log w) := by ring
    _ ≤ scale * w ^ θ * w ^ (1 - θ) :=
      mul_le_mul_of_nonneg_left hKlog (by positivity)
    _ = scale * (w ^ θ * w ^ (1 - θ)) := by ring
    _ = scale * w ^ (θ + (1 - θ)) := by
      rw [← Real.rpow_add (by linarith : 0 < w)]
    _ = scale * w := by rw [show θ + (1 - θ) = 1 by ring, Real.rpow_one]

private theorem prefix_scaled_rpow_absorption {c K θ w scale : ℝ}
    (hscale : 0 ≤ scale) (hcK : c ≤ scale * K) (hW : 1 ≤ w)
    (hK : K ≤ w ^ (1 - θ)) : c * w ^ θ ≤ scale * w := by
  have hpow : 0 ≤ w ^ θ := Real.rpow_nonneg (by linarith : 0 ≤ w) _
  calc
    c * w ^ θ ≤ (scale * K) * w ^ θ :=
      mul_le_mul_of_nonneg_right hcK hpow
    _ = scale * (K * w ^ θ) := by ring
    _ ≤ scale * (w ^ (1 - θ) * w ^ θ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK hpow) hscale
    _ = scale * w := by
      rw [mul_comm (w ^ (1 - θ)) (w ^ θ)]
      rw [← Real.rpow_add (by linarith : 0 < w)]
      rw [show θ + (1 - θ) = 1 by ring, Real.rpow_one]

/-- A convenient exact choice of absorption constant: multiplying the maximum
by the positive scale dominates `c`. -/
private theorem prefix_le_scale_mul_max_ratio {c scale : ℝ}
    (hscale : 0 < scale) : c ≤ scale * max 1 (c / scale) := by
  calc
    c = scale * (c / scale) := by field_simp
    _ ≤ scale * max 1 (c / scale) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hscale.le

private theorem prefix_absorption_eventually {a b K : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hK : 1 ≤ K) :
    ∀ᶠ w : ℝ in Filter.atTop, K * (Real.log w) ^ b ≤ w ^ a := by
  filter_upwards [Filter.eventually_ge_atTop
      (prefixLogAbsorptionThreshold a b K)] with w hw
  exact prefix_log_absorption_of_threshold ha hb hK hw

/-- The four explicit large-`w` inequalities chosen in the proof of
`lrc:twisted-prefix`, together with the two baseline conditions needed by the
rectangle theorem. -/
private def prefixGrowthConditions (α A B D w : ℝ) : Prop :=
  Real.exp 8 ≤ w ∧
  α * w ≥ 2 ∧
  α * w ≥ (D + 2) * Real.log w ∧
  twistedMobiusRectangleErrorExponent A B (Real.exp w) +
      Real.log (1 + (A + 2) * w) + (D + 2) * Real.log w ≤
    α * w / (8 * Real.log w) ∧
  twistedMobiusRectangleErrorExponent A B (Real.exp w) +
      2 * (D + 2) * Real.log w ≤ 2 * (A + 2) * w ∧
  Real.log 3 + (2 * D + 5) * Real.log w ≤ (A + 2) * w ∧
  w ^ B ≤ Real.exp w

set_option maxHeartbeats 0

/-- Every fixed-parameter threshold condition used by `lrc:twisted-prefix`
holds eventually. The proof is a direct application of the project's
explicit `lu:elementary-growth` absorption bound. -/
private theorem prefix_growth_eventually {α A B D : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) :
    ∀ᶠ w : ℝ in Filter.atTop, prefixGrowthConditions α A B D w := by
  let θ := FractionalPrimes.Literature.Analytic.explicitLogarithmTheta
  let d := D + 2
  let c := (A + B + 6) ^ θ
  have hθpos : 0 < θ := by
    dsimp [θ, FractionalPrimes.Literature.Analytic.explicitLogarithmTheta]
    apply div_pos
    · exact Real.log_pos (by norm_num)
    · exact Real.log_pos (by norm_num)
  have hθlt : θ < 1 := by
    dsimp [θ, FractionalPrimes.Literature.Analytic.explicitLogarithmTheta]
    apply (div_lt_one (Real.log_pos (by norm_num))).2
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hdpos : 0 < d := by dsimp [d]; linarith
  have hAplus : 0 < A + 2 := by linarith
  have hcpos : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos (by linarith) _
  have hlogA : 0 < Real.log (A + 3) := Real.log_pos (by linarith)
  have hC0pos : 0 < 12 + Real.log (A + 3) := by positivity
  have hC1pos : 0 < 13 + d := by positivity
  have hC2pos : 0 < 600 * c := by positivity
  have hC3pos : 0 < 12 + 2 * d := by positivity
  have hC4pos : 0 < (2 * D + 5) := by linarith
  have hscaleα : 0 < α / 24 := by positivity
  have hscaleA : 0 < 2 * (A + 2) / 3 := by positivity
  have hscaleT : 0 < (A + 2) / 2 := by positivity
  let K1 := max 1 (d / α)
  let Kx := max 1 B
  let K20 := max 1 ((12 + Real.log (A + 3)) / (α / 24))
  let K21 := max 1 ((13 + d) / (α / 24))
  let K22 := max 1 ((600 * c) / (α / 24))
  let K31 := max 1 ((12 + 2 * d) / (2 * (A + 2) / 3))
  let K32 := max 1 ((600 * c) / (2 * (A + 2) / 3))
  let K4 := max 1 ((2 * D + 5) / ((A + 2) / 2))
  have hK1 : 1 ≤ K1 := le_max_left _ _
  have hKx : 1 ≤ Kx := le_max_left _ _
  have hK20 : 1 ≤ K20 := le_max_left _ _
  have hK21 : 1 ≤ K21 := le_max_left _ _
  have hK22 : 1 ≤ K22 := le_max_left _ _
  have hK31 : 1 ≤ K31 := le_max_left _ _
  have hK32 : 1 ≤ K32 := le_max_left _ _
  have hK4 : 1 ≤ K4 := le_max_left _ _
  have hK1c : d ≤ α * K1 := by
    dsimp [K1]
    calc
      d = α * (d / α) := by field_simp
      _ ≤ α * max 1 (d / α) := mul_le_mul_of_nonneg_left (le_max_right _ _) hα.le
  have hK20c : 12 + Real.log (A + 3) ≤ (α / 24) * K20 :=
    prefix_le_scale_mul_max_ratio (c := 12 + Real.log (A + 3)) hscaleα
  have hK21c : 13 + d ≤ (α / 24) * K21 :=
    prefix_le_scale_mul_max_ratio (c := 13 + d) hscaleα
  have hK22c : 600 * c ≤ (α / 24) * K22 :=
    prefix_le_scale_mul_max_ratio (c := 600 * c) hscaleα
  have hK31c : 12 + 2 * d ≤ (2 * (A + 2) / 3) * K31 :=
    prefix_le_scale_mul_max_ratio (c := 12 + 2 * d) hscaleA
  have hK32c : 600 * c ≤ (2 * (A + 2) / 3) * K32 :=
    prefix_le_scale_mul_max_ratio (c := 600 * c) hscaleA
  have hK4c : 2 * D + 5 ≤ ((A + 2) / 2) * K4 :=
    prefix_le_scale_mul_max_ratio (c := 2 * D + 5) hscaleT
  have hK1abs := prefix_absorption_eventually
    (a := 1) (b := 1) (K := K1) (by norm_num) (by norm_num) hK1
  have hKxabs := prefix_absorption_eventually
    (a := 1) (b := 1) (K := Kx) (by norm_num) (by norm_num) hKx
  have hK20abs := prefix_absorption_eventually
    (a := 1) (b := 1) (K := K20) (by norm_num) (by norm_num) hK20
  have hK21abs := prefix_absorption_eventually
    (a := 1) (b := 2) (K := K21) (by norm_num) (by norm_num) hK21
  have hK22abs := prefix_absorption_eventually
    (a := 1 - θ) (b := 1) (K := K22) (by linarith) (by norm_num) hK22
  have hK31abs := prefix_absorption_eventually
    (a := 1) (b := 1) (K := K31) (by norm_num) (by norm_num) hK31
  have hK32abs := prefix_absorption_eventually
    (a := 1 - θ) (b := 0) (K := K32) (by linarith) (by norm_num) hK32
  have hK4abs := prefix_absorption_eventually
    (a := 1) (b := 1) (K := K4) (by norm_num) (by norm_num) hK4
  have htheta := hθpos
  have htheta' := hθlt
  have hscaleα0 : 0 ≤ α / 24 := hscaleα.le
  have hscaleA0 : 0 ≤ 2 * (A + 2) / 3 := hscaleA.le
  have hscaleT0 : 0 ≤ (A + 2) / 2 := hscaleT.le
  filter_upwards
    [Filter.eventually_ge_atTop (Real.exp 8),
     Filter.eventually_ge_atTop (2 / α),
     Filter.eventually_ge_atTop (18 / (A + 2)),
     Filter.eventually_ge_atTop (2 * Real.log 3 / (A + 2)),
     hK1abs, hKxabs, hK20abs, hK21abs, hK22abs,
     hK31abs, hK32abs, hK4abs] with w hw8 hw2 hw18 hw4 hK1w hKxw
      hK20w hK21w hK22w hK31w hK32w hK4w
  have hwone : 1 ≤ w := by
    have : 1 ≤ Real.exp 8 := by
      linarith [Real.add_one_le_exp (8 : ℝ)]
    exact this.trans hw8
  have hwpos : 0 < w := by linarith
  have hlogw : 0 ≤ Real.log w := Real.log_nonneg hwone
  have hlogwpos : 0 < Real.log w := by
    have hbig : 1 < Real.exp 8 := by
      linarith [Real.add_one_le_exp (8 : ℝ)]
    have : 1 < w := hbig.trans_le hw8
    exact Real.log_pos this
  have hcond1 : α * w ≥ d * Real.log w := by
    have h := prefix_scaled_linear_absorption (c := d) (K := K1)
      (t := Real.log w) (w := w) (scale := α) hα.le hK1c hlogw
      (by simpa using hK1w)
    linarith
  have hE : twistedMobiusRectangleErrorExponent A B (Real.exp w) =
      12 + 12 * Real.log w + 600 * c * w ^ θ := by
    simp [twistedMobiusRectangleErrorExponent, c, θ,
      FractionalPrimes.Literature.Analytic.explicitLogarithmTheta,
      Real.log_exp]
  have hlog_arg : Real.log (1 + (A + 2) * w) ≤
      Real.log (A + 3) + Real.log w := by
    have hleft : 0 < 1 + (A + 2) * w := by positivity
    have hright : 0 < (A + 3) * w := by positivity
    have hle : 1 + (A + 2) * w ≤ (A + 3) * w := by nlinarith
    calc
      Real.log (1 + (A + 2) * w) ≤ Real.log ((A + 3) * w) :=
        Real.log_le_log hleft hle
      _ = Real.log (A + 3) + Real.log w := by
        rw [Real.log_mul (by positivity) (by linarith)]
  have h20w : (12 + Real.log (A + 3)) * Real.log w ≤
      (α / 24) * w :=
    prefix_scaled_linear_absorption (c := 12 + Real.log (A + 3))
      (K := K20) (t := Real.log w) (w := w) (scale := α / 24)
      hscaleα0 hK20c hlogw (by simpa using hK20w)
  have h21w : (13 + d) * (Real.log w) ^ 2 ≤ (α / 24) * w :=
    prefix_scaled_linear_absorption (c := 13 + d) (K := K21)
      (t := (Real.log w) ^ 2) (w := w) (scale := α / 24)
      hscaleα0 hK21c (sq_nonneg _) (by simpa using hK21w)
  have h22w : 600 * c * w ^ θ * Real.log w ≤ (α / 24) * w :=
    prefix_scaled_power_absorption (c := 600 * c) (K := K22)
      (θ := θ) (w := w) (scale := α / 24) hscaleα0 hK22c hwone hlogw
      (by simpa using hK22w)
  have hsecond_mul :
      (12 + 12 * Real.log w + 600 * c * w ^ θ +
        Real.log (A + 3) + Real.log w + d * Real.log w) *
          (8 * Real.log w) ≤ α * w := by
    calc
      _ = 8 * ((12 + Real.log (A + 3)) * Real.log w) +
          8 * ((13 + d) * (Real.log w) ^ 2) +
          8 * (600 * c * w ^ θ * Real.log w) := by ring
      _ ≤ 8 * ((α / 24) * w) + 8 * ((α / 24) * w) +
          8 * ((α / 24) * w) := by
        gcongr
      _ = α * w := by ring
  have hsecond :
      twistedMobiusRectangleErrorExponent A B (Real.exp w) +
          Real.log (1 + (A + 2) * w) + d * Real.log w ≤
        α * w / (8 * Real.log w) := by
    rw [hE]
    apply (le_div_iff₀ (by positivity : 0 < 8 * Real.log w)).2
    calc
      (12 + 12 * Real.log w + 600 * c * w ^ θ +
          Real.log (1 + (A + 2) * w) + d * Real.log w) *
          (8 * Real.log w) ≤
        (12 + 12 * Real.log w + 600 * c * w ^ θ +
          (Real.log (A + 3) + Real.log w) + d * Real.log w) *
          (8 * Real.log w) := by
            exact mul_le_mul_of_nonneg_right (by gcongr) (by positivity)
      _ ≤ α * w := by simpa [add_assoc] using hsecond_mul
  have hconst3 : 12 ≤ (2 * (A + 2) / 3) * w := by
    have hmul : 18 ≤ (A + 2) * w :=
      by simpa [mul_comm] using (div_le_iff₀ hAplus).mp hw18
    calc
      12 = (2 / 3 : ℝ) * 18 := by norm_num
      _ ≤ (2 / 3 : ℝ) * ((A + 2) * w) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = (2 * (A + 2) / 3) * w := by ring
  have h31w : (12 + 2 * d) * Real.log w ≤
      (2 * (A + 2) / 3) * w :=
    prefix_scaled_linear_absorption (c := 12 + 2 * d) (K := K31)
      (t := Real.log w) (w := w) (scale := 2 * (A + 2) / 3)
      hscaleA0 hK31c hlogw (by simpa using hK31w)
  have h32w : 600 * c * w ^ θ ≤ (2 * (A + 2) / 3) * w :=
    prefix_scaled_rpow_absorption (c := 600 * c) (K := K32)
      (θ := θ) (w := w) (scale := 2 * (A + 2) / 3)
      hscaleA0 hK32c hwone (by simpa using hK32w)
  have hthird :
      twistedMobiusRectangleErrorExponent A B (Real.exp w) +
          2 * d * Real.log w ≤ 2 * (A + 2) * w := by
    rw [hE]
    nlinarith [hconst3, h31w, h32w]
  have hconst4 : Real.log 3 ≤ ((A + 2) / 2) * w := by
    have hmul : 2 * Real.log 3 ≤ (A + 2) * w :=
      by simpa [mul_comm] using (div_le_iff₀ hAplus).mp hw4
    calc
      Real.log 3 = (1 / 2 : ℝ) * (2 * Real.log 3) := by ring
      _ ≤ (1 / 2 : ℝ) * ((A + 2) * w) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = ((A + 2) / 2) * w := by ring
  have h4w : (2 * D + 5) * Real.log w ≤ ((A + 2) / 2) * w :=
    prefix_scaled_linear_absorption (c := 2 * D + 5) (K := K4)
      (t := Real.log w) (w := w) (scale := (A + 2) / 2)
      hscaleT0 hK4c hlogw (by simpa using hK4w)
  have hfourth : Real.log 3 + (2 * D + 5) * Real.log w ≤
      (A + 2) * w := by nlinarith [hconst4, h4w]
  have hXpow : w ^ B ≤ Real.exp w := by
    have hBlog : B * Real.log w ≤ w := by
      have hBmax : B ≤ Kx := le_max_right _ _
      simpa using prefix_scaled_linear_absorption (c := B) (K := Kx)
        (t := Real.log w) (w := w) (scale := 1) (by norm_num)
        (by simpa using hBmax) hlogw
        (by simpa using hKxw)
    rw [Real.rpow_def_of_pos hwpos B]
    exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hBlog)
  refine ⟨hw8, ?_, ?_, ?_, ?_, ?_, hXpow⟩
  · have hmul := (div_le_iff₀ hα).mp hw2
    simpa [mul_comm] using hmul
  · simpa [d] using hcond1
  · simpa [d] using hsecond
  · simpa [d] using hthird
  · exact hfourth

private theorem exists_prefix_growth_threshold {α A B D : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) :
    ∃ W₀ : ℝ, Real.exp 8 ≤ W₀ ∧
      ∀ w : ℝ, W₀ ≤ w → prefixGrowthConditions α A B D w := by
  obtain ⟨W, hW⟩ := Filter.eventually_atTop.1
    (prefix_growth_eventually hα hα1 hA hB hD)
  refine ⟨max W (Real.exp 8), le_max_right _ _, ?_⟩
  intro w hw
  exact hW w (le_trans (le_max_left _ _) hw)

private theorem prefix_perronCoefficient_eq {q : ℕ} [NeZero q]
    (r : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
    perronCoefficient (twistedMobiusRectangleCoefficient r χ t) =
      twistedMobiusRectangleCoefficient r χ t := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [perronCoefficient, twistedMobiusRectangleCoefficient,
      shiftedCharacterMobiusCoefficient, mobiusMultiplierCoefficient]
  · simp [perronCoefficient, hn]

private theorem prefix_three_le_exp_two : (3 : ℝ) ≤ Real.exp 2 := by
  have h := Real.exp_one_gt_two
  have hsq : 4 ≤ (Real.exp 1) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp 1 - 2)]
  have hexp : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [← pow_two]
  rw [hexp]
  nlinarith

/-- Uniform cumulative Möbius cancellation at polynomial height, exactly the
approved `lrc:twisted-prefix` statement. -/
theorem twistedMobiusPrefix {α A B D : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧
      ∀ {q : ℕ} [NeZero q] (hZFR : fixedHalfPlaneProperty)
        {X y : ℝ} (hX₀ : X₀ ≤ X) (hXα : X ^ α ≤ y) (hyX : y ≤ 2 * X)
        (r : ℕ) (hr : 1 ≤ r) (hrX : (r : ℝ) ≤ X)
        (hq : 1 ≤ q) (hqX : (q : ℝ) ≤ (Real.log X) ^ B)
        (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : |t| ≤ X ^ A),
        ‖cesaroPerronSharpSum (twistedMobiusRectangleCoefficient r χ t) y‖ ≤
          (2 + 384 * Real.exp 1) * y * (Real.log X) ^ (-(D + 2)) := by
  obtain ⟨W₀, hW₀, hW₀all⟩ :=
    exists_prefix_growth_threshold hα hα1 hA hB hD
  let X₀ : ℝ := Real.exp W₀
  have hW₀ge1 : 1 ≤ W₀ := by
    have h1 : 1 ≤ Real.exp 8 := by
      linarith [Real.add_one_le_exp (8 : ℝ)]
    exact h1.trans hW₀
  have hW₀ge2 : 2 ≤ W₀ := by
    have h2 : 2 ≤ Real.exp 8 := by
      linarith [Real.add_one_le_exp (8 : ℝ)]
    exact h2.trans hW₀
  have hX₀ge3 : 3 ≤ X₀ := by
    dsimp [X₀]
    calc
      3 ≤ Real.exp 2 := prefix_three_le_exp_two
      _ ≤ Real.exp W₀ := Real.exp_le_exp.mpr hW₀ge2
  refine ⟨X₀, hX₀ge3, ?_⟩
  intro q inst hZFR X y hX₀ hXα hyX r hr hrX hq hqX χ t ht
  let w : ℝ := Real.log X
  have hXpos : 0 < X := by
    exact (Real.exp_pos W₀).trans_le (by simpa [X₀] using hX₀)
  have hwW₀ : W₀ ≤ w := by
    rw [Real.le_log_iff_exp_le hXpos]
    simpa [X₀, w] using hX₀
  have hgrowth := hW₀all w hwW₀
  rcases hgrowth with ⟨hw8, hαw2, hαwd, hcond2, hcond3, hcond4, hwB⟩
  have hwpos : 0 < w := by
    have : 0 < Real.exp 8 := Real.exp_pos 8
    dsimp [w]
    exact (this.trans_le hw8)
  have hwone : 1 ≤ w := by
    have h1 : 1 ≤ Real.exp 8 := by
      linarith [Real.add_one_le_exp (8 : ℝ)]
    exact h1.trans hw8
  have hlogw8 : 8 ≤ Real.log w :=
    (Real.le_log_iff_exp_le hwpos).2 hw8
  have hlogwpos : 0 < Real.log w := by linarith
  have hXlogPow : (Real.log X) ^ B ≤ X := by
    simpa [w, Real.exp_log hXpos] using hwB
  have hXαexp : X ^ α = Real.exp (α * w) := by
    rw [Real.rpow_def_of_pos hXpos α]
    simp [w, mul_comm]
  have hXαge3 : 3 ≤ X ^ α := by
    rw [hXαexp]
    exact prefix_three_le_exp_two.trans (Real.exp_le_exp.mpr hαw2)
  have hy3 : 3 ≤ y := hXαge3.trans hXα
  have hypos : 0 < y := by linarith
  have hyExp2 : Real.exp 2 ≤ y := by
    calc
      Real.exp 2 ≤ Real.exp (α * w) := Real.exp_le_exp.mpr hαw2
      _ = X ^ α := hXαexp.symm
      _ ≤ y := hXα
  have hlogy2 : 2 ≤ Real.log y :=
    (Real.le_log_iff_exp_le hypos).2 hyExp2
  have hTexp : X ^ (A + 2) = Real.exp ((A + 2) * w) := by
    rw [Real.rpow_def_of_pos hXpos]
    simp [w, mul_comm]
  have hTge2 : 2 ≤ X ^ (A + 2) := by
    rw [hTexp]
    have harg : 1 ≤ (A + 2) * w := by
      have hA2 : 2 ≤ A + 2 := by linarith
      nlinarith [hwone]
    exact (le_of_lt Real.exp_one_gt_two).trans
      (Real.exp_le_exp.mpr harg)
  let δ : ℝ := twistedMobiusRectangleDelta X
  have hδdef : δ = twistedMobiusRectangleDelta X := rfl
  have hδeq : δ = 1 / (8 * Real.log w) := by
    simp [δ, twistedMobiusRectangleDelta, w]
  have hδpos : 0 < δ := by
    rw [hδeq]
    positivity
  have hδhi : δ ≤ 1 / 2 := by
    rw [hδeq]
    have h64 : (64 : ℝ) ≤ 8 * Real.log w := by nlinarith [hlogw8]
    calc
      1 / (8 * Real.log w) ≤ 1 / 64 :=
        one_div_le_one_div_of_le (by norm_num) h64
      _ ≤ 1 / 2 := by norm_num
  let d : ℝ := D + 2
  have hdpos : 0 < d := by dsimp [d]; linarith
  have hwdexp : w ^ d = Real.exp (Real.log w * d) :=
    Real.rpow_def_of_pos hwpos d
  have hwdpos : 0 < w ^ d := Real.rpow_pos_of_pos hwpos d
  have hwdge1 : 1 ≤ w ^ d := by
    rw [hwdexp]
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hwdleXα : w ^ d ≤ X ^ α := by
    rw [hwdexp, hXαexp]
    exact Real.exp_le_exp.mpr (by nlinarith [hαwd])
  have hwdleY : w ^ d ≤ y := hwdleXα.trans hXα
  let Δ : ℝ := y * w ^ (-d)
  have hfactor : w ^ (-d) ≤ 1 := by
    rw [Real.rpow_neg hwpos.le d]
    exact inv_le_one_of_one_le₀ hwdge1
  have hΔeq : Δ = y / w ^ d := by
    simp [Δ, Real.rpow_neg hwpos.le d, div_eq_mul_inv]
  have hΔpos : 0 < Δ := by
    dsimp [Δ]
    positivity
  have hΔle : Δ ≤ y := by
    dsimp [Δ]
    exact mul_le_of_le_one_right (by linarith) hfactor
  have hΔge1 : 1 ≤ Δ := by
    rw [hΔeq]
    exact (le_div_iff₀ hwdpos).2 (by simpa using hwdleY)
  let T : ℝ := X ^ (A + 2)
  have hTge : 2 ≤ T := by simpa [T] using hTge2
  let E : ℝ := twistedMobiusRectangleErrorExponent A B X
  let M : ℝ := Real.exp E
  have hM : 0 ≤ M := by positivity
  have hEeq : E = 12 + 12 * Real.log w +
      600 * (A + B + 6) ^
        FractionalPrimes.Literature.Analytic.explicitLogarithmTheta *
          w ^ FractionalPrimes.Literature.Analytic.explicitLogarithmTheta := by
    simp [E, twistedMobiusRectangleErrorExponent, w]
  have hrectangle := twistedMobiusRectangle hZFR hA hB hw8 hXlogPow
    r hr hrX hq hqX χ t ht
  rcases hrectangle with ⟨hFseriesRect, hFanalytic, hFboundRect, hcoeff⟩
  let F : ℂ → ℂ := twistedMobiusRectangleExtension r χ t
  obtain ⟨U, hUopen, hUregion, hFcont⟩ :=
    analyticOnNhd_open_contDiffOn_adapter (f := F) hFanalytic
  have hcontourRegion :
      ([[1 - δ, 1 + 1 / Real.log y]] ×ℂ [[-T, T]]) ⊆
        twistedMobiusRectangleRegion X A := by
    intro s hs
    have hleft : 1 - δ ≤ 1 + 1 / Real.log y := by
      have : 0 < 1 / Real.log y := one_div_pos.mpr (Real.log_pos (by linarith))
      linarith
    have hTpos : 0 ≤ T := by linarith
    have hscomplex := Complex.mem_reProdIm.mp hs
    have hsRe : s.re ∈ Set.Icc (1 - δ) (1 + 1 / Real.log y) := by
      simpa only [Set.uIcc_of_le hleft] using hscomplex.1
    have hsIm : s.im ∈ Set.Icc (-T) T := by
      simpa only [Set.uIcc_of_le (by linarith : -T ≤ T)] using hscomplex.2
    have hs' : s.re ∈ Set.Icc (1 - δ) (1 + 1 / Real.log y) ∧
        s.im ∈ Set.Icc (-T) T := ⟨hsRe, hsIm⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [δ] using hs'.1.1
    · have hrecip : 1 / Real.log y ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) hlogy2
      have : s.re ≤ 1 + 1 / Real.log y := hs'.1.2
      calc
        s.re ≤ 1 + 1 / Real.log y := this
        _ ≤ 3 / 2 := by linarith
    · have him : -T ≤ s.im ∧ s.im ≤ T := hs'.2
      simpa [abs_le] using him
  have hUrect :
      ([[1 - δ, 1 + 1 / Real.log y]] ×ℂ [[-T, T]]) ⊆ U :=
    hcontourRegion.trans hUregion
  have ha : ∀ n, 0 < n →
      ‖twistedMobiusRectangleCoefficient r χ t n‖ ≤ 1 := by
    intro n hn
    exact (hcoeff n)
  have hFseries : ∀ s : ℂ, 1 < s.re →
      F s = perronDirichletSeries (twistedMobiusRectangleCoefficient r χ t) s := by
    intro s hs
    simpa [F, perronDirichletSeries, prefix_perronCoefficient_eq] using
      hFseriesRect s hs
  have hFbound : ∀ s ∈
      ([[1 - δ, 1 + 1 / Real.log y]] ×ℂ [[-T, T]]), ‖F s‖ ≤ M := by
    intro s hs
    have hregion := hcontourRegion hs
    simpa [F, M, E] using hFboundRect s hregion
  have htransfer := reciprocalSeriesTransfer
    (a := twistedMobiusRectangleCoefficient r χ t) ha
    (x := y) (Δ := Δ) (T := T) (δ := δ) (M := M)
    hy3 hΔpos hΔle hTge hδpos hδhi hM
    hUopen hUrect hFcont hFseries hFbound
  let S : ℝ := y * w ^ (-d)
  have hΔS : Δ = S := rfl
  have hTexpT : T = Real.exp ((A + 2) * w) := by
    simpa [T] using hTexp
  have hTlog : 1 + Real.log T ≤ 1 + (A + 2) * w := by
    rw [hTexpT, Real.log_exp]
  have hlog2le1 : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ Real.log (Real.exp 1) :=
        Real.log_le_log (by norm_num) (le_of_lt Real.exp_one_gt_two)
      _ = 1 := Real.log_exp 1
  have hlogyUpper : 1 + Real.log y ≤ 3 * w := by
    have hlogyLe : Real.log y ≤ w + Real.log 2 := by
      have hlog : Real.log y ≤ Real.log (2 * X) := Real.log_le_log hypos (by nlinarith [hyX])
      have hmul : Real.log (2 * X) = Real.log 2 + Real.log X := by
        rw [Real.log_mul (by norm_num) hXpos.ne']
      simpa [w, hmul, add_comm, add_left_comm, add_assoc] using hlog
    nlinarith [hwone, hlog2le1]
  have hXeq : X = Real.exp w := by
    dsimp [w]
    exact (Real.exp_log hXpos).symm
  have hEw : E = twistedMobiusRectangleErrorExponent A B (Real.exp w) := by
    simp [E, hXeq]
  have hcond2E : E + Real.log (1 + (A + 2) * w) + d * Real.log w ≤
      α * w / (8 * Real.log w) := by
    have h := hcond2
    rw [← hEw] at h
    simpa [d] using h
  have hcond2δ : E + Real.log (1 + (A + 2) * w) + d * Real.log w ≤
      δ * α * w := by
    rw [hδeq]
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcond2E
  have hlogyLower : α * w ≤ Real.log y := by
    apply (Real.le_log_iff_exp_le hypos).2
    rw [← hXαexp]
    exact hXα
  have hfirstPow : y ^ (1 - δ) ≤ y * Real.exp (-(δ * α * w)) := by
    rw [Real.rpow_def_of_pos hypos]
    rw [← Real.exp_log hypos, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hlogyLower hδpos.le
    rw [Real.log_exp]
    nlinarith
  have hfirstExpBound :
      Real.exp (E + Real.log (1 + (A + 2) * w) + d * Real.log w -
        δ * α * w) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [hcond2δ]
  have hargpos : 0 < 1 + (A + 2) * w := by positivity
  have hargexp : 1 + (A + 2) * w =
      Real.exp (Real.log (1 + (A + 2) * w)) :=
    (Real.exp_log hargpos).symm
  have hargFactor :
      (Real.exp E * (1 + (A + 2) * w) * Real.exp (-(δ * α * w))) * w ^ d =
        (Real.exp E * Real.exp (Real.log (1 + (A + 2) * w)) *
          Real.exp (-(δ * α * w))) * Real.exp (Real.log w * d) := by
    calc
      _ = (Real.exp E * Real.exp (Real.log (1 + (A + 2) * w)) *
          Real.exp (-(δ * α * w))) * w ^ d :=
        congrArg (fun z : ℝ => Real.exp E * z * Real.exp (-(δ * α * w)) * w ^ d)
          hargexp
      _ = _ := congrArg
        (fun z : ℝ => (Real.exp E * Real.exp (Real.log (1 + (A + 2) * w)) *
          Real.exp (-(δ * α * w))) * z) hwdexp
  have hfirstFactEq :
      M * (1 + (A + 2) * w) * Real.exp (-(δ * α * w)) * w ^ d =
        Real.exp (E + Real.log (1 + (A + 2) * w) + d * Real.log w -
          δ * α * w) := by
    calc
      _ = (Real.exp E * (1 + (A + 2) * w) *
          Real.exp (-(δ * α * w))) * w ^ d := by
            rw [show M = Real.exp E from rfl]
      _ = (Real.exp E * Real.exp (Real.log (1 + (A + 2) * w)) *
          Real.exp (-(δ * α * w))) * Real.exp (Real.log w * d) := by
            exact hargFactor
      _ = (Real.exp E * Real.exp (Real.log (1 + (A + 2) * w))) *
          (Real.exp (Real.log w * d) * Real.exp (-(δ * α * w))) := by ring
      _ = Real.exp (E + Real.log (1 + (A + 2) * w)) *
          Real.exp (Real.log w * d - δ * α * w) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1 <;> ring
      _ = Real.exp (E + Real.log (1 + (A + 2) * w) +
          (Real.log w * d - δ * α * w)) := by rw [← Real.exp_add]
      _ = _ := by congr 1 <;> ring
  have hfirstFactor :
      M * (1 + (A + 2) * w) * Real.exp (-(δ * α * w)) ≤ w ^ (-d) := by
    rw [Real.rpow_neg hwpos.le d]
    rw [← one_div]
    apply (le_div_iff₀ hwdpos).2
    exact le_trans (le_of_eq hfirstFactEq) hfirstExpBound
  have hlogTnonneg : 0 ≤ 1 + Real.log T := by
    have hTone : 1 ≤ T := by linarith
    have : 0 ≤ Real.log T := Real.log_nonneg hTone
    linarith
  have hfirst : M * y ^ (1 - δ) * (1 + Real.log T) ≤ S := by
    calc
      M * y ^ (1 - δ) * (1 + Real.log T) ≤
          M * (y * Real.exp (-(δ * α * w))) * (1 + Real.log T) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfirstPow hM) hlogTnonneg
      _ ≤ M * (y * Real.exp (-(δ * α * w))) *
          (1 + (A + 2) * w) := by
        apply mul_le_mul_of_nonneg_left hTlog
        positivity
      _ = y * (M * (1 + (A + 2) * w) * Real.exp (-(δ * α * w))) := by ring
      _ ≤ S := by
        dsimp [S]
        exact mul_le_mul_of_nonneg_left hfirstFactor hypos.le
  have hcond3E : E + 2 * d * Real.log w ≤ 2 * (A + 2) * w := by
    have h := hcond3
    rw [← hEw] at h
    simpa [d] using h
  have hT2exp : T ^ 2 = Real.exp (2 * (A + 2) * w) := by
    rw [hTexpT, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hwd2 : w ^ (2 * d) = (w ^ d) ^ 2 := by
    calc
      w ^ (2 * d) = w ^ (d + d) := by congr 1 <;> ring
      _ = w ^ d * w ^ d := Real.rpow_add hwpos d d
      _ = (w ^ d) ^ 2 := by rw [pow_two]
  have hMwd2exp : M * (w ^ d) ^ 2 = Real.exp (E + 2 * d * Real.log w) := by
    rw [show M = Real.exp E from rfl, hwdexp, pow_two]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsecondFactor : M * (w ^ d) ^ 2 / T ^ 2 ≤ 1 := by
    rw [hMwd2exp, hT2exp]
    apply (div_le_one (by positivity : 0 < Real.exp (2 * (A + 2) * w))).2
    exact Real.exp_le_exp.mpr (by nlinarith [hcond3E])
  have hsecondEq :
      M * y ^ 2 / (Δ * T ^ 2) = S * (M * (w ^ d) ^ 2 / T ^ 2) := by
    dsimp [S]
    rw [hΔeq, Real.rpow_neg hwpos.le d]
    field_simp [ne_of_gt hypos, ne_of_gt hwdpos, ne_of_gt (by linarith : 0 < T)]
    <;> ring
  have hsecond : M * y ^ 2 / (Δ * T ^ 2) ≤ S := by
    rw [hsecondEq]
    exact mul_le_of_le_one_right (by positivity) hsecondFactor
  have hcond4d : Real.log 3 + (2 * d + 1) * Real.log w ≤
      (A + 2) * w := by
    have hdeq : 2 * d + 1 = 2 * D + 5 := by dsimp [d]; ring
    simpa [hdeq, mul_comm] using hcond4
  have hthreeExpEq : 3 * w * (w ^ d) ^ 2 =
      Real.exp (Real.log 3 + (2 * d + 1) * Real.log w) := by
    have h3exp : 3 = Real.exp (Real.log 3) :=
      (Real.exp_log (by norm_num : (0 : ℝ) < 3)).symm
    have hwexp : w = Real.exp (Real.log w) := (Real.exp_log hwpos).symm
    have hwdExp : w ^ d = Real.exp (Real.log w * d) := hwdexp
    calc
      3 * w * (w ^ d) ^ 2 =
          Real.exp (Real.log 3) * Real.exp (Real.log w) *
            (Real.exp (Real.log w * d)) ^ 2 := by
              calc
                _ = Real.exp (Real.log 3) * w * (w ^ d) ^ 2 :=
                  congrArg (fun z : ℝ => z * w * (w ^ d) ^ 2) h3exp
                _ = Real.exp (Real.log 3) * Real.exp (Real.log w) * (w ^ d) ^ 2 :=
                  congrArg (fun z : ℝ => Real.exp (Real.log 3) * z * (w ^ d) ^ 2) hwexp
                _ = _ := by rw [hwdExp]
      _ = Real.exp (Real.log 3 + (2 * d + 1) * Real.log w) := by
        calc
          _ = Real.exp (Real.log 3 + Real.log w) *
              (Real.exp (Real.log w * d) * Real.exp (Real.log w * d)) := by
                rw [← Real.exp_add, pow_two]
          _ = Real.exp (Real.log 3 + Real.log w) *
              Real.exp (2 * (Real.log w * d)) := by
                congr 1
                rw [← Real.exp_add]
                congr 1
                ring
          _ = Real.exp (Real.log 3 + Real.log w + 2 * (Real.log w * d)) := by
                rw [← Real.exp_add]
          _ = _ := by congr 1 <;> ring
  have hthreeLeT : 3 * w * (w ^ d) ^ 2 ≤ T := by
    rw [hthreeExpEq, hTexpT]
    exact Real.exp_le_exp.mpr hcond4d
  have hthirdFactor : (1 + Real.log y) * (w ^ d) ^ 2 / T ≤ 1 := by
    apply (div_le_one (by linarith : 0 < T)).2
    calc
      (1 + Real.log y) * (w ^ d) ^ 2 ≤ 3 * w * (w ^ d) ^ 2 :=
        mul_le_mul_of_nonneg_right hlogyUpper (sq_nonneg (w ^ d))
      _ ≤ T := hthreeLeT
  have hthirdEq :
      (1 + Real.log y) * y ^ 2 / (Δ * T) =
        S * ((1 + Real.log y) * (w ^ d) ^ 2 / T) := by
    dsimp [S]
    rw [hΔeq, Real.rpow_neg hwpos.le d]
    field_simp [ne_of_gt hypos, ne_of_gt hwdpos, ne_of_gt (by linarith : 0 < T)]
    <;> ring
  have hthird : (1 + Real.log y) * y ^ 2 / (Δ * T) ≤ S := by
    rw [hthirdEq]
    exact mul_le_of_le_one_right (by positivity) hthirdFactor
  have hsum : M * y ^ (1 - δ) * (1 + Real.log T) +
      M * y ^ 2 / (Δ * T ^ 2) +
      (1 + Real.log y) * y ^ 2 / (Δ * T) ≤ 3 * S := by
    linarith [hfirst, hsecond, hthird]
  have hcontourBound :
      ‖cesaroPerronSharpSum (twistedMobiusRectangleCoefficient r χ t) y‖ ≤
        Δ + 1 + 128 * Real.exp 1 * (3 * S) := by
    calc
      _ ≤ Δ + 1 + 128 * Real.exp 1 *
          (M * y ^ (1 - δ) * (1 + Real.log T) +
            M * y ^ 2 / (Δ * T ^ 2) +
            (1 + Real.log y) * y ^ 2 / (Δ * T)) := htransfer
      _ ≤ Δ + 1 + 128 * Real.exp 1 * (3 * S) := by
        have hcoeff : 0 ≤ 128 * Real.exp 1 := by positivity
        have hscaled := mul_le_mul_of_nonneg_left hsum hcoeff
        exact add_le_add_right hscaled (Δ + 1)
  have hsmall : Δ + 1 ≤ 2 * S := by
    rw [hΔS] at hΔge1 ⊢
    linarith
  have hmain :
      ‖cesaroPerronSharpSum (twistedMobiusRectangleCoefficient r χ t) y‖ ≤
        (2 + 384 * Real.exp 1) * S := by
    calc
      _ ≤ Δ + 1 + 128 * Real.exp 1 * (3 * S) := hcontourBound
      _ ≤ 2 * S + 384 * Real.exp 1 * S := by
        nlinarith [hsmall]
      _ = (2 + 384 * Real.exp 1) * S := by ring
  convert hmain using 1 <;> simp [S, w, d] <;> ring

#print axioms twistedMobiusPrefix

end FractionalPrimes.Literature.Reciprocal

end
