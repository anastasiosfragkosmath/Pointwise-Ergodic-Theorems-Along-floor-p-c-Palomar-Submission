module

public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import FractionalPrimes.Literature.Analytic.NormalizedDiskLogarithm

@[expose] public section

noncomputable section

open Set Metric
open scoped Topology

namespace FractionalPrimes.Literature.Analytic

/-- The interpolation exponent in the approved radii estimate. -/
noncomputable def explicitLogarithmTheta : ℝ :=
  Real.log (67 / 32) / Real.log (17 / 8)

/-- The exact bound appearing in `lag:radii`. -/
noncomputable def explicitLogarithmConstant (M : ℝ) : ℝ :=
  7 ^ (1 - explicitLogarithmTheta) * (483 + 68 * M) ^ explicitLogarithmTheta

/-- The Borel--Carathéodory estimate used in `lag:radii`, with the approved
center, outer radius, and inner radius. -/
theorem explicitLogarithmBorelCaratheodoryBound
    {a : ℂ} {M : ℝ} (hM : 0 ≤ M) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball a (35 / 32 : ℝ)))
    (hre : ∀ z ∈ ball a (35 / 32 : ℝ), (g z).re ≤ M)
    (hbase : ‖g a‖ ≤ 7)
    {z : ℂ} (hz : z ∈ closedBall a (17 / 16 : ℝ)) :
    ‖g z‖ ≤ 483 + 68 * M := by
  let f : ℂ → ℂ := fun w => g (a + w)
  have hR : (0 : ℝ) < 35 / 32 := by norm_num
  have hrR : (17 / 16 : ℝ) < 35 / 32 := by norm_num
  have hnorm : ‖z - a‖ ≤ (17 / 16 : ℝ) := by
    simpa [dist_eq_norm, sub_eq_add_neg, add_comm] using hz
  have hf : DifferentiableOn ℂ f (ball 0 (35 / 32 : ℝ)) := by
    intro w hw
    have hw' : ‖w‖ < 35 / 32 := by
      simpa [mem_ball_iff_norm] using hw
    have hmem : a + w ∈ ball a (35 / 32 : ℝ) := by
      rw [mem_ball_iff_norm]
      simpa using hw'
    have harg : DifferentiableAt ℂ (fun v : ℂ => a + v) w :=
      (differentiableAt_const a).add differentiableAt_id
    exact ((hg (a + w) hmem).differentiableAt.comp w harg).differentiableWithinAt
  have hmaps : MapsTo f (ball 0 (35 / 32 : ℝ)) {w : ℂ | w.re ≤ M} := by
    intro w hw
    have hw' : ‖w‖ < 35 / 32 := by
      simpa [mem_ball_iff_norm] using hw
    have hmem : a + w ∈ ball a (35 / 32 : ℝ) := by
      rw [mem_ball_iff_norm]
      simpa using hw'
    simpa [f] using hre (a + w) hmem
  have hzero : ‖f 0‖ ≤ 7 := by simpa [f] using hbase
  let w : ℂ := z - a
  have hw_norm : ‖w‖ = ‖z - a‖ := rfl
  have hw_le : ‖w‖ ≤ (17 / 16 : ℝ) := hnorm
  have hw_ball : w ∈ ball 0 (35 / 32 : ℝ) := by
    rw [mem_ball_iff_norm]
    simpa using lt_of_le_of_lt hw_le hrR
  by_contra hgoal
  have hgap : 0 < ‖g z‖ - (483 + 68 * M) := by
    have : ¬ ‖g z‖ ≤ 483 + 68 * M := hgoal
    linarith
  let ε : ℝ := (‖g z‖ - (483 + 68 * M)) / 136
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hMε : 0 < M + ε := lt_of_lt_of_le hε (by nlinarith [hM])
  have hMεmaps : MapsTo f (ball 0 (35 / 32 : ℝ))
      {w : ℂ | w.re ≤ M + ε} := by
    intro x hx
    have hx' : ‖x‖ < 35 / 32 := by simpa [mem_ball_iff_norm] using hx
    have hmem : a + x ∈ ball a (35 / 32 : ℝ) := by
      rw [mem_ball_iff_norm]
      simpa using hx'
    have hxre : (f x).re ≤ M := by
      simpa [f] using hre (a + x) hmem
    exact le_trans hxre (by linarith)
  have hbc := Complex.borelCaratheodory (f := f) (z := w)
    hMε hf hMεmaps hR hw_ball
  have hden : 0 < (35 / 32 : ℝ) - ‖w‖ := by
    have : ‖w‖ ≤ (17 / 16 : ℝ) := hw_le
    norm_num at hrR ⊢
    linarith
  have hfirst :
      (‖w‖ / ((35 / 32 : ℝ) - ‖w‖)) ≤
        (17 / 16 : ℝ) / ((35 / 32 : ℝ) - (17 / 16 : ℝ)) := by
    have hden' : 0 < (35 / 32 : ℝ) - (17 / 16 : ℝ) := by norm_num
    apply (div_le_div_iff₀ hden hden').2
    nlinarith [hw_le]
  have hsecond :
      ((35 / 32 : ℝ) + ‖w‖) / ((35 / 32 : ℝ) - ‖w‖) ≤
        ((35 / 32 : ℝ) + (17 / 16 : ℝ)) /
          ((35 / 32 : ℝ) - (17 / 16 : ℝ)) := by
    have hden' : 0 < (35 / 32 : ℝ) - (17 / 16 : ℝ) := by norm_num
    apply (div_le_div_iff₀ hden hden').2
    nlinarith [hw_le]
  have hcoefle : ‖w‖ / ((35 / 32 : ℝ) - ‖w‖) ≤ 34 := by
    calc
      _ ≤ (17 / 16 : ℝ) / ((35 / 32 : ℝ) - (17 / 16 : ℝ)) := hfirst
      _ = 34 := by norm_num
  have hcoef2 :
      ((35 / 32 : ℝ) + ‖w‖) / ((35 / 32 : ℝ) - ‖w‖) ≤ 69 := by
    calc
      _ ≤ ((35 / 32 : ℝ) + (17 / 16 : ℝ)) /
            ((35 / 32 : ℝ) - (17 / 16 : ℝ)) := hsecond
      _ = 69 := by norm_num
  have hmult :
      2 * (M + ε) * (‖w‖ / ((35 / 32 : ℝ) - ‖w‖)) ≤
        68 * (M + ε) := by
    calc
      2 * (M + ε) * (‖w‖ / ((35 / 32 : ℝ) - ‖w‖)) =
          (2 * (M + ε)) * (‖w‖ / ((35 / 32 : ℝ) - ‖w‖)) := by ring
      _ ≤ (2 * (M + ε)) * 34 :=
        mul_le_mul_of_nonneg_left hcoefle (by positivity)
      _ = 68 * (M + ε) := by ring
  have hmul2 :
      ‖f 0‖ * (((35 / 32 : ℝ) + ‖w‖) / ((35 / 32 : ℝ) - ‖w‖)) ≤ 7 * 69 :=
    mul_le_mul hzero hcoef2 (by positivity) (by positivity)
  have hbc' : ‖g z‖ ≤ 483 + 68 * M + 68 * ε := by
    have hz_eval : f w = g z := by simp [f, w, sub_eq_add_neg]
    rw [← hz_eval]
    calc
      ‖f w‖ ≤ 2 * (M + ε) * ‖w‖ / ((35 / 32 : ℝ) - ‖w‖) +
          ‖f 0‖ * ((35 / 32 : ℝ) + ‖w‖) /
            ((35 / 32 : ℝ) - ‖w‖) := hbc
      _ = 2 * (M + ε) *
            (‖w‖ / ((35 / 32 : ℝ) - ‖w‖)) +
          ‖f 0‖ * (((35 / 32 : ℝ) + ‖w‖) /
            ((35 / 32 : ℝ) - ‖w‖)) := by ring
      _ ≤ 68 * (M + ε) + 7 * 69 := add_le_add hmult hmul2
      _ = 483 + 68 * M + 68 * ε := by ring
  have hεeq : 68 * ε = (‖g z‖ - (483 + 68 * M)) / 2 := by
    dsimp [ε]
    ring
  nlinarith [hgap, hbc', hεeq]

private theorem threeCircleBoundAtApprovedRadii
    {a : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball a (35 / 32 : ℝ)))
    {K : ℝ} (_hK : 0 < K)
    (hsmall : ∀ z ∈ closedBall a (1 / 2 : ℝ), ‖g z‖ ≤ 7)
    (hlarge : ∀ z ∈ closedBall a (17 / 16 : ℝ), ‖g z‖ ≤ K) :
    ∀ z ∈ closedBall a (67 / 64 : ℝ),
      ‖g z‖ ≤ 7 ^ (1 - explicitLogarithmTheta) * K ^ explicitLogarithmTheta := by
  let l : ℝ := Real.log (1 / 2)
  let m : ℝ := Real.log (67 / 64)
  let u : ℝ := Real.log (17 / 16)
  let F : ℂ → ℂ := fun w => g (a + Complex.exp w)
  have hlm : l < m := by
    dsimp [l, m]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hmu : m < u := by
    dsimp [m, u]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hlu : l < u := hlm.trans hmu
  have hratio : (m - l) / (u - l) = explicitLogarithmTheta := by
    dsimp [l, m, u, explicitLogarithmTheta]
    rw [← Real.log_div (by norm_num : (67 / 64 : ℝ) ≠ 0)
          (by norm_num : (1 / 2 : ℝ) ≠ 0),
        ← Real.log_div (by norm_num : (17 / 16 : ℝ) ≠ 0)
          (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    norm_num
  have hclosedStrip :
      closure (Complex.HadamardThreeLines.verticalStrip l u) ⊆
        Complex.HadamardThreeLines.verticalClosedStrip l u := by
    apply closure_minimal
    · intro w hw
      have hw' : l < w.re ∧ w.re < u := by
        simpa [Complex.HadamardThreeLines.verticalStrip] using hw
      have : w.re ∈ Set.Icc l u := ⟨hw'.1.le, hw'.2.le⟩
      simpa [Complex.HadamardThreeLines.verticalClosedStrip] using this
    · exact isClosed_Icc.preimage Complex.continuous_re
  have hFanalytic :
      AnalyticOnNhd ℂ F (Complex.HadamardThreeLines.verticalClosedStrip l u) := by
    intro w hw
    have hw' : w.re ∈ Set.Icc l u := by
      simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hw
    have hnormExp : ‖Complex.exp w‖ = Real.exp w.re := by
      rw [Complex.norm_exp]
    have hExpBound : ‖Complex.exp w‖ ≤ (17 / 16 : ℝ) := by
      rw [hnormExp]
      calc
        Real.exp w.re ≤ Real.exp u := Real.exp_le_exp.mpr hw'.2
        _ = 17 / 16 := by
          dsimp [u]
          exact Real.exp_log (by norm_num)
    have hmem : a + Complex.exp w ∈ ball a (35 / 32 : ℝ) := by
      rw [mem_ball_iff_norm]
      have hadd : ‖(a + Complex.exp w) - a‖ = ‖Complex.exp w‖ := by simp
      rw [hadd]
      exact hExpBound.trans_lt (by norm_num)
    have hAdd : AnalyticAt ℂ (fun v : ℂ => a + v) (Complex.exp w) := by
      fun_prop
    have hExp : AnalyticAt ℂ Complex.exp w := by
      fun_prop
    simpa [F, Function.comp_def] using
      ((hg (a + Complex.exp w) hmem).comp hAdd).comp hExp
  have hFdiffClosure :
      DifferentiableOn ℂ F (closure (Complex.HadamardThreeLines.verticalStrip l u)) := by
    intro w hw
    exact (hFanalytic w (hclosedStrip hw)).differentiableAt.differentiableWithinAt
  have hFdiffCont :
      DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip l u) :=
    hFdiffClosure.diffContOnCl
  have hFclosedBound :
      ∀ w ∈ Complex.HadamardThreeLines.verticalClosedStrip l u, ‖F w‖ ≤ K := by
    intro w hw
    have hw' : w.re ∈ Set.Icc l u := by
      simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hw
    have hnormExp : ‖Complex.exp w‖ = Real.exp w.re := by
      rw [Complex.norm_exp]
    have hExpBound : ‖Complex.exp w‖ ≤ (17 / 16 : ℝ) := by
      rw [hnormExp]
      calc
        Real.exp w.re ≤ Real.exp u := Real.exp_le_exp.mpr hw'.2
        _ = 17 / 16 := by
          dsimp [u]
          exact Real.exp_log (by norm_num)
    have hmem : a + Complex.exp w ∈ closedBall a (17 / 16 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm]
      have hadd : ‖(a + Complex.exp w) - a‖ = ‖Complex.exp w‖ := by simp
      rw [hadd]
      exact hExpBound
    simpa [F] using hlarge (a + Complex.exp w) hmem
  have hFbdd : BddAbove
      ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip l u) := by
    refine ⟨K, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    exact hFclosedBound w hw
  have hleft : ∀ w ∈ Complex.re ⁻¹' {l}, ‖F w‖ ≤ 7 := by
    intro w hw
    have hRe : w.re = l := by simpa using hw
    have hnormExp : ‖Complex.exp w‖ = (1 / 2 : ℝ) := by
      rw [Complex.norm_exp, hRe]
      dsimp [l]
      exact Real.exp_log (by norm_num)
    have hmem : a + Complex.exp w ∈ closedBall a (1 / 2 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm]
      have hadd : ‖(a + Complex.exp w) - a‖ = ‖Complex.exp w‖ := by simp
      rw [hadd, hnormExp]
    simpa [F] using hsmall (a + Complex.exp w) hmem
  have hright : ∀ w ∈ Complex.re ⁻¹' {u}, ‖F w‖ ≤ K := by
    intro w hw
    have hRe : w.re = u := by simpa using hw
    have hnormExp : ‖Complex.exp w‖ = (17 / 16 : ℝ) := by
      rw [Complex.norm_exp, hRe]
      dsimp [u]
      exact Real.exp_log (by norm_num)
    have hmem : a + Complex.exp w ∈ closedBall a (17 / 16 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm]
      have hadd : ‖(a + Complex.exp w) - a‖ = ‖Complex.exp w‖ := by simp
      rw [hadd, hnormExp]
    simpa [F] using hlarge (a + Complex.exp w) hmem
  have hcircle : ∀ z ∈ sphere a (67 / 64 : ℝ),
      ‖g z‖ ≤ 7 ^ (1 - explicitLogarithmTheta) * K ^ explicitLogarithmTheta := by
    intro z hz
    have hdist : dist z a = (67 / 64 : ℝ) := hz
    have hnorm : ‖z - a‖ = (67 / 64 : ℝ) := by
      simpa [dist_eq_norm] using hdist
    have hne : z - a ≠ 0 := by
      intro hzero
      rw [hzero] at hnorm
      norm_num at hnorm
    let w : ℂ := Complex.log (z - a)
    have hRe : w.re = m := by
      dsimp [w, m]
      rw [Complex.log_re, hnorm]
    have hwstrip :
        w ∈ Complex.HadamardThreeLines.verticalClosedStrip l u := by
      change w.re ∈ Set.Icc l u
      rw [hRe]
      exact ⟨hlm.le, hmu.le⟩
    have hinterp := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      hlu hwstrip hFdiffCont hFbdd hleft hright
    have hFw : F w = g z := by
      simp [F, w, Complex.exp_log hne]
    rw [hFw, hRe, hratio] at hinterp
    exact hinterp
  have hgDiff : DifferentiableOn ℂ g (ball a (35 / 32 : ℝ)) := by
    intro z hz
    exact (hg z hz).differentiableAt.differentiableWithinAt
  have hinnerSubset : closedBall a (67 / 64 : ℝ) ⊆ ball a (35 / 32 : ℝ) :=
    closedBall_subset_ball (by norm_num)
  have hgDiffCont : DiffContOnCl ℂ g (ball a (67 / 64 : ℝ)) :=
    hgDiff.diffContOnCl_ball hinnerSubset
  have hfrontier : ∀ z ∈ frontier (ball a (67 / 64 : ℝ)),
      ‖g z‖ ≤ 7 ^ (1 - explicitLogarithmTheta) * K ^ explicitLogarithmTheta := by
    intro z hz
    exact hcircle z (Metric.frontier_ball_subset_sphere hz)
  intro z hz
  have hzclosure : z ∈ closure (ball a (67 / 64 : ℝ)) := by
    rw [closure_ball a (by norm_num)]
    exact hz
  exact Complex.norm_le_of_forall_mem_frontier_norm_le
    (Metric.isBounded_ball (x := a) (r := (67 / 64 : ℝ)))
    hgDiffCont hfrontier hzclosure

/-- Explicit quantitative logarithm growth on the approved radii. This is the
exact result `lag:radii`, with an open neighborhood `U` encoding the specified
analytic logarithm on a neighborhood of the closed half-radius disk. -/
theorem explicitLogarithmRadii
    {a : ℂ} {M : ℝ} (hM : 0 ≤ M) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H (ball a (35 / 32 : ℝ)))
    (hHne : ∀ z ∈ ball a (35 / 32 : ℝ), H z ≠ 0)
    (hHbound : ∀ z ∈ ball a (35 / 32 : ℝ), ‖H z‖ ≤ Real.exp M)
    {U : Set ℂ} (_hUopen : IsOpen U)
    (hclosedU : closedBall a (1 / 2 : ℝ) ⊆ U)
    {g₀ : ℂ → ℂ} (hg₀ : AnalyticOnNhd ℂ g₀ U)
    (hg₀exp : ∀ z ∈ U, Complex.exp (g₀ z) = H z)
    (hg₀bound : ∀ z ∈ closedBall a (1 / 2 : ℝ), ‖g₀ z‖ ≤ 7) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball a (35 / 32 : ℝ)) ∧
      (∀ z ∈ ball a (35 / 32 : ℝ), Complex.exp (g z) = H z) ∧
      (∀ z ∈ closedBall a (1 / 2 : ℝ), g z = g₀ z) ∧
      0 < explicitLogarithmTheta ∧ explicitLogarithmTheta < 1 ∧
      (∀ z ∈ closedBall a (67 / 64 : ℝ),
        ‖g z‖ ≤ explicitLogarithmConstant M) ∧
      (∀ z ∈ closedBall a (67 / 64 : ℝ),
        ‖H z‖⁻¹ ≤ Real.exp (explicitLogarithmConstant M)) ∧
      (∀ z ∈ closedBall a (65 / 64 : ℝ),
        ‖deriv H z / H z‖ ≤ 32 * explicitLogarithmConstant M) := by
  have hUsmall : ball a (1 / 2 : ℝ) ⊆ U :=
    ball_subset_closedBall.trans hclosedU
  have hb : Complex.exp (g₀ a) = H a := by
    exact hg₀exp a (hclosedU (by simp [Metric.mem_closedBall]))
  obtain ⟨g, hg, hgexp, hgbase, hgderiv, hgreal, hgcompat, _⟩ :=
    normalizedDiskLogarithm (a := a) (R := (35 / 32 : ℝ)) (by norm_num)
      hH hHne (b := g₀ a) hb
  have hg₀small : AnalyticOnNhd ℂ g₀ (ball a (1 / 2 : ℝ)) := by
    intro z hz
    exact hg₀ z (hUsmall hz)
  have hg₀expSmall : ∀ z ∈ ball a (1 / 2 : ℝ), Complex.exp (g₀ z) = H z := by
    intro z hz
    exact hg₀exp z (hUsmall hz)
  have hEqOpen : ∀ z ∈ ball a (1 / 2 : ℝ), g z = g₀ z :=
    hgcompat (by norm_num) (by norm_num) g₀ hg₀small hg₀expSmall rfl
  have hgcont : ContinuousOn g (closedBall a (1 / 2 : ℝ)) :=
    hg.continuousOn.mono (closedBall_subset_ball (by norm_num))
  have hg₀cont : ContinuousOn g₀ (closedBall a (1 / 2 : ℝ)) :=
    hg₀.continuousOn.mono hclosedU
  have hEqClosed : EqOn g g₀ (closedBall a (1 / 2 : ℝ)) :=
    Set.EqOn.of_subset_closure hEqOpen hgcont hg₀cont ball_subset_closedBall
      (by rw [closure_ball a (by norm_num)])
  have htheta_pos : 0 < explicitLogarithmTheta := by
    unfold explicitLogarithmTheta
    apply div_pos
    · exact Real.log_pos (by norm_num)
    · exact Real.log_pos (by norm_num)
  have htheta_lt : explicitLogarithmTheta < 1 := by
    have hden : 0 < Real.log (17 / 8 : ℝ) := Real.log_pos (by norm_num)
    have hnumlt : Real.log (67 / 32 : ℝ) < Real.log (17 / 8 : ℝ) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    unfold explicitLogarithmTheta
    exact (div_lt_one hden).2 hnumlt
  have hbase : ‖g a‖ ≤ 7 := by
    have ha : a ∈ closedBall a (1 / 2 : ℝ) := by simp [Metric.mem_closedBall]
    rw [hEqClosed ha]
    exact hg₀bound a ha
  have hrealBound : ∀ z ∈ ball a (35 / 32 : ℝ), (g z).re ≤ M := by
    intro z hz
    have hnormPos : 0 < ‖H z‖ := norm_pos_iff.mpr (hHne z hz)
    have hlogle : Real.log ‖H z‖ ≤ Real.log (Real.exp M) :=
      Real.log_le_log hnormPos (hHbound z hz)
    rw [Real.log_exp] at hlogle
    rw [hgreal z hz]
    exact hlogle
  have hBC : ∀ z ∈ closedBall a (17 / 16 : ℝ), ‖g z‖ ≤ 483 + 68 * M := by
    intro z hz
    exact explicitLogarithmBorelCaratheodoryBound hM hg hrealBound hbase hz
  have hKpos : 0 < 483 + 68 * M := by nlinarith [hM]
  have hmid := threeCircleBoundAtApprovedRadii hg hKpos
    (by
      intro z hz
      rw [hEqClosed hz]
      exact hg₀bound z hz)
    hBC
  have hCpos : 0 < explicitLogarithmConstant M := by
    unfold explicitLogarithmConstant
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos hKpos _)
  have hbound : ∀ z ∈ closedBall a (67 / 64 : ℝ),
      ‖g z‖ ≤ explicitLogarithmConstant M := by
    intro z hz
    have h := hmid z hz
    simpa [explicitLogarithmConstant] using h
  have hinvBound : ∀ z ∈ closedBall a (67 / 64 : ℝ),
      ‖H z‖⁻¹ ≤ Real.exp (explicitLogarithmConstant M) := by
    intro z hz
    have hzopen : z ∈ ball a (35 / 32 : ℝ) :=
      (closedBall_subset_ball (by norm_num)) hz
    have hnormExp : ‖H z‖ = Real.exp (g z).re := by
      rw [← hgexp z hzopen, Complex.norm_exp]
    have hre : -((g z).re) ≤ explicitLogarithmConstant M := by
      have habs : |(g z).re| ≤ ‖g z‖ := Complex.abs_re_le_norm (g z)
      have : |(g z).re| ≤ explicitLogarithmConstant M := habs.trans (hbound z hz)
      have hlow := (abs_le.mp this).1
      linarith
    calc
      ‖H z‖⁻¹ = (Real.exp (g z).re)⁻¹ := by rw [hnormExp]
      _ = Real.exp (-((g z).re)) := by rw [Real.exp_neg]
      _ ≤ Real.exp (explicitLogarithmConstant M) := Real.exp_le_exp.mpr hre
  have hderivLarge : DifferentiableOn ℂ g (ball a (35 / 32 : ℝ)) := by
    intro z hz
    exact (hg z hz).differentiableAt.differentiableWithinAt
  have hderivBound : ∀ z ∈ closedBall a (65 / 64 : ℝ),
      ‖deriv g z‖ ≤ 32 * explicitLogarithmConstant M := by
    intro z hz
    have hzdist : ‖z - a‖ ≤ (65 / 64 : ℝ) := by
      simpa [dist_eq_norm] using hz
    have hsmallSubset : closedBall z (1 / 32 : ℝ) ⊆ ball a (35 / 32 : ℝ) := by
      intro w hw
      rw [mem_ball_iff_norm]
      have hwdist : ‖w - z‖ ≤ (1 / 32 : ℝ) := by
        simpa [dist_eq_norm] using hw
      have htriangle : ‖w - a‖ ≤ ‖w - z‖ + ‖z - a‖ := by
        calc
          ‖w - a‖ = ‖(w - z) + (z - a)‖ := by congr 1; abel
          _ ≤ ‖w - z‖ + ‖z - a‖ := norm_add_le _ _
      calc
        ‖w - a‖ ≤ ‖w - z‖ + ‖z - a‖ := htriangle
        _ ≤ (1 / 32 : ℝ) + (65 / 64 : ℝ) := add_le_add hwdist hzdist
        _ < (35 / 32 : ℝ) := by norm_num
    have hcircle : ∀ w ∈ sphere z (1 / 32 : ℝ),
        ‖g w‖ ≤ explicitLogarithmConstant M := by
      intro w hw
      have hwdist : ‖w - z‖ = (1 / 32 : ℝ) := by
        simpa [dist_eq_norm] using (show dist w z = (1 / 32 : ℝ) from hw)
      have htriangle : ‖w - a‖ ≤ ‖w - z‖ + ‖z - a‖ := by
        calc
          ‖w - a‖ = ‖(w - z) + (z - a)‖ := by congr 1; abel
          _ ≤ ‖w - z‖ + ‖z - a‖ := norm_add_le _ _
      have hmem : w ∈ closedBall a (67 / 64 : ℝ) := by
        rw [mem_closedBall, dist_eq_norm]
        have : ‖w - a‖ ≤ (1 / 32 : ℝ) + (65 / 64 : ℝ) := by
          calc
            ‖w - a‖ ≤ ‖w - z‖ + ‖z - a‖ := htriangle
            _ ≤ (1 / 32 : ℝ) + (65 / 64 : ℝ) := add_le_add (by rw [hwdist]) hzdist
        norm_num at this ⊢
        exact this
      exact hbound w hmem
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (by norm_num : (0 : ℝ) < 1 / 32)
      (hderivLarge.diffContOnCl_ball hsmallSubset) hcircle
    have hcauchy' : ‖deriv g z‖ ≤ 32 * explicitLogarithmConstant M := by
      norm_num at hcauchy ⊢
      nlinarith
    exact hcauchy'
  have hlogDerivBound : ∀ z ∈ closedBall a (65 / 64 : ℝ),
      ‖deriv H z / H z‖ ≤ 32 * explicitLogarithmConstant M := by
    intro z hz
    have hzopen : z ∈ ball a (35 / 32 : ℝ) :=
      (closedBall_subset_ball (by norm_num)) hz
    rw [← hgderiv z hzopen]
    exact hderivBound z hz
  exact ⟨g, hg, hgexp, hEqClosed, htheta_pos, htheta_lt,
    hbound, hinvBound, hlogDerivBound⟩


end FractionalPrimes.Literature.Analytic

#print axioms FractionalPrimes.Literature.Analytic.explicitLogarithmRadii

end
