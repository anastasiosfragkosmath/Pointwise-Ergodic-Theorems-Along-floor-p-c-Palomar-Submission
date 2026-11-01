module
public import FractionalPrimes.Literature.Analytic.NormalizedDiskLogarithm
public import FractionalPrimes.Literature.Reciprocal.NormalizedDirichletFamilyOuter
public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletEulerLog
public import FractionalPrimes.Literature.Reciprocal.PrincipalRegularizedLogB
public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletZetaIdentification
@[expose] public section

@[expose] public section

open Complex Set
open scoped Topology

noncomputable section

namespace FractionalPrimes.Literature.Reciprocal

/-- The exact zero-free half-plane proposition `ZFR_{7/8}` assumed in the
approved reciprocal-closure blueprint. -/
def fixedHalfPlaneProperty : Prop :=
  ∀ {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re)
    (hnotpole : ¬ (χ = FractionalPrimes.Literature.Twisted.principalCharacter q ∧ s = 1)),
    continuedDirichletL χ s (by linarith [hs]) hnotpole ≠ 0

/-- The imported, explicitly identified E1 theorem supplies the blueprint's
fixed-half-plane proposition in this development. -/
theorem fixedHalfPlaneProperty_of_OAISource : fixedHalfPlaneProperty := by
  intro q inst χ s hs hnotpole
  exact fixedHalfPlaneOfOAISource χ hs hnotpole

private theorem normalizedDirichletFamily_ne_zero_on_logarithm_ball_of_fixedHalfPlane
    (hZFR : fixedHalfPlaneProperty)
    {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) (t : ℝ) {s : ℂ}
    (hs : s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (35 / 32 : ℝ)) :
    normalizedDirichletFamily χ s ≠ 0 := by
  have hdist : ‖s - (2 + (t : ℂ) * Complex.I)‖ < (35 / 32 : ℝ) := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hs
  have hreDist : |s.re - 2| ≤ ‖s - (2 + (t : ℂ) * Complex.I)‖ := by
    simpa [Complex.sub_re] using
      (Complex.abs_re_le_norm (s - (2 + (t : ℂ) * Complex.I)))
  have hAbs : |s.re - 2| < (35 / 32 : ℝ) := hreDist.trans_lt hdist
  have hlow : -(35 / 32 : ℝ) < s.re - 2 := (abs_lt.mp hAbs).1
  have hs29 : (29 / 32 : ℝ) < s.re := by linarith
  have hs78 : (7 / 8 : ℝ) < s.re := by norm_num at hs29 ⊢; linarith
  have hspos : 0 < s.re := by linarith
  by_cases hχ : χ = FractionalPrimes.Literature.Twisted.principalCharacter q
  · simp only [normalizedDirichletFamily, if_pos hχ]
    by_cases hs1 : s = 1
    · subst s
      rw [continuedDirichletH0Total_one]
      norm_num
    · have hnotpole₁ :
          ¬ ((1 : _root_.DirichletCharacter ℂ 1) =
              FractionalPrimes.Literature.Twisted.principalCharacter 1 ∧ s = 1) := by
        rintro ⟨_, h⟩
        exact hs1 h
      have hL₁ne :
          continuedDirichletL (1 : _root_.DirichletCharacter ℂ 1) s hspos hnotpole₁ ≠ 0 :=
        hZFR (q := 1) (1 : _root_.DirichletCharacter ℂ 1) hs78 hnotpole₁
      have hZne : continuedDirichletZ s hspos hs1 ≠ 0 := by
        simpa [continuedDirichletL, principalContinuedDirichletL,
          FractionalPrimes.Literature.Twisted.principalCharacter] using hL₁ne
      have hsplus : s + 1 ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      have hfactor : (s - 1) / (s + 1) ≠ 0 :=
        div_ne_zero (sub_ne_zero.mpr hs1) hsplus
      have hH0 : continuedDirichletH0 s hspos ≠ 0 := by
        rw [continuedDirichletH0_eq_mul_Z hspos hs1]
        exact mul_ne_zero hfactor hZne
      simpa only [continuedDirichletH0Total_eq hspos] using hH0
  · have hnotpole :
        ¬ (χ = FractionalPrimes.Literature.Twisted.principalCharacter q ∧ s = 1) := by
      rintro ⟨h, _⟩
      exact hχ h
    have hLne : nonprincipalContinuedDirichletL χ hχ s hspos ≠ 0 := by
      have h := hZFR χ hs78 hnotpole
      simpa [continuedDirichletL, hχ] using h
    have hCore := nonprincipalContinuedDirichletL_eq_core χ hχ s hspos
    rw [normalizedDirichletFamily, if_neg hχ, ← hCore]
    exact hLne

private theorem normalizedLog_inner_ball_re_gt_one {t : ℝ} {s : ℂ}
    (hs : s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (17 / 32 : ℝ)) :
    1 < s.re := by
  have hdist : ‖s - (2 + (t : ℂ) * Complex.I)‖ < (17 / 32 : ℝ) := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hs
  have hre : |s.re - 2| ≤ ‖s - (2 + (t : ℂ) * Complex.I)‖ := by
    simpa [Complex.sub_re] using
      (Complex.abs_re_le_norm (s - (2 + (t : ℂ) * Complex.I)))
  have hlow : -(17 / 32 : ℝ) < s.re - 2 := by
    have hAbs : |s.re - 2| < (17 / 32 : ℝ) := hre.trans_lt hdist
    exact (abs_lt.mp hAbs).1
  have hbound : (1 : ℝ) < 2 - 17 / 32 := by norm_num
  linarith

private theorem normalizedLog_inner_closedBall_re_ge_three_halves {t : ℝ} {s : ℂ}
    (hs : s ∈ Metric.closedBall (2 + (t : ℂ) * Complex.I) (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) ≤ s.re := by
  let c : ℂ := 2 + (t : ℂ) * Complex.I
  have hdist : ‖s - c‖ ≤ (1 / 2 : ℝ) := by
    simpa [dist_eq_norm, c] using Metric.mem_closedBall.mp hs
  have hAbs : |(s - c).re| ≤ (1 / 2 : ℝ) := by
    exact (Complex.abs_re_le_norm (s - c)).trans hdist
  have hlow : -(1 / 2 : ℝ) ≤ (s - c).re := by
    calc
      -(1 / 2 : ℝ) ≤ -(abs ((s - c).re)) := neg_le_neg hAbs
      _ ≤ (s - c).re := neg_abs_le _
  have hrepr : s.re = 2 + (s - c).re := by
    calc
      s.re = ((s - c) + c).re := by congr 1 <;> abel
      _ = (s - c).re + 2 := by simp [c]
      _ = 2 + (s - c).re := by ring
  rw [hrepr]
  linarith

/-- The already constructed Euler logarithm and interval-integral correction
give the exact bounded logarithm of the regularized principal branch from
`lrc:regularized-principal`. -/
def principalRegularizedEulerLog (s : ℂ) : ℂ :=
  continuedDirichletEulerLog (1 : _root_.DirichletCharacter ℂ 1) s +
    principalRegularizedLogB s

/-- Analyticity, exponential identity, and the exact norm-six bound for
`G₁ + B` on the half-plane required by `lrc:regularized-principal`. -/
theorem principalRegularizedEulerLog_spec :
    AnalyticOnNhd ℂ principalRegularizedEulerLog {s : ℂ | 1 < s.re} ∧
    (∀ s : ℂ, (hs : 1 < s.re) →
      Complex.exp (principalRegularizedEulerLog s) =
        continuedDirichletH0 s (by linarith [hs])) ∧
    (∀ s : ℂ, (3 / 2 : ℝ) ≤ s.re →
      ‖principalRegularizedEulerLog s‖ ≤ 6) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact (continuedDirichletEulerLog_one_analyticOnNhd s hs).add
      (analyticOnNhd_principalRegularizedLogB s hs)
  · intro s hs
    have hspos : 0 < s.re := by linarith
    have hsne : s ≠ 1 := by
      intro h
      subst s
      norm_num at hs
    have hG := exp_continuedDirichletEulerLog_one_eq_riemannZeta hs
    have hB := exp_principalRegularizedLogB hs
    have hZ := continuedDirichletZ_eq_riemannZeta hspos hsne
    have hH0 := continuedDirichletH0_eq_mul_Z hspos hsne
    calc
      Complex.exp (principalRegularizedEulerLog s) =
          ((s - 1) / (s + 1)) * riemannZeta s := by
            simp only [principalRegularizedEulerLog, Complex.exp_add]
            rw [hG, hB]
            ring
      _ = continuedDirichletH0 s hspos := by rw [← hZ, hH0]
  · intro s hs
    calc
      ‖principalRegularizedEulerLog s‖ ≤
          ‖continuedDirichletEulerLog (1 : _root_.DirichletCharacter ℂ 1) s‖ +
            ‖principalRegularizedLogB s‖ := by
              simp only [principalRegularizedEulerLog]
              exact norm_add_le _ _
      _ ≤ 2 + 4 := add_le_add
        (continuedDirichletEulerLog_one_norm_le_two hs)
        (norm_principalRegularizedLogB_le_four hs)
      _ = 6 := by norm_num

/-- The inner logarithm clause of blueprint `lrc:normalized-family`, under its
exact fixed-half-plane hypothesis `ZFR_{7/8}`.
The open disk of radius `17/32` is a neighborhood of the closed radius-`1/2`
disk and lies in `Re(s) > 1`; the logarithm is bounded by six on the closed
disk. -/
theorem normalizedDirichletFamily_inner_log_on_logarithm_ball
    (hZFR : fixedHalfPlaneProperty)
    {q : ℕ} [NeZero q] (_hq : 1 ≤ q)
    (χ : _root_.DirichletCharacter ℂ q) (t : ℝ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g
        (Metric.ball (2 + (t : ℂ) * Complex.I) (17 / 32 : ℝ)) ∧
      (∀ s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (17 / 32 : ℝ),
        Complex.exp (g s) = normalizedDirichletFamily χ s) ∧
      (∀ s ∈ Metric.closedBall (2 + (t : ℂ) * Complex.I) (1 / 2 : ℝ),
        ‖g s‖ ≤ 6) := by
  let c : ℂ := 2 + (t : ℂ) * Complex.I
  let r : ℝ := 17 / 32
  have hr : 0 < r := by norm_num [r]
  have hrR : r ≤ (35 / 32 : ℝ) := by norm_num [r]
  have hOuterAnalytic : AnalyticOnNhd ℂ (normalizedDirichletFamily χ)
      (Metric.ball c (35 / 32 : ℝ)) := by
    simpa [c] using
      analyticOnNhd_normalizedDirichletFamily_on_logarithm_ball χ t
  have hOuterNe : ∀ s ∈ Metric.ball c (35 / 32 : ℝ),
      normalizedDirichletFamily χ s ≠ 0 := by
    intro s hs
    exact normalizedDirichletFamily_ne_zero_on_logarithm_ball_of_fixedHalfPlane
      hZFR χ t (by simpa [c] using hs)
  by_cases hχ : χ = FractionalPrimes.Literature.Twisted.principalCharacter q
  · let K : ℂ → ℂ := principalRegularizedEulerLog
    have hKanalytic : AnalyticOnNhd ℂ K (Metric.ball c r) := by
      intro s hs
      have hsRe : 1 < s.re := by
        have h : s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (17 / 32 : ℝ) := by
          simpa [c, r] using hs
        exact normalizedLog_inner_ball_re_gt_one h
      simpa only [K] using principalRegularizedEulerLog_spec.1 s hsRe
    have hKexp : ∀ s ∈ Metric.ball c r,
        Complex.exp (K s) = normalizedDirichletFamily χ s := by
      intro s hs
      have hsRe : 1 < s.re := by
        have h : s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (17 / 32 : ℝ) := by
          simpa [c, r] using hs
        exact normalizedLog_inner_ball_re_gt_one h
      have hspos : 0 < s.re := by linarith
      have hH0Total := continuedDirichletH0Total_eq hspos
      calc
        Complex.exp (K s) = continuedDirichletH0 s hspos := by
          simpa only [K] using principalRegularizedEulerLog_spec.2.1 s hsRe
        _ = continuedDirichletH0Total s := hH0Total.symm
        _ = normalizedDirichletFamily χ s := by
          simp [normalizedDirichletFamily, hχ]
    have hcBall : c ∈ Metric.ball c r := Metric.mem_ball_self hr
    have hbase : Complex.exp (K c) = normalizedDirichletFamily χ c := hKexp c hcBall
    obtain ⟨g, hgAnalytic, hgExp, hgBase, _, _, hgCompat, _⟩ :=
      FractionalPrimes.Literature.Analytic.normalizedDiskLogarithm
        (a := c) (R := (35 / 32 : ℝ))
        (by norm_num) hOuterAnalytic hOuterNe (b := K c) hbase
    have hgK : ∀ s ∈ Metric.ball c r, g s = K s :=
      hgCompat hr hrR K hKanalytic hKexp rfl
    refine ⟨g, ?_, ?_, ?_⟩
    · exact hgAnalytic.mono (Metric.ball_subset_ball hrR)
    · intro s hs
      have hsOuter : s ∈ Metric.ball c (35 / 32 : ℝ) :=
        Metric.ball_subset_ball hrR hs
      rw [hgK s hs]
      exact hKexp s hs
    · intro s hs
      have hsInner : s ∈ Metric.ball c r := by
        apply Metric.mem_ball.mpr
        have hdist : dist s c ≤ (1 / 2 : ℝ) := by
          simpa [c] using Metric.mem_closedBall.mp hs
        exact hdist.trans_lt (by norm_num [r])
      have hsRe := normalizedLog_inner_closedBall_re_ge_three_halves
        (by simpa [c] using hs)
      rw [hgK s hsInner]
      simpa only [K] using principalRegularizedEulerLog_spec.2.2 s hsRe
  · let K : ℂ → ℂ := fun s => continuedDirichletEulerLog χ s
    have hKanalytic : AnalyticOnNhd ℂ K (Metric.ball c r) := by
      intro s hs
      have hsRe : 1 < s.re := by
        have h : s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (17 / 32 : ℝ) := by
          simpa [c, r] using hs
        exact normalizedLog_inner_ball_re_gt_one h
      exact continuedDirichletEulerLog_analyticOnNhd χ s hsRe
    have hKexp : ∀ s ∈ Metric.ball c r,
        Complex.exp (K s) = normalizedDirichletFamily χ s := by
      intro s hs
      have hsRe : 1 < s.re := by
        have h : s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (17 / 32 : ℝ) := by
          simpa [c, r] using hs
        exact normalizedLog_inner_ball_re_gt_one h
      have hspos : 0 < s.re := by linarith
      have hExp := exp_continuedDirichletEulerLog_eq_LSeries χ hsRe
      have hL := nonprincipalContinuedDirichletL_eq_LSeries_of_one_lt_re χ hχ hsRe
      have hCore := nonprincipalContinuedDirichletL_eq_core χ hχ s hspos
      rw [normalizedDirichletFamily, if_neg hχ]
      dsimp [K]
      calc
        Complex.exp (continuedDirichletEulerLog χ s) = LSeries (χ ·) s := hExp
        _ = nonprincipalContinuedDirichletL χ hχ s hspos := hL.symm
        _ = nonprincipalContinuedDirichletLCore χ s := hCore
    have hcBall : c ∈ Metric.ball c r := Metric.mem_ball_self hr
    have hbase : Complex.exp (K c) = normalizedDirichletFamily χ c := hKexp c hcBall
    obtain ⟨g, hgAnalytic, hgExp, hgBase, _, _, hgCompat, _⟩ :=
      FractionalPrimes.Literature.Analytic.normalizedDiskLogarithm
        (a := c) (R := (35 / 32 : ℝ))
        (by norm_num) hOuterAnalytic hOuterNe (b := K c) hbase
    have hgK : ∀ s ∈ Metric.ball c r, g s = K s :=
      hgCompat hr hrR K hKanalytic hKexp rfl
    refine ⟨g, ?_, ?_, ?_⟩
    · exact hgAnalytic.mono (Metric.ball_subset_ball hrR)
    · intro s hs
      have hsOuter : s ∈ Metric.ball c (35 / 32 : ℝ) :=
        Metric.ball_subset_ball hrR hs
      rw [hgK s hs]
      exact hKexp s hs
    · intro s hs
      have hsInner : s ∈ Metric.ball c r := by
        apply Metric.mem_ball.mpr
        have hdist : dist s c ≤ (1 / 2 : ℝ) := by
          simpa [c] using Metric.mem_closedBall.mp hs
        exact hdist.trans_lt (by norm_num [r])
      have hsRe := normalizedLog_inner_closedBall_re_ge_three_halves
        (by simpa [c] using hs)
      rw [hgK s hsInner]
      calc
        ‖K s‖ = ‖continuedDirichletEulerLog χ s‖ := by simp [K]
        _ ≤ 2 := continuedDirichletEulerLog_norm_le_two χ hsRe
        _ ≤ 6 := by norm_num

/-- The accepted E1 source proves the hypothesis of the blueprint-faithful
conditional inner-log result, yielding its unconditional instance in this
development. -/
theorem normalizedDirichletFamily_inner_log_on_logarithm_ball_of_OAISource
    {q : ℕ} [NeZero q] (_hq : 1 ≤ q)
    (χ : _root_.DirichletCharacter ℂ q) (t : ℝ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g
        (Metric.ball (2 + (t : ℂ) * Complex.I) (17 / 32 : ℝ)) ∧
      (∀ s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (17 / 32 : ℝ),
        Complex.exp (g s) = normalizedDirichletFamily χ s) ∧
      (∀ s ∈ Metric.closedBall (2 + (t : ℂ) * Complex.I) (1 / 2 : ℝ),
        ‖g s‖ ≤ 6) :=
  normalizedDirichletFamily_inner_log_on_logarithm_ball
    fixedHalfPlaneProperty_of_OAISource _hq χ t

/-- The full conditional normalized-family conclusion from blueprint
`lrc:normalized-family`: outer-disk analyticity, nonvanishing, the exact
`4q(|t|+4)` bound, and the norm-six analytic logarithm on the inner disk. -/
theorem normalizedDirichletFamily_spec
    (hZFR : fixedHalfPlaneProperty)
    {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    (χ : _root_.DirichletCharacter ℂ q) (t : ℝ) :
    AnalyticOnNhd ℂ (normalizedDirichletFamily χ)
        (Metric.ball (2 + (t : ℂ) * Complex.I) (35 / 32 : ℝ)) ∧
    (∀ s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (35 / 32 : ℝ),
      normalizedDirichletFamily χ s ≠ 0) ∧
    (∀ s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (35 / 32 : ℝ),
      ‖normalizedDirichletFamily χ s‖ ≤ 4 * (q : ℝ) * (|t| + 4)) ∧
    (∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g
        (Metric.ball (2 + (t : ℂ) * Complex.I) (17 / 32 : ℝ)) ∧
      (∀ s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (17 / 32 : ℝ),
        Complex.exp (g s) = normalizedDirichletFamily χ s) ∧
      (∀ s ∈ Metric.closedBall (2 + (t : ℂ) * Complex.I) (1 / 2 : ℝ),
        ‖g s‖ ≤ 6)) := by
  refine ⟨analyticOnNhd_normalizedDirichletFamily_on_logarithm_ball χ t, ?_, ?_, ?_⟩
  · intro s hs
    exact normalizedDirichletFamily_ne_zero_on_logarithm_ball_of_fixedHalfPlane
      hZFR χ t hs
  · intro s hs
    exact norm_normalizedDirichletFamily_le_on_logarithm_ball hq χ t hs
  · exact normalizedDirichletFamily_inner_log_on_logarithm_ball hZFR hq χ t

#print axioms normalizedDirichletFamily_inner_log_on_logarithm_ball
#print axioms fixedHalfPlaneProperty_of_OAISource
#print axioms principalRegularizedEulerLog_spec
#print axioms normalizedDirichletFamily_inner_log_on_logarithm_ball_of_OAISource
#print axioms normalizedDirichletFamily_spec

end FractionalPrimes.Literature.Reciprocal

end
