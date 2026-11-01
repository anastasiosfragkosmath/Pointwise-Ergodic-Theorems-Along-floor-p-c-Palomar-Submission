module
public import FractionalPrimes.Literature.Reciprocal.FixedHalfPlaneOfE1
public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletPrincipalAnalyticity
public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletNormEstimate
public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletPrincipalBounds
@[expose] public section

@[expose] public section

open Complex Set
open scoped Topology

namespace FractionalPrimes.Literature.Reciprocal

/-- The normalized branch used on the logarithm discs in blueprint
`lrc:normalized-family`: use the nonprincipal continuation for nonprincipal
characters and the pole-regularized zeta function for the principal branch. -/
noncomputable def normalizedDirichletFamily {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  if χ = FractionalPrimes.Literature.Twisted.principalCharacter q then
    continuedDirichletH0Total s
  else nonprincipalContinuedDirichletLCore χ s

private theorem normalizedDirichletFamily_analyticOnNhd_pos_re
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (normalizedDirichletFamily χ) {s : ℂ | 0 < s.re} := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  have hopen : IsOpen U := by
    dsimp [U]
    exact isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (normalizedDirichletFamily χ) U := by
    intro s hs
    change 0 < s.re at hs
    by_cases hχ : χ = FractionalPrimes.Literature.Twisted.principalCharacter q
    · have hfun : normalizedDirichletFamily χ = continuedDirichletH0Total := by
        funext z
        simp [normalizedDirichletFamily, hχ]
      rw [hfun]
      exact (differentiableAt_continuedDirichletH0Total hs).differentiableWithinAt
    · have hfun : normalizedDirichletFamily χ =
          fun z => nonprincipalContinuedDirichletLCore χ z := by
        funext z
        simp [normalizedDirichletFamily, hχ]
      rw [hfun]
      exact (nonprincipalContinuedDirichletL_differentiableAt χ hχ hs).differentiableWithinAt
  exact hdiff.analyticOnNhd hopen

private theorem normalizedDirichletFamily_ball_geometry {t : ℝ} {s : ℂ}
    (hs : s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (35 / 32 : ℝ)) :
    (29 / 32 : ℝ) < s.re ∧ ‖s‖ ≤ |t| + 4 := by
  let c : ℂ := 2 + (t : ℂ) * Complex.I
  have hdist : ‖s - c‖ < (35 / 32 : ℝ) := by
    have h := Metric.mem_ball.mp hs
    simpa [dist_eq_norm, c] using h
  have hreDist : |s.re - 2| ≤ ‖s - c‖ := by
    simpa [c, Complex.sub_re] using Complex.abs_re_le_norm (s - c)
  have hlow : 2 - s.re < (35 / 32 : ℝ) := by
    calc
      2 - s.re ≤ |s.re - 2| := by
        calc
          2 - s.re = -(s.re - 2) := by ring
          _ ≤ |-(s.re - 2)| := le_abs_self _
          _ = |s.re - 2| := by rw [abs_neg]
      _ ≤ ‖s - c‖ := hreDist
      _ < (35 / 32 : ℝ) := hdist
  have htri : ‖s‖ ≤ ‖s - c‖ + ‖c‖ := by
    calc
      ‖s‖ = ‖(s - c) + c‖ := by rw [show (s - c) + c = s by abel]
      _ ≤ ‖s - c‖ + ‖c‖ := norm_add_le _ _
  have hc : ‖c‖ ≤ 2 + |t| := by
    dsimp [c]
    calc
      ‖(2 : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ = 2 + |t| := by simp
  refine ⟨?_, ?_⟩
  · have : s.re > 2 - (35 / 32 : ℝ) := by linarith
    norm_num at this ⊢
    linarith
  · calc
      ‖s‖ ≤ ‖s - c‖ + ‖c‖ := htri
      _ ≤ (35 / 32 : ℝ) + (2 + |t|) := add_le_add hdist.le hc
      _ ≤ |t| + 4 := by linarith

/-- The normalized branch is analytic on each outer disk in the approved
`lrc:normalized-family` statement. -/
theorem analyticOnNhd_normalizedDirichletFamily_on_logarithm_ball
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) (t : ℝ) :
    AnalyticOnNhd ℂ (normalizedDirichletFamily χ)
      (Metric.ball (2 + (t : ℂ) * Complex.I) (35 / 32 : ℝ)) := by
  apply (normalizedDirichletFamily_analyticOnNhd_pos_re χ).mono
  intro s hs
  change 0 < s.re
  exact (lt_trans (by norm_num : (0 : ℝ) < 29 / 32)
    (normalizedDirichletFamily_ball_geometry hs).1)

/-- The exact outer-disk bound in blueprint `lrc:normalized-family`. -/
theorem norm_normalizedDirichletFamily_le_on_logarithm_ball
    {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    (χ : _root_.DirichletCharacter ℂ q) (t : ℝ) {s : ℂ}
    (hs : s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (35 / 32 : ℝ)) :
    ‖normalizedDirichletFamily χ s‖ ≤ 4 * (q : ℝ) * (|t| + 4) := by
  obtain ⟨hsre, hsnorm⟩ := normalizedDirichletFamily_ball_geometry hs
  have hspos : 0 < s.re := by linarith
  have hinv : 1 / s.re ≤ 2 := by
    calc
      1 / s.re ≤ 1 / (29 / 32 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      _ = 32 / 29 := by norm_num
      _ ≤ 2 := by norm_num
  have hratio : ‖s‖ / s.re ≤ 2 * (|t| + 4) := by
    calc
      ‖s‖ / s.re = ‖s‖ * (1 / s.re) := by ring
      _ ≤ (|t| + 4) * 2 :=
        mul_le_mul hsnorm hinv (by positivity) (by positivity)
      _ = 2 * (|t| + 4) := by ring
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  by_cases hχ : χ = FractionalPrimes.Literature.Twisted.principalCharacter q
  · simp only [normalizedDirichletFamily, if_pos hχ]
    calc
      ‖continuedDirichletH0Total s‖ = ‖continuedDirichletH0 s hspos‖ := by
        rw [continuedDirichletH0Total_eq hspos]
      _ ≤ 1 + ‖s‖ / s.re :=
        norm_continuedDirichletH0_le_of_pos_re hspos
      _ ≤ 1 + 2 * (|t| + 4) := by linarith [hratio]
      _ ≤ 4 * (q : ℝ) * (|t| + 4) := by
        have ht : 0 ≤ |t| + 4 := by positivity
        have ht4 : 4 ≤ |t| + 4 := by linarith [abs_nonneg t]
        have hsmall : 1 + 2 * (|t| + 4) ≤ 4 * (|t| + 4) := by nlinarith
        have hlarge : 4 * (|t| + 4) ≤ 4 * (q : ℝ) * (|t| + 4) := by
          calc
            4 * (|t| + 4) = 4 * (1 * (|t| + 4)) := by ring
            _ ≤ 4 * ((q : ℝ) * (|t| + 4)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hqreal ht) (by norm_num)
            _ = 4 * (q : ℝ) * (|t| + 4) := by ring
        exact hsmall.trans hlarge
  · simp only [normalizedDirichletFamily, if_neg hχ]
    have hcore :
        nonprincipalContinuedDirichletLCore χ s =
          nonprincipalContinuedDirichletL χ hχ s hspos :=
      (nonprincipalContinuedDirichletL_eq_core χ hχ s hspos).symm
    rw [hcore]
    calc
      ‖nonprincipalContinuedDirichletL χ hχ s hspos‖ ≤
          (q : ℝ) * ‖s‖ / s.re :=
        norm_nonprincipalContinuedDirichletL_le_of_pos_re χ hχ s hspos
      _ ≤ (q : ℝ) * (2 * (|t| + 4)) := by
        have hqnonneg : 0 ≤ (q : ℝ) := by positivity
        calc
          (q : ℝ) * ‖s‖ / s.re = (q : ℝ) * (‖s‖ / s.re) := by ring
          _ ≤ (q : ℝ) * (2 * (|t| + 4)) := mul_le_mul_of_nonneg_left hratio hqnonneg
      _ ≤ 4 * (q : ℝ) * (|t| + 4) := by
        have hqnonneg : 0 ≤ (q : ℝ) := by positivity
        have ht : 0 ≤ |t| + 4 := by positivity
        nlinarith [mul_nonneg hqnonneg ht]

/-- The exact outer-disk nonvanishing required by `lrc:normalized-family`.
For the principal branch this uses the modulus-one instance of the approved
fixed-half-plane input and the exact regularization identity for `H₀`. -/
theorem normalizedDirichletFamily_ne_zero_on_logarithm_ball
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) (t : ℝ)
    {s : ℂ}
    (hs : s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (35 / 32 : ℝ)) :
    normalizedDirichletFamily χ s ≠ 0 := by
  have ⟨hsre, _⟩ := normalizedDirichletFamily_ball_geometry hs
  have hspos : 0 < s.re := by linarith
  have hs78 : (7 / 8 : ℝ) < s.re := by
    exact lt_trans (by norm_num : (7 / 8 : ℝ) < 29 / 32) hsre
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
        fixedHalfPlaneOfOAISource (1 : _root_.DirichletCharacter ℂ 1) hs78 hnotpole₁
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
    have hLne : continuedDirichletL χ s hspos hnotpole ≠ 0 :=
      fixedHalfPlaneOfOAISource χ hs78 hnotpole
    simpa [continuedDirichletL, normalizedDirichletFamily, hχ,
      nonprincipalContinuedDirichletL_eq_core] using hLne

#print axioms analyticOnNhd_normalizedDirichletFamily_on_logarithm_ball
#print axioms norm_normalizedDirichletFamily_le_on_logarithm_ball
#print axioms normalizedDirichletFamily_ne_zero_on_logarithm_ball

end FractionalPrimes.Literature.Reciprocal

end
