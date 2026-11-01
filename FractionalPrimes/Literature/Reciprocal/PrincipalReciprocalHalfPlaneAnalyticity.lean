module
public import FractionalPrimes.Literature.Reciprocal.NormalizedDirichletFamilyInnerLog
public import FractionalPrimes.Literature.Reciprocal.PrincipalReciprocalExtension
@[expose] public section

noncomputable section

open Complex Set

namespace FractionalPrimes.Literature.Reciprocal

private theorem continuedDirichletH0Total_ne_zero_of_fixedHalfPlane
    (hZFR : fixedHalfPlaneProperty) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    continuedDirichletH0Total s ≠ 0 := by
  have hspos : 0 < s.re := by linarith
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
        continuedDirichletL (1 : _root_.DirichletCharacter ℂ 1) s hspos
          hnotpole₁ ≠ 0 :=
      hZFR (q := 1) (1 : _root_.DirichletCharacter ℂ 1) hs hnotpole₁
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
    simpa [continuedDirichletH0Total_eq hspos] using hH0

#print axioms continuedDirichletH0Total_ne_zero_of_fixedHalfPlane

/-- Under the exact zero-free half-plane hypothesis `ZFR_{7/8}`, the
regularized reciprocal of the principal Dirichlet function is analytic on
the full half-plane `Re(s) > 7/8`. This is the principal-branch analytic
continuation needed for `lrc:twisted-rectangle`; the assigned zero at `s=1`
is included in the domain. -/
theorem analyticOnNhd_continuedDirichletPrincipalReciprocal_of_fixedHalfPlane
    (hZFR : fixedHalfPlaneProperty) :
    AnalyticOnNhd ℂ continuedDirichletPrincipalReciprocal
      {s : ℂ | (7 / 8 : ℝ) < s.re} := by
  let U : Set ℂ := {s : ℂ | (7 / 8 : ℝ) < s.re}
  have hH0analytic : AnalyticOnNhd ℂ continuedDirichletH0Total U := by
    apply analyticOnNhd_continuedDirichletH0Total.mono
    intro s hs
    exact lt_trans (by norm_num : (0 : ℝ) < 7 / 8) hs
  have hnum : AnalyticOnNhd ℂ (fun s : ℂ => s - 1) U :=
    analyticOnNhd_id.sub analyticOnNhd_const
  have hplus : AnalyticOnNhd ℂ (fun s : ℂ => s + 1) U :=
    analyticOnNhd_id.add analyticOnNhd_const
  have hden : AnalyticOnNhd ℂ
      (fun s : ℂ => (s + 1) * continuedDirichletH0Total s) U :=
    hplus.mul hH0analytic
  have hden_ne : ∀ s ∈ U,
      (s + 1) * continuedDirichletH0Total s ≠ 0 := by
    intro s hs
    have hsplus : s + 1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      change (7 / 8 : ℝ) < s.re at hs
      linarith
    exact mul_ne_zero hsplus
      (continuedDirichletH0Total_ne_zero_of_fixedHalfPlane hZFR hs)
  change AnalyticOnNhd ℂ
    (fun s : ℂ => (s - 1) / ((s + 1) * continuedDirichletH0Total s)) U
  exact hnum.div hden hden_ne

#print axioms analyticOnNhd_continuedDirichletPrincipalReciprocal_of_fixedHalfPlane

end FractionalPrimes.Literature.Reciprocal

end
