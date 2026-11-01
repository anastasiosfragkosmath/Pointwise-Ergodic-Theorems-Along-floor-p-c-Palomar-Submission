module

public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletDifferentiability
public import FractionalPrimes.Literature.Reciprocal.ContinuedDirichletSeriesIdentity
public import Mathlib.Analysis.Complex.Convex

@[expose] public section

noncomputable section

open Set
open scoped Topology

namespace FractionalPrimes.Literature.Reciprocal

/-- The nonprincipal integral continuation agrees with Mathlib's named
Dirichlet L-function throughout the open right half-plane. -/
theorem nonprincipalContinuedDirichletL_eq_LFunction_of_pos_re
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q)
    (hχ : χ ≠ FractionalPrimes.Literature.Twisted.principalCharacter q)
    {s : ℂ} (hs : 0 < s.re) :
    nonprincipalContinuedDirichletL χ hχ s hs =
      _root_.DirichletCharacter.LFunction χ s := by
  let H : Set ℂ := {z | 0 < z.re}
  have hH_open : IsOpen H := by
    change IsOpen {z : ℂ | 0 < z.re}
    exact isOpen_lt continuous_const Complex.continuous_re
  have hH_preconnected : IsPreconnected H := by
    change IsPreconnected {z : ℂ | 0 < z.re}
    exact (convex_halfSpace_re_gt (r := 0)).isPreconnected
  have hχ_one : χ ≠ 1 := by
    simpa [FractionalPrimes.Literature.Twisted.principalCharacter] using hχ
  have hcontinued_analytic :
      AnalyticOnNhd ℂ (nonprincipalContinuedDirichletLCore χ) H :=
    DifferentiableOn.analyticOnNhd
      (fun z hz =>
        (nonprincipalContinuedDirichletL_differentiableAt χ hχ
          (by simpa [H] using hz)).differentiableWithinAt)
      hH_open
  have hL_analytic :
      AnalyticOnNhd ℂ (_root_.DirichletCharacter.LFunction χ) H :=
    DifferentiableOn.analyticOnNhd
      (fun z _ =>
        (_root_.DirichletCharacter.differentiableAt_LFunction χ z
          (Or.inr hχ_one)).differentiableWithinAt)
      hH_open
  have htwo : (2 : ℂ) ∈ H := by
    simp [H]
  have hRe_gt_one : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heventually :
      nonprincipalContinuedDirichletLCore χ =ᶠ[𝓝 (2 : ℂ)]
        _root_.DirichletCharacter.LFunction χ := by
    filter_upwards [hRe_gt_one.mem_nhds (by norm_num : 1 < (2 : ℂ).re)] with z hz
    have hz_pos : 0 < z.re := by linarith
    calc
      nonprincipalContinuedDirichletLCore χ z =
          nonprincipalContinuedDirichletL χ hχ z hz_pos := by
        exact (nonprincipalContinuedDirichletL_eq_core χ hχ z hz_pos).symm
      _ = _root_.DirichletCharacter.LFunction χ z := by
        exact nonprincipalContinuedDirichletL_eq_LFunction_of_one_lt_re χ hχ hz
  have heqOn := hcontinued_analytic.eqOn_of_preconnected_of_eventuallyEq
    hL_analytic hH_preconnected htwo heventually
  calc
    nonprincipalContinuedDirichletL χ hχ s hs =
        nonprincipalContinuedDirichletLCore χ s :=
      nonprincipalContinuedDirichletL_eq_core χ hχ s hs
    _ = _root_.DirichletCharacter.LFunction χ s :=
      heqOn (by simpa [H] using hs)

#print axioms nonprincipalContinuedDirichletL_eq_LFunction_of_pos_re

end FractionalPrimes.Literature.Reciprocal

end
