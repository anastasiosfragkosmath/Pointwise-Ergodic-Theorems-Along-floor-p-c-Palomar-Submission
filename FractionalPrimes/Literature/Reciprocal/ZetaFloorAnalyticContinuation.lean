module

public import FractionalPrimes.Literature.Reciprocal.ZetaFloorIdentity
public import Mathlib.Analysis.Complex.Convex

@[expose] public section

open Set
open scoped Topology

namespace FractionalPrimes.Literature.Reciprocal

/-- The floor-correction regular part agrees with Mathlib's entire regular
part of the Riemann zeta function throughout the open right half-plane.
This continuation includes `s = 1`; neither side is the pole-valued function
`riemannZeta` with its singular term left in place. -/
theorem zetaFloorRegularPart_eq_riemannZeta₀_of_pos_re {s : ℂ}
    (hs : 0 < s.re) : zetaFloorRegularPart s = riemannZeta₀ s := by
  let H : Set ℂ := {z | 0 < z.re}
  have hH_open : IsOpen H := by
    change IsOpen {z : ℂ | 0 < z.re}
    exact isOpen_lt continuous_const Complex.continuous_re
  have hH_preconnected : IsPreconnected H := by
    change IsPreconnected {z : ℂ | 0 < z.re}
    exact (convex_halfSpace_re_gt (r := 0)).isPreconnected
  have hregular_analytic : AnalyticOnNhd ℂ zetaFloorRegularPart H :=
    DifferentiableOn.analyticOnNhd
      (fun z hz =>
        (differentiableAt_zetaFloorRegularPart (by simpa [H] using hz)).differentiableWithinAt)
      hH_open
  have hzeta₀_analytic : AnalyticOnNhd ℂ riemannZeta₀ H :=
    DifferentiableOn.analyticOnNhd
      (fun z _ => differentiable_riemannZeta₀.differentiableAt.differentiableWithinAt)
      hH_open
  have htwo : (2 : ℂ) ∈ H := by
    simp [H]
  have hRe_gt_one : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heventually :
      zetaFloorRegularPart =ᶠ[𝓝 (2 : ℂ)] riemannZeta₀ := by
    filter_upwards [hRe_gt_one.mem_nhds (by norm_num : 1 < (2 : ℂ).re)] with z hz
    exact zetaFloorRegularPart_eq_riemannZeta₀_of_one_lt_re hz
  have heqOn := hregular_analytic.eqOn_of_preconnected_of_eventuallyEq
    hzeta₀_analytic hH_preconnected htwo heventually
  exact heqOn (by simpa [H] using hs)

#print axioms zetaFloorRegularPart_eq_riemannZeta₀_of_pos_re

end FractionalPrimes.Literature.Reciprocal
