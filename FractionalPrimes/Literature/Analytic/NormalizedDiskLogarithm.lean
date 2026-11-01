module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

noncomputable section

open Set Metric
open scoped Topology

namespace FractionalPrimes.Literature.Analytic

private theorem analyticLog_deriv_eq {a : ℂ} {R : ℝ} {H g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball a R))
    (hHne : ∀ z ∈ ball a R, H z ≠ 0)
    (hexp : ∀ z ∈ ball a R, Complex.exp (g z) = H z) :
    ∀ z ∈ ball a R, deriv g z = deriv H z / H z := by
  intro z hz
  have hlocal : (fun w : ℂ => Complex.exp (g w)) =ᶠ[𝓝 z] H := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hexp w hw
  have hderiv := hlocal.deriv_eq
  rw [deriv_cexp (hg z hz).differentiableAt, hexp z hz] at hderiv
  calc
    deriv g z = (H z)⁻¹ * (H z * deriv g z) := by
      field_simp [hHne z hz]
    _ = (H z)⁻¹ * deriv H z := by rw [hderiv]
    _ = deriv H z / H z := by rw [div_eq_mul_inv, mul_comm]

private theorem analyticLog_eq_of_base_eq {a : ℂ} {R : ℝ} {H f g : ℂ → ℂ}
    (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball a R))
    (hg : AnalyticOnNhd ℂ g (ball a R))
    (hHne : ∀ z ∈ ball a R, H z ≠ 0)
    (hfexp : ∀ z ∈ ball a R, Complex.exp (f z) = H z)
    (hgexp : ∀ z ∈ ball a R, Complex.exp (g z) = H z)
    (hbase : f a = g a) :
    ∀ z ∈ ball a R, f z = g z := by
  have hfderiv := analyticLog_deriv_eq hf hHne hfexp
  have hgderiv := analyticLog_deriv_eq hg hHne hgexp
  have hdiff : DifferentiableOn ℂ (fun z => f z - g z) (ball a R) := by
    intro z hz
    exact ((hf z hz).differentiableAt.sub (hg z hz).differentiableAt).differentiableWithinAt
  have hderivzero : ∀ z ∈ ball a R, deriv (fun z => f z - g z) z = 0 := by
    intro z hz
    have hsub := ((hf z hz).differentiableAt.hasDerivAt).sub
      ((hg z hz).differentiableAt.hasDerivAt)
    have hsubderiv : deriv (fun w : ℂ => f w - g w) z = deriv f z - deriv g z := by
      rw [show (fun w : ℂ => f w - g w) = f - g by rfl]
      exact hsub.deriv
    rw [hsubderiv, hfderiv z hz, hgderiv z hz]
    ring
  intro z hz
  have hconst := IsOpen.is_const_of_deriv_eq_zero isOpen_ball
    (convex_ball a R).isPreconnected hdiff hderivzero hz (mem_ball_self hR)
  have hzEq : f z - g z = 0 := by simpa [hbase] using hconst
  exact sub_eq_zero.mp hzEq

/-- The normalized analytic logarithm on a disk, with its derivative, real-part
identity, uniqueness, and compatibility with logarithms on smaller concentric
disks. This is the exact disk-logarithm result `lag:disk-logarithm`. -/
theorem normalizedDiskLogarithm {a : ℂ} {R : ℝ} (hR : 0 < R)
    {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H (ball a R))
    (hHne : ∀ z ∈ ball a R, H z ≠ 0)
    {b : ℂ} (hb : Complex.exp b = H a) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball a R) ∧
      (∀ z ∈ ball a R, Complex.exp (g z) = H z) ∧
      g a = b ∧
      (∀ z ∈ ball a R, deriv g z = deriv H z / H z) ∧
      (∀ z ∈ ball a R, (g z).re = Real.log ‖H z‖) ∧
      (∀ {r : ℝ}, 0 < r → r ≤ R → ∀ k : ℂ → ℂ,
        AnalyticOnNhd ℂ k (ball a r) →
        (∀ z ∈ ball a r, Complex.exp (k z) = H z) →
        k a = b → ∀ z ∈ ball a r, g z = k z) ∧
      (∀ g' : ℂ → ℂ, AnalyticOnNhd ℂ g' (ball a R) →
        (∀ z ∈ ball a R, Complex.exp (g' z) = H z) →
        g' a = b → ∀ z ∈ ball a R, g z = g' z) := by
  let logDeriv : ℂ → ℂ := fun z => deriv H z / H z
  have hlogDerivAnalytic : AnalyticOnNhd ℂ logDeriv (ball a R) := by
    intro z hz
    exact (hH.deriv z hz).div (hH z hz) (hHne z hz)
  have hlogDerivDiff : DifferentiableOn ℂ logDeriv (ball a R) := by
    intro z hz
    exact (hlogDerivAnalytic z hz).differentiableAt.differentiableWithinAt
  obtain ⟨F, hF⟩ := DifferentiableOn.isExactOn_ball hlogDerivDiff
  let g : ℂ → ℂ := fun z => F z + (b - F a)
  have hGderivAt : ∀ z ∈ ball a R, HasDerivAt g (logDeriv z) z := by
    intro z hz
    simpa [g] using (hF z hz).add_const (b - F a)
  have hGdiff : DifferentiableOn ℂ g (ball a R) := by
    intro z hz
    exact (hGderivAt z hz).differentiableAt.differentiableWithinAt
  have hGanalytic : AnalyticOnNhd ℂ g (ball a R) :=
    hGdiff.analyticOnNhd isOpen_ball
  have hGbase : g a = b := by
    simp [g]
  let K : ℂ → ℂ := fun z => H z * Complex.exp (-g z)
  have hKderivAt : ∀ z ∈ ball a R,
      HasDerivAt K
        (deriv H z * Complex.exp (-g z) +
          H z * (Complex.exp (-g z) * (-logDeriv z))) z := by
    intro z hz
    have hHd : HasDerivAt H (deriv H z) z := (hH z hz).differentiableAt.hasDerivAt
    have hneg : HasDerivAt (fun w : ℂ => -g w) (-logDeriv z) z :=
      (hGderivAt z hz).neg
    have hexp : HasDerivAt (fun w : ℂ => Complex.exp (-g w))
        (Complex.exp (-g z) * (-logDeriv z)) z := hneg.cexp
    change HasDerivAt (fun w : ℂ => H w * Complex.exp (-g w)) _ z
    exact hHd.mul hexp
  have hKdiff : DifferentiableOn ℂ K (ball a R) := by
    intro z hz
    exact (hKderivAt z hz).differentiableAt.differentiableWithinAt
  have hKderivzero : ∀ z ∈ ball a R, deriv K z = 0 := by
    intro z hz
    rw [(hKderivAt z hz).deriv]
    dsimp [logDeriv]
    field_simp [hHne z hz]
    ring
  have hKa : K a = 1 := by
    calc
      K a = H a * Complex.exp (-b) := by simp [K, hGbase]
      _ = Complex.exp b * Complex.exp (-b) := by rw [← hb]
      _ = 1 := by rw [← Complex.exp_add]; simp
  have hKconst : ∀ z ∈ ball a R, K z = 1 := by
    intro z hz
    have hconst := IsOpen.is_const_of_deriv_eq_zero isOpen_ball
      (convex_ball a R).isPreconnected hKdiff hKderivzero
      hz (mem_ball_self hR)
    simpa [hKa] using hconst
  have hGexp : ∀ z ∈ ball a R, Complex.exp (g z) = H z := by
    intro z hz
    have hKz : H z * Complex.exp (-g z) = 1 := by
      simpa [K] using hKconst z hz
    have hcancel : Complex.exp (-g z) * Complex.exp (g z) = 1 := by
      rw [← Complex.exp_add]
      simp
    have hEq : H z = Complex.exp (g z) := by
      calc
        H z = H z * (Complex.exp (-g z) * Complex.exp (g z)) := by
          rw [hcancel, mul_one]
        _ = (H z * Complex.exp (-g z)) * Complex.exp (g z) := by rw [mul_assoc]
        _ = Complex.exp (g z) := by rw [hKz]; simp
    exact hEq.symm
  have hGderiv : ∀ z ∈ ball a R, deriv g z = deriv H z / H z := by
    intro z hz
    simpa [logDeriv] using (hGderivAt z hz).deriv
  have hGre : ∀ z ∈ ball a R, (g z).re = Real.log ‖H z‖ := by
    intro z hz
    rw [← hGexp z hz, Complex.norm_exp, Real.log_exp]
  refine ⟨g, ?_⟩
  refine ⟨hGanalytic, ?_⟩
  refine ⟨hGexp, ?_⟩
  refine ⟨hGbase, ?_⟩
  refine ⟨hGderiv, ?_⟩
  refine ⟨hGre, ?_⟩
  constructor
  · intro r hr hrR k hk hkexp hkbase z hz
    have hHsmall : AnalyticOnNhd ℂ H (ball a r) :=
      hH.mono (Metric.ball_subset_ball hrR)
    have hGsmall : AnalyticOnNhd ℂ g (ball a r) :=
      hGanalytic.mono (Metric.ball_subset_ball hrR)
    have hHneSmall : ∀ w ∈ ball a r, H w ≠ 0 := fun w hw => hHne w
      (Metric.ball_subset_ball hrR hw)
    exact (analyticLog_eq_of_base_eq hr hk hGsmall hHneSmall
      hkexp (fun w hw => hGexp w (Metric.ball_subset_ball hrR hw))
      (by rw [hkbase, hGbase]) z hz).symm
  · intro g' hg' hG'exp hG'base z hz
    exact analyticLog_eq_of_base_eq hR hGanalytic hg' hHne hGexp hG'exp
      (by rw [hGbase, hG'base]) z hz

#print axioms normalizedDiskLogarithm

end FractionalPrimes.Literature.Analytic

end
