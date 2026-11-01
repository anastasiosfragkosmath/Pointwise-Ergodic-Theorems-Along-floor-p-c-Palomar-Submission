module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace FractionalPrimes.Literature.Reciprocal

/-- The exact auxiliary logarithm from `lrc:regularized-principal`. -/
def principalRegularizedLogB (s : ℂ) : ℂ :=
  -∫ u : ℝ in (-1 : ℝ)..1, (s + (u : ℂ))⁻¹

private theorem principalRegularizedLogB_eq_log_sub {s : ℂ} (hs : 1 < s.re) :
    principalRegularizedLogB s = Complex.log (s - 1) - Complex.log (s + 1) := by
  let f : ℝ → ℂ := fun u => Complex.log (s + (u : ℂ))
  let g : ℝ → ℂ := fun u => (s + (u : ℂ))⁻¹
  have hderiv : ∀ u ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt f (g u) u := by
    intro u hu
    have hu' : u ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hu
    have hmem : s + (u : ℂ) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      have hure : (-1 : ℝ) ≤ u := hu'.1
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    have hlin : HasDerivAt (fun x : ℝ => s + (x : ℂ)) (1 : ℂ) u := by
      simpa [add_comm] using ((hasDerivAt_id u).ofReal_comp.const_add s)
    have hlog := hlin.clog_real hmem
    simpa [f, g, div_eq_mul_inv] using hlog
  have hint : IntervalIntegrable g volume (-1 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro u hu hz
    have hu' : u ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hu
    have hre : 0 < (s + (u : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [hs, hu'.1]
    have hz0 : s + (u : ℂ) = 0 := by simpa using hz
    have hre0 := congrArg Complex.re hz0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre0
    exact (ne_of_gt hre) hre0
  have hintegral := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  unfold principalRegularizedLogB
  dsimp [f] at hintegral
  rw [hintegral]
  simp only [Complex.ofReal_one, Complex.ofReal_neg, sub_eq_add_neg]
  ring

/-- `B` is analytic throughout the open half-plane `Re(s)>1`. -/
theorem differentiableOn_principalRegularizedLogB :
    DifferentiableOn ℂ principalRegularizedLogB {s : ℂ | 1 < s.re} := by
  have hlogs : DifferentiableOn ℂ
      (fun s : ℂ => Complex.log (s - 1) - Complex.log (s + 1))
      {s : ℂ | 1 < s.re} := by
    intro s hs
    change 1 < s.re at hs
    have hminus : s - 1 ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hplus : s + 1 ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simp only [Complex.add_re, Complex.one_re]
      linarith
    exact (((differentiableAt_id.sub_const (1 : ℂ)).clog hminus).sub
      ((differentiableAt_id.add_const (1 : ℂ)).clog hplus)).differentiableWithinAt
  apply hlogs.congr
  intro s hs
  exact principalRegularizedLogB_eq_log_sub hs

/-- The integral-defined `B` is analytic on the open half-plane in the
blueprint. -/
theorem analyticOnNhd_principalRegularizedLogB :
    AnalyticOnNhd ℂ principalRegularizedLogB {s : ℂ | 1 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact differentiableOn_principalRegularizedLogB.analyticOnNhd hopen

/-- The exponential of the exact integral-defined logarithm is the approved
principal factor on `Re(s)>1`. -/
theorem exp_principalRegularizedLogB {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (principalRegularizedLogB s) = (s - 1) / (s + 1) := by
  have hminus : s - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hplus : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  rw [principalRegularizedLogB_eq_log_sub hs, Complex.exp_sub,
    Complex.exp_log hminus, Complex.exp_log hplus]

/-- The exact interval-integral bound for `B`. -/
theorem norm_principalRegularizedLogB_le_two_div_re_sub_one {s : ℂ}
    (hs : 1 < s.re) :
    ‖principalRegularizedLogB s‖ ≤ 2 / (s.re - 1) := by
  have hgap : 0 < s.re - 1 := by linarith
  have hpoint : ∀ u ∈ Set.uIoc (-1 : ℝ) 1,
      ‖(s + (u : ℂ))⁻¹‖ ≤ 1 / (s.re - 1) := by
    intro u hu
    have hure : (-1 : ℝ) ≤ u := by
      have hu' : -1 < u ∧ u ≤ 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hu
      exact hu'.1.le
    have hnorm : s.re - 1 ≤ ‖s + (u : ℂ)‖ := by
      calc
        s.re - 1 ≤ (s + (u : ℂ)).re := by
          simp only [Complex.add_re, Complex.ofReal_re]
          linarith
        _ ≤ |(s + (u : ℂ)).re| := le_abs_self _
        _ ≤ ‖s + (u : ℂ)‖ := Complex.abs_re_le_norm _
    rw [norm_inv]
    simpa [one_div] using one_div_le_one_div_of_le hgap hnorm
  calc
    ‖principalRegularizedLogB s‖ =
        ‖∫ u : ℝ in (-1 : ℝ)..1, (s + (u : ℂ))⁻¹‖ := by
          simp [principalRegularizedLogB]
    _ ≤ (1 / (s.re - 1)) * |(1 : ℝ) - (-1 : ℝ)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = 2 / (s.re - 1) := by ring

/-- On the closed half-plane `Re(s)≥3/2`, the bound in the blueprint is 4. -/
theorem norm_principalRegularizedLogB_le_four {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    ‖principalRegularizedLogB s‖ ≤ 4 := by
  have hs' : 1 < s.re := by linarith
  have h := norm_principalRegularizedLogB_le_two_div_re_sub_one hs'
  have hgap : (1 / 2 : ℝ) ≤ s.re - 1 := by linarith
  have hsmall : 2 / (s.re - 1) ≤ 4 := by
    calc
      2 / (s.re - 1) ≤ 2 / (1 / 2 : ℝ) := by
        gcongr
      _ = 4 := by norm_num
  exact h.trans hsmall

#print axioms differentiableOn_principalRegularizedLogB
#print axioms analyticOnNhd_principalRegularizedLogB
#print axioms exp_principalRegularizedLogB
#print axioms norm_principalRegularizedLogB_le_four

end FractionalPrimes.Literature.Reciprocal

end
