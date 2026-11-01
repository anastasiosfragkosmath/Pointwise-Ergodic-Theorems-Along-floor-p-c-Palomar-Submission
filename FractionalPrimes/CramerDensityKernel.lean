module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Derivative kernel for the Cramér Euler-product estimate

This standalone calculus lemma is the local analytic input to the weighted
theta partial-summation identity in `lc:product`.
-/

@[expose] public section

open MeasureTheory

namespace FractionalPrimes

noncomputable section

def reciprocalThetaKernel (t : ℝ) : ℝ :=
  (t * Real.log t)⁻¹

theorem reciprocalThetaKernel_deriv {t : ℝ} (ht : 1 < t) :
    deriv reciprocalThetaKernel t =
      -((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
  have htpos : 0 < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have htne : t ≠ 0 := ne_of_gt htpos
  have hlogne : Real.log t ≠ 0 := ne_of_gt hlogpos
  have hdiffId : DifferentiableAt ℝ (fun x : ℝ => x) t := differentiableAt_id
  have hdiffLog : DifferentiableAt ℝ Real.log t := Real.differentiableAt_log htne
  have hdiffMul : DifferentiableAt ℝ (fun x : ℝ => x * Real.log x) t :=
    hdiffId.mul hdiffLog
  have hmulne : t * Real.log t ≠ 0 := mul_ne_zero htne hlogne
  have hmulFun :
      (fun x : ℝ => x * Real.log x) = (fun x : ℝ => x) * Real.log := rfl
  change deriv (fun x : ℝ => (x * Real.log x)⁻¹) t = _
  rw [deriv_fun_inv'' hdiffMul hmulne, hmulFun, deriv_mul hdiffId hdiffLog,
    deriv_id'', Real.deriv_log]
  field_simp [htne, hlogne]
  <;> ring

/-- The reciprocal-theta derivative is integrable on every compact interval
whose left endpoint is at least `2`. -/
theorem reciprocalThetaKernel_deriv_integrable {z : ℝ} (hz : 2 ≤ z) :
    IntegrableOn (deriv reciprocalThetaKernel) (Set.Icc 2 z) volume := by
  have hformula : ∀ t ∈ Set.Icc (2 : ℝ) z,
      deriv reciprocalThetaKernel t =
        -((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
    intro t ht
    exact reciprocalThetaKernel_deriv (by linarith [ht.1])
  have hlogpos : ∀ t ∈ Set.Icc (2 : ℝ) z, 0 < Real.log t := by
    intro t ht
    exact Real.log_pos (by linarith [ht.1])
  have hlogcont : ContinuousOn Real.log (Set.Icc 2 z) := by
    refine ContinuousOn.mono Real.continuousOn_log ?_
    intro t ht
    exact ne_of_gt (by linarith [ht.1])
  have htne : ∀ t ∈ Set.Icc (2 : ℝ) z, t ≠ 0 := by
    intro t ht
    exact ne_of_gt (by linarith [ht.1])
  have hnum : ContinuousOn (fun t : ℝ => Real.log t + 1) (Set.Icc 2 z) :=
    hlogcont.add continuousOn_const
  have hden : ContinuousOn
      (fun t : ℝ => t ^ 2 * (Real.log t) ^ 2) (Set.Icc 2 z) :=
    (continuousOn_id.pow 2).mul (hlogcont.pow 2)
  have hden_ne : ∀ t ∈ Set.Icc (2 : ℝ) z,
      t ^ 2 * (Real.log t) ^ 2 ≠ 0 := by
    intro t ht
    exact mul_ne_zero (pow_ne_zero 2 (htne t ht))
      (pow_ne_zero 2 (ne_of_gt (hlogpos t ht)))
  have hcont : ContinuousOn
      (fun t : ℝ => -((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      (Set.Icc 2 z) :=
    (hnum.div hden hden_ne).neg
  have hderiv_cont : ContinuousOn (deriv reciprocalThetaKernel) (Set.Icc 2 z) :=
    hcont.congr hformula
  exact hderiv_cont.integrableOn_compact isCompact_Icc

end
end FractionalPrimes
