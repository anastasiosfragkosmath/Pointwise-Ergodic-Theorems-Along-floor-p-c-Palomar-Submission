module

public import FractionalPrimes.Literature.JSW.FoundationBoundary
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Fixed real-line cutoffs for the JSW conventions

`φ` is the integral-one normalization of Mathlib's even smooth bump with
inner radius `1/2` and outer radius `3/4`.  `χ` is the even bump with inner
radius `1` and outer radius `3/2`.  These choices satisfy the support and
plateau conditions in `lj:conventions`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.JSW

open Set Metric MeasureTheory
open scoped ContDiff

noncomputable section

/-- The fixed bump used to construct the unit-integral cutoff `φ`. -/
def phiBump : ContDiffBump (0 : ℝ) :=
  ⟨(1 / 2 : ℝ), (3 / 4 : ℝ), by norm_num, by norm_num⟩

/-- The fixed even, nonnegative, unit-integral cutoff. -/
def φ : ℝ → ℝ := phiBump.normed volume

theorem phi_even (x : ℝ) : φ (-x) = φ x :=
  phiBump.normed_neg x

theorem phi_nonneg (x : ℝ) : 0 ≤ φ x :=
  phiBump.nonneg_normed x

theorem phi_contDiff : ContDiff ℝ (∞ : ℕ∞ω) φ :=
  phiBump.contDiff_normed

theorem phi_hasCompactSupport : HasCompactSupport φ :=
  phiBump.hasCompactSupport_normed

theorem integral_phi : ∫ x, φ x ∂volume = 1 :=
  phiBump.integral_normed

theorem tsupport_phi : tsupport φ = Metric.closedBall (0 : ℝ) (3 / 4 : ℝ) :=
  phiBump.tsupport_normed_eq

theorem tsupport_phi_subset : tsupport φ ⊆ Icc (-(1 : ℝ)) 1 := by
  rw [tsupport_phi]
  intro x hx
  have hxabs : |x| ≤ (3 / 4 : ℝ) := by
    simpa [Real.dist_eq] using hx
  have hx' := abs_le.mp hxabs
  exact ⟨by linarith, by linarith⟩

/-- The fixed even real-valued cutoff `χ`. -/
def chiBump : ContDiffBump (0 : ℝ) :=
  ⟨(1 : ℝ), (3 / 2 : ℝ), by norm_num, by norm_num⟩

def χ : ℝ → ℝ := chiBump

theorem chi_even (x : ℝ) : χ (-x) = χ x :=
  chiBump.neg x

theorem chi_nonneg (x : ℝ) : 0 ≤ χ x :=
  chiBump.nonneg

theorem chi_le_one (x : ℝ) : χ x ≤ 1 :=
  chiBump.le_one

theorem chi_eq_one_of_abs_le (x : ℝ) (hx : |x| ≤ 1) : χ x = 1 := by
  apply chiBump.one_of_mem_closedBall
  change dist x 0 ≤ (1 : ℝ)
  simpa [Real.dist_eq] using hx

theorem chi_contDiff : ContDiff ℝ (∞ : ℕ∞ω) χ :=
  chiBump.contDiff

theorem chi_hasCompactSupport : HasCompactSupport χ :=
  chiBump.hasCompactSupport

theorem tsupport_chi : tsupport χ = Metric.closedBall (0 : ℝ) (3 / 2 : ℝ) :=
  chiBump.tsupport_eq

theorem tsupport_chi_subset : tsupport χ ⊆ Ioo (-(2 : ℝ)) 2 := by
  rw [tsupport_chi]
  intro x hx
  have hxabs : |x| ≤ (3 / 2 : ℝ) := by
    simpa [Real.dist_eq] using hx
  have hx' := abs_le.mp hxabs
  exact ⟨by linarith, by linarith⟩

end

end FractionalPrimes.Literature.JSW

end
