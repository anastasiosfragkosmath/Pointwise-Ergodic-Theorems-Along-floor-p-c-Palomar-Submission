module

public import Mathlib.Analysis.Normed.Lp.lpSpace

@[expose] public section

/-!
# Exhaustion from uniform finite-set moment bounds

For a finite, positive real exponent, a uniform bound on all finite partial
moments gives the corresponding `Memℓp` witness.  The same finite-set bounds
also give the exact sequence norm estimate.  This is the general exhaustion
step needed to pass from estimates uniform in a finite output set to the
full sequence-space conclusion.
-/

namespace FractionalPrimes

open scoped ENNReal

universe u v

variable {α : Type u} {E : α → Type v}
variable [∀ i, NormedAddCommGroup (E i)]

/-- Uniform bounds for all finite partial `p`-moments imply `Memℓp` at any
finite positive exponent. -/
theorem memlp_of_uniform_finite_moment_bound
    {p : ℝ≥0∞} (f : ∀ i, E i) {C : ℝ}
    (hfinite : ∀ s : Finset α, ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C) :
    Memℓp f p := by
  exact memℓp_gen' hfinite

/-- The `lp` vector obtained from uniform finite-set moment bounds. -/
def lpOfUniformFiniteMomentBound
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (f : ∀ i, E i) {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ s : Finset α, ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C) : lp E p :=
  ⟨f, memlp_of_uniform_finite_moment_bound f hfinite⟩

/-- The exhaustion constructor retains the original pointwise function. -/
@[simp] theorem lpOfUniformFiniteMomentBound_apply
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (f : ∀ i, E i) {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ s : Finset α, ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C) (i : α) :
    lpOfUniformFiniteMomentBound hp0 hpTop f hC hfinite i = f i := rfl

/-- The sequence norm is at most the p-th root of the uniform finite-moment
bound. -/
theorem lpOfUniformFiniteMomentBound_norm_le
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (f : ∀ i, E i) {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ s : Finset α, ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C) :
    ‖lpOfUniformFiniteMomentBound hp0 hpTop f hC hfinite‖ ≤
      C ^ (1 / p.toReal) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hroot : (C ^ (1 / p.toReal)) ^ p.toReal = C := by
    rw [← Real.rpow_mul hC]
    have hexp : (1 / p.toReal) * p.toReal = 1 := by
      field_simp [ne_of_gt hp]
    rw [hexp, Real.rpow_one]
  apply lp.norm_le_of_forall_sum_le hp (Real.rpow_nonneg hC _)
  intro s
  calc
    ∑ i ∈ s, ‖lpOfUniformFiniteMomentBound hp0 hpTop f hC hfinite i‖ ^ p.toReal =
        ∑ i ∈ s, ‖f i‖ ^ p.toReal := by simp
    _ ≤ C := hfinite s
    _ = (C ^ (1 / p.toReal)) ^ p.toReal := hroot.symm

end FractionalPrimes
