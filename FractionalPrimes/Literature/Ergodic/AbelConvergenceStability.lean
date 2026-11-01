module

public import FractionalPrimes.Literature.Ergodic.PrimeAbelIdentity
public import Mathlib.Analysis.Normed.Group.Bounded

/-! The normed-space convergence step of the approved prime Abel normalization. -/
@[expose] public section
namespace FractionalPrimes
open Filter
open scoped Topology
noncomputable section

/-- A convergent sequence retains its limit after a scalar factor tending to
one and a finite positive remainder whose total coefficient tends to zero. -/
theorem tendsto_of_abel_positive_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℕ → E) (z : E) (hv : Tendsto v atTop (𝓝 z))
    (α : ℕ → ℝ) (s : ℕ → Finset ℕ) (β : ℕ → ℕ → ℝ)
    (hα : Tendsto α atTop (𝓝 1))
    (hβ : ∀ N, ∀ n ∈ s N, 0 ≤ β N n)
    (hmass : Tendsto (fun N => ∑ n ∈ s N, β N n) atTop (𝓝 0)) :
    Tendsto (fun N => α N • v N + ∑ n ∈ s N, β N n • v n) atTop (𝓝 z) := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto v hv).exists_norm_le
  have hbound (N : ℕ) : ‖∑ n ∈ s N, β N n • v n‖ ≤
      B * ∑ n ∈ s N, β N n := by
    calc
      _ ≤ ∑ n ∈ s N, ‖β N n • v n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ s N, β N n * B := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_smul, Real.norm_of_nonneg (hβ N n hn)]
        exact mul_le_mul_of_nonneg_left (hB _ ⟨n, rfl⟩) (hβ N n hn)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  have hnorm : Tendsto (fun N => ‖∑ n ∈ s N, β N n • v n‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hbound (by simpa using tendsto_const_nhds.mul hmass)
  have hrem : Tendsto (fun N => ∑ n ∈ s N, β N n • v n) atTop (𝓝 (0 : E)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa only [one_smul, add_zero] using (hα.smul hv).add hrem

#print axioms tendsto_of_abel_positive_remainder
end
end FractionalPrimes
