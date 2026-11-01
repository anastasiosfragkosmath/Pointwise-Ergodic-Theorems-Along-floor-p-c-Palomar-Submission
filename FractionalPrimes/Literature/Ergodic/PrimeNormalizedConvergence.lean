module

public import FractionalPrimes.Literature.Ergodic.PrimeAbelNormalizationCoefficients
public import FractionalPrimes.Literature.Ergodic.AbelConvergenceStability

@[expose] public section
open Filter
open scoped Topology
namespace FractionalPrimes
noncomputable section

/-- The exact finite normalized Abel identity in any real normed space. -/
theorem primeAbelNormalizedIdentity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℕ → E) {N : ℕ} (hN : 2 ≤ N) :
    (Nat.primeCounting N : ℝ)⁻¹ • primePartialSum g N =
      primeAbelAlpha N • ((N : ℝ)⁻¹ • primeLogPartialSum g N) +
        ∑ n ∈ Finset.Ico 2 N,
          primeAbelBeta N n • ((n : ℝ)⁻¹ • primeLogPartialSum g n) := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hpine : (Nat.primeCounting N : ℝ) ≠ 0 := by
    exact_mod_cast (primeCounting_pos_of_two_le hN).ne'
  rw [primePartialSum, ← Finset.sum_filter, primeAbelIdentity g hN,
    smul_add, Finset.smul_sum]
  congr 1
  · simp only [smul_smul]
    congr 1
    unfold primeAbelAlpha
    field_simp [hNne, hlog, hpine]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (by have hn2 := (Finset.mem_Ico.mp hn).1; omega : n ≠ 0)
    simp only [smul_smul]
    congr 1
    unfold primeAbelBeta
    field_simp [hnne, hpine]

/-- The source normalization argument simultaneously applies pointwise and
in Lp: its only numerical premise is the source prime-counting asymptotic. -/
theorem normalizedPrimeMean_tendsto_of_logMean
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℕ → E) (z : E)
    (hweighted : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • primeLogPartialSum g N)
      atTop (𝓝 z))
    (hpi : Tendsto (fun N : ℕ =>
      (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ)⁻¹ • primePartialSum g N)
      atTop (𝓝 z) := by
  obtain ⟨hAlpha, hMass⟩ := primeAbelNormalizationCoefficientLimits hpi
  have hstable := tendsto_of_abel_positive_remainder
    (fun N : ℕ => (N : ℝ)⁻¹ • primeLogPartialSum g N) z hweighted
    primeAbelAlpha (fun N => Finset.Ico 2 N) primeAbelBeta
    hAlpha primeAbelBeta_nonneg hMass
  apply hstable.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (primeAbelNormalizedIdentity g hN).symm

#print axioms normalizedPrimeMean_tendsto_of_logMean
end
end FractionalPrimes
