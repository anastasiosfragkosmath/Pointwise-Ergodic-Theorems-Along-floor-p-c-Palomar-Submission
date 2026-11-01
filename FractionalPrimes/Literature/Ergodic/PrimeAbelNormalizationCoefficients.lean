module

public import FractionalPrimes.Literature.Ergodic.PrimeCountingNormalization

@[expose] public section
open Filter
open scoped Topology
namespace FractionalPrimes
noncomputable section

def primeAbelAlpha (N : ℕ) : ℝ :=
  (N : ℝ) / ((Nat.primeCounting N : ℝ) * Real.log (N : ℝ))

def primeAbelBeta (N n : ℕ) : ℝ :=
  (n : ℝ) * primeAbelDifference n / (Nat.primeCounting N : ℝ)

theorem primeAbelBeta_nonneg (N n : ℕ) (hn : n ∈ Finset.Ico 2 N) :
    0 ≤ primeAbelBeta N n :=
  div_nonneg (mul_nonneg (by positivity)
    (primeAbelDifference_pos (Finset.mem_Ico.mp hn).1).le) (by positivity)

theorem primeAbelBeta_sum (N : ℕ) :
    (∑ n ∈ Finset.Ico 2 N, primeAbelBeta N n) =
      primeAbelRemainderCoefficient N / (Nat.primeCounting N : ℝ) := by
  simp only [primeAbelBeta, primeAbelRemainderCoefficient, Finset.sum_div]

/-- The source prime-counting asymptotic gives the exact Abel coefficient
limits; the arithmetic premise is retained explicitly. -/
theorem primeAbelNormalizationCoefficientLimits
    (hpi : Tendsto (fun N : ℕ =>
      (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 1)) :
    Tendsto primeAbelAlpha atTop (𝓝 1) ∧
      Tendsto (fun N => ∑ n ∈ Finset.Ico 2 N, primeAbelBeta N n) atTop (𝓝 0) := by
  have hAlpha : Tendsto primeAbelAlpha atTop (𝓝 1) := by
    unfold primeAbelAlpha
    simpa only [inv_one, inv_div] using hpi.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hden : Tendsto (fun N : ℕ =>
      (Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log (N : ℝ))) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, mul_comm, mul_left_comm] using hpi
  have hH := primeAbelRemainderCoefficient_littleO.tendsto_div_nhds_zero
  have hratio := hH.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hratio' : Tendsto (fun N : ℕ =>
      (primeAbelRemainderCoefficient N / ((N : ℝ) / Real.log (N : ℝ))) /
        ((Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log (N : ℝ)))) atTop (𝓝 0) := by
    simpa only [zero_div, Pi.div_def] using hratio
  have hmass : Tendsto (fun N => ∑ n ∈ Finset.Ico 2 N, primeAbelBeta N n)
      atTop (𝓝 0) := by
    apply hratio'.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    rw [primeAbelBeta_sum]
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hlog : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
    have hpine : (Nat.primeCounting N : ℝ) ≠ 0 := by
      exact_mod_cast (primeCounting_pos_of_two_le hN).ne'
    field_simp [hNne, hlog, hpine]
  exact ⟨hAlpha, hmass⟩

#print axioms primeAbelNormalizationCoefficientLimits
end
end FractionalPrimes
