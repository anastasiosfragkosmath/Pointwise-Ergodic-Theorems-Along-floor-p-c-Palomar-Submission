module

public import FractionalPrimes.Literature.Ergodic.KernelZeroFrequencyBound
public import FractionalPrimes.Literature.Ergodic.ArithmeticKernelMass
public import FractionalPrimes.Chebyshev

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FractionalPrimes
noncomputable section

theorem primeComparisonScalar_eq_psi (N : Scale) :
    (N.val : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N.val, ((vonMangoldtWeight n : ℂ) - 1) =
      ((paperPsi N.val / (N.val : ℝ) - 1 : ℝ) : ℂ) := by
  have hN : (N.val : ℂ) ≠ 0 := by exact_mod_cast N.property.ne'
  have hsum : (∑ n ∈ Finset.Icc 1 N.val, ((vonMangoldtWeight n : ℂ) - 1)) =
      (paperPsi N.val : ℂ) - (N.val : ℂ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
    rw [paperPsi_eq_sum_vonMangoldt, Complex.ofReal_sum]
  rw [hsum]
  push_cast
  field_simp [hN]
  <;> ring

theorem primeComparisonScalar_norm_le_operatorNorm
    {p : ℝ} (hp : 1 < p) (c : ℝ) (N : Scale) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    ‖paperPsi N.val / (N.val : ℝ) - 1‖ ≤
      ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p) (primeComparisonIntegerKernel c N)‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have h := weightedScalarMean_norm_le_discreteOperatorNorm hp c N
    (fun n => (vonMangoldtWeight n : ℂ) - 1)
  simpa only [primeComparisonScalar_eq_psi, Complex.norm_real,
    primeComparisonIntegerKernel] using h

/-- The numerical normalization is an internal zero-frequency consequence of
the actual comparison decay; no independent prime number theorem is assumed. -/
theorem paperPsi_div_tendsto_one_of_operatorDecay
    {p : ℝ} (hp : 1 < p) (c : ℝ)
    (hdecay : letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ∀ D : ℝ, 0 < D → ∃ C : ℝ, ∀ N : Scale, 3 ≤ N.val →
        ‖integerKernelLpConvolutionCLM (p := ENNReal.ofReal p)
          (primeComparisonIntegerKernel c N)‖ ≤
            C * (Real.log (N.val : ℝ)) ^ (-D)) :
    Tendsto (fun N : ℕ => paperPsi N / (N : ℝ)) atTop (𝓝 1) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨C, hC⟩ := hdecay 1 (by norm_num)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrate : Tendsto (fun N : ℕ => C * (Real.log (N : ℝ)) ^ (-1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_neg_one, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hlog).const_mul C
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖paperPsi N / (N : ℝ) - 1‖ ≤ C * (Real.log (N : ℝ)) ^ (-1 : ℝ) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN
    exact (primeComparisonScalar_norm_le_operatorNorm hp c ⟨N, by omega⟩).trans
      (hC ⟨N, by omega⟩ hN)
  have herr : Tendsto (fun N : ℕ => paperPsi N / (N : ℝ) - 1) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hbound hrate
  simpa only [Pi.add_apply, Pi.add_def, sub_add_cancel, zero_add] using herr.add_const 1

#print axioms paperPsi_div_tendsto_one_of_operatorDecay
end
end FractionalPrimes
