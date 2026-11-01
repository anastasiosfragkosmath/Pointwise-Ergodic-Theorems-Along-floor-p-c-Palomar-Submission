module

public import FractionalPrimes.Literature.JSW.SmoothDyadicOperatorBlock

/-! Uniform finite square bounds for finite dyadic expansions. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothDyadicSquareConstant (a : ℝ) (ha : 0 < a) : ℝ :=
  smoothDyadicAmplitude * Real.sqrt (jswMultiplicity a ha : ℝ) * smoothDyadicW0

theorem smoothDyadicSquareConstant_nonneg {a : ℝ} (ha : 0 < a) :
    0 ≤ smoothDyadicSquareConstant a ha :=
  mul_nonneg (mul_nonneg (le_trans (by norm_num) smoothDyadicAmplitude_eight_le)
    (Real.sqrt_nonneg _)) smoothDyadicW0_nonneg

theorem smoothDyadic_finite_expansion_energy
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    [Fact (1 ≤ ENNReal.ofReal (2 : ℝ))]
    {a : ℝ} (ha : 0 < a) (K J : Finset ℤ)
    {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal (2 : ℝ)) volume) :
    ∑ k ∈ K, ‖smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num)
      (jswTau a ha k) (jswM a ha k)
      (∑ j ∈ J, dyadicDifferenceLpAt (by norm_num) hf j)‖^2 ≤
      (smoothDyadicSquareConstant a ha)^2 * ‖hf.toLp f‖^2 := by
  let δ := fun j : ℤ => dyadicDifferenceLpAt (by norm_num : ENNReal.ofReal (2 : ℝ) = 2) hf j
  let R := fun k : ℤ => smoothDyadicErrorLpOperator hSupp (p := 2) (by norm_num)
    (jswTau a ha k) (jswM a ha k)
  have hA : 0 ≤ smoothDyadicAmplitude := le_trans (by norm_num) smoothDyadicAmplitude_eight_le
  have hblock (k j : ℤ) : ‖R k (δ j)‖ ≤
      smoothDyadicAmplitude*smoothDyadicWeight (jswM a ha k-j)*‖δ j‖ := by
    have hτ : 0 < jswTau a ha k := zpow_pos (by linarith [jswB_gt_one ha]) _
    obtain ⟨hlo,hhi⟩ := jswTau_floor_bounds a ha k
    exact smoothDyadicErrorLpOperator_L2_block hSupp hτ hlo hhi.le j hf
  have hrow (k : ℤ) : ‖R k (∑ j ∈ J, δ j)‖ ≤
      smoothDyadicAmplitude*(∑ j ∈ J, smoothDyadicWeight (jswM a ha k-j)*‖δ j‖) := by
    calc
      _ = ‖∑ j ∈ J, R k (δ j)‖ := by rw [map_sum]
      _ ≤ ∑ j ∈ J, ‖R k (δ j)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ J, smoothDyadicAmplitude*smoothDyadicWeight (jswM a ha k-j)*‖δ j‖ :=
        Finset.sum_le_sum (fun j _ => hblock k j)
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
  have hparseval := dyadicDifferenceLpAt_parseval (by norm_num : ENNReal.ofReal (2 : ℝ) = 2) hf
  have hsumD : (∑ j ∈ J, ‖δ j‖^2) ≤ ‖hf.toLp f‖^2 := by
    rw [← hparseval.tsum_eq]
    exact Summable.sum_le_tsum J (fun j _ => sq_nonneg _) hparseval.summable
  change (∑ k ∈ K, ‖R k (∑ j ∈ J, δ j)‖^2) ≤ _
  calc
    _ ≤ ∑ k ∈ K, smoothDyadicAmplitude^2*
        (∑ j ∈ J, smoothDyadicWeight (jswM a ha k-j)*‖δ j‖)^2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hs := pow_le_pow_left₀ (norm_nonneg _) (hrow k) 2
      simpa only [mul_pow] using hs
    _ = smoothDyadicAmplitude^2*(∑ k ∈ K,
        (∑ j ∈ J, smoothDyadicWeight (jswM a ha k-j)*‖δ j‖)^2) := by rw [Finset.mul_sum]
    _ ≤ smoothDyadicAmplitude^2*((jswMultiplicity a ha : ℝ)*smoothDyadicW0^2*
        (∑ j ∈ J, ‖δ j‖^2)) := mul_le_mul_of_nonneg_left
      (smoothDyadic_finite_weighted_square_bound ha K J (fun j => ‖δ j‖)) (sq_nonneg _)
    _ ≤ smoothDyadicAmplitude^2*((jswMultiplicity a ha : ℝ)*smoothDyadicW0^2*‖hf.toLp f‖^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumD
        (mul_nonneg (by positivity) (sq_nonneg _))) (sq_nonneg _)
    _ = _ := by
      unfold smoothDyadicSquareConstant
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (jswMultiplicity a ha : ℝ))]
      ring

#print axioms smoothDyadic_finite_expansion_energy
end
end FractionalPrimes.Literature.JSW
end
