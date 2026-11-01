module

public import FractionalPrimes.InterpolationLayercake
public import FractionalPrimes.FiniteInterpolationWeightedDistribution
public import FractionalPrimes.InterpolationWeightedLayercake

@[expose] public section

/-!
# Layer cake on a finite output restriction

The counting-measure layer-cake identity specialized to a finite output set.
This converts the integrated distribution estimate in the interpolation
argument into an exact finite `p`-moment bound.
-/

namespace FractionalPrimes

open MeasureTheory
open Set
open scoped ENNReal

theorem finiteOutput_pMoment_eq_weighted_layercake
    {p : ℝ} (hp : 0 < p) (out : Finset ℤ) (g : ℤ → ℂ) :
    (∑ k ∈ out, ‖g k‖ₑ ^ p) =
      ENNReal.ofReal p *
        ∫⁻ t in Ioi (0 : ℝ),
          ((out.filter fun k => t < ‖g k‖).card : ℝ≥0∞) *
            ENNReal.ofReal (t ^ (p - 1)) := by
  let trunc : ℤ → ℂ := fun k => if k ∈ out then g k else 0
  have hmoment :
      (∫⁻ k : ℤ, ‖trunc k‖ₑ ^ p ∂(Measure.count : Measure ℤ)) =
        ∑ k ∈ out, ‖g k‖ₑ ^ p := by
    rw [lintegral_count]
    calc
      ∑' k : ℤ, ‖trunc k‖ₑ ^ p =
          ∑ k ∈ out, ‖trunc k‖ₑ ^ p := by
            apply tsum_eq_sum (s := out)
            intro k hk
            simp [trunc, hk, ENNReal.zero_rpow_of_pos hp]
      _ = ∑ k ∈ out, ‖g k‖ₑ ^ p := by
            apply Finset.sum_congr rfl
            intro k hk
            simp [trunc, hk]
  have hlevel :
      (fun t : ℝ =>
        Measure.count {k : ℤ | t < ‖trunc k‖} *
          ENNReal.ofReal (t ^ (p - 1))) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t =>
        ((out.filter fun k => t < ‖g k‖).card : ℝ≥0∞) *
          ENNReal.ofReal (t ^ (p - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    have hset :
        {k : ℤ | t < ‖trunc k‖} =
          ((out.filter fun k => t < ‖g k‖) : Set ℤ) := by
      ext k
      by_cases hk : k ∈ out
      · simp [trunc, hk]
      · have hnot : ¬ t < 0 := by linarith
        simp [trunc, hk, hnot]
    rw [hset, Measure.count_apply_finset]
  calc
    (∑ k ∈ out, ‖g k‖ₑ ^ p) =
        ∫⁻ k : ℤ, ‖trunc k‖ₑ ^ p ∂(Measure.count : Measure ℤ) := hmoment.symm
    _ = ENNReal.ofReal p *
          ∫⁻ t in Ioi (0 : ℝ),
            Measure.count {k : ℤ | t < ‖trunc k‖} *
              ENNReal.ofReal (t ^ (p - 1)) :=
        integerSequence_lintegral_enorm_rpow_eq_lintegral_meas_lt hp trunc
    _ = ENNReal.ofReal p *
          ∫⁻ t in Ioi (0 : ℝ),
            ((out.filter fun k => t < ‖g k‖).card : ℝ≥0∞) *
              ENNReal.ofReal (t ^ (p - 1)) := by
        congr 1
        exact lintegral_congr_ae hlevel

/-- For `1 < p < 2`, integrating the checked low/high distribution estimate
gives the exact finite-output p-moment bound from the approved interpolation
argument. The split scale `a` is arbitrary and positive here; its optimized
choice is recorded separately in `interpolation_optimal_scale_coefficient`.
-/
theorem finiteIntegerKernelConvolution_output_pMoment_le
    {p a B epsilon : ℝ}
    (hp1 : 1 < p) (hp2 : p < 2) (ha : 0 < a)
    (K : IntegerL1Kernel) (s out : Finset ℤ) (f : ℤ → ℂ)
    (hB : ∑' m : ℤ, ‖K.coeff m‖ ≤ B)
    (hBpos : 0 < B) (hepsilon : 0 < epsilon)
    (hL2 : ∀ g : Lp ℂ 2 (Measure.count : Measure ℤ),
      eLpNorm (integerKernelConvolution K (g : ℤ → ℂ)) 2 Measure.count ≤
        ENNReal.ofReal epsilon * eLpNorm (g : ℤ → ℂ) 2 Measure.count) :
    (∑ k ∈ out,
      ‖integerKernelConvolution K (finiteSupportCountLpTwo s f : ℤ → ℂ) k‖ₑ ^ p) ≤
      ENNReal.ofReal p *
        (4 * ENNReal.ofReal (epsilon ^ 2) *
            (∑ k ∈ s, ENNReal.ofReal
              (a ^ (2 - p) * ‖f k‖ ^ p / (2 - p))) +
          2 * ENNReal.ofReal B *
            (∑ k ∈ s, ENNReal.ofReal
              (a ^ (1 - p) * ‖f k‖ ^ p / (p - 1)))) := by
  let g : ℤ → ℂ :=
    integerKernelConvolution K (finiteSupportCountLpTwo s f : ℤ → ℂ)
  have hDist := finiteIntegerKernelConvolution_weighted_distribution
    (p := p) (a := a) (B := B) (epsilon := epsilon)
    K s out f hB hBpos hepsilon hL2
  have hIntegrated := finite_weighted_distribution_integral_le
    hp1 hp2 ha (ENNReal.ofReal B) (ENNReal.ofReal (epsilon ^ 2)) s out f g
    (by
      intro t ht
      exact hDist t ht)
  have hLayercake := finiteOutput_pMoment_eq_weighted_layercake
    (lt_trans zero_lt_one hp1) out g
  rw [hLayercake]
  exact mul_le_mul_of_nonneg_left hIntegrated (by positivity)

end FractionalPrimes
