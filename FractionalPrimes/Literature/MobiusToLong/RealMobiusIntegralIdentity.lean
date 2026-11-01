module

public import FractionalPrimes.Literature.MobiusToLong.RealMobiusProduct
public import FractionalPrimes.Literature.MobiusToLong.RealMobiusMellin
public import FractionalPrimes.Literature.MobiusToLong.MobiusMellinDerivative
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace FractionalPrimes.Literature.MobiusToLong

noncomputable section

/-- The crude coefficient bound gives the corresponding linear bound for the
positive-index Möbius summatory function at every real cutoff at least one. -/
theorem mobiusSummatory_abs_le_cutoff {x : ℝ} (hx : 1 ≤ x) :
    |mobiusSummatory x| ≤ x := by
  rw [mobiusSummatory]
  have hfloor : 1 ≤ Nat.floor x := Nat.le_floor (by exact_mod_cast hx)
  have hsum :
      |∑ n ∈ Finset.Icc 1 (Nat.floor x),
          (ArithmeticFunction.moebius n : ℝ)| ≤
        ∑ n ∈ Finset.Icc 1 (Nat.floor x), (1 : ℝ) := by
    calc
      _ = ‖∑ n ∈ Finset.Icc 1 (Nat.floor x),
            (ArithmeticFunction.moebius n : ℝ)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor x),
            ‖(ArithmeticFunction.moebius n : ℝ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor x), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Real.norm_eq_abs]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor x), (1 : ℝ) := hsum
    _ = (Nat.floor x : ℝ) := by simp [Nat.card_Icc]
    _ ≤ x := Nat.floor_le (by linarith)

private theorem mobius_dirichlet_partial_sum_eq_range {σ : ℝ} (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ)) =
      ∑ i ∈ Finset.range N,
        (ArithmeticFunction.moebius (i + 1) : ℝ) *
          (((i + 1 : ℕ) : ℝ) ^ (-σ)) := by
  symm
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro i hi j hj hij
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨n - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

/-- The explicit real-power form of the source Mellin kernel. -/
theorem mobiusMellinKernel_eq_rpow {σ t : ℝ} :
    mobiusMellinKernel σ t =
      mobiusSummatory t * t ^ (-(σ + 1)) := by
  rfl

private theorem mobiusMellinKernel_integrableOn_sigma_gt_one {σ : ℝ}
    (hσ : 1 < σ) :
    IntegrableOn (mobiusMellinKernel σ) (Set.Ioi 1) := by
  have hmajor : IntegrableOn (fun t : ℝ => t ^ (-σ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hmeas : AEStronglyMeasurable (mobiusMellinKernel σ)
      (volume.restrict (Set.Ioi 1)) := mobiusMellinKernel_aestronglyMeasurable σ
  apply Integrable.mono' hmajor.integrable hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 < t := Set.mem_Ioi.mp ht
  have htpos : 0 < t := by linarith
  have hM := mobiusSummatory_abs_le_cutoff ht1.le
  have hpowNonneg : 0 ≤ t ^ (-(σ + 1)) := Real.rpow_nonneg htpos.le _
  rw [Real.norm_eq_abs]
  change |mobiusSummatory t * t ^ (-(σ + 1))| ≤ t ^ (-σ)
  rw [abs_mul, abs_of_nonneg hpowNonneg]
  calc
    |mobiusSummatory t| * t ^ (-(σ + 1)) ≤
        t * t ^ (-(σ + 1)) :=
      mul_le_mul_of_nonneg_right hM hpowNonneg
    _ = t ^ (-σ) := by
      rw [show -(σ + 1) = -σ + (-1) by ring, Real.rpow_add htpos,
        Real.rpow_neg_one]
      field_simp [ne_of_gt htpos]

private theorem mobiusDirichlet_endpoint_tendsto_zero {σ : ℝ}
    (hσ : 1 < σ) :
    Tendsto (fun x : ℝ => mobiusSummatory x * x ^ (-σ)) atTop (𝓝 0) := by
  have hpower : Tendsto (fun x : ℝ => x ^ (1 - σ)) atTop (𝓝 0) := by
    have hsmall := tendsto_rpow_neg_atTop (by linarith : 0 < σ - 1)
    have hexp : 1 - σ = -(σ - 1) := by ring
    simpa only [hexp] using hsmall
  have hbound : ∀ᶠ x : ℝ in atTop,
      |mobiusSummatory x * x ^ (-σ)| ≤ x ^ (1 - σ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hM := mobiusSummatory_abs_le_cutoff hx
    have hpowNonneg : 0 ≤ x ^ (-σ) := Real.rpow_nonneg hxpos.le _
    rw [abs_mul, abs_of_nonneg hpowNonneg]
    calc
      |mobiusSummatory x| * x ^ (-σ) ≤ x * x ^ (-σ) :=
        mul_le_mul_of_nonneg_right hM hpowNonneg
      _ = x ^ (1 - σ) := by
        rw [show (1 : ℝ) - σ = 1 + (-σ) by ring, Real.rpow_add hxpos,
          Real.rpow_one]
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hpower
    (Filter.Eventually.of_forall fun x => abs_nonneg (mobiusSummatory x * x ^ (-σ)))
    hbound

/-- The real positive-integer Möbius Dirichlet series equals the source's
outer-factor Mellin transform for every `σ > 1`. This is the finite Abel
identity followed by absolute convergence, the vanishing endpoint, and the
improper-integral limit. -/
theorem realMobiusDirichletSeries_eq_mobiusMellinTransform
    {σ : ℝ} (hσ : 1 < σ) :
    realMobiusDirichletSeries σ = mobiusMellinTransform σ := by
  have hsumNat : Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ))
      atTop (𝓝 (realMobiusDirichletSeries σ)) := by
    have hsum := (realMobiusDirichletSeries_summable hσ).hasSum.tendsto_sum_nat
    have heq :
        (fun N : ℕ =>
          ∑ i ∈ Finset.range N,
            (ArithmeticFunction.moebius (i + 1) : ℝ) *
              (((i + 1 : ℕ) : ℝ) ^ (-σ))) =ᶠ[atTop]
        (fun N : ℕ =>
          ∑ n ∈ Finset.Icc 1 N,
            (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ)) :=
      Filter.Eventually.of_forall fun N =>
        (mobius_dirichlet_partial_sum_eq_range (σ := σ) N).symm
    exact Tendsto.congr' heq hsum
  have hsumReal : Tendsto
      (fun y : ℝ =>
        ∑ n ∈ Finset.Icc 1 (Nat.floor y),
          (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ))
      atTop (𝓝 (realMobiusDirichletSeries σ)) := by
    have h := hsumNat.comp (tendsto_nat_floor_atTop (α := ℝ))
    change Tendsto
      (fun y : ℝ =>
        ∑ n ∈ Finset.Icc 1 (Nat.floor y),
          (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ))
      atTop (𝓝 (realMobiusDirichletSeries σ)) at h
    exact h
  have hkernelInt := mobiusMellinKernel_integrableOn_sigma_gt_one hσ
  have hintegral : Tendsto
      (fun y : ℝ => ∫ t in Set.Ioc 1 y, mobiusMellinKernel σ t)
      atTop (𝓝 (∫ t in Set.Ioi 1, mobiusMellinKernel σ t)) := by
    have hinterval := intervalIntegral_tendsto_integral_Ioi 1 hkernelInt tendsto_id
    have heq :
        (fun y : ℝ => ∫ t in (1 : ℝ)..y, mobiusMellinKernel σ t) =ᶠ[atTop]
        (fun y : ℝ => ∫ t in Set.Ioc 1 y, mobiusMellinKernel σ t) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      rw [intervalIntegral.integral_of_le hy]
    exact Tendsto.congr' heq hinterval
  have hfinite :
      (fun y : ℝ =>
        ∑ n ∈ Finset.Icc 1 (Nat.floor y),
          (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ)) =ᶠ[atTop]
      (fun y : ℝ => mobiusSummatory y * y ^ (-σ) +
        σ * ∫ t in Set.Ioc 1 y, mobiusMellinKernel σ t) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    simpa only [mobiusMellinKernel_eq_rpow] using
      mobius_dirichlet_finite_abel_from_one (σ := σ) hy
  have hlimRhs : Tendsto
      (fun y : ℝ => mobiusSummatory y * y ^ (-σ) +
        σ * ∫ t in Set.Ioc 1 y, mobiusMellinKernel σ t)
      atTop (𝓝 (mobiusMellinTransform σ)) := by
    have h := (mobiusDirichlet_endpoint_tendsto_zero hσ).add (hintegral.const_mul σ)
    simpa [mobiusMellinTransform] using h
  exact tendsto_nhds_unique hsumReal (Tendsto.congr' hfinite.symm hlimRhs)

end
end FractionalPrimes.Literature.MobiusToLong
