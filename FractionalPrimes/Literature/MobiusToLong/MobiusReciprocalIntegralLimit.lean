module

public import FractionalPrimes.Literature.MobiusToLong.MobiusMellinDerivative
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.Basic

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace FractionalPrimes.Literature.MobiusToLong

/-- The truncated reciprocal Möbius integral converges to the Mellin transform
at the endpoint parameter. -/
theorem mobius_reciprocal_integral_truncated_tendsto {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    Tendsto
      (fun Y : ℝ => ∫ t in Set.Ioc 1 Y, mobiusSummatory t / t ^ 2)
      atTop (𝓝 (mobiusMellinTransform 1)) := by
  have hkernelInt := mobiusMellinKernel_integrableOn
    (σ := 1) le_rfl hR hC hM
  have hintegral : Tendsto
      (fun Y : ℝ => ∫ t in Set.Ioc 1 Y, mobiusMellinKernel 1 t)
      atTop (𝓝 (∫ t in Set.Ioi 1, mobiusMellinKernel 1 t)) := by
    have hinterval := intervalIntegral_tendsto_integral_Ioi 1 hkernelInt tendsto_id
    have heq :
        (fun Y : ℝ => ∫ t in (1 : ℝ)..Y, mobiusMellinKernel 1 t) =ᶠ[atTop]
        (fun Y : ℝ => ∫ t in Set.Ioc 1 Y, mobiusMellinKernel 1 t) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
      rw [intervalIntegral.integral_of_le hY]
    exact Tendsto.congr' heq hinterval
  have hkernel_eq :
      (∫ t in Set.Ioi 1, mobiusMellinKernel 1 t) = mobiusMellinTransform 1 := by
    rw [mobiusMellinTransform_eq_integral]
    simp [mobiusMellinIntegrand]
  have hfinite_eq : ∀ Y : ℝ,
      (∫ t in Set.Ioc 1 Y, mobiusSummatory t / t ^ 2) =
        ∫ t in Set.Ioc 1 Y, mobiusMellinKernel 1 t := by
    intro Y
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have hpow : Real.rpow t (-(1 + 1 : ℝ)) = (t ^ 2)⁻¹ := by
      simpa using mobiusMellin_rpow_neg_one_add_neg_one htpos
    simp only [mobiusMellinKernel, hpow, div_eq_mul_inv]
  have hfinite := Tendsto.congr'
    (Filter.Eventually.of_forall fun Y => (hfinite_eq Y).symm) hintegral
  simpa only [hkernel_eq] using hfinite

end FractionalPrimes.Literature.MobiusToLong
