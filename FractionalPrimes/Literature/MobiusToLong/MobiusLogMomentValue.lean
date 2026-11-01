module

public import FractionalPrimes.Literature.MobiusToLong.ReciprocalMobiusMoments
public import FractionalPrimes.Literature.MobiusToLong.MobiusMellinDerivative
public import FractionalPrimes.Literature.MobiusToLong.MobiusMellinEndpointValues

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace FractionalPrimes.Literature.MobiusToLong

noncomputable section

/-- The terminal term in logarithmic Abel summation tends to zero at real
cutoffs, including nonintegral cutoffs. -/
theorem mobiusLogReciprocalEndpoint_tendsto_zero {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    Tendsto (fun x : ℝ => mobiusSummatory x * (Real.log x / x))
      atTop (𝓝 0) := by
  have hscale : Tendsto
      (fun x : ℝ => C * Real.rpow (Real.log x) (1 - R)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (log_rpow_one_sub_tendsto_zero hR)
  have hbound : ∀ᶠ x : ℝ in atTop,
      |mobiusSummatory x * (Real.log x / x)| ≤
        C * Real.rpow (Real.log x) (1 - R) := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    exact mobius_log_reciprocal_endpoint_bound hC hx hM
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hscale
    (Filter.Eventually.of_forall fun x =>
      abs_nonneg (mobiusSummatory x * (Real.log x / x))) hbound

/-- Pointwise, the finite logarithmic Abel integrand is the negative of the
Mellin derivative integrand. -/
theorem mobiusLogReciprocalAbelIntegrand_eq_neg_mellinDerivative {t M : ℝ}
    (ht : 0 < t) :
    M * ((Real.log t - 1) / t ^ 2) =
      -(M * Real.rpow t (-2 : ℝ) * (1 - Real.log t)) := by
  have hpow : Real.rpow t (-2 : ℝ) = (t ^ 2)⁻¹ := by
    calc
      Real.rpow t (-2 : ℝ) = Real.rpow t (-1 + -1) := by
        congr 1 <;> norm_num
      _ = (t ^ 2)⁻¹ := mobiusMellin_rpow_neg_one_add_neg_one ht
  rw [div_eq_mul_inv, hpow]
  ring

/-- Integrability of the finite Abel integrand on the full Mellin domain,
using the derivative majorant from the one-sided Mellin argument. -/
theorem mobiusLogReciprocalAbelIntegrand_integrableOn {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    IntegrableOn
      (fun t : ℝ => mobiusSummatory t * ((Real.log t - 1) / t ^ 2))
      (Set.Ioi 1) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 1)
  have hMmeas : AEStronglyMeasurable mobiusSummatory μ := by
    simpa [μ] using mobiusSummatory_measurable.aestronglyMeasurable.restrict
  have hlog : ContinuousOn Real.log (Set.Ioi 1) :=
    Real.continuousOn_log.mono fun t ht =>
      ne_of_gt (lt_trans zero_lt_one (Set.mem_Ioi.mp ht))
  have hnum : ContinuousOn (fun t : ℝ => Real.log t - 1) (Set.Ioi 1) :=
    hlog.sub continuousOn_const
  have hpow : ContinuousOn (fun t : ℝ => t ^ 2) (Set.Ioi 1) := by
    fun_prop
  have hinv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Ioi 1) :=
    hpow.inv₀ fun t ht => pow_ne_zero 2
      (ne_of_gt (lt_trans zero_lt_one (Set.mem_Ioi.mp ht)))
  have hweight :
      ContinuousOn (fun t : ℝ => (Real.log t - 1) / t ^ 2) (Set.Ioi 1) := by
    change ContinuousOn (fun t : ℝ => (Real.log t - 1) * (t ^ 2)⁻¹)
      (Set.Ioi 1)
    exact hnum.mul hinv
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => mobiusSummatory t * ((Real.log t - 1) / t ^ 2)) μ := by
    change AEStronglyMeasurable (fun t : ℝ => mobiusSummatory t *
      ((Real.log t - 1) / t ^ 2)) μ
    exact hMmeas.mul (hweight.aestronglyMeasurable measurableSet_Ioi)
  have hmajor : IntegrableOn (mobiusMellinSlopeMajorant R C) (Set.Ioi 1) :=
    mobiusMellinSlopeMajorant_integrableOn hR hC
  apply Integrable.mono' hmajor.integrable hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htgt : 1 < t := Set.mem_Ioi.mp ht
  have htpos : 0 < t := lt_trans zero_lt_one htgt
  have hderivBound := mobiusMellinIntegrand_derivative_abs_le
    hR hC hM htgt le_rfl (by norm_num : (1 : ℝ) ≤ 2)
  have hpowEndpoint : Real.rpow t (-(1 + 1 : ℝ)) = (t ^ 2)⁻¹ := by
    calc
      Real.rpow t (-(1 + 1 : ℝ)) = Real.rpow t (-1 + -1) := by
        congr 1 <;> norm_num
      _ = (t ^ 2)⁻¹ := mobiusMellin_rpow_neg_one_add_neg_one htpos
  have hendpoint :
      mobiusSummatory t * ((Real.log t - 1) / t ^ 2) =
        -(mobiusSummatory t * Real.rpow t (-(1 + 1 : ℝ)) *
          (1 - Real.log t)) := by
    rw [div_eq_mul_inv, hpowEndpoint]
    ring
  rw [Real.norm_eq_abs, hendpoint, abs_neg]
  simpa only [one_mul] using hderivBound

/-- The finite Abel integral converges to its improper integral. -/
theorem mobiusLogReciprocalAbelIntegral_tendsto {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    Tendsto
      (fun y : ℝ => ∫ t in Set.Ioc 1 y,
        mobiusSummatory t * ((Real.log t - 1) / t ^ 2))
      atTop
      (𝓝 (∫ t in Set.Ioi 1,
        mobiusSummatory t * ((Real.log t - 1) / t ^ 2))) := by
  have hint := mobiusLogReciprocalAbelIntegrand_integrableOn hR hC hM
  have hinterval := intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id
  have heq :
      (fun y : ℝ => ∫ t in (1 : ℝ)..y,
        mobiusSummatory t * ((Real.log t - 1) / t ^ 2)) =ᶠ[atTop]
      (fun y : ℝ => ∫ t in Set.Ioc 1 y,
        mobiusSummatory t * ((Real.log t - 1) / t ^ 2)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    rw [intervalIntegral.integral_of_le hy]
  exact Tendsto.congr' heq hinterval

/-- The weighted reciprocal Möbius partial sums converge in increasing
positive-integer order to `-1`, with no absolute-convergence assertion. -/
theorem mobiusLogReciprocalPartialSum_tendsto_neg_one {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    Tendsto mobiusLogReciprocalPartialSum atTop (𝓝 (-1)) := by
  let g : ℝ → ℝ := fun t =>
    mobiusSummatory t * ((Real.log t - 1) / t ^ 2)
  have hAbelIntegralValue :
      (∫ t in Set.Ioi 1, g t) = -1 := by
    have hderivValue := mobiusMellinTransform_deriv_value_eq_one hR hC hM
    have hIntegralEq :
        (∫ t in Set.Ioi 1, g t) =
          -(∫ t in Set.Ioi 1,
            mobiusSummatory t * Real.rpow t (-2) * (1 - Real.log t)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact (ae_restrict_iff' measurableSet_Ioi).2
        (Filter.Eventually.of_forall fun t ht => by
          have htpos : 0 < t := lt_trans zero_lt_one (Set.mem_Ioi.mp ht)
          simpa [g] using
            (mobiusLogReciprocalAbelIntegrand_eq_neg_mellinDerivative
              (t := t) (M := mobiusSummatory t) htpos))
    rw [hIntegralEq, hderivValue]
  have hEndpoint := mobiusLogReciprocalEndpoint_tendsto_zero hR hC hM
  have hIntegral := mobiusLogReciprocalAbelIntegral_tendsto hR hC hM
  have hRhs : Tendsto
      (fun Y : ℝ => mobiusSummatory Y * (Real.log Y / Y) +
        ∫ t in Set.Ioc 1 Y, g t)
      atTop (𝓝 (-1)) := by
    have h := hEndpoint.add hIntegral
    simpa [g, hAbelIntegralValue] using h
  let A : ℝ → ℝ := fun Y =>
    ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
      (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)
  have hFinite : A =ᶠ[atTop] (fun Y : ℝ =>
      mobiusSummatory Y * (Real.log Y / Y) +
        ∫ t in Set.Ioc 1 Y, g t) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    dsimp [A, g]
    exact mobius_log_reciprocal_finite_abel_from_one hY
  have hReal : Tendsto A atTop (𝓝 (-1)) :=
    Tendsto.congr' hFinite.symm hRhs
  have hNat := hReal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun N : ℕ =>
      ∑ n ∈ Finset.Icc 1 (Nat.floor (N : ℝ)),
        (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
    atTop (𝓝 (-1)) at hNat
  have hNat' : Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 (-1)) := by
    simpa only [Nat.floor_natCast] using hNat
  have hEq :
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) =
        mobiusLogReciprocalPartialSum := by
    funext N
    rfl
  exact Tendsto.congr'
    (Filter.Eventually.of_forall fun N => congrFun hEq N) hNat'

end

end FractionalPrimes.Literature.MobiusToLong

end
