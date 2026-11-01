module

public import FractionalPrimes.Literature.MobiusToLong.ReciprocalMobiusMoments
public import FractionalPrimes.Literature.MobiusToLong.MobiusReciprocalInitialAbel
public import FractionalPrimes.Literature.MobiusToLong.MobiusReciprocalIntegralLimit
public import FractionalPrimes.Literature.MobiusToLong.MobiusMellinEndpointValues

@[expose] public section

open Filter
open scoped Topology

namespace FractionalPrimes.Literature.MobiusToLong

/-- The natural ordered reciprocal Möbius partial sums tend to zero under the
stated Mertens bound. The proof passes through the real cutoff and retains the
`Nat.floor` convention in the summatory function and finite Abel identity. -/
theorem reciprocalMobiusPartialSum_tendsto_zero {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    Tendsto reciprocalMobiusPartialSum atTop (𝓝 0) := by
  have hendpoint := mobiusMellinTransform_at_one_eq_zero hR hC hM
  have hboundary := mobiusSummatory_div_tendsto_zero hR hC hM
  have hintegral := mobius_reciprocal_integral_truncated_tendsto hR hC hM
  have hintegralZero : Tendsto
      (fun Y : ℝ => ∫ t in Set.Ioc 1 Y, mobiusSummatory t / t ^ 2)
      atTop (𝓝 0) := by
    simpa only [hendpoint] using hintegral
  have hreal : Tendsto
      (fun Y : ℝ =>
        ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
          (ArithmeticFunction.moebius n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    have hsum := hboundary.add hintegralZero
    have heq :
        (fun Y : ℝ =>
          ∑ n ∈ Finset.Icc 1 (Nat.floor Y),
            (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) =ᶠ[atTop]
        (fun Y : ℝ => mobiusSummatory Y / Y +
          ∫ t in Set.Ioc 1 Y, mobiusSummatory t / t ^ 2) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
      exact mobius_reciprocal_finite_abel_from_one hY
    exact Tendsto.congr' heq.symm (by simpa using hsum)
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun N : ℕ =>
      ∑ n ∈ Finset.Icc 1 (Nat.floor (N : ℝ)),
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ))
    atTop (𝓝 0) at hnat
  have hEq :
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 (Nat.floor (N : ℝ)),
          (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) =
        reciprocalMobiusPartialSum := by
    funext N
    simp [reciprocalMobiusPartialSum]
  exact hEq ▸ hnat

end FractionalPrimes.Literature.MobiusToLong
