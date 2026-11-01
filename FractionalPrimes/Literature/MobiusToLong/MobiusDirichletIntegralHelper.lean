module

public import FractionalPrimes.Literature.MobiusToLong.ReciprocalMobiusMoments

@[expose] public section

open Set MeasureTheory

namespace FractionalPrimes.Literature.MobiusToLong

/-- Convert the zero-based Möbius partial sum in Mathlib's Abel integral to
the approved positive-index summatory function, while keeping the outer
constant and sign explicit. -/
theorem mobius_dirichlet_integral_fromZero_eq {σ Y : ℝ} :
    (∫ t in Set.Ioc 1 Y,
        (-σ) * t ^ (-(σ + 1)) *
          ∑ n ∈ Finset.Icc 0 (Nat.floor t),
            (ArithmeticFunction.moebius n : ℝ)) =
      -(∫ t in Set.Ioc 1 Y,
        σ * mobiusSummatory t * t ^ (-(σ + 1))) := by
  rw [← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  change (-σ) * t ^ (-(σ + 1)) *
      (∑ n ∈ Finset.Icc 0 (Nat.floor t),
        (ArithmeticFunction.moebius n : ℝ)) =
    -(σ * mobiusSummatory t * t ^ (-(σ + 1)))
  have hpart :
      (∑ n ∈ Finset.Icc 0 (Nat.floor t),
        (ArithmeticFunction.moebius n : ℝ)) = mobiusSummatory t := by
    change mobiusSummatoryFromZero t = mobiusSummatory t
    exact (mobiusSummatory_eq_fromZero t).symm
  rw [hpart]
  ring

end FractionalPrimes.Literature.MobiusToLong
