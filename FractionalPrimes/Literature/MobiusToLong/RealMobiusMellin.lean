module

public import FractionalPrimes.Literature.MobiusToLong.ReciprocalMobiusMoments
public import FractionalPrimes.Literature.MobiusToLong.MobiusDirichletIntegralHelper

@[expose] public section

open Set MeasureTheory

namespace FractionalPrimes.Literature.MobiusToLong

noncomputable section

/-- Finite Abel summation for the positive-index Möbius Dirichlet polynomial.
The cutoff is real and the finite sum uses the floor convention from the
approved blueprint. -/
theorem mobius_dirichlet_finite_abel_from_one {σ Y : ℝ} (hY : 1 ≤ Y) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ)) =
      mobiusSummatory Y * Y ^ (-σ) +
        σ * ∫ t in Set.Ioc 1 Y,
          mobiusSummatory t * t ^ (-(σ + 1)) := by
  have hYpos : 0 < Y := by linarith
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) Y,
      DifferentiableAt ℝ (fun x : ℝ => x ^ (-σ)) t := by
    intro t ht
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))).differentiableAt
  have hderiv : deriv (fun x : ℝ => x ^ (-σ)) =
      fun x => (-σ) * x ^ (-(σ + 1)) := by
    funext x
    rw [Real.deriv_rpow_const]
    congr 1
    ring
  have hderivCont : ContinuousOn
      (fun x : ℝ => (-σ) * x ^ (-(σ + 1))) (Set.Icc 1 Y) := by
    apply ContinuousOn.const_mul
    exact ContinuousOn.rpow_const continuousOn_id fun t ht =>
      Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hint : IntegrableOn (deriv (fun x : ℝ => x ^ (-σ)))
      (Set.Icc 1 Y) := by
    rw [hderiv]
    exact hderivCont.integrableOn_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul
    (c := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ))
    (f := fun x : ℝ => x ^ (-σ)) (show 0 ≤ (1 : ℝ) by norm_num) hY hdiff hint
  have hM_Y :
      (∑ n ∈ Finset.Icc 0 (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ)) = mobiusSummatory Y := by
    change mobiusSummatoryFromZero Y = mobiusSummatory Y
    exact (mobiusSummatory_eq_fromZero Y).symm
  have hM_one :
      (∑ n ∈ Finset.Icc 0 (Nat.floor (1 : ℝ)),
        (ArithmeticFunction.moebius n : ℝ)) = 1 := by
    have hμ0 : (ArithmeticFunction.moebius 0 : ℝ) = 0 := by
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by simp)]
      norm_num
    have hμ1 : (ArithmeticFunction.moebius 1 : ℝ) = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_apply_one
    change mobiusSummatoryFromZero 1 = 1
    rw [mobiusSummatoryFromZero, Nat.floor_one, Finset.sum_Icc_succ_top (by omega)]
    simp [hμ0, hμ1]
  have habel' := habel
  rw [hM_Y, hM_one, hderiv] at habel'
  rw [Nat.floor_one] at habel'
  rw [mobius_dirichlet_integral_fromZero_eq] at habel'
  have hsplit :
      (∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ)) =
        (1 : ℝ) + ∑ n ∈ Finset.Ioc 1 (Nat.floor Y),
          (n : ℝ) ^ (-σ) * (ArithmeticFunction.moebius n : ℝ) := by
    have hfloor : 1 ≤ Nat.floor Y := Nat.le_floor (by exact_mod_cast hY)
    rw [Finset.Icc_eq_cons_Ioc hfloor, Finset.sum_cons]
    have hμ1 : (ArithmeticFunction.moebius 1 : ℝ) = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_apply_one
    simp only [Nat.cast_one, hμ1, Real.one_rpow, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hsplit, habel']
  rw [show (1 : ℝ) ^ (-σ) = 1 by simp]
  rw [← integral_const_mul]
  ring

end
end FractionalPrimes.Literature.MobiusToLong
