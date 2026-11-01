module

public import Mathlib.NumberTheory.AbelSummation
public import FractionalPrimes.Literature.MobiusToLong.ReciprocalMobiusMoments

@[expose] public section

open MeasureTheory

namespace FractionalPrimes.Literature.MobiusToLong

theorem mobius_reciprocal_finite_abel_from_one {Y : ℝ} (hY : 1 ≤ Y) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) =
      mobiusSummatory Y / Y +
        ∫ t in Set.Ioc 1 Y, mobiusSummatory t / t ^ 2 := by
  have h1pos : 0 < (1 : ℝ) := by norm_num
  have hfloorY : 1 ≤ Nat.floor Y := Nat.le_floor (by exact_mod_cast hY)
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) Y,
      DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le h1pos ht.1))).differentiableAt
  have hint : IntegrableOn (deriv (fun x : ℝ => x⁻¹)) (Set.Icc (1 : ℝ) Y) := by
    rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    have hpow : ContinuousOn (fun x : ℝ => x ^ 2) (Set.Icc (1 : ℝ) Y) := by fun_prop
    exact (hpow.inv₀ fun t ht => pow_ne_zero 2
      (ne_of_gt (lt_of_lt_of_le h1pos ht.1))).neg
  have habel := sum_mul_eq_sub_sub_integral_mul
    (c := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ))
    (f := fun x : ℝ => x⁻¹) (show 0 ≤ (1 : ℝ) by norm_num) hY hdiff hint
  have hsumY :
      (∑ n ∈ Finset.Icc 0 (Nat.floor Y), (ArithmeticFunction.moebius n : ℝ)) =
        mobiusSummatory Y := by
    change mobiusSummatoryFromZero Y = mobiusSummatory Y
    exact (mobiusSummatory_eq_fromZero Y).symm
  have hsum1 :
      (∑ n ∈ Finset.Icc 0 (Nat.floor (1 : ℝ)), (ArithmeticFunction.moebius n : ℝ)) =
        mobiusSummatory 1 := by
    change mobiusSummatoryFromZero 1 = mobiusSummatory 1
    exact (mobiusSummatory_eq_fromZero 1).symm
  have habel' := habel
  rw [hsumY, hsum1, Nat.floor_one] at habel'
  have hInt :
      (∫ t in Set.Ioc 1 Y,
          deriv (fun x : ℝ => x⁻¹) t *
            (∑ n ∈ Finset.Icc 0 (Nat.floor t), (ArithmeticFunction.moebius n : ℝ))) =
        -(∫ t in Set.Ioc 1 Y, mobiusSummatory t / t ^ 2) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv (fun x : ℝ => x⁻¹) t *
        (∑ n ∈ Finset.Icc 0 (Nat.floor t), (ArithmeticFunction.moebius n : ℝ)) =
      -(mobiusSummatory t / t ^ 2)
    have hpart :
        (∑ n ∈ Finset.Icc 0 (Nat.floor t), (ArithmeticFunction.moebius n : ℝ)) =
          mobiusSummatory t := by
      change mobiusSummatoryFromZero t = mobiusSummatory t
      exact (mobiusSummatory_eq_fromZero t).symm
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans h1pos ht.1)
    rw [hpart, deriv_inv]
    field_simp [ht0]
  have hsumIoc :
      (∑ n ∈ Finset.Ioc 1 (Nat.floor Y),
          (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) =
        ∑ n ∈ Finset.Ioc 1 (Nat.floor Y),
          (fun x : ℝ => x⁻¹) n * (ArithmeticFunction.moebius n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [div_eq_mul_inv, mul_comm]
  have hM1 : mobiusSummatory 1 = 1 := by
    simp [mobiusSummatory]
  have hIoc :
      (∑ n ∈ Finset.Ioc 1 (Nat.floor Y),
          (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) =
        mobiusSummatory Y / Y - 1 +
          ∫ t in Set.Ioc 1 Y, mobiusSummatory t / t ^ 2 := by
    rw [hsumIoc]
    calc
      _ = Y⁻¹ * mobiusSummatory Y - (1 : ℝ)⁻¹ * mobiusSummatory 1 -
            ∫ t in Set.Ioc 1 Y,
              deriv (fun x : ℝ => x⁻¹) t *
                (∑ n ∈ Finset.Icc 0 (Nat.floor t), (ArithmeticFunction.moebius n : ℝ)) :=
          habel'
      _ = mobiusSummatory Y / Y - 1 +
            ∫ t in Set.Ioc 1 Y, mobiusSummatory t / t ^ 2 := by
          rw [hInt, hM1]
          norm_num
          ring
  rw [Finset.Icc_eq_cons_Ioc hfloorY, Finset.sum_cons, hIoc]
  simp
  ring

end FractionalPrimes.Literature.MobiusToLong
