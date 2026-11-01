module

public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import FractionalPrimes.Literature.MobiusToLong.LogPowerLimit
public import FractionalPrimes.Literature.MobiusToLong.LogReciprocalDerivative

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology
open scoped ArithmeticFunction.Moebius

namespace FractionalPrimes.Literature.MobiusToLong

noncomputable section

/-- The ordered Möbius summatory function at a real cutoff. -/
def mobiusSummatory (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), (ArithmeticFunction.moebius n : ℝ)

/-- The summatory function with the zeroth coefficient included, as used by
Mathlib's Abel-summation API. -/
def mobiusSummatoryFromZero (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 (Nat.floor x), (ArithmeticFunction.moebius n : ℝ)

theorem mobiusSummatory_eq_fromZero (x : ℝ) :
    mobiusSummatory x = mobiusSummatoryFromZero x := by
  have hset : Finset.Icc (1 : ℕ) (Nat.floor x) = Finset.Ioc 0 (Nat.floor x) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hμ0 : (ArithmeticFunction.moebius 0 : ℝ) = 0 := by
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by simp)]
    norm_num
  rw [mobiusSummatory, mobiusSummatoryFromZero, hset,
    Finset.Icc_eq_cons_Ioc (show 0 ≤ Nat.floor x by omega), Finset.sum_cons, hμ0, zero_add]

/-- Finite Abel summation for the reciprocal Möbius coefficient on a real
interval. The endpoints need not be integers. -/
theorem mobius_reciprocal_finite_abel {D Y : ℝ}
    (hD : 3 ≤ D) (hDY : D ≤ Y) :
    (∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) =
      mobiusSummatory Y / Y - mobiusSummatory D / D +
        ∫ t in Set.Ioc D Y, mobiusSummatory t / t ^ 2 := by
  have hDpos : 0 < D := by linarith
  have hdiff : ∀ t ∈ Set.Icc D Y, DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le hDpos ht.1))).differentiableAt
  have hint : IntegrableOn (deriv (fun x : ℝ => x⁻¹)) (Set.Icc D Y) := by
    rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    have hpow : ContinuousOn (fun x : ℝ => x ^ 2) (Set.Icc D Y) := by fun_prop
    exact (hpow.inv₀ fun t ht => pow_ne_zero 2
      (ne_of_gt (lt_of_lt_of_le hDpos ht.1))).neg
  have habel := sum_mul_eq_sub_sub_integral_mul
    (c := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ))
    (f := fun x : ℝ => x⁻¹) (show 0 ≤ D by linarith) hDY hdiff hint
  have hsumY :
      (∑ n ∈ Finset.Icc 0 (Nat.floor Y), (ArithmeticFunction.moebius n : ℝ)) =
        mobiusSummatory Y := by
    change mobiusSummatoryFromZero Y = mobiusSummatory Y
    exact (mobiusSummatory_eq_fromZero Y).symm
  have hsumD :
      (∑ n ∈ Finset.Icc 0 (Nat.floor D), (ArithmeticFunction.moebius n : ℝ)) =
        mobiusSummatory D := by
    change mobiusSummatoryFromZero D = mobiusSummatory D
    exact (mobiusSummatory_eq_fromZero D).symm
  have habel' := habel
  rw [hsumY, hsumD] at habel'
  have hInt :
      (∫ t in Set.Ioc D Y,
          deriv (fun x : ℝ => x⁻¹) t *
            (∑ n ∈ Finset.Icc 0 (Nat.floor t), (ArithmeticFunction.moebius n : ℝ))) =
        -(∫ t in Set.Ioc D Y, mobiusSummatory t / t ^ 2) := by
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
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans hDpos ht.1)
    rw [hpart, deriv_inv]
    field_simp [ht0]
  have hsum :
      (∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
          (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) =
        ∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
          (fun x : ℝ => x⁻¹) n * (ArithmeticFunction.moebius n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [div_eq_mul_inv, mul_comm]
  rw [hsum]
  calc
    _ = Y⁻¹ * mobiusSummatory Y - D⁻¹ * mobiusSummatory D -
          ∫ t in Set.Ioc D Y,
            deriv (fun x : ℝ => x⁻¹) t *
              (∑ n ∈ Finset.Icc 0 (Nat.floor t), (ArithmeticFunction.moebius n : ℝ)) :=
      habel'
    _ = mobiusSummatory Y / Y - mobiusSummatory D / D +
          ∫ t in Set.Ioc D Y, mobiusSummatory t / t ^ 2 := by
      rw [hInt]
      ring

/-- Finite Abel summation for the logarithmically weighted reciprocal Möbius
coefficient on a real interval. -/
theorem mobius_log_reciprocal_finite_abel {D Y : ℝ}
    (hD : 3 ≤ D) (hDY : D ≤ Y) :
    (∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) =
      mobiusSummatory Y * (Real.log Y / Y) -
        mobiusSummatory D * (Real.log D / D) +
          ∫ t in Set.Ioc D Y,
            mobiusSummatory t * ((Real.log t - 1) / t ^ 2) := by
  have hDpos : 0 < D := by linarith
  let f : ℝ → ℝ := fun x => Real.log x * x⁻¹
  have hdiff : ∀ t ∈ Set.Icc D Y, DifferentiableAt ℝ f t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hDpos ht.1
    exact ((Real.hasDerivAt_log (ne_of_gt htpos)).mul
      (hasDerivAt_inv (ne_of_gt htpos))).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc D Y,
      deriv f t = (1 - Real.log t) / t ^ 2 := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hDpos ht.1
    have htne : t ≠ 0 := ne_of_gt htpos
    change deriv (fun x : ℝ => Real.log x * x⁻¹) t = _
    exact log_reciprocal_weight_deriv htne
  have hint : IntegrableOn (deriv f) (Set.Icc D Y) := by
    have hlog : ContinuousOn Real.log (Set.Icc D Y) :=
      Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (lt_of_lt_of_le hDpos ht.1)
    have hnum : ContinuousOn (fun t : ℝ => 1 - Real.log t) (Set.Icc D Y) :=
      continuousOn_const.sub hlog
    have hpow : ContinuousOn (fun t : ℝ => t ^ 2) (Set.Icc D Y) := by
      fun_prop
    have hinv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc D Y) :=
      hpow.inv₀ fun t ht => pow_ne_zero 2
        (ne_of_gt (lt_of_lt_of_le hDpos ht.1))
    have hcont :
        ContinuousOn (fun t : ℝ => (1 - Real.log t) / t ^ 2) (Set.Icc D Y) := by
      change ContinuousOn (fun t : ℝ => (1 - Real.log t) * (t ^ 2)⁻¹)
        (Set.Icc D Y)
      exact hnum.mul hinv
    have hderivcont : ContinuousOn (deriv f) (Set.Icc D Y) :=
      hcont.congr fun t ht => hderiv t ht
    exact hderivcont.integrableOn_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul
    (c := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ))
    (f := f) (show 0 ≤ D by linarith) hDY hdiff hint
  have hsumY :
      (∑ n ∈ Finset.Icc 0 (Nat.floor Y),
          (ArithmeticFunction.moebius n : ℝ)) = mobiusSummatory Y := by
    change mobiusSummatoryFromZero Y = mobiusSummatory Y
    exact (mobiusSummatory_eq_fromZero Y).symm
  have hsumD :
      (∑ n ∈ Finset.Icc 0 (Nat.floor D),
          (ArithmeticFunction.moebius n : ℝ)) = mobiusSummatory D := by
    change mobiusSummatoryFromZero D = mobiusSummatory D
    exact (mobiusSummatory_eq_fromZero D).symm
  have habel' := habel
  rw [hsumY, hsumD] at habel'
  have hInt :
      (∫ t in Set.Ioc D Y,
          deriv f t *
            (∑ n ∈ Finset.Icc 0 (Nat.floor t),
              (ArithmeticFunction.moebius n : ℝ))) =
        -(∫ t in Set.Ioc D Y,
          mobiusSummatory t * ((Real.log t - 1) / t ^ 2)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv f t *
        (∑ n ∈ Finset.Icc 0 (Nat.floor t),
          (ArithmeticFunction.moebius n : ℝ)) =
      -(mobiusSummatory t * ((Real.log t - 1) / t ^ 2))
    have hpart :
        (∑ n ∈ Finset.Icc 0 (Nat.floor t),
          (ArithmeticFunction.moebius n : ℝ)) = mobiusSummatory t := by
      change mobiusSummatoryFromZero t = mobiusSummatory t
      exact (mobiusSummatory_eq_fromZero t).symm
    have htmem : t ∈ Set.Icc D Y := ⟨ht.1.le, ht.2⟩
    rw [hpart, hderiv t htmem]
    ring
  have hsum :
      (∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
          (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) =
        ∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y), f n *
          (ArithmeticFunction.moebius n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [f, div_eq_mul_inv]
    ring
  rw [hsum]
  calc
    _ = f Y * mobiusSummatory Y - f D * mobiusSummatory D -
          ∫ t in Set.Ioc D Y,
            deriv f t *
              (∑ n ∈ Finset.Icc 0 (Nat.floor t),
                (ArithmeticFunction.moebius n : ℝ)) := habel'
    _ = mobiusSummatory Y * (Real.log Y / Y) -
          mobiusSummatory D * (Real.log D / D) +
            ∫ t in Set.Ioc D Y,
              mobiusSummatory t * ((Real.log t - 1) / t ^ 2) := by
      rw [hInt]
      dsimp [f]
      ring

/-- Finite logarithmic Abel summation from the initial endpoint `1`. This
separate adapter retains the full positive-integer partial sum; its `n = 1`
term vanishes because `log 1 = 0`. -/
theorem mobius_log_reciprocal_finite_abel_from_one {Y : ℝ}
    (hY : 1 ≤ Y) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) =
      mobiusSummatory Y * (Real.log Y / Y) +
        ∫ t in Set.Ioc 1 Y,
          mobiusSummatory t * ((Real.log t - 1) / t ^ 2) := by
  have h1pos : 0 < (1 : ℝ) := by norm_num
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) Y,
      DifferentiableAt ℝ (fun x : ℝ => Real.log x * x⁻¹) t := by
    intro t ht
    exact ((Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le h1pos ht.1))).mul
      (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le h1pos ht.1)))).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc (1 : ℝ) Y,
      deriv (fun x : ℝ => Real.log x * x⁻¹) t =
        (1 - Real.log t) / t ^ 2 := by
    intro t ht
    exact log_reciprocal_weight_deriv
      (ne_of_gt (lt_of_lt_of_le h1pos ht.1))
  have hint : IntegrableOn
      (deriv (fun x : ℝ => Real.log x * x⁻¹)) (Set.Icc (1 : ℝ) Y) := by
    have hlog : ContinuousOn Real.log (Set.Icc (1 : ℝ) Y) :=
      Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (lt_of_lt_of_le h1pos ht.1)
    have hnum : ContinuousOn (fun t : ℝ => 1 - Real.log t)
        (Set.Icc (1 : ℝ) Y) := continuousOn_const.sub hlog
    have hpow : ContinuousOn (fun t : ℝ => t ^ 2)
        (Set.Icc (1 : ℝ) Y) := by fun_prop
    have hinv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹)
        (Set.Icc (1 : ℝ) Y) :=
      hpow.inv₀ fun t ht => pow_ne_zero 2
        (ne_of_gt (lt_of_lt_of_le h1pos ht.1))
    have hcont : ContinuousOn (fun t : ℝ => (1 - Real.log t) / t ^ 2)
        (Set.Icc (1 : ℝ) Y) := by
      change ContinuousOn (fun t : ℝ => (1 - Real.log t) * (t ^ 2)⁻¹)
        (Set.Icc (1 : ℝ) Y)
      exact hnum.mul hinv
    have hderivcont : ContinuousOn
        (deriv (fun x : ℝ => Real.log x * x⁻¹)) (Set.Icc (1 : ℝ) Y) :=
      hcont.congr fun t ht => hderiv t ht
    exact hderivcont.integrableOn_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul
    (c := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ))
    (f := fun x : ℝ => Real.log x * x⁻¹) (show 0 ≤ (1 : ℝ) by norm_num)
    hY hdiff hint
  have hsumY :
      (∑ n ∈ Finset.Icc 0 (Nat.floor Y),
          (ArithmeticFunction.moebius n : ℝ)) = mobiusSummatory Y := by
    change mobiusSummatoryFromZero Y = mobiusSummatory Y
    exact (mobiusSummatory_eq_fromZero Y).symm
  have hsum1 :
      (∑ n ∈ Finset.Icc 0 (Nat.floor (1 : ℝ)),
          (ArithmeticFunction.moebius n : ℝ)) = mobiusSummatory 1 := by
    change mobiusSummatoryFromZero 1 = mobiusSummatory 1
    exact (mobiusSummatory_eq_fromZero 1).symm
  have habel' := habel
  rw [hsumY, hsum1, Nat.floor_one] at habel'
  have hInt :
      (∫ t in Set.Ioc 1 Y,
          deriv (fun x : ℝ => Real.log x * x⁻¹) t *
            (∑ n ∈ Finset.Icc 0 (Nat.floor t),
              (ArithmeticFunction.moebius n : ℝ))) =
        -(∫ t in Set.Ioc 1 Y,
          mobiusSummatory t * ((Real.log t - 1) / t ^ 2)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv (fun x : ℝ => Real.log x * x⁻¹) t *
        (∑ n ∈ Finset.Icc 0 (Nat.floor t),
          (ArithmeticFunction.moebius n : ℝ)) =
      -(mobiusSummatory t * ((Real.log t - 1) / t ^ 2))
    have hpart :
        (∑ n ∈ Finset.Icc 0 (Nat.floor t),
          (ArithmeticFunction.moebius n : ℝ)) = mobiusSummatory t := by
      change mobiusSummatoryFromZero t = mobiusSummatory t
      exact (mobiusSummatory_eq_fromZero t).symm
    have htpos : 0 < t := by linarith [ht.1]
    rw [hpart, hderiv t ⟨ht.1.le, ht.2⟩]
    ring
  have hsum :
      (∑ n ∈ Finset.Icc 1 (Nat.floor Y),
          (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) =
        ∑ n ∈ Finset.Ioc 1 (Nat.floor Y),
          (fun x : ℝ => Real.log x * x⁻¹) n *
            (ArithmeticFunction.moebius n : ℝ) := by
    have hfloorY : 1 ≤ Nat.floor Y := Nat.le_floor (by exact_mod_cast hY)
    rw [Finset.Icc_eq_cons_Ioc hfloorY, Finset.sum_cons]
    simp [div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hsum]
  calc
    _ = (Real.log Y * Y⁻¹) * mobiusSummatory Y -
          (Real.log 1 * (1 : ℝ)⁻¹) * mobiusSummatory 1 -
            ∫ t in Set.Ioc 1 Y,
              deriv (fun x : ℝ => Real.log x * x⁻¹) t *
                (∑ n ∈ Finset.Icc 0 (Nat.floor t),
                  (ArithmeticFunction.moebius n : ℝ)) := habel'
    _ = mobiusSummatory Y * (Real.log Y / Y) +
          ∫ t in Set.Ioc 1 Y,
            mobiusSummatory t * ((Real.log t - 1) / t ^ 2) := by
      rw [hInt]
      simp
      ring

/-- The weighted upper-endpoint term is controlled by the lower logarithmic
scale whenever the endpoint lies beyond the lower cutoff. -/
theorem mobius_log_reciprocal_endpoint_bound {R C x : ℝ}
    (hC : 1 ≤ C) (hx : 3 ≤ x)
    (hM : ∀ y : ℝ, 3 ≤ y →
      |mobiusSummatory y| ≤ C * y * Real.rpow (Real.log y) (-R)) :
    |mobiusSummatory x * (Real.log x / x)| ≤
      C * Real.rpow (Real.log x) (1 - R) := by
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hCnonneg : 0 ≤ C := by linarith
  rw [abs_mul, abs_div, abs_of_pos hlogpos, abs_of_pos hxpos]
  calc
    |mobiusSummatory x| * (Real.log x / x) ≤
        (C * x * Real.rpow (Real.log x) (-R)) * (Real.log x / x) :=
      mul_le_mul_of_nonneg_right (hM x hx)
        (div_nonneg hlogpos.le hxpos.le)
    _ = C * (Real.rpow (Real.log x) (-R) * Real.log x) := by
      field_simp [ne_of_gt hxpos]
      <;> ring
    _ = C * Real.rpow (Real.log x) (1 - R) := by
      exact congrArg (fun z : ℝ => C * z)
        (realRpow_neg_mul_base_eq_one_sub hlogpos)

/-- Exact integral of the shifted logarithmic-power majorant for the second
reciprocal Möbius tail. -/
theorem reciprocal_log_power_shifted_Ioi_integral {R D : ℝ}
    (hR : 3 < R) (hD : 3 ≤ D) :
    (∫ t in Set.Ioi D, t⁻¹ * Real.rpow (Real.log t) (1 - R)) =
      Real.rpow (Real.log D) (2 - R) / (R - 2) := by
  have hDpos : 0 < D := by linarith
  have hDgt : 1 < D := by linarith
  have hlog : 0 < Real.log D := Real.log_pos hDgt
  have hsub :
      (∫ t in Set.Ioi D, t⁻¹ * Real.rpow (Real.log t) (1 - R)) =
        ∫ u in Set.Ioi (Real.log D), Real.rpow u (1 - R) := by
    simpa only [smul_eq_mul] using
      (MeasureTheory.integral_comp_log_Ioi
        (fun u : ℝ => Real.rpow u (1 - R)) hDpos)
  rw [hsub]
  simp only [Real.rpow_eq_pow]
  rw [integral_Ioi_rpow_of_lt (show 1 - R < -1 by linarith) hlog]
  rw [show (1 - R) + 1 = 2 - R by ring]
  have hRpos : 0 < R - 2 := by linarith
  have hden : 2 - R ≠ 0 := by linarith
  field_simp [hRpos.ne', hden]
  <;> ring

/-- The finite interval integral of the shifted logarithmic-power majorant is
bounded by its exact improper tail integral. -/
theorem reciprocal_log_power_shifted_interval_le {R D Y : ℝ}
    (hR : 3 < R) (hD : 3 ≤ D) (hDY : D ≤ Y) :
    (∫ t in D..Y, t⁻¹ * Real.rpow (Real.log t) (1 - R)) ≤
      Real.rpow (Real.log D) (2 - R) / (R - 2) := by
  have hDpos : 0 < D := by linarith
  have hDgt : 1 < D := by linarith
  have hlog : 0 < Real.log D := Real.log_pos hDgt
  have hIntegrable :
      IntegrableOn (fun t : ℝ => t⁻¹ * Real.rpow (Real.log t) (1 - R))
        (Set.Ioi D) := by
    simpa only [smul_eq_mul] using
      (MeasureTheory.integrableOn_comp_log_Ioi
        (fun u : ℝ => Real.rpow u (1 - R)) hDpos).2
        (integrableOn_Ioi_rpow_of_lt (show 1 - R < -1 by linarith) hlog)
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi D)]
        (fun t : ℝ => t⁻¹ * Real.rpow (Real.log t) (1 - R)) := by
    exact (ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun t ht => by
        have hDt : D < t := Set.mem_Ioi.mp ht
        have htpos : 0 < t := by linarith
        have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
        exact mul_nonneg (inv_nonneg.mpr htpos.le)
          (Real.rpow_nonneg hlogt.le _))
  calc
    (∫ t in D..Y, t⁻¹ * Real.rpow (Real.log t) (1 - R)) =
        ∫ t in Set.Ioc D Y, t⁻¹ * Real.rpow (Real.log t) (1 - R) := by
      rw [intervalIntegral.integral_of_le hDY]
    _ ≤ ∫ t in Set.Ioi D, t⁻¹ * Real.rpow (Real.log t) (1 - R) :=
      MeasureTheory.setIntegral_mono_set hIntegrable hNonneg
        Set.Ioc_subset_Ioi_self.eventuallySubset
    _ = Real.rpow (Real.log D) (2 - R) / (R - 2) :=
      reciprocal_log_power_shifted_Ioi_integral hR hD

/-- Uniform finite-Y tail bound for the logarithmically weighted reciprocal
Möbius coefficients. The constant and the real-cutoff endpoint convention
match the approved ordered-tail estimate. -/
theorem mobius_log_reciprocal_finite_uniform_tail_bound {R C D Y : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C) (hD : 3 ≤ D) (hDY : D ≤ Y)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    |∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)| ≤
      3 * C * Real.rpow (Real.log D) (2 - R) := by
  have hDpos : 0 < D := by linarith
  have hCnonneg : 0 ≤ C := by linarith
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have h := Real.le_log_one_add_of_nonneg (x := (2 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hlogDpos : 0 < Real.log D := Real.log_pos (by linarith)
  have hlogDone : 1 ≤ Real.log D :=
    hlog3.trans (Real.log_le_log (by norm_num : (0 : ℝ) < 3) hD)
  have hlogMono : Real.log D ≤ Real.log Y := Real.log_le_log hDpos hDY
  have hpowMono :
      Real.rpow (Real.log Y) (1 - R) ≤ Real.rpow (Real.log D) (1 - R) :=
    Real.rpow_le_rpow_of_nonpos hlogDpos hlogMono (by linarith)
  have hYendpoint := mobius_log_reciprocal_endpoint_bound hC
    (hD.trans hDY) hM
  have hDendpoint := mobius_log_reciprocal_endpoint_bound hC hD hM
  have hYterm :
      |mobiusSummatory Y * (Real.log Y / Y)| ≤
        C * Real.rpow (Real.log D) (1 - R) := by
    exact hYendpoint.trans
      (mul_le_mul_of_nonneg_left hpowMono hCnonneg)
  have hDterm :
      |mobiusSummatory D * (Real.log D / D)| ≤
        C * Real.rpow (Real.log D) (1 - R) := hDendpoint
  let g : ℝ → ℝ := fun t => t⁻¹ * Real.rpow (Real.log t) (1 - R)
  have hg_cont : ContinuousOn g (Set.Icc D Y) := by
    change ContinuousOn
      (fun t : ℝ => t⁻¹ * Real.rpow (Real.log t) (1 - R)) (Set.Icc D Y)
    have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc D Y) :=
      continuousOn_id.inv₀ fun t ht =>
        ne_of_gt (lt_of_lt_of_le hDpos ht.1)
    have hlog : ContinuousOn Real.log (Set.Icc D Y) :=
      Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (lt_of_lt_of_le hDpos ht.1)
    have hlogpos : ∀ t ∈ Set.Icc D Y, 0 < Real.log t := by
      intro t ht
      apply Real.log_pos
      linarith [hD, ht.1]
    have hpow :
        ContinuousOn (fun t : ℝ => Real.rpow (Real.log t) (1 - R))
          (Set.Icc D Y) := by
      exact hlog.rpow_const fun t ht => Or.inl (ne_of_gt (hlogpos t ht))
    exact hinv.mul hpow
  have hg_int : IntegrableOn g (Set.Ioc D Y) :=
    (hg_cont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hgC_int : Integrable (fun t => C * g t)
      (volume.restrict (Set.Ioc D Y)) := hg_int.const_mul C
  have hpoint : ∀ t ∈ Set.Ioc D Y,
      |mobiusSummatory t * ((Real.log t - 1) / t ^ 2)| ≤ C * g t := by
    intro t ht
    have ht3 : 3 ≤ t := hD.trans ht.1.le
    have htpos : 0 < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
    have hlogone : 1 ≤ Real.log t :=
      hlog3.trans (Real.log_le_log (by norm_num : (0 : ℝ) < 3) ht3)
    have hcoeff : 0 ≤ (Real.log t - 1) / t ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg t)
    have htM := hM t ht3
    rw [abs_mul_log_kernel_eq htpos hlogone]
    change |mobiusSummatory t| * ((Real.log t - 1) / t ^ 2) ≤
      C * (t⁻¹ * Real.rpow (Real.log t) (1 - R))
    calc
      |mobiusSummatory t| * ((Real.log t - 1) / t ^ 2) ≤
          (C * t * Real.rpow (Real.log t) (-R)) *
            ((Real.log t - 1) / t ^ 2) :=
        mul_le_mul_of_nonneg_right htM hcoeff
      _ ≤ (C * t * Real.rpow (Real.log t) (-R)) *
            (Real.log t / t ^ 2) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (mul_nonneg hCnonneg htpos.le)
            (Real.rpow_nonneg hlogpos.le _))
        exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg t)
      _ = C * (t⁻¹ * Real.rpow (Real.log t) (1 - R)) := by
        calc
          _ = C * ((Real.rpow (Real.log t) (-R) * Real.log t) / t) := by
            field_simp [ne_of_gt htpos]
            <;> ring
          _ = C * (t⁻¹ * Real.rpow (Real.log t) (1 - R)) := by
            rw [realRpow_neg_mul_base_eq_one_sub hlogpos]
            ring
  have hdom : ∀ᵐ t ∂(volume.restrict (Set.Ioc D Y)),
      ‖mobiusSummatory t * ((Real.log t - 1) / t ^ 2)‖ ≤ C * g t := by
    exact (ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun t ht => by
        simpa only [Real.norm_eq_abs] using hpoint t ht)
  have hIntBound :
      |∫ t in Set.Ioc D Y,
          mobiusSummatory t * ((Real.log t - 1) / t ^ 2)| ≤
        C * ∫ t in Set.Ioc D Y, g t := by
    have hnorm := norm_integral_le_of_norm_le hgC_int hdom
    simpa [Real.norm_eq_abs, g, integral_const_mul] using hnorm
  have hIntegralTail :
      C * ∫ t in Set.Ioc D Y, g t ≤
        C * (Real.rpow (Real.log D) (2 - R) / (R - 2)) := by
    have h := reciprocal_log_power_shifted_interval_le hR hD hDY
    rw [intervalIntegral.integral_of_le hDY] at h
    exact mul_le_mul_of_nonneg_left (by simpa only [g] using h) hCnonneg
  have hsmall :
      Real.rpow (Real.log D) (1 - R) ≤ Real.rpow (Real.log D) (2 - R) :=
    Real.rpow_le_rpow_of_exponent_le hlogDone (by linarith)
  have hpowerNonneg : 0 ≤ Real.rpow (Real.log D) (2 - R) :=
    Real.rpow_nonneg hlogDpos.le _
  have hdiv :
      Real.rpow (Real.log D) (2 - R) / (R - 2) ≤
        Real.rpow (Real.log D) (2 - R) :=
    div_le_self hpowerNonneg (by linarith : 1 ≤ R - 2)
  calc
    |∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)| =
      |mobiusSummatory Y * (Real.log Y / Y) -
        mobiusSummatory D * (Real.log D / D) +
          ∫ t in Set.Ioc D Y,
            mobiusSummatory t * ((Real.log t - 1) / t ^ 2)| := by
      rw [mobius_log_reciprocal_finite_abel hD hDY]
    _ ≤ |mobiusSummatory Y * (Real.log Y / Y)| +
          |mobiusSummatory D * (Real.log D / D)| +
          |∫ t in Set.Ioc D Y,
            mobiusSummatory t * ((Real.log t - 1) / t ^ 2)| := by
      calc
        _ ≤ |mobiusSummatory Y * (Real.log Y / Y) -
              mobiusSummatory D * (Real.log D / D)| +
              |∫ t in Set.Ioc D Y,
                mobiusSummatory t * ((Real.log t - 1) / t ^ 2)| := abs_add_le _ _
        _ ≤ (|mobiusSummatory Y * (Real.log Y / Y)| +
              |mobiusSummatory D * (Real.log D / D)|) +
              |∫ t in Set.Ioc D Y,
                mobiusSummatory t * ((Real.log t - 1) / t ^ 2)| := by
          simpa using add_le_add_right
            (abs_sub_le (mobiusSummatory Y * (Real.log Y / Y)) 0
              (mobiusSummatory D * (Real.log D / D)))
            |∫ t in Set.Ioc D Y,
              mobiusSummatory t * ((Real.log t - 1) / t ^ 2)|
        _ = _ := by ring
    _ ≤ (C * Real.rpow (Real.log D) (1 - R) +
          C * Real.rpow (Real.log D) (1 - R)) +
          C * ∫ t in Set.Ioc D Y, g t := by
      exact add_le_add (add_le_add hYterm hDterm) hIntBound
    _ ≤ (C * Real.rpow (Real.log D) (1 - R) +
          C * Real.rpow (Real.log D) (1 - R)) +
          C * (Real.rpow (Real.log D) (2 - R) / (R - 2)) :=
      add_le_add (le_rfl) hIntegralTail
    _ ≤ 3 * C * Real.rpow (Real.log D) (2 - R) := by
      calc
        _ ≤ (C * Real.rpow (Real.log D) (2 - R) +
              C * Real.rpow (Real.log D) (2 - R)) +
              C * Real.rpow (Real.log D) (2 - R) := by
          apply add_le_add
          · exact add_le_add
              (mul_le_mul_of_nonneg_left hsmall hCnonneg)
              (mul_le_mul_of_nonneg_left hsmall hCnonneg)
          · exact mul_le_mul_of_nonneg_left hdiv hCnonneg
        _ = 3 * C * Real.rpow (Real.log D) (2 - R) := by ring

/-- A finite-cutoff reciprocal Möbius estimate. The upper endpoint term is
kept explicit; it vanishes only after a later limit in `Y`. -/
theorem mobius_reciprocal_finite_tail_bound {R C D Y : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C) (hD : 3 ≤ D) (hDY : D ≤ Y)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    |∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤
      |mobiusSummatory Y / Y| +
        C * Real.rpow (Real.log D) (-R) +
          C * ∫ t in Set.Ioc D Y, t⁻¹ * Real.rpow (Real.log t) (-R) := by
  have hDpos : 0 < D := by linarith
  have hCnonneg : 0 ≤ C := by linarith
  let g : ℝ → ℝ := fun t => t⁻¹ * Real.rpow (Real.log t) (-R)
  have hg_cont : ContinuousOn g (Set.Icc D Y) := by
    change ContinuousOn (fun t : ℝ => t⁻¹ * Real.rpow (Real.log t) (-R))
      (Set.Icc D Y)
    have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc D Y) :=
      continuousOn_id.inv₀ fun t ht =>
        ne_of_gt (lt_of_lt_of_le hDpos ht.1)
    have hlog : ContinuousOn Real.log (Set.Icc D Y) :=
      Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (lt_of_lt_of_le hDpos ht.1)
    have hlogpos : ∀ t ∈ Set.Icc D Y, 0 < Real.log t := by
      intro t ht
      apply Real.log_pos
      linarith [hD, ht.1]
    have hpow : ContinuousOn (fun t : ℝ => Real.rpow (Real.log t) (-R))
        (Set.Icc D Y) := by
      exact hlog.rpow_const fun t ht => Or.inl (ne_of_gt (hlogpos t ht))
    exact hinv.mul hpow
  have hg_int : IntegrableOn g (Set.Ioc D Y) :=
    (hg_cont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hgC_int : Integrable (fun t => C * g t) (volume.restrict (Set.Ioc D Y)) := by
    exact hg_int.const_mul C
  have hpoint : ∀ t ∈ Set.Ioc D Y,
      |mobiusSummatory t / t ^ 2| ≤ C * g t := by
    intro t ht
    have ht3 : 3 ≤ t := hD.trans ht.1.le
    have htpos : 0 < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
    have htM := hM t ht3
    rw [abs_div, abs_of_pos (sq_pos_of_pos htpos)]
    calc
      |mobiusSummatory t| / t ^ 2 ≤
          (C * t * Real.rpow (Real.log t) (-R)) / t ^ 2 :=
        div_le_div_of_nonneg_right htM (sq_nonneg t)
      _ = C * g t := by
        dsimp [g]
        field_simp [ne_of_gt htpos]
        <;> ring
  have hdom : ∀ᵐ t ∂(volume.restrict (Set.Ioc D Y)),
      ‖mobiusSummatory t / t ^ 2‖ ≤ C * g t := by
    exact (ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun t ht => by
        simpa only [Real.norm_eq_abs] using hpoint t ht)
  have hIntBound :
      |∫ t in Set.Ioc D Y, mobiusSummatory t / t ^ 2| ≤
        C * ∫ t in Set.Ioc D Y, g t := by
    have hnorm := norm_integral_le_of_norm_le hgC_int hdom
    simpa [Real.norm_eq_abs, g, integral_const_mul] using hnorm
  have hDterm :
      |mobiusSummatory D / D| ≤ C * Real.rpow (Real.log D) (-R) := by
    rw [abs_div, abs_of_pos hDpos]
    calc
      |mobiusSummatory D| / D ≤
          (C * D * Real.rpow (Real.log D) (-R)) / D :=
        div_le_div_of_nonneg_right (hM D hD) hDpos.le
      _ = C * Real.rpow (Real.log D) (-R) := by
        field_simp [ne_of_gt hDpos]
  have habel := mobius_reciprocal_finite_abel hD hDY
  calc
    |∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| =
      |mobiusSummatory Y / Y - mobiusSummatory D / D +
          ∫ t in Set.Ioc D Y, mobiusSummatory t / t ^ 2| := by rw [habel]
    _ ≤ |mobiusSummatory Y / Y| + |mobiusSummatory D / D| +
          |∫ t in Set.Ioc D Y, mobiusSummatory t / t ^ 2| := by
      calc
        _ ≤ |mobiusSummatory Y / Y - mobiusSummatory D / D| +
              |∫ t in Set.Ioc D Y, mobiusSummatory t / t ^ 2| := abs_add_le _ _
        _ ≤ (|mobiusSummatory Y / Y| + |mobiusSummatory D / D|) +
              |∫ t in Set.Ioc D Y, mobiusSummatory t / t ^ 2| := by
          simpa using add_le_add_right
            (abs_sub_le (mobiusSummatory Y / Y) 0 (mobiusSummatory D / D))
            |∫ t in Set.Ioc D Y, mobiusSummatory t / t ^ 2|
        _ = _ := by ring
    _ ≤ |mobiusSummatory Y / Y| + C * Real.rpow (Real.log D) (-R) +
          C * ∫ t in Set.Ioc D Y, g t := by
      have hEndpoints :
          |mobiusSummatory Y / Y| + |mobiusSummatory D / D| ≤
            |mobiusSummatory Y / Y| + C * Real.rpow (Real.log D) (-R) :=
        calc
          |mobiusSummatory Y / Y| + |mobiusSummatory D / D| =
              |mobiusSummatory D / D| + |mobiusSummatory Y / Y| := add_comm _ _
          _ ≤ C * Real.rpow (Real.log D) (-R) + |mobiusSummatory Y / Y| :=
            add_le_add_left hDterm _
          _ = |mobiusSummatory Y / Y| + C * Real.rpow (Real.log D) (-R) :=
            add_comm _ _
      exact add_le_add hEndpoints hIntBound

/-- Decompose an interval sum over `(m, n]` as the difference of the positive
integer partial sums through `n` and `m`. -/
theorem sum_Ioc_eq_sum_Icc_sub_of_le {m n : ℕ} (hmn : m ≤ n) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Ioc m n, f k) =
      (∑ k ∈ Finset.Icc 1 n, f k) - (∑ k ∈ Finset.Icc 1 m, f k) := by
  have hsub : Finset.Icc 1 m ⊆ Finset.Icc 1 n := by
    intro k hk
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hmn⟩
  have hdiff : Finset.Icc 1 n \ Finset.Icc 1 m = Finset.Ioc m n := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← hdiff, ← Finset.sum_sdiff hsub]
  ring

/-- Exact integral of the logarithmic-power majorant used for the first
reciprocal Möbius tail. -/
theorem reciprocal_log_power_Ioi_integral {R D : ℝ}
    (hR : 3 < R) (hD : 3 ≤ D) :
    (∫ t in Set.Ioi D, t⁻¹ * Real.rpow (Real.log t) (-R)) =
      Real.rpow (Real.log D) (1 - R) / (R - 1) := by
  have hDpos : 0 < D := by linarith
  have hDgt : 1 < D := by linarith
  have hlog : 0 < Real.log D := Real.log_pos hDgt
  have hsub :
      (∫ t in Set.Ioi D, t⁻¹ * Real.rpow (Real.log t) (-R)) =
        ∫ u in Set.Ioi (Real.log D), Real.rpow u (-R) := by
    simpa only [smul_eq_mul] using
      (MeasureTheory.integral_comp_log_Ioi
        (fun u : ℝ => Real.rpow u (-R)) hDpos)
  rw [hsub]
  simp only [Real.rpow_eq_pow]
  rw [integral_Ioi_rpow_of_lt (show -R < -1 by linarith) hlog]
  rw [show -R + 1 = 1 - R by ring]
  have hRpos : 0 < R - 1 := by linarith
  have hden : 1 - R ≠ 0 := by linarith
  field_simp [hRpos.ne', hden]
  <;> ring

/-- The finite interval integral of the logarithmic-power majorant is bounded
by its exact improper tail integral. -/
theorem reciprocal_log_power_interval_le {R D Y : ℝ}
    (hR : 3 < R) (hD : 3 ≤ D) (hDY : D ≤ Y) :
    (∫ t in D..Y, t⁻¹ * Real.rpow (Real.log t) (-R)) ≤
      Real.rpow (Real.log D) (1 - R) / (R - 1) := by
  have hDpos : 0 < D := by linarith
  have hDgt : 1 < D := by linarith
  have hlog : 0 < Real.log D := Real.log_pos hDgt
  have hIntegrable :
      IntegrableOn (fun t : ℝ => t⁻¹ * Real.rpow (Real.log t) (-R))
        (Set.Ioi D) := by
    simpa only [smul_eq_mul] using
      (MeasureTheory.integrableOn_comp_log_Ioi
        (fun u : ℝ => Real.rpow u (-R)) hDpos).2
        (integrableOn_Ioi_rpow_of_lt (show -R < -1 by linarith) hlog)
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi D)]
        (fun t : ℝ => t⁻¹ * Real.rpow (Real.log t) (-R)) := by
    exact (ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun t ht => by
        have hDt : D < t := Set.mem_Ioi.mp ht
        have htpos : 0 < t := by linarith
        have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
        exact mul_nonneg (inv_nonneg.mpr htpos.le)
          (Real.rpow_nonneg hlogt.le _))
  calc
    (∫ t in D..Y, t⁻¹ * Real.rpow (Real.log t) (-R)) =
        ∫ t in Set.Ioc D Y, t⁻¹ * Real.rpow (Real.log t) (-R) := by
      rw [intervalIntegral.integral_of_le hDY]
    _ ≤ ∫ t in Set.Ioi D, t⁻¹ * Real.rpow (Real.log t) (-R) :=
      MeasureTheory.setIntegral_mono_set hIntegrable hNonneg
        Set.Ioc_subset_Ioi_self.eventuallySubset
    _ = Real.rpow (Real.log D) (1 - R) / (R - 1) :=
      reciprocal_log_power_Ioi_integral hR hD

/-- Uniform finite-Y reciprocal Möbius tail bound, with the upper endpoint
controlled by the same logarithmic scale as the lower endpoint. -/
theorem mobius_reciprocal_finite_uniform_tail_bound {R C D Y : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C) (hD : 3 ≤ D) (hDY : D ≤ Y)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    |∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤
      C * (2 * Real.rpow (Real.log D) (-R) +
        Real.rpow (Real.log D) (1 - R) / (R - 1)) := by
  have hDpos : 0 < D := by linarith
  have hYpos : 0 < Y := by linarith
  have hCnonneg : 0 ≤ C := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos (by linarith)
  have hlogMono : Real.log D ≤ Real.log Y := Real.log_le_log hDpos hDY
  have hYterm :
      |mobiusSummatory Y / Y| ≤ C * Real.rpow (Real.log D) (-R) := by
    rw [abs_div, abs_of_pos hYpos]
    calc
      |mobiusSummatory Y| / Y ≤
          (C * Y * Real.rpow (Real.log Y) (-R)) / Y :=
        div_le_div_of_nonneg_right (hM Y (hD.trans hDY)) hYpos.le
      _ = C * Real.rpow (Real.log Y) (-R) := by
        field_simp [ne_of_gt hYpos]
      _ ≤ C * Real.rpow (Real.log D) (-R) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hlogD hlogMono (by linarith)) hCnonneg
  have hInt :
      (∫ t in Set.Ioc D Y, t⁻¹ * Real.rpow (Real.log t) (-R)) ≤
        Real.rpow (Real.log D) (1 - R) / (R - 1) := by
    have h := reciprocal_log_power_interval_le hR hD hDY
    rw [intervalIntegral.integral_of_le hDY] at h
    exact h
  have hIntMul := mul_le_mul_of_nonneg_left hInt hCnonneg
  have hfinite := mobius_reciprocal_finite_tail_bound hR hC hD hDY hM
  calc
    |∑ n ∈ Finset.Ioc (Nat.floor D) (Nat.floor Y),
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)| ≤
      |mobiusSummatory Y / Y| + C * Real.rpow (Real.log D) (-R) +
        C * ∫ t in Set.Ioc D Y, t⁻¹ * Real.rpow (Real.log t) (-R) := hfinite
    _ ≤ (C * Real.rpow (Real.log D) (-R) +
          C * Real.rpow (Real.log D) (-R)) +
        C * (Real.rpow (Real.log D) (1 - R) / (R - 1)) := by
      calc
        _ ≤ (C * Real.rpow (Real.log D) (-R) +
              C * Real.rpow (Real.log D) (-R)) +
              C * ∫ t in Set.Ioc D Y,
                t⁻¹ * Real.rpow (Real.log t) (-R) := by
          nlinarith [hYterm]
        _ ≤ _ := by nlinarith [hIntMul]
    _ = C * (2 * Real.rpow (Real.log D) (-R) +
          Real.rpow (Real.log D) (1 - R) / (R - 1)) := by ring

/-- Natural cutoff partial sums for the reciprocal Möbius coefficients. -/
def reciprocalMobiusPartialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)

/-- The reciprocal Möbius partial sums are Cauchy in their natural increasing
order under the stated scalar Mertens bound. -/
theorem reciprocalMobiusPartialSum_cauchy {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    CauchySeq reciprocalMobiusPartialSum := by
  let B : ℝ → ℝ := fun x =>
    C * (2 * Real.rpow (Real.log x) (-R) +
      Real.rpow (Real.log x) (1 - R) / (R - 1))
  have hpow1 :
      Tendsto (fun x : ℝ => Real.rpow (Real.log x) (-R)) atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < R)).comp
      Real.tendsto_log_atTop
  have hpow2 :
      Tendsto (fun x : ℝ => Real.rpow (Real.log x) (1 - R)) atTop (𝓝 0) := by
    exact log_rpow_one_sub_tendsto_zero hR
  have hB : Tendsto B atTop (𝓝 0) := by
    dsimp [B]
    have hsum :
        Tendsto (fun x : ℝ =>
          2 * Real.rpow (Real.log x) (-R) +
            Real.rpow (Real.log x) (1 - R) / (R - 1)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hpow1).add
        (hpow2.div_const (R - 1))
    simpa using tendsto_const_nhds.mul hsum
  have hBN : Tendsto (fun N : ℕ => B (N : ℝ)) atTop (𝓝 0) :=
    hB.comp tendsto_natCast_atTop_atTop
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hBsmall : ∀ᶠ N : ℕ in atTop, |B (N : ℝ)| < ε := by
    simpa only [dist_zero_right, Real.norm_eq_abs] using
      (Metric.tendsto_nhds.mp hBN) ε hε
  simp only [eventually_atTop] at hBsmall
  rcases hBsmall with ⟨N₀, hN₀⟩
  refine ⟨max N₀ 3, ?_⟩
  intro m hm n hn
  by_cases hmn : m ≤ n
  · have hm3 : 3 ≤ m := by omega
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hm3R : 3 ≤ (m : ℝ) := by exact_mod_cast hm3
    have hpartial := sum_Ioc_eq_sum_Icc_sub_of_le hmn
      (fun k : ℕ => (ArithmeticFunction.moebius k : ℝ) / (k : ℝ))
    have htail := mobius_reciprocal_finite_uniform_tail_bound
      hR hC hm3R hmnR hM
    have htail' :
        |reciprocalMobiusPartialSum n - reciprocalMobiusPartialSum m| ≤
          B (m : ℝ) := by
      simpa only [Nat.floor_natCast, reciprocalMobiusPartialSum, hpartial, B]
        using htail
    have hsmall := hN₀ m (by omega)
    have hdist :
        dist (reciprocalMobiusPartialSum m) (reciprocalMobiusPartialSum n) =
          |reciprocalMobiusPartialSum n - reciprocalMobiusPartialSum m| := by
      rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm]
    rw [hdist]
    exact lt_of_le_of_lt htail'
      (lt_of_le_of_lt (le_abs_self _) hsmall)
  · have hnm : n ≤ m := by omega
    have hn3 : 3 ≤ n := by omega
    have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    have hn3R : 3 ≤ (n : ℝ) := by exact_mod_cast hn3
    have hpartial := sum_Ioc_eq_sum_Icc_sub_of_le hnm
      (fun k : ℕ => (ArithmeticFunction.moebius k : ℝ) / (k : ℝ))
    have htail := mobius_reciprocal_finite_uniform_tail_bound
      hR hC hn3R hnmR hM
    have htail' :
        |reciprocalMobiusPartialSum m - reciprocalMobiusPartialSum n| ≤
          B (n : ℝ) := by
      simpa only [Nat.floor_natCast, reciprocalMobiusPartialSum, hpartial, B]
        using htail
    have hsmall := hN₀ n (by omega)
    have hdist :
        dist (reciprocalMobiusPartialSum m) (reciprocalMobiusPartialSum n) =
          |reciprocalMobiusPartialSum m - reciprocalMobiusPartialSum n| := by
      rw [dist_eq_norm, Real.norm_eq_abs]
    rw [hdist]
    exact lt_of_le_of_lt htail'
      (lt_of_le_of_lt (le_abs_self _) hsmall)

/-- The reciprocal Möbius partial sums converge in increasing natural order
to some real limit under the scalar Mertens bound. -/
theorem reciprocalMobiusPartialSum_has_ordered_limit {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    ∃ L : ℝ, Tendsto reciprocalMobiusPartialSum atTop (𝓝 L) := by
  let hCauchy := reciprocalMobiusPartialSum_cauchy hR hC hM
  exact ⟨limUnder atTop reciprocalMobiusPartialSum, hCauchy.tendsto_limUnder⟩

/-- The logarithmic power in the weighted Möbius tail tends to zero. -/
theorem log_rpow_two_sub_tendsto_zero {R : ℝ} (hR : 3 < R) :
    Tendsto (fun x : ℝ => Real.rpow (Real.log x) (2 - R)) atTop (𝓝 0) := by
  have hpow :
      Tendsto (fun y : ℝ => y ^ (-(R - 2))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith : 0 < R - 2)
  have hlog := hpow.comp Real.tendsto_log_atTop
  have hEq :
      (fun y : ℝ => y ^ (-(R - 2))) ∘ Real.log =ᶠ[atTop]
        (fun x : ℝ => Real.rpow (Real.log x) (2 - R)) := by
    exact Filter.Eventually.of_forall fun x => by
      simp only [Function.comp_apply, Real.rpow_eq_pow,
        show 2 - R = -(R - 2) by ring]
  exact Tendsto.congr' hEq hlog

/-- Natural cutoff partial sums for the logarithmically weighted reciprocal
Möbius coefficients. -/
def mobiusLogReciprocalPartialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)

/-- The logarithmically weighted reciprocal Möbius partial sums are Cauchy
in increasing natural-integer order under the scalar Mertens bound. -/
theorem mobiusLogReciprocalPartialSum_cauchy {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    CauchySeq mobiusLogReciprocalPartialSum := by
  let B : ℝ → ℝ := fun x => 3 * C * Real.rpow (Real.log x) (2 - R)
  have hpow : Tendsto (fun x : ℝ => Real.rpow (Real.log x) (2 - R))
      atTop (𝓝 0) := log_rpow_two_sub_tendsto_zero hR
  have hB : Tendsto B atTop (𝓝 0) := by
    have hconstant : Tendsto (fun _ : ℝ => 3 * C) atTop (𝓝 (3 * C)) :=
      tendsto_const_nhds
    simpa [B] using hconstant.mul hpow
  have hBN : Tendsto (fun N : ℕ => B (N : ℝ)) atTop (𝓝 0) :=
    hB.comp tendsto_natCast_atTop_atTop
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hBsmall : ∀ᶠ N : ℕ in atTop, |B (N : ℝ)| < ε := by
    simpa only [dist_zero_right, Real.norm_eq_abs] using
      (Metric.tendsto_nhds.mp hBN) ε hε
  simp only [eventually_atTop] at hBsmall
  rcases hBsmall with ⟨N₀, hN₀⟩
  refine ⟨max N₀ 3, ?_⟩
  intro m hm n hn
  by_cases hmn : m ≤ n
  · have hm3 : 3 ≤ m := by omega
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hm3R : 3 ≤ (m : ℝ) := by exact_mod_cast hm3
    have hpartial := sum_Ioc_eq_sum_Icc_sub_of_le hmn
      (fun k : ℕ => (ArithmeticFunction.moebius k : ℝ) *
        Real.log (k : ℝ) / (k : ℝ))
    have htail := mobius_log_reciprocal_finite_uniform_tail_bound
      hR hC hm3R hmnR hM
    have htail' :
        |mobiusLogReciprocalPartialSum n - mobiusLogReciprocalPartialSum m| ≤
          B (m : ℝ) := by
      simpa only [Nat.floor_natCast, mobiusLogReciprocalPartialSum,
        hpartial, B] using htail
    have hsmall := hN₀ m (by omega)
    have hdist :
        dist (mobiusLogReciprocalPartialSum m)
          (mobiusLogReciprocalPartialSum n) =
          |mobiusLogReciprocalPartialSum n -
            mobiusLogReciprocalPartialSum m| := by
      rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm]
    rw [hdist]
    exact lt_of_le_of_lt htail'
      (lt_of_le_of_lt (le_abs_self _) hsmall)
  · have hnm : n ≤ m := by omega
    have hn3 : 3 ≤ n := by omega
    have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    have hn3R : 3 ≤ (n : ℝ) := by exact_mod_cast hn3
    have hpartial := sum_Ioc_eq_sum_Icc_sub_of_le hnm
      (fun k : ℕ => (ArithmeticFunction.moebius k : ℝ) *
        Real.log (k : ℝ) / (k : ℝ))
    have htail := mobius_log_reciprocal_finite_uniform_tail_bound
      hR hC hn3R hnmR hM
    have htail' :
        |mobiusLogReciprocalPartialSum m - mobiusLogReciprocalPartialSum n| ≤
          B (n : ℝ) := by
      simpa only [Nat.floor_natCast, mobiusLogReciprocalPartialSum,
        hpartial, B] using htail
    have hsmall := hN₀ n (by omega)
    have hdist :
        dist (mobiusLogReciprocalPartialSum m)
          (mobiusLogReciprocalPartialSum n) =
          |mobiusLogReciprocalPartialSum m -
            mobiusLogReciprocalPartialSum n| := by
      rw [dist_eq_norm, Real.norm_eq_abs]
    rw [hdist]
    exact lt_of_le_of_lt htail'
      (lt_of_le_of_lt (le_abs_self _) hsmall)

/-- The logarithmically weighted reciprocal Möbius partial sums converge in
increasing natural-integer order to a real limit under the scalar Mertens
bound. -/
theorem mobiusLogReciprocalPartialSum_has_ordered_limit {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    ∃ L : ℝ, Tendsto mobiusLogReciprocalPartialSum atTop (𝓝 L) := by
  let hCauchy := mobiusLogReciprocalPartialSum_cauchy hR hC hM
  exact ⟨limUnder atTop mobiusLogReciprocalPartialSum,
    hCauchy.tendsto_limUnder⟩

/-- The terminal real-cutoff term in finite Abel summation vanishes under the
stated Mertens bound. The summatory function uses `Nat.floor x`, so this is a
real-cutoff limit, including nonintegral `x`. -/
theorem mobiusSummatory_div_tendsto_zero {R C : ℝ}
    (hR : 3 < R) (_hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    Tendsto (fun x : ℝ => mobiusSummatory x / x) atTop (𝓝 0) := by
  have hsmallLog :
      Tendsto (fun x : ℝ => Real.rpow (Real.log x) (-R)) atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < R)).comp Real.tendsto_log_atTop
  have hsmall :
      Tendsto (fun x : ℝ => C * Real.rpow (Real.log x) (-R)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hsmallLog
  have hbound : ∀ᶠ x : ℝ in atTop,
      |mobiusSummatory x / x| ≤ C * Real.rpow (Real.log x) (-R) := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    rw [abs_div, abs_of_pos hxpos]
    calc
      |mobiusSummatory x| / x ≤
          (C * x * Real.rpow (Real.log x) (-R)) / x :=
        div_le_div_of_nonneg_right (hM x hx) hxpos.le
      _ = C * Real.rpow (Real.log x) (-R) := by
        field_simp [ne_of_gt hxpos]
        <;> ring
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsmall
    (Filter.Eventually.of_forall fun x => abs_nonneg (mobiusSummatory x / x)) hbound

end

end FractionalPrimes.Literature.MobiusToLong
