module

public import Mathlib.MeasureTheory.Function.Floor

public import FractionalPrimes.Literature.MobiusToLong.ReciprocalMobiusMoments
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace FractionalPrimes.Literature.MobiusToLong

noncomputable section

/-- The integrand inside the real Mellin transform used in the Möbius moment
argument. -/
def mobiusMellinKernel (σ t : ℝ) : ℝ :=
  mobiusSummatory t * Real.rpow t (-(σ + 1))

/-- The parameter-dependent integrand after moving the source's outer factor
inside the integral. -/
def mobiusMellinIntegrand (σ t : ℝ) : ℝ :=
  σ * mobiusMellinKernel σ t

/-- The real Mellin transform of the ordered Möbius summatory function. -/
def mobiusMellinTransform (σ : ℝ) : ℝ :=
  σ * ∫ t in Set.Ioi 1, mobiusMellinKernel σ t

/-- The endpoint exponent in the Mellin derivative is the inverse square. -/
theorem mobiusMellin_rpow_neg_one_add_neg_one {t : ℝ} (ht : 0 < t) :
    Real.rpow t (-1 + -1) = (t ^ 2)⁻¹ := by
  calc
    Real.rpow t (-1 + -1) = Real.rpow t (-(2 : ℝ)) := by
      congr 1 <;> norm_num
    _ = (Real.rpow t (2 : ℝ))⁻¹ := Real.rpow_neg ht.le _
    _ = (t ^ 2)⁻¹ :=
      congrArg (fun z : ℝ => z⁻¹) (Real.rpow_natCast t 2)

/-- The finite-floor Möbius summatory function is measurable. -/
theorem mobiusSummatory_measurable : Measurable mobiusSummatory := by
  let g : ℕ → ℝ := fun k =>
    ∑ n ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius n : ℝ)
  have hg : Measurable g := measurable_of_countable g
  have hrepr : mobiusSummatory = g ∘ Nat.floor := by
    funext x
    rfl
  rw [hrepr]
  exact hg.comp Nat.measurable_floor

/-- A uniform finite bound for the summatory function on the initial
interval. -/
theorem mobiusSummatory_abs_le_four {x : ℝ} (hx0 : 0 ≤ x) (hx3 : x ≤ 3) :
    |mobiusSummatory x| ≤ 4 := by
  rw [mobiusSummatory]
  have hfloor : Nat.floor x ≤ 3 := by
    have hcast : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
    exact_mod_cast (hcast.trans hx3)
  have hsubset : Finset.Icc 1 (Nat.floor x) ⊆ Finset.Icc 1 3 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  have hsum :
      |∑ n ∈ Finset.Icc 1 (Nat.floor x), (ArithmeticFunction.moebius n : ℝ)| ≤
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
  have hcard : (Finset.Icc 1 (Nat.floor x)).card ≤ (Finset.Icc 1 3).card :=
    Finset.card_le_card hsubset
  have hsumcard :
      (∑ n ∈ Finset.Icc 1 (Nat.floor x), (1 : ℝ)) =
        ((Finset.Icc 1 (Nat.floor x)).card : ℝ) := by simp
  rw [hsumcard] at hsum
  have hthree : (Finset.Icc 1 3).card = 3 := by decide
  rw [hthree] at hcard
  have hcardReal : ((Finset.Icc 1 (Nat.floor x)).card : ℝ) ≤ 3 := by
    exact_mod_cast hcard
  linarith

/-- Measurability of the kernel on its positive integration domain. -/
theorem mobiusMellinKernel_aestronglyMeasurable (σ : ℝ) :
    AEStronglyMeasurable (mobiusMellinKernel σ)
      (volume.restrict (Set.Ioi 1)) := by
  apply (mobiusSummatory_measurable.aestronglyMeasurable.restrict).mul
  apply ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  intro t ht
  exact ((Real.continuousAt_rpow_const t (-(σ + 1))
    (Or.inl (ne_of_gt (lt_trans zero_lt_one (Set.mem_Ioi.mp ht))))).continuousWithinAt)

/-- Integrability of the Mellin kernel on `(1,∞)` under the source's scalar
Mertens bound. -/
theorem mobiusMellinKernel_integrableOn {σ R C : ℝ} (hσ : 1 ≤ σ)
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    IntegrableOn (mobiusMellinKernel σ) (Set.Ioi 1) := by
  let low : Set ℝ := Set.Ioc 1 3
  have hpowLow : ContinuousOn (fun t : ℝ => Real.rpow t (-(σ + 1))) low := by
    intro t ht
    exact (Real.continuousAt_rpow_const t (-(σ + 1))
      (Or.inl (ne_of_gt (lt_trans zero_lt_one ht.1)))).continuousWithinAt
  have hlowMeas : AEStronglyMeasurable (mobiusMellinKernel σ)
      (volume.restrict low) := by
    apply (mobiusSummatory_measurable.aestronglyMeasurable.restrict).mul
    exact hpowLow.aestronglyMeasurable measurableSet_Ioc
  have hlow : IntegrableOn (mobiusMellinKernel σ) low := by
    apply IntegrableOn.of_bound measure_Ioc_lt_top hlowMeas 4
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : 0 ≤ t := by linarith [ht.1]
    have ht3 : t ≤ 3 := ht.2
    have hMt := mobiusSummatory_abs_le_four ht1 ht3
    have hpow : 0 ≤ Real.rpow t (-(σ + 1)) := Real.rpow_nonneg ht1 _
    have hpow_le : Real.rpow t (-(σ + 1)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ht.1])
      linarith
    rw [Real.norm_eq_abs]
    change |mobiusSummatory t * Real.rpow t (-(σ + 1))| ≤ 4
    rw [abs_mul, abs_of_nonneg hpow]
    exact (mul_le_of_le_one_right (abs_nonneg _) hpow_le).trans hMt
  have hlogpos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogTail : IntegrableOn (fun t : ℝ => t⁻¹ * Real.rpow (Real.log t) (-R))
      (Set.Ioi 3) := by
    simpa only [smul_eq_mul] using
      (MeasureTheory.integrableOn_comp_log_Ioi
        (fun u : ℝ => Real.rpow u (-R)) (by norm_num : (0 : ℝ) < 3)).2
        (integrableOn_Ioi_rpow_of_lt (by linarith : -R < -1) hlogpos)
  have hpowOnTail : ContinuousOn (fun t : ℝ => Real.rpow t (-(σ + 1)))
      (Set.Ioi 3) := by
    intro t ht
    exact (Real.continuousAt_rpow_const t (-(σ + 1))
      (Or.inl (ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 3) ht)))).continuousWithinAt
  have htailMeas : AEStronglyMeasurable (mobiusMellinKernel σ)
      (volume.restrict (Set.Ioi 3)) := by
    apply (mobiusSummatory_measurable.aestronglyMeasurable.restrict).mul
    exact hpowOnTail.aestronglyMeasurable measurableSet_Ioi
  have htailMajorant : IntegrableOn
      (fun t : ℝ => C * (t⁻¹ * Real.rpow (Real.log t) (-R))) (Set.Ioi 3) := by
    simpa only [IntegrableOn, mul_assoc] using hlogTail.integrable.const_mul C
  have htail : IntegrableOn (mobiusMellinKernel σ) (Set.Ioi 3) := by
    apply Integrable.mono' htailMajorant.integrable htailMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht3 : 3 < t := Set.mem_Ioi.mp ht
    have htpos : 0 < t := by linarith
    have htone : 1 ≤ t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hMt := hM t ht3.le
    have hpow : 0 ≤ Real.rpow t (-(σ + 1)) := Real.rpow_nonneg htpos.le _
    have hpow_le : Real.rpow t (-(σ + 1)) ≤ t⁻¹ * t⁻¹ := by
      calc
        Real.rpow t (-(σ + 1)) ≤ Real.rpow t (-2) :=
          Real.rpow_le_rpow_of_exponent_le htone (by linarith)
        _ = t⁻¹ * t⁻¹ := by
          calc
            Real.rpow t (-2 : ℝ) = Real.rpow t (-(2 : ℝ)) := by congr 1 <;> norm_num
            _ = (Real.rpow t (2 : ℝ))⁻¹ := Real.rpow_neg htpos.le _
            _ = (t ^ 2)⁻¹ := congrArg (fun z : ℝ => z⁻¹) (Real.rpow_natCast t 2)
            _ = t⁻¹ * t⁻¹ := by
              rw [pow_two]
              field_simp [ne_of_gt htpos]
              <;> ring
    have hcoeff : 0 ≤ C * t * Real.rpow (Real.log t) (-R) :=
      mul_nonneg (mul_nonneg (by linarith [hC]) htpos.le)
        (Real.rpow_nonneg hlogt.le _)
    have hbound : |mobiusSummatory t| * Real.rpow t (-(σ + 1)) ≤
        C * (t⁻¹ * Real.rpow (Real.log t) (-R)) := by
      calc
        _ ≤ (C * t * Real.rpow (Real.log t) (-R)) * Real.rpow t (-(σ + 1)) :=
          mul_le_mul_of_nonneg_right hMt hpow
        _ ≤ (C * t * Real.rpow (Real.log t) (-R)) * (t⁻¹ * t⁻¹) :=
          mul_le_mul_of_nonneg_left hpow_le hcoeff
        _ = C * (t⁻¹ * Real.rpow (Real.log t) (-R)) := by
          field_simp [ne_of_gt htpos]
          <;> ring
    change |mobiusSummatory t * Real.rpow t (-(σ + 1))| ≤ _
    rw [abs_mul, abs_of_nonneg hpow]
    exact hbound
  have hset : low ∪ Set.Ioi 3 = Set.Ioi 1 := by
    dsimp [low]
    exact Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 3)
  rw [← hset]
  exact hlow.union htail

/-- Pointwise majorant for the parameter slopes on the interval `1 ≤ σ ≤ 2`.
Its tail is the Astra bound `C(1+2 log t)/(t(log t)^R)`. -/
def mobiusMellinSlopeMajorant (R C t : ℝ) : ℝ :=
  if t ≤ 3 then 4 * (1 + 2 * Real.log 3) else C * (1 + 2 * Real.log t) *
    (t⁻¹ * Real.rpow (Real.log t) (-R))

/-- The exact source slope majorant is integrable on the Mellin domain. -/
theorem mobiusMellinSlopeMajorant_integrableOn {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C) :
    IntegrableOn (mobiusMellinSlopeMajorant R C) (Set.Ioi 1) := by
  have hlow : IntegrableOn (mobiusMellinSlopeMajorant R C) (Set.Ioc 1 3) := by
    have hconst : IntegrableOn (fun _ : ℝ => 4 * (1 + 2 * Real.log 3))
        (Set.Ioc 1 3) :=
      integrableOn_const (hs := ne_of_lt measure_Ioc_lt_top)
    exact hconst.congr_fun (by
      intro t ht
      simp [mobiusMellinSlopeMajorant, ht.2]) measurableSet_Ioc
  have hlogpos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let g : ℝ → ℝ := fun u =>
    C * (Real.rpow u (-R) + 2 * Real.rpow u (1 - R))
  have hg₁ : IntegrableOn (fun u : ℝ => Real.rpow u (-R)) (Set.Ioi (Real.log 3)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -R < -1) hlogpos
  have hg₂ : IntegrableOn (fun u : ℝ => Real.rpow u (1 - R))
      (Set.Ioi (Real.log 3)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : 1 - R < -1) hlogpos
  have hg : IntegrableOn g (Set.Ioi (Real.log 3)) := by
    dsimp [g]
    have hsum : IntegrableOn
        (fun u : ℝ => Real.rpow u (-R) + 2 * Real.rpow u (1 - R))
        (Set.Ioi (Real.log 3)) := by
      have h₂ : IntegrableOn
          (fun u : ℝ => 2 * Real.rpow u (1 - R)) (Set.Ioi (Real.log 3)) := by
        simpa only [IntegrableOn] using hg₂.integrable.const_mul 2
      exact hg₁.add h₂
    change Integrable (fun u : ℝ => C *
      (Real.rpow u (-R) + 2 * Real.rpow u (1 - R)))
      (volume.restrict (Set.Ioi (Real.log 3)))
    exact hsum.integrable.const_mul C
  have htailBase : IntegrableOn (fun t : ℝ => t⁻¹ * g (Real.log t))
      (Set.Ioi 3) := by
    simpa only [g, smul_eq_mul] using
      (MeasureTheory.integrableOn_comp_log_Ioi g (by norm_num : (0 : ℝ) < 3)).2 hg
  have htail : IntegrableOn (mobiusMellinSlopeMajorant R C) (Set.Ioi 3) := by
    refine htailBase.congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht3 : 3 < t := Set.mem_Ioi.mp ht
    have htpos : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 3) ht3
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    simp only [mobiusMellinSlopeMajorant]
    rw [if_neg (not_le_of_gt ht3)]
    dsimp [g]
    have hpowid : Real.rpow (Real.log t) (1 - R) =
        Real.log t * Real.rpow (Real.log t) (-R) := by
      calc
        Real.rpow (Real.log t) (1 - R) =
            Real.rpow (Real.log t) ((1 : ℝ) + (-R)) := by congr 1 <;> ring
        _ = Real.rpow (Real.log t) 1 * Real.rpow (Real.log t) (-R) :=
          Real.rpow_add hlogt 1 (-R)
        _ = Real.log t * Real.rpow (Real.log t) (-R) :=
          congrArg (fun z : ℝ => z * Real.rpow (Real.log t) (-R))
            (Real.rpow_one (Real.log t))
    have hsum : C * (Real.rpow (Real.log t) (-R) +
        2 * Real.rpow (Real.log t) (1 - R)) =
        C * ((1 + 2 * Real.log t) * Real.rpow (Real.log t) (-R)) := by
      rw [hpowid]
      ring
    calc
      _ = t⁻¹ * (C * (Real.rpow (Real.log t) (-R) +
            2 * Real.rpow (Real.log t) (1 - R))) := rfl
      _ = t⁻¹ * (C * ((1 + 2 * Real.log t) *
            Real.rpow (Real.log t) (-R))) :=
        congrArg (fun z : ℝ => t⁻¹ * z) hsum
      _ = C * (1 + 2 * Real.log t) *
          (t⁻¹ * Real.rpow (Real.log t) (-R)) := by ring
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 3)]
  exact hlow.union htail

/-- The slope majorant is nonnegative on the integration domain. -/
theorem mobiusMellinSlopeMajorant_nonneg {R C t : ℝ} (hC : 1 ≤ C)
    (ht : 1 < t) : 0 ≤ mobiusMellinSlopeMajorant R C t := by
  by_cases hlow : t ≤ 3
  · have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    simp only [mobiusMellinSlopeMajorant, if_pos hlow]
    positivity
  · have ht3 : 3 < t := lt_of_not_ge hlow
    have hlog : 0 < Real.log t := Real.log_pos (by linarith)
    simp [mobiusMellinSlopeMajorant, hlow]
    positivity

/-- Uniform bound for the derivative of the parameter integrand on the
source's two ranges. -/
theorem mobiusMellinIntegrand_derivative_abs_le {R C σ t : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R))
    (ht : 1 < t) (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2) :
    |mobiusSummatory t * Real.rpow t (-(σ + 1)) *
      (1 - σ * Real.log t)| ≤ mobiusMellinSlopeMajorant R C t := by
  have htpos : 0 < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hpow : 0 ≤ Real.rpow t (-(σ + 1)) := Real.rpow_nonneg htpos.le _
  by_cases hlow : t ≤ 3
  · have hMt : |mobiusSummatory t| ≤ 4 :=
      mobiusSummatory_abs_le_four (by linarith) hlow
    have hpow_le : Real.rpow t (-(σ + 1)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      linarith
    have hlogle : Real.log t ≤ Real.log 3 := Real.log_le_log htpos hlow
    have hfactor : |1 - σ * Real.log t| ≤ 1 + 2 * Real.log 3 := by
      calc
        |1 - σ * Real.log t| ≤ |(1 : ℝ)| + |σ * Real.log t| := abs_sub _ _
        _ = 1 + σ * Real.log t := by
          rw [abs_one, abs_mul, abs_of_nonneg (by linarith [hσ₁]),
            abs_of_nonneg hlogt.le]
        _ ≤ 1 + 2 * Real.log 3 := by
          have hmul := mul_le_mul_of_nonneg_right hσ₂ hlogt.le
          have hlogmul := mul_le_mul_of_nonneg_left hlogle (by norm_num : 0 ≤ (2 : ℝ))
          nlinarith
    have habs :
        |mobiusSummatory t * Real.rpow t (-(σ + 1)) *
          (1 - σ * Real.log t)| =
          |mobiusSummatory t| * Real.rpow t (-(σ + 1)) *
            |1 - σ * Real.log t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hpow]
    rw [habs]
    calc
      |mobiusSummatory t| * Real.rpow t (-(σ + 1)) *
          |1 - σ * Real.log t|
        = |mobiusSummatory t| *
            (Real.rpow t (-(σ + 1)) * |1 - σ * Real.log t|) := by ring
      _ ≤ 4 * (Real.rpow t (-(σ + 1)) * |1 - σ * Real.log t|) :=
          mul_le_mul_of_nonneg_right hMt
            (mul_nonneg hpow (abs_nonneg _))
      _ ≤ 4 * (1 * |1 - σ * Real.log t|) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow_le (abs_nonneg _)) (by norm_num)
      _ ≤ 4 * (1 * (1 + 2 * Real.log 3)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hfactor (by norm_num)) (by norm_num)
      _ = mobiusMellinSlopeMajorant R C t := by
          simp [mobiusMellinSlopeMajorant, hlow]
  · have ht3 : 3 < t := lt_of_not_ge hlow
    have hMt := hM t (le_of_lt ht3)
    have htone : 1 ≤ t := by linarith
    have hpow_le : Real.rpow t (-(σ + 1)) ≤ t⁻¹ * t⁻¹ := by
      calc
        Real.rpow t (-(σ + 1)) ≤ Real.rpow t (-2) :=
          Real.rpow_le_rpow_of_exponent_le htone (by linarith)
        _ = t⁻¹ * t⁻¹ := by
          calc
            Real.rpow t (-2 : ℝ) = Real.rpow t (-(2 : ℝ)) := by congr 1 <;> norm_num
            _ = (Real.rpow t (2 : ℝ))⁻¹ := Real.rpow_neg htpos.le _
            _ = (t ^ 2)⁻¹ := congrArg (fun z : ℝ => z⁻¹) (Real.rpow_natCast t 2)
            _ = t⁻¹ * t⁻¹ := by
              rw [pow_two]
              field_simp [ne_of_gt htpos]
              <;> ring
    have hcoeff : 0 ≤ C * t * Real.rpow (Real.log t) (-R) :=
      mul_nonneg (mul_nonneg (by linarith [hC]) htpos.le)
        (Real.rpow_nonneg hlogt.le _)
    have hkernel : |mobiusSummatory t| * Real.rpow t (-(σ + 1)) ≤
        C * (t⁻¹ * Real.rpow (Real.log t) (-R)) := by
      calc
        _ ≤ (C * t * Real.rpow (Real.log t) (-R)) * Real.rpow t (-(σ + 1)) :=
          mul_le_mul_of_nonneg_right hMt hpow
        _ ≤ (C * t * Real.rpow (Real.log t) (-R)) * (t⁻¹ * t⁻¹) :=
          mul_le_mul_of_nonneg_left hpow_le hcoeff
        _ = C * (t⁻¹ * Real.rpow (Real.log t) (-R)) := by
          field_simp [ne_of_gt htpos]
          <;> ring
    have hkernelNonneg : 0 ≤ C * (t⁻¹ * Real.rpow (Real.log t) (-R)) :=
      mul_nonneg (by linarith [hC])
        (mul_nonneg (inv_nonneg.mpr htpos.le) (Real.rpow_nonneg hlogt.le _))
    have hfactor : |1 - σ * Real.log t| ≤ 1 + 2 * Real.log t := by
      calc
        |1 - σ * Real.log t| ≤ |(1 : ℝ)| + |σ * Real.log t| := abs_sub _ _
        _ = 1 + σ * Real.log t := by
          rw [abs_one, abs_mul, abs_of_nonneg (by linarith [hσ₁]),
            abs_of_nonneg hlogt.le]
        _ ≤ 1 + 2 * Real.log t := by
          nlinarith [mul_le_mul_of_nonneg_right hσ₂ hlogt.le]
    have habs :
        |mobiusSummatory t * Real.rpow t (-(σ + 1)) *
          (1 - σ * Real.log t)| =
          |mobiusSummatory t| * Real.rpow t (-(σ + 1)) *
            |1 - σ * Real.log t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hpow]
    rw [habs]
    calc
      |mobiusSummatory t| * Real.rpow t (-(σ + 1)) *
          |1 - σ * Real.log t|
        ≤ C * (t⁻¹ * Real.rpow (Real.log t) (-R)) *
            |1 - σ * Real.log t| :=
          mul_le_mul_of_nonneg_right hkernel (abs_nonneg _)
      _ ≤ C * (t⁻¹ * Real.rpow (Real.log t) (-R)) *
            (1 + 2 * Real.log t) :=
          mul_le_mul_of_nonneg_left hfactor hkernelNonneg
      _ = mobiusMellinSlopeMajorant R C t := by
          simp [mobiusMellinSlopeMajorant, hlow]
          ring

/-- Pointwise parameter derivative of the Mellin integrand. This is the scalar
calculation used for the one-sided dominated-difference-quotient argument. -/
theorem mobiusMellinIntegrand_hasDerivAt (σ t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => mobiusMellinIntegrand s t)
      (mobiusSummatory t * Real.rpow t (-(σ + 1)) * (1 - σ * Real.log t)) σ := by
  have hexp : HasDerivAt (fun s : ℝ => -(s + 1)) (-1) σ := by
    convert (hasDerivAt_id' σ).add_const 1 |>.neg using 1 <;> norm_num
  have hpow := hexp.const_rpow ht
  have hscaled :
      HasDerivAt (fun s : ℝ => mobiusSummatory t * Real.rpow t (-(s + 1)))
        (mobiusSummatory t * (Real.log t * -1 * Real.rpow t (-(σ + 1)))) σ :=
    HasDerivAt.const_mul (mobiusSummatory t) hpow
  have hprod := (hasDerivAt_id' σ).mul hscaled
  convert hprod using 1
  · funext s
    simp only [mobiusMellinIntegrand, mobiusMellinKernel]
    congr 1
  · ring

/-- On the compact parameter interval `[1,2]`, each scalar Mellin integrand
is Lipschitz with the common source majorant. -/
theorem mobiusMellinIntegrand_lipschitzOn_Icc {R C t : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R))
    (ht : 1 < t) :
    LipschitzOnWith (Real.nnabs (mobiusMellinSlopeMajorant R C t))
      (fun σ : ℝ => mobiusMellinIntegrand σ t) (Set.Icc 1 2) := by
  refine Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f := fun σ : ℝ => mobiusMellinIntegrand σ t)
    (f' := fun σ : ℝ => mobiusSummatory t * Real.rpow t (-(σ + 1)) *
      (1 - σ * Real.log t)) (s := Set.Icc 1 2) (convex_Icc (1 : ℝ) 2) ?_ ?_
  · intro σ hσ
    exact (mobiusMellinIntegrand_hasDerivAt σ t (by linarith [ht])).hasDerivWithinAt
  · intro σ hσ
    have hσ₁ : 1 ≤ σ := hσ.1
    have hσ₂ : σ ≤ 2 := hσ.2
    have hnorm := mobiusMellinIntegrand_derivative_abs_le hR hC hM ht hσ₁ hσ₂
    have hmaj := mobiusMellinSlopeMajorant_nonneg (R := R) hC ht
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, Real.norm_eq_abs,
      abs_of_nonneg hmaj]
    exact hnorm

/-- Pointwise difference quotients inherit the same uniform majorant on the
right of the endpoint. -/
theorem mobiusMellinPointwiseSlope_abs_le {R C σ t : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R))
    (ht : 1 < t) (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2) (hσne : σ ≠ 1) :
    ‖slope (fun s : ℝ => mobiusMellinIntegrand s t) 1 σ‖ ≤
      mobiusMellinSlopeMajorant R C t := by
  have hσgt : 1 < σ := lt_of_le_of_ne hσ₁ (Ne.symm hσne)
  have hB : 0 ≤ mobiusMellinSlopeMajorant R C t :=
    mobiusMellinSlopeMajorant_nonneg (R := R) hC ht
  have hlip := mobiusMellinIntegrand_lipschitzOn_Icc hR hC hM ht
  have hdist := hlip.dist_le_mul σ ⟨hσ₁, hσ₂⟩ 1 ⟨le_rfl, by norm_num⟩
  have hdiff :
      |mobiusMellinIntegrand σ t - mobiusMellinIntegrand 1 t| ≤
        mobiusMellinSlopeMajorant R C t * |σ - 1| := by
    simpa [Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hB] using hdist
  have hdiff' :
      |mobiusMellinIntegrand σ t - mobiusMellinIntegrand 1 t| ≤
        mobiusMellinSlopeMajorant R C t * (σ - 1) := by
    simpa [abs_of_pos (sub_pos.mpr hσgt)] using hdiff
  rw [slope_def_field, Real.norm_eq_abs, abs_div,
    abs_of_pos (sub_pos.mpr hσgt)]
  calc
    |mobiusMellinIntegrand σ t - mobiusMellinIntegrand 1 t| / (σ - 1)
      ≤ (mobiusMellinSlopeMajorant R C t * (σ - 1)) / (σ - 1) :=
        div_le_div_of_nonneg_right hdiff' (sub_nonneg.mpr hσ₁)
    _ = mobiusMellinSlopeMajorant R C t := by
      field_simp [ne_of_gt hσgt]

/-- Each parameter integrand is strongly measurable on the Mellin domain. -/
theorem mobiusMellinIntegrand_aestronglyMeasurable (σ : ℝ) :
    AEStronglyMeasurable (mobiusMellinIntegrand σ)
      (volume.restrict (Set.Ioi 1)) := by
  change AEStronglyMeasurable (fun t => σ * mobiusMellinKernel σ t)
    (volume.restrict (Set.Ioi 1))
  exact (mobiusMellinKernel_aestronglyMeasurable σ).const_mul σ

/-- Integrability of each parameter integrand for `σ ≥ 1`. -/
theorem mobiusMellinIntegrand_integrableOn {R C σ : ℝ} (hσ : 1 ≤ σ)
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    IntegrableOn (mobiusMellinIntegrand σ) (Set.Ioi 1) := by
  change Integrable (fun t => σ * mobiusMellinKernel σ t)
    (volume.restrict (Set.Ioi 1))
  exact (mobiusMellinKernel_integrableOn hσ hR hC hM).const_mul σ

/-- The exact outer-factor Mellin transform equals the integral of its
parameter integrand. -/
theorem mobiusMellinTransform_eq_integral (σ : ℝ) :
    mobiusMellinTransform σ =
      ∫ t in Set.Ioi 1, mobiusMellinIntegrand σ t := by
  simp only [mobiusMellinTransform, mobiusMellinIntegrand, mobiusMellinKernel]
  exact (integral_const_mul σ _).symm

/-- Dominated convergence for the pointwise slopes at the right endpoint. -/
theorem mobiusMellinPointwiseSlope_integral_tendsto {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    Tendsto
      (fun σ => ∫ t in Set.Ioi 1,
        slope (fun s : ℝ => mobiusMellinIntegrand s t) 1 σ)
      (𝓝[Set.Ici 1 \ {1}] 1)
      (𝓝 (∫ t in Set.Ioi 1,
        mobiusSummatory t * Real.rpow t (-2) * (1 - Real.log t))) := by
  let l : Filter ℝ := 𝓝[Set.Ici 1 \ {1}] 1
  let μ : Measure ℝ := volume.restrict (Set.Ioi 1)
  let Q : ℝ → ℝ → ℝ := fun σ t =>
    slope (fun s : ℝ => mobiusMellinIntegrand s t) 1 σ
  let q : ℝ → ℝ := fun t =>
    mobiusSummatory t * Real.rpow t (-2) * (1 - Real.log t)
  have hQmeas : ∀ᶠ σ in l, AEStronglyMeasurable (Q σ) μ := by
    apply Filter.Eventually.of_forall
    intro σ
    have hσ : AEStronglyMeasurable (mobiusMellinIntegrand σ) μ := by
      simpa [μ] using mobiusMellinIntegrand_aestronglyMeasurable σ
    have h1 : AEStronglyMeasurable (mobiusMellinIntegrand 1) μ := by
      simpa [μ] using mobiusMellinIntegrand_aestronglyMeasurable 1
    have hEq : Q σ = fun t =>
        (mobiusMellinIntegrand σ t - mobiusMellinIntegrand 1 t) /
          (σ - 1) := by
      funext t
      simp only [Q]
      rw [slope_def_field]
    rw [hEq, show (fun t =>
      (mobiusMellinIntegrand σ t - mobiusMellinIntegrand 1 t) / (σ - 1)) =
        (fun t => (mobiusMellinIntegrand σ t - mobiusMellinIntegrand 1 t) *
          (σ - 1)⁻¹) by
        funext t
        rw [div_eq_mul_inv]]
    exact (hσ.sub h1).mul_const _
  have hdomain : ∀ᶠ σ in l, σ ∈ Set.Ici 1 \ {1} := by
    exact eventually_mem_nhdsWithin
  have hupper : ∀ᶠ σ in l, σ < 2 := by
    exact mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Iio 2))
  have hbound : ∀ᶠ σ in l, ∀ᵐ t ∂μ,
      ‖Q σ t‖ ≤ mobiusMellinSlopeMajorant R C t := by
    filter_upwards [hdomain, hupper] with σ hσ hσ₂
    have hσ₁ : 1 ≤ σ := Set.mem_Ici.mp hσ.1
    have hσ₂' : σ ≤ 2 := le_of_lt hσ₂
    have hσne : σ ≠ 1 := by simpa using hσ.2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mobiusMellinPointwiseSlope_abs_le hR hC hM
      (Set.mem_Ioi.mp ht) hσ₁ hσ₂' hσne
  have hbound_integrable : Integrable (mobiusMellinSlopeMajorant R C) μ := by
    simpa [μ, IntegrableOn] using mobiusMellinSlopeMajorant_integrableOn hR hC
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun σ => Q σ t) l (𝓝 (q t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := lt_trans zero_lt_one (Set.mem_Ioi.mp ht)
    have hderiv : HasDerivWithinAt (fun s : ℝ => mobiusMellinIntegrand s t)
        (q t) (Set.Ici 1) 1 := by
      have h : HasDerivWithinAt (fun s : ℝ => mobiusMellinIntegrand s t)
          (mobiusSummatory t * Real.rpow t (-(1 + 1)) * (1 - 1 * Real.log t))
          (Set.Ici 1) 1 :=
        (mobiusMellinIntegrand_hasDerivAt 1 t htpos).hasDerivWithinAt
      have hpow₁ : Real.rpow t (-2 : ℝ) = (t ^ 2)⁻¹ := by
        calc
          Real.rpow t (-2 : ℝ) = Real.rpow t (-1 + -1) := by
            congr 1 <;> norm_num
          _ = (t ^ 2)⁻¹ := mobiusMellin_rpow_neg_one_add_neg_one htpos
      have hpow₂ : Real.rpow t (-(1 + 1 : ℝ)) = (t ^ 2)⁻¹ := by
        calc
          Real.rpow t (-(1 + 1 : ℝ)) = Real.rpow t (-1 + -1) := by
            congr 1 <;> norm_num
          _ = (t ^ 2)⁻¹ := mobiusMellin_rpow_neg_one_add_neg_one htpos
      have hval : q t =
          mobiusSummatory t * Real.rpow t (-(1 + 1 : ℝ)) *
            (1 - 1 * Real.log t) := by
        change mobiusSummatory t * Real.rpow t (-2 : ℝ) *
          (1 - Real.log t) =
            mobiusSummatory t * Real.rpow t (-(1 + 1 : ℝ)) *
              (1 - 1 * Real.log t)
        rw [hpow₁, hpow₂]
        simp only [one_mul]
      rw [hval]
      exact h
    simpa [Q, l] using
      (hasDerivWithinAt_iff_tendsto_slope).mp hderiv
  have hDCT : Tendsto (fun σ => ∫ t, Q σ t ∂μ) l
      (𝓝 (∫ t, q t ∂μ)) := by
    exact tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := l) (F := Q) (f := q)
      (bound := mobiusMellinSlopeMajorant R C)
      hQmeas hbound hbound_integrable hlim
  simpa [μ, Q, q, l] using hDCT

/-- The source's real Mellin transform has the exact right derivative at the
endpoint `σ = 1`. The proof differentiates under the integral on `Ici 1`
using the Astra majorant. -/
theorem mobiusMellinTransform_hasDerivWithinAt_one {R C : ℝ}
    (hR : 3 < R) (hC : 1 ≤ C)
    (hM : ∀ x : ℝ, 3 ≤ x →
      |mobiusSummatory x| ≤ C * x * Real.rpow (Real.log x) (-R)) :
    HasDerivWithinAt mobiusMellinTransform
      (∫ t in Set.Ioi 1,
        mobiusSummatory t * Real.rpow t (-2) * (1 - Real.log t))
      (Set.Ici 1) 1 := by
  let l : Filter ℝ := 𝓝[Set.Ici 1 \ {1}] 1
  let μ : Measure ℝ := volume.restrict (Set.Ioi 1)
  let Q : ℝ → ℝ → ℝ := fun σ t =>
    slope (fun s : ℝ => mobiusMellinIntegrand s t) 1 σ
  let q : ℝ → ℝ := fun t =>
    mobiusSummatory t * Real.rpow t (-2) * (1 - Real.log t)
  have hDCT : Tendsto (fun σ => ∫ t, Q σ t ∂μ) l (𝓝 (∫ t, q t ∂μ)) := by
    simpa [μ, Q, q, l] using
      (mobiusMellinPointwiseSlope_integral_tendsto hR hC hM)
  have hSlopeIntegral : ∀ᶠ σ in l,
      (∫ t, Q σ t ∂μ) = slope mobiusMellinTransform 1 σ := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ
    have hσ₁ : 1 ≤ σ := Set.mem_Ici.mp hσ.1
    have hIntσ : Integrable (mobiusMellinIntegrand σ) μ := by
      simpa [μ, IntegrableOn] using
        (mobiusMellinIntegrand_integrableOn hσ₁ hR hC hM)
    have hInt1 : Integrable (mobiusMellinIntegrand 1) μ := by
      simpa [μ, IntegrableOn] using
        (mobiusMellinIntegrand_integrableOn (R := R) (C := C) (σ := 1)
          le_rfl hR hC hM)
    have hQ : Q σ = fun t =>
        (mobiusMellinIntegrand σ t - mobiusMellinIntegrand 1 t) /
          (σ - 1) := by
      funext t
      dsimp [Q]
      rw [slope_def_field]
    calc
      (∫ t, Q σ t ∂μ) =
          ∫ t, (mobiusMellinIntegrand σ t - mobiusMellinIntegrand 1 t) /
            (σ - 1) ∂μ := by rw [hQ]
      _ = (∫ t, mobiusMellinIntegrand σ t - mobiusMellinIntegrand 1 t ∂μ) /
            (σ - 1) := integral_div _ _
      _ = ((∫ t, mobiusMellinIntegrand σ t ∂μ) -
            (∫ t, mobiusMellinIntegrand 1 t ∂μ)) / (σ - 1) := by
          rw [integral_sub hIntσ hInt1]
      _ = (mobiusMellinTransform σ - mobiusMellinTransform 1) / (σ - 1) := by
          rw [← mobiusMellinTransform_eq_integral σ,
            ← mobiusMellinTransform_eq_integral 1]
      _ = slope mobiusMellinTransform 1 σ := by rw [slope_def_field]
  have hSlopeTendsto :
      Tendsto (slope mobiusMellinTransform 1) l
        (𝓝 (∫ t, q t ∂μ)) := by
    refine hDCT.congr' ?_
    filter_upwards [hSlopeIntegral] with σ hσ
    exact hσ
  apply (hasDerivWithinAt_iff_tendsto_slope).2
  simpa [l, μ, q] using hSlopeTendsto

end

end FractionalPrimes.Literature.MobiusToLong

end
