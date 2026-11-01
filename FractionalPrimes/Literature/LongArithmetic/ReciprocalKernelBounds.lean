module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import FractionalPrimes.Literature.LongArithmetic.ReciprocalKernelMiddleBound

@[expose] public section

open scoped Interval

namespace FractionalPrimes.Literature.LongArithmetic

/-- The analytic smoothed Perron kernel, written in the approved exponential
convention so it can be compared definitionally with `cesaroPerronKernel`. -/
noncomputable def transferKernel (x Δ : ℝ) (s : ℂ) : ℂ :=
  (Complex.exp ((s + 1) * (Real.log (x + Δ) : ℂ)) -
    Complex.exp ((s + 1) * (Real.log x : ℂ))) /
      ((Δ : ℂ) * s * (s + 1))

private theorem transferKernel_eq_intervalIntegral
    {x Δ σ t : ℝ} (hx : 0 < x) (hΔ : 0 < Δ)
    (hσ : 0 < σ) :
    transferKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ)) =
      (Δ : ℂ)⁻¹ * (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹ *
        ∫ r in x..x + Δ, (r : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ))) := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsRe : s.re = σ := by simp [s]
  have hs : s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [s] at hr
    linarith
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [s] at hr
    linarith
  have hxΔ : 0 < x + Δ := by positivity
  have hpow (r : ℝ) (hr : 0 < r) :
      Complex.exp ((s + 1) * (Real.log r : ℂ)) = (r : ℂ) ^ (s + 1) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
      Complex.ofReal_log hr.le]
    congr 1
    ring
  have hzero : (0 : ℝ) ∉ [[x, x + Δ]] := by
    rw [Set.uIcc_of_le (le_of_lt (by linarith : x < x + Δ))]
    simp only [Set.mem_Icc, not_and]
    intro hleft
    linarith
  have hInt := integral_cpow
    (a := x) (b := x + Δ) (r := s) (Or.inr ⟨by
      intro h
      have hr := congrArg Complex.re h
      simp [hsRe] at hr
      linarith, hzero⟩)
  rw [transferKernel, hpow x hx, hpow (x + Δ) hxΔ]
  dsimp [s] at hInt ⊢
  rw [hInt]
  field_simp [hΔ.ne', hs, hs1]

/-- The low-height kernel bound from the quantitative reciprocal-series
transfer proof. -/
theorem transferKernel_norm_le
    {x Δ σ t : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) (hΔx : Δ ≤ x)
    (hσlo : 1 / 2 ≤ σ) (hσhi : σ ≤ 2) :
    ‖transferKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      4 * x ^ σ / ‖(σ : ℂ) + Complex.I * (t : ℂ)‖ := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsRe : s.re = σ := by simp [s]
  have hσpos : 0 < σ := by linarith
  have hs : s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [s] at hr
    linarith
  have hIntNorm : ‖∫ r in x..x + Δ, (r : ℂ) ^ s‖ ≤
      (4 * x ^ σ) * Δ := by
    have hbase (r : ℝ) (hr : r ∈ Ι x (x + Δ)) : ‖(r : ℂ) ^ s‖ ≤ 4 * x ^ σ := by
      have hrIoc : r ∈ Set.Ioc x (x + Δ) := by
        simpa [Set.uIoc_of_le (le_of_lt (by linarith : x < x + Δ))] using hr
      have hrpos : 0 < r := lt_of_lt_of_le hx hrIoc.1.le
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hrpos, hsRe]
      have hrx : r ≤ 2 * x := by nlinarith [hrIoc.2]
      have hpowBase : r ^ σ ≤ (2 * x) ^ σ :=
        Real.rpow_le_rpow (by positivity) hrx (by linarith)
      have hfactor : (2 * x) ^ σ = (2 : ℝ) ^ σ * x ^ σ := by
        rw [Real.mul_rpow (by norm_num) hx.le]
      have htwo : (2 : ℝ) ^ σ ≤ 4 := by
        calc
          (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hσhi
          _ = 4 := by norm_num
      rw [hfactor] at hpowBase
      calc
        r ^ σ ≤ (2 : ℝ) ^ σ * x ^ σ := hpowBase
        _ ≤ 4 * x ^ σ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hx.le _)
    have htmp := intervalIntegral.norm_integral_le_of_norm_le_const hbase
    have hlen : x + Δ - x = Δ := by ring
    rw [hlen, abs_of_pos hΔ] at htmp
    simpa using htmp
  have hsNorm : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hraw : ‖transferKernel x Δ s‖ =
      Δ⁻¹ * ‖s‖⁻¹ * ‖∫ r in x..x + Δ, (r : ℂ) ^ s‖ := by
    rw [transferKernel_eq_intervalIntegral hx hΔ (by linarith : 0 < σ)]
    simp [s, Real.norm_eq_abs, abs_of_pos hΔ]
    ring
  rw [show transferKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ)) = transferKernel x Δ s by rfl,
    hraw]
  calc
    Δ⁻¹ * ‖s‖⁻¹ * ‖∫ r in x..x + Δ, (r : ℂ) ^ s‖ ≤
        Δ⁻¹ * ‖s‖⁻¹ * ((4 * x ^ σ) * Δ) :=
          mul_le_mul_of_nonneg_left hIntNorm (by positivity)
    _ = 4 * x ^ σ / ‖s‖ := by
      field_simp [ne_of_gt hΔ, ne_of_gt hsNorm]

/-- The large-height kernel bound used on the horizontal edges and on the
original-line tails of the contour shift. -/
theorem transferKernel_norm_le_of_one_le_abs
    {x Δ σ t : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) (hΔx : Δ ≤ x)
    (hσlo : 1 / 2 ≤ σ) (hσhi : σ ≤ 2) (ht : 1 ≤ |t|) :
    ‖transferKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      16 * x ^ (σ + 1) / (Δ * t ^ 2) := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsRe : s.re = σ := by simp [s]
  have hs1Re : (s + 1).re = σ + 1 := by simp [s]
  have hσpos : 0 < σ := by linarith
  have hσ1pos : 0 < σ + 1 := by linarith
  have hs : s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [s] at hr
    linarith
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [s] at hr
    linarith
  have hxΔ : 0 < x + Δ := by positivity
  have hpow (r : ℝ) (hr : 0 < r) :
      Complex.exp ((s + 1) * (Real.log r : ℂ)) = (r : ℂ) ^ (s + 1) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
      Complex.ofReal_log hr.le]
    congr 1
    ring
  have hK : transferKernel x Δ s =
      (((x + Δ : ℝ) : ℂ) ^ (s + 1) - (x : ℂ) ^ (s + 1)) /
        ((Δ : ℂ) * s * (s + 1)) := by
    rw [transferKernel, hpow x hx, hpow (x + Δ) hxΔ]
  have hnum :
      ‖((x + Δ : ℝ) : ℂ) ^ (s + 1) - (x : ℂ) ^ (s + 1)‖ ≤
        16 * x ^ (σ + 1) := by
    have htop : x + Δ ≤ 2 * x := by nlinarith
    have htwo : (2 : ℝ) ^ (σ + 1) ≤ 8 := by
      calc
        (2 : ℝ) ^ (σ + 1) ≤ (2 : ℝ) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 8 := by norm_num
    have hpowTop : (x + Δ) ^ (σ + 1) ≤ 8 * x ^ (σ + 1) := by
      calc
        (x + Δ) ^ (σ + 1) ≤ (2 * x) ^ (σ + 1) :=
          Real.rpow_le_rpow (by positivity) htop (by linarith)
        _ = (2 : ℝ) ^ (σ + 1) * x ^ (σ + 1) :=
          Real.mul_rpow (by norm_num) hx.le
        _ ≤ 8 * x ^ (σ + 1) :=
          mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hx.le _)
    have hnum' :
        ‖((x + Δ : ℝ) : ℂ) ^ (s + 1) - (x : ℂ) ^ (s + 1)‖ ≤
          (x + Δ) ^ (σ + 1) + x ^ (σ + 1) := by
      calc
        _ ≤ ‖((x + Δ : ℝ) : ℂ) ^ (s + 1)‖ + ‖(x : ℂ) ^ (s + 1)‖ := norm_sub_le _ _
        _ = (x + Δ) ^ (σ + 1) + x ^ (σ + 1) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hxΔ (s + 1), hs1Re,
            Complex.norm_cpow_eq_rpow_re_of_pos hx (s + 1), hs1Re]
    calc
      _ ≤ (x + Δ) ^ (σ + 1) + x ^ (σ + 1) := hnum'
      _ ≤ 8 * x ^ (σ + 1) + x ^ (σ + 1) := add_le_add hpowTop le_rfl
      _ ≤ 16 * x ^ (σ + 1) := by
        have hnonneg : 0 ≤ x ^ (σ + 1) := Real.rpow_nonneg hx.le _
        nlinarith
  let denominator : ℂ := (Δ : ℂ) * s * (s + 1)
  have hdenNorm : ‖denominator‖ = Δ * ‖s‖ * ‖s + 1‖ := by
    simp [denominator, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΔ, mul_assoc]
  have hsT : |t| ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    simpa [s] using h
  have hs1T : |t| ≤ ‖s + 1‖ := by
    have h := Complex.abs_im_le_norm (s + 1)
    simpa [s] using h
  have hprod : t ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    calc
      t ^ 2 = |t| * |t| := by rw [← sq_abs]; ring
      _ ≤ ‖s‖ * ‖s + 1‖ :=
        mul_le_mul hsT hs1T (abs_nonneg t) (norm_nonneg _)
  have hden : Δ * t ^ 2 ≤ ‖denominator‖ := by
    rw [hdenNorm]
    calc
      Δ * t ^ 2 ≤ Δ * (‖s‖ * ‖s + 1‖) := mul_le_mul_of_nonneg_left hprod hΔ.le
      _ = Δ * ‖s‖ * ‖s + 1‖ := by ring
  have htpos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
  have htne : t ≠ 0 := abs_pos.mp htpos
  have hdenTarget : 0 < Δ * t ^ 2 := mul_pos hΔ (sq_pos_of_ne_zero htne)
  have hdenPositive : 0 < ‖denominator‖ := lt_of_lt_of_le hdenTarget hden
  have hfrac :
      ‖((x + Δ : ℝ) : ℂ) ^ (s + 1) - (x : ℂ) ^ (s + 1)‖ / ‖denominator‖ ≤
        16 * x ^ (σ + 1) / (Δ * t ^ 2) := by
    rw [div_le_div_iff₀ hdenPositive hdenTarget]
    calc
      ‖((x + Δ : ℝ) : ℂ) ^ (s + 1) - (x : ℂ) ^ (s + 1)‖ * (Δ * t ^ 2) ≤
          (16 * x ^ (σ + 1)) * (Δ * t ^ 2) :=
            mul_le_mul_of_nonneg_right hnum (by positivity)
      _ ≤ (16 * x ^ (σ + 1)) * ‖denominator‖ :=
            mul_le_mul_of_nonneg_left hden (by positivity)
  rw [show transferKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ)) = transferKernel x Δ s by rfl,
    hK]
  simpa [norm_div, denominator] using hfrac

/-- Integrated low-height estimate for the vertical side of the contour
rectangle. -/
theorem transferKernel_vertical_integral_bound
    {x Δ σ T : ℝ} (hx : 0 < x) (hΔ : 0 < Δ) (hΔx : Δ ≤ x)
    (hσlo : 1 / 2 ≤ σ) (hσhi : σ ≤ 2) (hT : 2 ≤ T) :
    (∫ t in -T..T,
      ‖transferKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))‖) ≤
        16 * x ^ σ * (1 + Real.log T) := by
  let f : ℝ → ℝ := fun t =>
    ‖transferKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))‖
  have hden : ∀ t : ℝ,
      (↑Δ * ((σ : ℂ) + Complex.I * (t : ℂ)) *
        (((σ : ℂ) + Complex.I * (t : ℂ)) + 1)) ≠ 0 := by
    intro t
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact Complex.ofReal_ne_zero.mpr hΔ.ne'
      · intro h
        have hr := congrArg Complex.re h
        simp at hr
        linarith
    · intro h
      have hr := congrArg Complex.re h
      simp at hr
      linarith
  have hKcont : Continuous (fun t : ℝ =>
      transferKernel x Δ ((σ : ℂ) + Complex.I * (t : ℂ))) := by
    unfold transferKernel
    fun_prop (disch := aesop)
  have hfcont : Continuous f := by
    dsimp [f]
    exact hKcont.norm
  have hfint (a b : ℝ) : IntervalIntegrable f MeasureTheory.volume a b :=
    hfcont.intervalIntegrable a b
  have hmiddle_point {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
      f t ≤ 8 * x ^ σ := by
    have hnorm : 1 / 2 ≤ ‖(σ : ℂ) + Complex.I * (t : ℂ)‖ := by
      calc
        1 / 2 ≤ σ := hσlo
        _ = |σ| := (abs_of_pos (by linarith : 0 < σ)).symm
        _ ≤ ‖(σ : ℂ) + Complex.I * (t : ℂ)‖ := by
          have h := Complex.abs_re_le_norm ((σ : ℂ) + Complex.I * (t : ℂ))
          simpa using h
    have hrecip : (‖(σ : ℂ) + Complex.I * (t : ℂ)‖)⁻¹ ≤ 2 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hnorm
    have hkernel := transferKernel_norm_le (x := x) (Δ := Δ) (σ := σ) (t := t)
      hx hΔ hΔx hσlo hσhi
    dsimp [f]
    calc
      _ ≤ 4 * x ^ σ / ‖(σ : ℂ) + Complex.I * (t : ℂ)‖ :=
        hkernel
      _ ≤ (4 * x ^ σ) * 2 := by
        exact mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = 8 * x ^ σ := by ring
  have hmiddle : (∫ t in -1..1, f t) ≤ 16 * x ^ σ := by
    have hle := intervalIntegral_le_of_Icc_nonneg_upper_bound
      (C := 8 * x ^ σ) (fun t ht => ⟨by
        dsimp [f]
        exact norm_nonneg _, hmiddle_point ht⟩)
    calc
      (∫ t in -1..1, f t) ≤ 2 * (8 * x ^ σ) := hle
      _ = 16 * x ^ σ := by ring
  have hpospoint {t : ℝ} (ht : t ∈ Set.Icc 1 T) :
      f t ≤ 4 * x ^ σ / t := by
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hnorm : t ≤ ‖(σ : ℂ) + Complex.I * (t : ℂ)‖ := by
      have h := Complex.abs_im_le_norm ((σ : ℂ) + Complex.I * (t : ℂ))
      simpa [abs_of_nonneg (show 0 ≤ t by linarith)] using h
    have hkernel := transferKernel_norm_le (x := x) (Δ := Δ) (σ := σ) (t := t)
      hx hΔ hΔx hσlo hσhi
    dsimp [f]
    exact hkernel.trans (div_le_div_of_nonneg_left (by positivity) htpos hnorm)
  have hnegpoint {t : ℝ} (ht : t ∈ Set.Icc 1 T) :
      f (-t) ≤ 4 * x ^ σ / t := by
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hnorm : t ≤ ‖(σ : ℂ) + Complex.I * ((-t : ℝ) : ℂ)‖ := by
      have h := Complex.abs_im_le_norm ((σ : ℂ) + Complex.I * ((-t : ℝ) : ℂ))
      simpa [abs_neg, abs_of_nonneg (show 0 ≤ t by linarith)] using h
    have hkernel := transferKernel_norm_le (x := x) (Δ := Δ) (σ := σ) (t := -t)
      hx hΔ hΔx hσlo hσhi
    dsimp [f]
    exact hkernel.trans (div_le_div_of_nonneg_left (by positivity) htpos hnorm)
  let g : ℝ → ℝ := fun t => 4 * x ^ σ / t
  have hgcont : ContinuousOn g (Set.Icc 1 T) := by
    dsimp [g]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
  have h1T : 1 ≤ T := by linarith
  have hgint : IntervalIntegrable g MeasureTheory.volume 1 T := hgcont.intervalIntegrable_of_Icc h1T
  have hpos : (∫ t in 1..T, f t) ≤ 4 * x ^ σ * Real.log T := by
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (a := (1 : ℝ)) (b := T) h1T (hfint 1 T) hgint (fun t ht => hpospoint ht)
    have hgEq : (∫ t in 1..T, g t) = 4 * x ^ σ * Real.log T := by
      calc
        _ = 4 * x ^ σ * (∫ t in 1..T, t⁻¹) := by
          dsimp [g]
          simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul]
        _ = 4 * x ^ σ * Real.log T := by
          rw [integral_inv_of_pos zero_lt_one (by linarith : 0 < T)]
          simp
    rw [hgEq] at hmono
    exact hmono
  have hneg : (∫ t in -T..-1, f t) ≤ 4 * x ^ σ * Real.log T := by
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (a := (1 : ℝ)) (b := T)
      h1T ((hfcont.comp continuous_neg).intervalIntegrable 1 T) hgint
      (fun t ht => hnegpoint ht)
    have hmono' : (∫ t in 1..T, f (-t)) ≤ ∫ t in 1..T, g t := by
      simpa using hmono
    have hgEq : (∫ t in 1..T, g t) = 4 * x ^ σ * Real.log T := by
      calc
        _ = 4 * x ^ σ * (∫ t in 1..T, t⁻¹) := by
          dsimp [g]
          simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul]
        _ = 4 * x ^ σ * Real.log T := by
          rw [integral_inv_of_pos zero_lt_one (by linarith : 0 < T)]
          simp
    calc
      (∫ t in -T..-1, f t) = ∫ t in 1..T, f (-t) := by
        symm
        simp
      _ ≤ ∫ t in 1..T, g t := hmono'
      _ = 4 * x ^ σ * Real.log T := hgEq
  have hsplit :
      (∫ t in -T..T, f t) =
        (∫ t in -T..-1, f t) +
          ((∫ t in -1..1, f t) + (∫ t in 1..T, f t)) := by
    calc
      (∫ t in -T..T, f t) =
          (∫ t in -T..-1, f t) + (∫ t in -1..T, f t) := by
        symm
        exact intervalIntegral.integral_add_adjacent_intervals (hfint (-T) (-1)) (hfint (-1) T)
      _ = (∫ t in -T..-1, f t) +
          ((∫ t in -1..1, f t) + (∫ t in 1..T, f t)) := by
        rw [intervalIntegral.integral_add_adjacent_intervals (hfint (-1) 1) (hfint 1 T)]
  rw [hsplit]
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hxpow : 0 ≤ x ^ σ := Real.rpow_nonneg hx.le _
  nlinarith [hneg, hmiddle, hpos, mul_nonneg hxpow hlog]

#print axioms transferKernel_norm_le
#print axioms transferKernel_norm_le_of_one_le_abs
#print axioms transferKernel_vertical_integral_bound

end FractionalPrimes.Literature.LongArithmetic

end
