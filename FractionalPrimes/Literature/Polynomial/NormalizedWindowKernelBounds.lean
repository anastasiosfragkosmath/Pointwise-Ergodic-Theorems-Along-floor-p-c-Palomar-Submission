module

public import FractionalPrimes.Literature.Polynomial.MellinWindowData
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open MeasureTheory
open intervalIntegral
open scoped Topology

/-- The exact Mellin kernel attached to the logarithmic window `[X,X+H]`. -/
noncomputable def normalizedMellinWindowKernel (X H t : ℝ) : ℂ :=
  (mellinHalfItPower (X + H) t - mellinHalfItPower X t) /
    ((H : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))

noncomputable def mellinKernelExponent (t : ℝ) : ℂ :=
  ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I

noncomputable def mellinKernelPrimitiveExponent (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I

private theorem mellinHalfItPower_eq_cpow (x t : ℝ) (hx : 0 < x) :
    mellinHalfItPower x t = (x : ℂ) ^ mellinKernelPrimitiveExponent t := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  unfold mellinHalfItPower mellinKernelPrimitiveExponent
  rw [Complex.ofReal_log hx.le]
  congr 1
  push_cast
  ring

/-- The exact kernel is the normalized average of the complex power
`x^(-1/2+it)` on the source interval. -/
theorem normalizedMellinWindowKernel_intervalAverage
    (X H t : ℝ) (hX : 0 < X) (hH : 0 < H) :
    normalizedMellinWindowKernel X H t =
      (H : ℂ)⁻¹ * ∫ x in X..X + H, (x : ℂ) ^ mellinKernelExponent t := by
  let c := mellinKernelPrimitiveExponent t
  let r := mellinKernelExponent t
  have hr : -1 < r.re := by
    norm_num [r, mellinKernelExponent]
  have hcpow := integral_cpow (a := X) (b := X + H) (r := r)
    (Or.inl hr)
  have hleft : mellinHalfItPower X t = (X : ℂ) ^ c :=
    mellinHalfItPower_eq_cpow X t hX
  have hright : mellinHalfItPower (X + H) t = (↑(X + H) : ℂ) ^ c :=
    mellinHalfItPower_eq_cpow (X + H) t (by linarith)
  have hrc : r + 1 = c := by
    dsimp [r, c, mellinKernelExponent, mellinKernelPrimitiveExponent]
    push_cast
    ring
  have hc : c ≠ 0 := mellinWindowDenominator_ne_zero t
  have hcpow' : ∫ x in X..X + H, (x : ℂ) ^ r =
      ((↑(X + H) : ℂ) ^ c - (X : ℂ) ^ c) / c := by
    simpa only [hrc] using hcpow
  rw [normalizedMellinWindowKernel, hleft, hright]
  change (((↑(X + H) : ℂ) ^ c - (X : ℂ) ^ c) /
    ((H : ℂ) * c)) = (H : ℂ)⁻¹ * ∫ x in X..X + H, (x : ℂ) ^ r
  rw [hcpow']
  field_simp [ne_of_gt hH, hc]

private theorem mellinKernelPower_norm_le
    (X x t : ℝ) (hX : 0 < X) (hXx : X ≤ x) :
    ‖(x : ℂ) ^ mellinKernelExponent t‖ ≤ X ^ ((-1 / 2 : ℝ)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x)]
  have hre : (mellinKernelExponent t).re = (-1 / 2 : ℝ) := by
    norm_num [mellinKernelExponent]
  rw [hre]
  exact Real.rpow_le_rpow_of_nonpos hX hXx (by norm_num)

private theorem normalizedMellinWindowKernel_norm_le
    (X H t : ℝ) (hX : 0 < X) (hH : 0 < H) :
    ‖normalizedMellinWindowKernel X H t‖ ≤ X ^ ((-1 / 2 : ℝ)) := by
  have hXle : X ≤ X + H := by linarith
  have hnormInt :
      ‖∫ x in X..X + H, (x : ℂ) ^ mellinKernelExponent t‖ ≤
        X ^ ((-1 / 2 : ℝ)) * |(X + H) - X| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.uIoc X (X + H) := hx
    rw [Set.uIoc_of_le hXle] at hx'
    exact mellinKernelPower_norm_le X x t hX hx'.1.le
  have hnormInt' :
      ‖∫ x in X..X + H, (x : ℂ) ^ mellinKernelExponent t‖ ≤
        X ^ ((-1 / 2 : ℝ)) * H := by
    simpa [show X + H - X = H by ring, abs_of_pos hH] using hnormInt
  calc
    ‖normalizedMellinWindowKernel X H t‖ =
        H⁻¹ * ‖∫ x in X..X + H,
          (x : ℂ) ^ mellinKernelExponent t‖ := by
      rw [normalizedMellinWindowKernel_intervalAverage X H t hX hH,
        norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
    _ ≤ H⁻¹ * (X ^ ((-1 / 2 : ℝ)) * H) := by
      exact mul_le_mul_of_nonneg_left hnormInt' (by positivity)
    _ = X ^ ((-1 / 2 : ℝ)) := by field_simp [ne_of_gt hH]

private theorem mellinHalfItPower_norm (x t : ℝ) (hx : 0 < x) :
    ‖mellinHalfItPower x t‖ = √x := by
  rw [mellinHalfItPower_eq_cpow x t hx,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (mellinKernelPrimitiveExponent t).re = (1 / 2 : ℝ) := by
    norm_num [mellinKernelPrimitiveExponent]
  rw [hre, ← Real.sqrt_eq_rpow]

private theorem sqrt_window_endpoint_sum_le
    (X H : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H) (hHX : H ≤ X) :
    √(X + H) + √X ≤ 3 * √X := by
  have hsum : X + H ≤ 2 * X := by linarith
  have hsumPos : 0 ≤ X + H := add_nonneg hX hH
  have hroot : √(X + H) ≤ 2 * √X := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hX, Real.sq_sqrt hsumPos]
  linarith

private theorem normalizedMellinWindowKernel_decay
    (X H t : ℝ) (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    (ht : t ≠ 0) :
    ‖normalizedMellinWindowKernel X H t‖ ≤ 3 * √X / (H * |t|) := by
  let c := mellinKernelPrimitiveExponent t
  have hc : c ≠ 0 := mellinWindowDenominator_ne_zero t
  have him : |t| ≤ ‖c‖ := by
    have him' := Complex.abs_im_le_norm c
    simpa [c, mellinKernelPrimitiveExponent] using him'
  have hden : H * |t| ≤ H * ‖mellinKernelPrimitiveExponent t‖ := by
    simpa [c] using mul_le_mul_of_nonneg_left him hH.le
  have hdenpos : 0 < H * |t| := mul_pos hH (abs_pos.mpr ht)
  have hnum :
      ‖mellinHalfItPower (X + H) t - mellinHalfItPower X t‖ ≤ 3 * √X := by
    calc
      _ ≤ ‖mellinHalfItPower (X + H) t‖ + ‖mellinHalfItPower X t‖ := norm_sub_le _ _
      _ = √(X + H) + √X := by
        rw [mellinHalfItPower_norm (X + H) t (by linarith),
          mellinHalfItPower_norm X t hX]
      _ ≤ 3 * √X := sqrt_window_endpoint_sum_le X H hX.le hH.le hHX
  rw [normalizedMellinWindowKernel, norm_div, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hH.le]
  exact div_le_div₀ (by positivity) hnum hdenpos
    (by simpa [c, mellinKernelPrimitiveExponent] using hden)

private theorem mellinKernelPower_deriv_norm_le
    (X x t : ℝ) (hX : 0 < X) (hXx : X ≤ x) :
    ‖deriv (fun y : ℝ => (y : ℂ) ^ mellinKernelExponent t) x‖ ≤
      (1 + |t|) * X ^ ((-3 / 2 : ℝ)) := by
  let r := mellinKernelExponent t
  have hrne : r ≠ 0 := by
    intro hr
    have hreal := congrArg Complex.re hr
    norm_num [r, mellinKernelExponent] at hreal
  have hx : 0 < x := lt_of_lt_of_le hX hXx
  have hderiv := hasDerivAt_ofReal_cpow_const (x := x) hx.ne' hrne
  have hpowNorm : ‖(x : ℂ) ^ (r - 1)‖ = x ^ ((-3 / 2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hre : (r - 1).re = (-3 / 2 : ℝ) := by
      norm_num [r, mellinKernelExponent]
    rw [hre]
  have hrNorm : ‖r‖ ≤ 1 + |t| := by
    calc
      ‖r‖ ≤ |r.re| + |r.im| := Complex.norm_le_abs_re_add_abs_im r
      _ = (1 / 2 : ℝ) + |t| := by
        norm_num [r, mellinKernelExponent, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im]
      _ ≤ 1 + |t| := by linarith
  have hpowLe : x ^ ((-3 / 2 : ℝ)) ≤ X ^ ((-3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hX hXx (by norm_num)
  rw [(hderiv.deriv)]
  rw [norm_mul, hpowNorm]
  exact mul_le_mul hrNorm hpowLe (Real.rpow_nonneg (by linarith) _)
    (by positivity)

private theorem mellinKernelPower_lipschitz
    (X y t : ℝ) (hX : 0 < X) (hXy : X ≤ y) :
    ‖(y : ℂ) ^ mellinKernelExponent t - (X : ℂ) ^ mellinKernelExponent t‖ ≤
      (y - X) * ((1 + |t|) * X ^ ((-3 / 2 : ℝ))) := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ mellinKernelExponent t
  have hrne : mellinKernelExponent t ≠ 0 := by
    intro hr
    have hreal := congrArg Complex.re hr
    norm_num [mellinKernelExponent] at hreal
  have hXy' : X ≤ y := hXy
  have hcont : ContinuousOn f (Set.Icc X y) := by
    intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const x (mellinKernelExponent t)
      (Or.inr (ne_of_gt (lt_of_lt_of_le hX hx.1)))).continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Set.Ioo X y) := by
    intro x hx
    exact ((hasDerivAt_ofReal_cpow_const (x := x)
      (ne_of_gt (lt_trans hX hx.1)) hrne).differentiableAt).differentiableWithinAt
  let C : ℝ := (1 + |t|) * X ^ ((-3 / 2 : ℝ))
  have hspeed : ∀ᵐ x, x ∈ Set.Ioo X y → ‖deriv f x‖ ≤ C :=
    Filter.Eventually.of_forall fun x hx => by
      exact mellinKernelPower_deriv_norm_le X x t hX hx.1.le
  have hBi : IntervalIntegrable (fun _ : ℝ => C) volume X y := intervalIntegrable_const
  have hdist := norm_sub_le_integral_of_norm_deriv_le_of_le
    hXy' hcont hdiff hspeed hBi
  have hconst : ∫ x in X..y, (C : ℝ) = (y - X) * C := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  change ‖f y - f X‖ ≤ (y - X) * C
  calc
    ‖f y - f X‖ ≤ ∫ x in X..y, (C : ℝ) := hdist
    _ = (y - X) * C := hconst

private theorem normalizedMellinWindowKernel_deviation
    (X H t : ℝ) (hX : 0 < X) (hH : 0 < H) :
    ‖normalizedMellinWindowKernel X H t -
        (X : ℂ) ^ mellinKernelExponent t‖ ≤
      H * ((1 + |t|) * X ^ ((-3 / 2 : ℝ))) / 2 := by
  let r := mellinKernelExponent t
  let C : ℝ := (1 + |t|) * X ^ ((-3 / 2 : ℝ))
  have hXle : X ≤ X + H := by linarith
  have hr : -1 < r.re := by norm_num [r, mellinKernelExponent]
  have hfi : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) volume X (X + H) :=
    intervalIntegrable_cpow' (r := r) hr
  have hconsti : IntervalIntegrable (fun _ : ℝ => (X : ℂ) ^ r) volume X (X + H) :=
    intervalIntegrable_const
  have hconst : ∫ x in X..X + H, ((X : ℂ) ^ r) = H * (X : ℂ) ^ r := by
    rw [intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    ring
  have hdevEq : normalizedMellinWindowKernel X H t - (X : ℂ) ^ r =
      (H : ℂ)⁻¹ * ∫ x in X..X + H, ((x : ℂ) ^ r - (X : ℂ) ^ r) := by
    rw [normalizedMellinWindowKernel_intervalAverage X H t hX hH]
    calc
      ((H : ℂ)⁻¹ * (∫ x in X..X + H, (x : ℂ) ^ r)) - (X : ℂ) ^ r =
          (H : ℂ)⁻¹ * (∫ x in X..X + H, (x : ℂ) ^ r) -
            (H : ℂ)⁻¹ * (∫ x in X..X + H, (X : ℂ) ^ r) := by
        rw [hconst]
        field_simp [ne_of_gt hH]
      _ = (H : ℂ)⁻¹ *
          ((∫ x in X..X + H, (x : ℂ) ^ r) -
            ∫ x in X..X + H, (X : ℂ) ^ r) := by ring
      _ = (H : ℂ)⁻¹ *
          (∫ x in X..X + H, ((x : ℂ) ^ r - (X : ℂ) ^ r)) := by
        rw [← intervalIntegral.integral_sub hfi hconsti]
  have hmajor :
      ‖∫ x in X..X + H, ((x : ℂ) ^ r - (X : ℂ) ^ r)‖ ≤
        ∫ x in X..X + H, ((x - X) * C) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hXle
    · filter_upwards with x hx
      exact mellinKernelPower_lipschitz X x t hX hx.1.le
    · have hgcont : Continuous fun x : ℝ => (x - X) * C := by fun_prop
      exact hgcont.intervalIntegrable X (X + H)
  have hfirstMoment : ∫ x in X..X + H, (x - X) = H ^ 2 / 2 := by
    have hid : IntervalIntegrable (fun x : ℝ => x) volume X (X + H) :=
      continuous_id.intervalIntegrable X (X + H)
    change ∫ x in X..X + H,
      ((fun y : ℝ => y) x - (fun _ : ℝ => X) x) = _
    rw [intervalIntegral.integral_sub hid intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hweighted : ∫ x in X..X + H, ((x - X) * C) = C * (H ^ 2 / 2) := by
    rw [intervalIntegral.integral_mul_const, hfirstMoment]
    ring
  have hmajor' :
      ‖∫ x in X..X + H, ((x : ℂ) ^ r - (X : ℂ) ^ r)‖ ≤ C * (H ^ 2 / 2) := by
    simpa [hweighted] using hmajor
  have hnorm :
      ‖normalizedMellinWindowKernel X H t - (X : ℂ) ^ r‖ ≤
        H⁻¹ * (C * (H ^ 2 / 2)) := by
    rw [hdevEq, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hH]
    exact mul_le_mul_of_nonneg_left hmajor' (by positivity)
  calc
    ‖normalizedMellinWindowKernel X H t -
        (X : ℂ) ^ mellinKernelExponent t‖ ≤ H⁻¹ * (C * (H ^ 2 / 2)) := by
      simpa [r] using hnorm
    _ = H * ((1 + |t|) * X ^ ((-3 / 2 : ℝ))) / 2 := by
      dsimp [C]
      field_simp [ne_of_gt hH]

private theorem normalizedMellinWindowKernel_diff_smooth
    (X H1 H2 t : ℝ) (hX : 0 < X) (hH1 : 0 < H1)
    (hH12 : H1 ≤ H2) :
    ‖normalizedMellinWindowKernel X H1 t -
        normalizedMellinWindowKernel X H2 t‖ ≤
      H2 * ((1 + |t|) * X ^ ((-3 / 2 : ℝ))) := by
  have hdev1 := normalizedMellinWindowKernel_deviation X H1 t hX hH1
  have hH2pos : 0 < H2 := lt_of_lt_of_le hH1 hH12
  have hdev2 := normalizedMellinWindowKernel_deviation X H2 t hX hH2pos
  have hC : 0 ≤ (1 + |t|) * X ^ ((-3 / 2 : ℝ)) := by positivity
  calc
    ‖normalizedMellinWindowKernel X H1 t -
        normalizedMellinWindowKernel X H2 t‖ =
        ‖(normalizedMellinWindowKernel X H1 t - (X : ℂ) ^ mellinKernelExponent t) -
          (normalizedMellinWindowKernel X H2 t - (X : ℂ) ^ mellinKernelExponent t)‖ := by
            congr 1; ring
    _ ≤ ‖normalizedMellinWindowKernel X H1 t - (X : ℂ) ^ mellinKernelExponent t‖ +
        ‖normalizedMellinWindowKernel X H2 t - (X : ℂ) ^ mellinKernelExponent t‖ :=
          norm_sub_le _ _
    _ ≤ H1 * ((1 + |t|) * X ^ ((-3 / 2 : ℝ))) / 2 +
        H2 * ((1 + |t|) * X ^ ((-3 / 2 : ℝ))) / 2 := add_le_add hdev1 hdev2
    _ ≤ H2 * ((1 + |t|) * X ^ ((-3 / 2 : ℝ))) := by nlinarith

private theorem normalizedMellinWindowKernel_diff_tail
    (X H1 H2 T0 t : ℝ) (hX : 0 < X) (hH1 : 0 < H1)
    (hH12 : H1 ≤ H2) (hH2X : H2 ≤ X) (hT0 : T0 = X / H1) :
    ‖normalizedMellinWindowKernel X H1 t -
        normalizedMellinWindowKernel X H2 t‖ ≤
      (6 / √X) * (if t = 0 then 1 else min 1 (T0 / |t|)) := by
  let T := normalizedMellinWindowKernel X H1 t -
    normalizedMellinWindowKernel X H2 t
  have hnorm1 := normalizedMellinWindowKernel_norm_le X H1 t hX hH1
  have hH2pos : 0 < H2 := lt_of_lt_of_le hH1 hH12
  have hnorm2 := normalizedMellinWindowKernel_norm_le X H2 t hX hH2pos
  have hfirst : ‖T‖ ≤ 2 * X ^ ((-1 / 2 : ℝ)) := by
    dsimp [T]
    calc
      _ ≤ ‖normalizedMellinWindowKernel X H1 t‖ +
          ‖normalizedMellinWindowKernel X H2 t‖ := norm_sub_le _ _
      _ ≤ X ^ ((-1 / 2 : ℝ)) + X ^ ((-1 / 2 : ℝ)) := add_le_add hnorm1 hnorm2
      _ = 2 * X ^ ((-1 / 2 : ℝ)) := by ring
  have hpow : X ^ ((-1 / 2 : ℝ)) = (√X)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hX.le, ← Real.sqrt_eq_rpow]
  have hfirst' : ‖T‖ ≤ 6 / √X := by
    rw [hpow] at hfirst
    have hsqrt : 0 < √X := Real.sqrt_pos.2 hX
    dsimp [T]
    calc
      _ ≤ 2 * (√X)⁻¹ := hfirst
      _ ≤ 6 * (√X)⁻¹ := by nlinarith [inv_pos.mpr hsqrt]
      _ = 6 / √X := by rw [div_eq_mul_inv]
  by_cases ht : t = 0
  · simpa [T, ht, mul_one] using hfirst'
  · have hdecay1 := normalizedMellinWindowKernel_decay X H1 t hX hH1
      (le_trans hH12 hH2X) ht
    have hdecay2 := normalizedMellinWindowKernel_decay X H2 t hX hH2pos hH2X ht
    have hsecond : ‖T‖ ≤ 6 * √X / (H1 * |t|) := by
      dsimp [T]
      calc
        _ ≤ ‖normalizedMellinWindowKernel X H1 t‖ +
            ‖normalizedMellinWindowKernel X H2 t‖ := norm_sub_le _ _
        _ ≤ 3 * √X / (H1 * |t|) + 3 * √X / (H2 * |t|) := add_le_add hdecay1 hdecay2
        _ ≤ 6 * √X / (H1 * |t|) := by
          have hden : H1 * |t| ≤ H2 * |t| :=
            mul_le_mul_of_nonneg_right hH12 (abs_nonneg t)
          have hpos : 0 < H1 * |t| := mul_pos hH1 (abs_pos.mpr ht)
          have hterm : 3 * √X / (H2 * |t|) ≤ 3 * √X / (H1 * |t|) :=
            div_le_div₀ (by positivity) le_rfl hpos hden
          calc
            3 * √X / (H1 * |t|) + 3 * √X / (H2 * |t|) ≤
                3 * √X / (H1 * |t|) + 3 * √X / (H1 * |t|) :=
              add_le_add le_rfl hterm
            _ = 6 * √X / (H1 * |t|) := by ring
    have hscale : 6 * √X / (H1 * |t|) =
        (6 / √X) * (T0 / |t|) := by
      rw [hT0]
      have hsqrt : √X ≠ 0 := (Real.sqrt_pos.2 hX).ne'
      field_simp [ne_of_gt hH1, abs_pos.mpr ht, hsqrt]
      rw [Real.sq_sqrt hX.le]
    have hsecond' : ‖T‖ ≤ (6 / √X) * (T0 / |t|) := by
      rw [← hscale]
      exact hsecond
    have hmin : ‖T‖ ≤ (6 / √X) * min 1 (T0 / |t|) := by
      by_cases hratio : T0 / |t| ≤ 1
      · rw [min_eq_right hratio]
        exact hsecond'
      · have hratio' : 1 ≤ T0 / |t| := le_of_not_ge hratio
        rw [min_eq_left hratio']
        simpa only [mul_one] using hfirst'
    simpa [T, ht]
      using hmin

/-- The two normalized logarithmic-window kernels obey the source's
individual size and decay bounds, and the two stated bounds for their
difference. The tail factor is defined to be one at `t = 0`. -/
theorem mellinWindowData_K_H_eq_normalized
    (rho : ℝ → ℝ) (X H B : ℝ) (a : ℕ → ℂ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X) (hB : 0 ≤ B)
    (hsupport : ∀ n, 0 < n → a n ≠ 0 →
      X / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 3 * X)
    (hbound : ∀ n, 0 < n → ‖a n‖ ≤ B) (t : ℝ) :
    (mellinWindowData rho X H B a hX hH hHX hB hsupport hbound).K_H t =
      normalizedMellinWindowKernel X H t := rfl

theorem normalizedWindowKernelBounds
    (X H1 H2 t : ℝ) (hX : 0 < X) (hH1 : 0 < H1)
    (hH12 : H1 ≤ H2) (hH2X : H2 ≤ X) :
    let T0 := X / H1
    ‖normalizedMellinWindowKernel X H1 t‖ ≤ X ^ ((-1 / 2 : ℝ)) ∧
    ‖normalizedMellinWindowKernel X H2 t‖ ≤ X ^ ((-1 / 2 : ℝ)) ∧
    (t ≠ 0 →
      ‖normalizedMellinWindowKernel X H1 t‖ ≤ 3 * √X / (H1 * |t|)) ∧
    (t ≠ 0 →
      ‖normalizedMellinWindowKernel X H2 t‖ ≤ 3 * √X / (H2 * |t|)) ∧
    ‖normalizedMellinWindowKernel X H1 t -
        normalizedMellinWindowKernel X H2 t‖ ≤
      H2 * ((1 + |t|) * X ^ ((-3 / 2 : ℝ))) ∧
    ‖normalizedMellinWindowKernel X H1 t -
        normalizedMellinWindowKernel X H2 t‖ ≤
      (6 / √X) * (if t = 0 then 1 else min 1 (T0 / |t|)) := by
  dsimp only
  have hH1X : H1 ≤ X := le_trans hH12 hH2X
  exact ⟨normalizedMellinWindowKernel_norm_le X H1 t hX hH1,
    normalizedMellinWindowKernel_norm_le X H2 t hX (lt_of_lt_of_le hH1 hH12),
    fun ht => normalizedMellinWindowKernel_decay X H1 t hX hH1 hH1X ht,
    fun ht => normalizedMellinWindowKernel_decay X H2 t hX
      (lt_of_lt_of_le hH1 hH12) hH2X ht,
    normalizedMellinWindowKernel_diff_smooth X H1 H2 t hX hH1 hH12,
    normalizedMellinWindowKernel_diff_tail X H1 H2 (X / H1) t hX hH1 hH12 hH2X rfl⟩

#print axioms normalizedWindowKernelBounds


