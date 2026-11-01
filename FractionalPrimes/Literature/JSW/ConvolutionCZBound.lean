module

public import FractionalPrimes.Literature.JSW.DyadicWeakCZSupport
public import FractionalPrimes.Literature.JSW.ComplexMeasureL2Representative
public import FractionalPrimes.Literature.JSW.FinitePositiveMaximalLp
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Star
public import FractionalPrimes.Literature.JSW.RealPlancherelCompletion

/-!
# The smooth convolution-kernel criterion

This file formalizes the kernel estimate in `lj:kernel-cz`, starting with
the integrable derivative-difference estimate on the complement of a
ninefold interval.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- A derivative bound of order `|x|⁻²` gives an integrable difference
estimate on one of the two components of the complement of `9Q`.  The
factor `4` is the elementary comparison `x - |h| ≥ x/2` on this tail. -/
theorem convolution_kernel_difference_integral_Ioi_le
    {K : ℝ → ℂ} (hK : ∀ x, DifferentiableAt ℝ K x)
    {B ell h : ℝ} (hB : 0 ≤ B) (hell : 0 < ell)
    (hderiv : ∀ x ≠ 0, ‖deriv K x‖ ≤ B / |x| ^ 2)
    (hh : |h| ≤ ell / 2) :
    ∫ x in Ioi (9 * ell / 2), ‖K (x - h) - K x‖ ∂(volume : Measure ℝ) ≤
      (4 / 9) * B := by
  let a : ℝ := 9 * ell / 2
  let C : ℝ := 4 * B * |h|
  have ha : 0 < a := by dsimp [a]; positivity
  have htail (x : ℝ) (hx : x ∈ Ioi a) :
      ‖K (x - h) - K x‖ ≤ C * x ^ (-2 : ℝ) := by
    have hx' : 9 * ell / 2 < x := by simpa [a] using hx
    have hxpos : 0 < x := by linarith [hell]
    have habslt : |h| < x / 2 := by
      have h1 : |h| ≤ ell / 2 := hh
      have h2 : ell / 2 < x / 2 := by nlinarith
      exact lt_of_le_of_lt h1 h2
    let s : Set ℝ := Icc (x - |h|) (x + |h|)
    have hleft : 0 < x - |h| := by linarith
    have hleftHalf : x / 2 ≤ x - |h| := by nlinarith [abs_nonneg h]
    have hxmem : x ∈ s := by
      simp only [s, mem_Icc]
      constructor <;> linarith [abs_nonneg h]
    have hxhm : x - h ∈ s := by
      simp only [s, mem_Icc]
      constructor
      · have : -|h| ≤ -h := neg_le_neg (le_abs_self h)
        linarith
      · have : h ≤ |h| := le_abs_self h
        have : -h ≤ |h| := neg_le_abs h
        linarith
    have hderivBound (z : ℝ) (hz : z ∈ s) :
        ‖deriv K z‖ ≤ 4 * B * x ^ (-2 : ℝ) := by
      have hzpos : 0 < z := lt_of_lt_of_le hleft hz.1
      have hzHalf : x / 2 ≤ z := le_trans hleftHalf hz.1
      have hdz : z ≠ 0 := ne_of_gt hzpos
      have hbase := hderiv z hdz
      have hdenSq : (x / 2) ^ 2 ≤ |z| ^ 2 := by
        have habs : x / 2 ≤ |z| := by rwa [abs_of_pos hzpos]
        nlinarith [sq_nonneg (|z| - x / 2)]
      have hden : 1 / |z| ^ 2 ≤ 1 / (x / 2) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) hdenSq
      calc
        ‖deriv K z‖ ≤ B / |z| ^ 2 := hbase
        _ = B * (1 / |z| ^ 2) := by ring
        _ ≤ B * (1 / (x / 2) ^ 2) := mul_le_mul_of_nonneg_left hden hB
        _ = B / (x / 2) ^ 2 := by ring
        _ = 4 * B * x ^ (-2 : ℝ) := by
          have hxpow : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
            rw [Real.rpow_neg (le_of_lt hxpos)]
            norm_num
          rw [hxpow]
          field_simp
          ring
    have hmv := (convex_Icc (x - |h|) (x + |h|)).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => hK z) hderivBound hxmem hxhm
    calc
      ‖K (x - h) - K x‖ ≤ (4 * B * x ^ (-2 : ℝ)) * ‖(x - h) - x‖ := hmv
      _ = C * x ^ (-2 : ℝ) := by
        simp [C, Real.norm_eq_abs]
        ring
  have hpowInt : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi a) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha
  have hmajor : IntegrableOn (fun x : ℝ => C * x ^ (-2 : ℝ)) (Ioi a) volume :=
    hpowInt.const_mul C
  have hsm : AEStronglyMeasurable
      (fun x : ℝ => ‖K (x - h) - K x‖) (volume.restrict (Ioi a)) := by
    have hKcont : Continuous K :=
      continuous_iff_continuousAt.mpr (fun x => (hK x).continuousAt)
    exact ((hKcont.comp (continuous_id.sub continuous_const)).sub hKcont).norm
      |>.aestronglyMeasurable
  have hnormInt : IntegrableOn
      (fun x : ℝ => ‖K (x - h) - K x‖) (Ioi a) volume := by
    apply hmajor.mono' hsm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    calc
      ‖‖K (x - h) - K x‖‖ = ‖K (x - h) - K x‖ :=
        Real.norm_of_nonneg (norm_nonneg _)
      _ ≤ C * x ^ (-2 : ℝ) := htail x hx
  have hmono := integral_mono_ae hnormInt hmajor
    (ae_restrict_mem measurableSet_Ioi |>.mono fun x hx => htail x hx)
  have hpowValue : (∫ x in Ioi a, x ^ (-2 : ℝ) ∂(volume : Measure ℝ)) = a⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (a := -2) (c := a) (by norm_num) ha]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num]
    simp [Real.rpow_neg (le_of_lt ha)]
  have hresult : C * a⁻¹ ≤ (4 / 9) * B := by
    dsimp [C, a]
    have hratio : (9 * ell / 2)⁻¹ = 2 / (9 * ell) := by
      field_simp
    rw [hratio]
    have hnum : 8 * B * |h| ≤ 4 * B * ell := by nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ 8 * B by positivity)]
    have hden : 0 < 9 * ell := by positivity
    calc
      4 * B * |h| * (2 / (9 * ell)) = (8 * B * |h|) / (9 * ell) := by ring
      _ ≤ (4 * B * ell) / (9 * ell) := div_le_div_of_nonneg_right hnum hden.le
      _ = (4 / 9) * B := by field_simp
  calc
    ∫ x in Ioi a, ‖K (x - h) - K x‖ ∂(volume : Measure ℝ) ≤
        ∫ x in Ioi a, C * x ^ (-2 : ℝ) ∂(volume : Measure ℝ) := hmono
    _ = C * a⁻¹ := by rw [integral_const_mul, hpowValue]
    _ ≤ (4 / 9) * B := hresult

/-- The two exterior tails together satisfy the source's off-support
integral bound. The left tail is reduced to the right tail by reflection. -/
theorem convolution_kernel_difference_integral_twoTails_le
    {K : ℝ → ℂ} (hK : ∀ x, DifferentiableAt ℝ K x)
    {B ell h : ℝ} (hB : 0 ≤ B) (hell : 0 < ell)
    (hderiv : ∀ x ≠ 0, ‖deriv K x‖ ≤ B / |x| ^ 2)
    (hh : |h| ≤ ell / 2) :
    (∫ x in Iio (-(9 * ell / 2)), ‖K (x - h) - K x‖ ∂(volume : Measure ℝ)) +
      ∫ x in Ioi (9 * ell / 2), ‖K (x - h) - K x‖ ∂(volume : Measure ℝ) ≤ B := by
  let Kneg : ℝ → ℂ := fun x => K (-x)
  have hKneg : ∀ x, DifferentiableAt ℝ Kneg x := by
    intro x
    change DifferentiableAt ℝ (fun y : ℝ => K (-y)) x
    exact (hK (-x)).comp x (hasDerivAt_neg x).differentiableAt
  have hderivNeg : ∀ x ≠ 0, ‖deriv Kneg x‖ ≤ B / |x| ^ 2 := by
    intro x hx
    have hchain : deriv Kneg x = -deriv K (-x) := by
      dsimp [Kneg]
      exact deriv_comp_neg K x
    rw [hchain, norm_neg]
    simpa only [abs_neg] using hderiv (-x) (neg_ne_zero.mpr hx)
  let f : ℝ → ℝ := fun x => ‖K (x - h) - K x‖
  have hleftEq : (∫ x in Iio (-(9 * ell / 2)), f x ∂(volume : Measure ℝ)) =
      ∫ x in Ioi (9 * ell / 2),
        ‖Kneg (x - (-h)) - Kneg x‖ ∂(volume : Measure ℝ) := by
    calc
      ∫ x in Iio (-(9 * ell / 2)), f x ∂(volume : Measure ℝ) =
          ∫ x in Iic (-(9 * ell / 2)), f x ∂(volume : Measure ℝ) := by
            rw [integral_Iic_eq_integral_Iio]
      _ = ∫ x in Ioi (9 * ell / 2), f (-x) ∂(volume : Measure ℝ) := by
            simpa using
              (integral_comp_neg_Iic (-(9 * ell / 2)) (fun x => f (-x)))
      _ = ∫ x in Ioi (9 * ell / 2),
          ‖Kneg (x - (-h)) - Kneg x‖ ∂(volume : Measure ℝ) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            change ‖K ((-x) - h) - K (-x)‖ =
              ‖K (-(x - (-h))) - K (-x)‖
            rw [show (-x) - h = -(x - (-h)) by ring]
  have hleft :
      (∫ x in Iio (-(9 * ell / 2)), f x ∂(volume : Measure ℝ)) ≤ (4 / 9) * B := by
    rw [hleftEq]
    apply convolution_kernel_difference_integral_Ioi_le hKneg hB hell hderivNeg
    simpa using hh
  have hright :
      (∫ x in Ioi (9 * ell / 2), f x ∂(volume : Measure ℝ)) ≤ (4 / 9) * B := by
    exact convolution_kernel_difference_integral_Ioi_le hK hB hell hderiv hh
  dsimp [f] at hleft hright
  calc
    (∫ x in Iio (-(9 * ell / 2)), ‖K (x - h) - K x‖ ∂(volume : Measure ℝ)) +
      ∫ x in Ioi (9 * ell / 2), ‖K (x - h) - K x‖ ∂(volume : Measure ℝ) ≤
        (4 / 9) * B + (4 / 9) * B := add_le_add hleft hright
    _ ≤ B := by nlinarith [hB]

/-- Translation to an arbitrary cell center: the derivative estimate bounds
the kernel difference on the complement of its ninefold interval by `B`. -/
theorem convolution_kernel_difference_integral_centered_twoTails_le
    {K : ℝ → ℂ} (hK : ∀ x, DifferentiableAt ℝ K x)
    {B ell c y : ℝ} (hB : 0 ≤ B) (hell : 0 < ell)
    (hderiv : ∀ x ≠ 0, ‖deriv K x‖ ≤ B / |x| ^ 2)
    (hy : |y - c| ≤ ell / 2) :
    (∫ x in Iio (c - 9 * ell / 2), ‖K (x - y) - K (x - c)‖
        ∂(volume : Measure ℝ)) +
      ∫ x in Ioi (c + 9 * ell / 2), ‖K (x - y) - K (x - c)‖
        ∂(volume : Measure ℝ) ≤ B := by
  let a : ℝ := 9 * ell / 2
  let G : ℝ → ℝ := fun x => ‖K (x - y) - K (x - c)‖
  let F : ℝ → ℝ := fun x => ‖K (x - (y - c)) - K x‖
  have ha : 0 < a := by dsimp [a]; positivity
  have hmp : MeasurePreserving (fun x : ℝ => x + c) volume volume :=
    measurePreserving_add_right volume c
  have hemb : MeasurableEmbedding (fun x : ℝ => x + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have hright :
      (∫ x in Ioi (c + a), G x ∂(volume : Measure ℝ)) =
        ∫ x in Ioi a, F x ∂(volume : Measure ℝ) := by
    have hmap := hmp.setIntegral_preimage_emb hemb G (Ioi (c + a))
    have hpre : (fun x : ℝ => x + c) ⁻¹' Ioi (c + a) = Ioi a := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi]
      constructor <;> intro hx <;> dsimp [a] at * <;> linarith
    rw [hpre] at hmap
    calc
      ∫ x in Ioi (c + a), G x ∂(volume : Measure ℝ) =
          ∫ x in Ioi a, G (x + c) ∂(volume : Measure ℝ) := hmap.symm
      _ = ∫ x in Ioi a, F x ∂(volume : Measure ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          simp only [G, F]
          congr 1
          congr 1 <;> ring
  have hleft :
      (∫ x in Iio (c - a), G x ∂(volume : Measure ℝ)) =
        ∫ x in Iio (-a), F x ∂(volume : Measure ℝ) := by
    have hmap := hmp.setIntegral_preimage_emb hemb G (Iio (c - a))
    have hpre : (fun x : ℝ => x + c) ⁻¹' Iio (c - a) = Iio (-a) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iio]
      constructor <;> intro hx <;> dsimp [a] at * <;> linarith
    rw [hpre] at hmap
    calc
      ∫ x in Iio (c - a), G x ∂(volume : Measure ℝ) =
          ∫ x in Iio (-a), G (x + c) ∂(volume : Measure ℝ) := hmap.symm
      _ = ∫ x in Iio (-a), F x ∂(volume : Measure ℝ) := by
          apply setIntegral_congr_fun measurableSet_Iio
          intro x hx
          simp only [G, F]
          congr 1
          congr 1 <;> ring
  have htails := convolution_kernel_difference_integral_twoTails_le
    hK hB hell hderiv (by simpa [a] using hy)
  simpa [G, F, a] using (add_le_add hleft.le hright.le).trans htails

/-- The constant in the derivative hypothesis of `lj:kernel-cz` is
nonnegative already: evaluating that hypothesis at `x = 1` bounds a norm by
`B`. The source statements in `expanded-blueprint.tex:3732–3742` and
`blueprint-sources 2/literature-expansion/sections/jsw.tex:446–468` do not
need a separate positivity assumption. -/
theorem convolution_kernel_derivative_constant_nonneg
    {K : ℝ → ℂ} {B : ℝ}
    (hderiv : ∀ x ≠ 0, ‖deriv K x‖ ≤ B / |x| ^ 2) :
    0 ≤ B := by
  have h := hderiv 1 (by norm_num)
  have h' : ‖deriv K 1‖ ≤ B := by simpa using h
  exact (norm_nonneg _).trans h'

/-- Pointwise form of the mean-value estimate on the right tail. The weak
inequality at the endpoint is useful for the half-open ninefold interval. -/
private theorem convolution_kernel_difference_Ioi_pointwise
    {K : ℝ → ℂ} (hK : ∀ x, DifferentiableAt ℝ K x)
    {B ell h x : ℝ} (hB : 0 ≤ B) (hell : 0 < ell)
    (hderiv : ∀ x ≠ 0, ‖deriv K x‖ ≤ B / |x| ^ 2)
    (hh : |h| ≤ ell / 2) (hx : 9 * ell / 2 ≤ x) :
    ‖K (x - h) - K x‖ ≤ 4 * B * |h| * x ^ (-2 : ℝ) := by
  have hxpos : 0 < x := by nlinarith
  let s : Set ℝ := Icc (x - |h|) (x + |h|)
  have hleft : 0 < x - |h| := by nlinarith [abs_nonneg h]
  have hleftHalf : x / 2 ≤ x - |h| := by nlinarith [abs_nonneg h]
  have hxmem : x ∈ s := by
    simp only [s, mem_Icc]
    constructor <;> linarith [abs_nonneg h]
  have hxhm : x - h ∈ s := by
    simp only [s, mem_Icc]
    constructor
    · have : -|h| ≤ -h := neg_le_neg (le_abs_self h)
      linarith
    · have : h ≤ |h| := le_abs_self h
      have : -h ≤ |h| := neg_le_abs h
      linarith
  have hderivBound (z : ℝ) (hz : z ∈ s) :
      ‖deriv K z‖ ≤ 4 * B * x ^ (-2 : ℝ) := by
    have hzpos : 0 < z := lt_of_lt_of_le hleft hz.1
    have hzHalf : x / 2 ≤ z := le_trans hleftHalf hz.1
    have hdz : z ≠ 0 := ne_of_gt hzpos
    have hbase := hderiv z hdz
    have hdenSq : (x / 2) ^ 2 ≤ |z| ^ 2 := by
      have habs : x / 2 ≤ |z| := by rwa [abs_of_pos hzpos]
      nlinarith [sq_nonneg (|z| - x / 2)]
    have hden : 1 / |z| ^ 2 ≤ 1 / (x / 2) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hdenSq
    calc
      ‖deriv K z‖ ≤ B / |z| ^ 2 := hbase
      _ = B * (1 / |z| ^ 2) := by ring
      _ ≤ B * (1 / (x / 2) ^ 2) := mul_le_mul_of_nonneg_left hden hB
      _ = 4 * B * x ^ (-2 : ℝ) := by
        have hxpow : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
          rw [Real.rpow_neg (le_of_lt hxpos)]
          norm_num
        rw [hxpow]
        field_simp
        ring
  have hmv := (convex_Icc (x - |h|) (x + |h|)).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => hK z) hderivBound hxmem hxhm
  calc
    ‖K (x - h) - K x‖ ≤ (4 * B * x ^ (-2 : ℝ)) * ‖(x - h) - x‖ := hmv
    _ = 4 * B * |h| * x ^ (-2 : ℝ) := by
      simp [Real.norm_eq_abs]
      ring

/-- The same pointwise estimate on both tails, expressed relative to an
arbitrary cell center. -/
private theorem convolution_kernel_difference_centered_pointwise
    {K : ℝ → ℂ} (hK : ∀ x, DifferentiableAt ℝ K x)
    {B ell c y x : ℝ} (hB : 0 ≤ B) (hell : 0 < ell)
    (hderiv : ∀ x ≠ 0, ‖deriv K x‖ ≤ B / |x| ^ 2)
    (hy : |y - c| ≤ ell / 2) (hx : 9 * ell / 2 ≤ |x - c|) :
    ‖K (x - y) - K (x - c)‖ ≤
      4 * B * |y - c| * |x - c| ^ (-2 : ℝ) := by
  let Kneg : ℝ → ℂ := fun z => K (-z)
  have hKneg : ∀ z, DifferentiableAt ℝ Kneg z := by
    intro z
    change DifferentiableAt ℝ (fun w : ℝ => K (-w)) z
    exact (hK (-z)).comp z (hasDerivAt_neg z).differentiableAt
  have hderivNeg : ∀ z ≠ 0, ‖deriv Kneg z‖ ≤ B / |z| ^ 2 := by
    intro z hz
    have hchain : deriv Kneg z = -deriv K (-z) := by
      dsimp [Kneg]
      exact deriv_comp_neg K z
    rw [hchain, norm_neg]
    simpa only [abs_neg] using hderiv (-z) (neg_ne_zero.mpr hz)
  let t : ℝ := x - c
  let d : ℝ := y - c
  by_cases ht : 0 ≤ t
  · have hpos : 9 * ell / 2 ≤ t := by simpa [t, abs_of_nonneg ht] using hx
    have h := convolution_kernel_difference_Ioi_pointwise hK hB hell hderiv
      (by simpa [d] using hy) hpos
    simpa [t, d, Real.norm_eq_abs, abs_of_nonneg ht] using h
  · have hneg : t < 0 := lt_of_not_ge ht
    have hpos : 9 * ell / 2 ≤ -t := by
      simpa [t, abs_of_neg hneg] using hx
    have hhneg : |-d| ≤ ell / 2 := by
      simpa [d, abs_sub_comm] using hy
    have h := convolution_kernel_difference_Ioi_pointwise (K := Kneg) hKneg
      (B := B) (ell := ell) (h := -d) (x := -t) hB hell hderivNeg
      hhneg hpos
    have harg : K (x - y) - K (x - c) = Kneg ((-t) - (-d)) - Kneg (-t) := by
      change K (x - y) - K (x - c) =
        K (-((-t) - (-d))) - K (-(-t))
      congr 1 <;> dsimp [t, d] <;> ring
    rw [harg]
    simpa [t, d, abs_of_neg hneg, abs_neg, abs_sub_comm] using h

/-- The reciprocal-square majorant is integrable on the two exterior tails;
each tail has integral `a⁻¹`. -/
private theorem reciprocalSquare_outer_integrable_and_integral
    {c a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => |x - c| ^ (-2 : ℝ))
        (Iio (c - a) ∪ Ici (c + a)) volume ∧
      ∫ x in Iio (c - a) ∪ Ici (c + a), |x - c| ^ (-2 : ℝ) ∂volume =
        2 * a⁻¹ := by
  let R : ℝ → ℝ := fun x => |x - c| ^ (-2 : ℝ)
  have hpowInt : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi a) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha
  have hpowValue : ∫ x in Ioi a, x ^ (-2 : ℝ) ∂volume = a⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (a := -2) (c := a) (by norm_num) ha]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num]
    simp [Real.rpow_neg (le_of_lt ha)]
  let eR : ℝ → ℝ := fun x => x + c
  have hmpR : MeasurePreserving eR volume volume := measurePreserving_add_right volume c
  have hembR : MeasurableEmbedding eR :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have hpreR : eR ⁻¹' Ioi (c + a) = Ioi a := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, eR]
    constructor <;> intro hx <;> linarith
  have hcompR : IntegrableOn (fun x => R (eR x)) (Ioi a) volume := by
    apply hpowInt.congr_fun
    · intro x hx
      have hxpos : 0 < x := lt_trans ha hx
      simp [R, eR, abs_of_pos hxpos]
    · exact measurableSet_Ioi
  have hRrightInt : IntegrableOn R (Ioi (c + a)) volume := by
    have hcompR' : IntegrableOn (R ∘ eR) (eR ⁻¹' Ioi (c + a)) volume := by
      simpa only [Function.comp_def, hpreR] using hcompR
    exact (hmpR.integrableOn_comp_preimage hembR (f := R)
      (s := Ioi (c + a))).mp hcompR'
  have hmapR := hmpR.setIntegral_preimage_emb hembR R (Ioi (c + a))
  rw [hpreR] at hmapR
  have hRrightValue : ∫ x in Ioi (c + a), R x ∂volume = a⁻¹ := by
    calc
      ∫ x in Ioi (c + a), R x ∂volume =
          ∫ x in Ioi a, R (x + c) ∂volume := hmapR.symm
      _ = ∫ x in Ioi a, x ^ (-2 : ℝ) ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          have hxpos : 0 < x := lt_trans ha hx
          change |(x + c) - c| ^ (-2 : ℝ) = x ^ (-2 : ℝ)
          rw [show (x + c) - c = x by ring, abs_of_pos hxpos]
      _ = a⁻¹ := hpowValue
  let eL : ℝ → ℝ := fun x => c - x
  have hmpL : MeasurePreserving eL volume volume := volume.measurePreserving_sub_left c
  have hembL : MeasurableEmbedding eL :=
    (Homeomorph.subLeft c).isClosedEmbedding.measurableEmbedding
  have hpreL : eL ⁻¹' Iio (c - a) = Ioi a := by
    ext x
    change c - x < c - a ↔ a < x
    constructor <;> intro hx <;> linarith
  have hcompL : IntegrableOn (fun x => R (eL x)) (Ioi a) volume := by
    apply hpowInt.congr_fun
    · intro x hx
      have hxpos : 0 < x := lt_trans ha hx
      change x ^ (-2 : ℝ) = |(c - x) - c| ^ (-2 : ℝ)
      rw [show (c - x) - c = -x by ring, abs_neg, abs_of_pos hxpos]
    · exact measurableSet_Ioi
  have hRleftInt : IntegrableOn R (Iio (c - a)) volume := by
    have hcompL' : IntegrableOn (R ∘ eL) (eL ⁻¹' Iio (c - a)) volume := by
      simpa only [Function.comp_def, hpreL] using hcompL
    exact (hmpL.integrableOn_comp_preimage hembL (f := R)
      (s := Iio (c - a))).mp hcompL'
  have hmapL := hmpL.setIntegral_preimage_emb hembL R (Iio (c - a))
  rw [hpreL] at hmapL
  have hRleftValue : ∫ x in Iio (c - a), R x ∂volume = a⁻¹ := by
    calc
      ∫ x in Iio (c - a), R x ∂volume =
          ∫ x in Ioi a, R (c - x) ∂volume := hmapL.symm
      _ = ∫ x in Ioi a, x ^ (-2 : ℝ) ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          have hxpos : 0 < x := lt_trans ha hx
          change |(c - x) - c| ^ (-2 : ℝ) = x ^ (-2 : ℝ)
          rw [show (c - x) - c = -x by ring, abs_neg, abs_of_pos hxpos]
      _ = a⁻¹ := hpowValue
  have hRclosedInt : IntegrableOn R (Ici (c + a)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hRrightInt
  have hEint : IntegrableOn R (Iio (c - a) ∪ Ici (c + a)) volume :=
    integrableOn_union.mpr ⟨hRleftInt, hRclosedInt⟩
  have hdisj : Disjoint (Iio (c - a)) (Ici (c + a)) := by
    apply disjoint_left.mpr
    intro x hxleft hxright
    exact (not_le_of_gt hxleft) (le_trans (by linarith [ha]) hxright)
  have hUnionValue :
      ∫ x in Iio (c - a) ∪ Ici (c + a), R x ∂volume = a⁻¹ + a⁻¹ := by
    rw [setIntegral_union hdisj measurableSet_Ici hRleftInt hRclosedInt,
      integral_Ici_eq_integral_Ioi, hRleftValue, hRrightValue]
  refine ⟨?_, ?_⟩
  · simpa [R] using hEint
  · simpa [R, two_mul] using hUnionValue

/-- Cancellation replaces the kernel by its difference from the value at the
cell center before taking the absolute value of the convolution integral. -/
theorem convolutionKernelOnCell_cancelledPointwiseBound
    {K u : ℝ → ℂ} {Q : Set ℝ} {x c : ℝ}
    (hQ : MeasurableSet Q)
    (hKint : IntegrableOn (fun y => K (x - y) * u y) Q volume)
    (huInt : IntegrableOn u Q volume)
    (hmean : ∫ y in Q, u y ∂(volume : Measure ℝ) = 0) :
    ‖∫ y in Q, K (x - y) * u y ∂(volume : Measure ℝ)‖ ≤
      ∫ y in Q, ‖K (x - y) - K (x - c)‖ * ‖u y‖ ∂(volume : Measure ℝ) := by
  let f : ℝ → ℂ := fun y => K (x - y) * u y
  let g : ℝ → ℂ := fun y => K (x - c) * u y
  have hgInt : IntegrableOn g Q volume := by
    exact huInt.const_mul (K (x - c))
  have hdiffInt : IntegrableOn (fun y => f y - g y) Q volume := hKint.sub hgInt
  have hpoint : (fun y => f y - g y) = fun y => (K (x - y) - K (x - c)) * u y := by
    funext y
    simp only [f, g]
    ring
  have hconst : (∫ y in Q, g y ∂(volume : Measure ℝ)) = 0 := by
    rw [show g = fun y => K (x - c) * u y by rfl, integral_const_mul, hmean]
    ring
  have hcancel :
      ∫ y in Q, f y ∂(volume : Measure ℝ) =
        ∫ y in Q, (K (x - y) - K (x - c)) * u y ∂(volume : Measure ℝ) := by
    calc
      ∫ y in Q, f y ∂(volume : Measure ℝ) =
          ∫ y in Q, (f y - g y) ∂(volume : Measure ℝ) +
            ∫ y in Q, g y ∂(volume : Measure ℝ) := by
              rw [integral_sub hKint hgInt]
              ring
      _ = ∫ y in Q, (K (x - y) - K (x - c)) * u y
            ∂(volume : Measure ℝ) := by rw [hconst, add_zero, ← hpoint]
  have hnorm :
      ‖∫ y in Q, (K (x - y) - K (x - c)) * u y
        ∂(volume : Measure ℝ)‖ ≤
      ∫ y in Q, ‖(K (x - y) - K (x - c)) * u y‖
        ∂(volume : Measure ℝ) := by
    change ‖∫ y, (K (x - y) - K (x - c)) * u y
        ∂((volume : Measure ℝ).restrict Q)‖ ≤
      ∫ y, ‖(K (x - y) - K (x - c)) * u y‖
        ∂((volume : Measure ℝ).restrict Q)
    exact norm_integral_le_integral_norm _
  calc
    ‖∫ y in Q, K (x - y) * u y ∂(volume : Measure ℝ)‖ =
        ‖∫ y in Q, (K (x - y) - K (x - c)) * u y
          ∂(volume : Measure ℝ)‖ := by rw [hcancel]
    _ ≤ ∫ y in Q, ‖(K (x - y) - K (x - c)) * u y‖
          ∂(volume : Measure ℝ) := hnorm
    _ = ∫ y in Q, ‖K (x - y) - K (x - c)‖ * ‖u y‖
          ∂(volume : Measure ℝ) := by
            apply setIntegral_congr_fun hQ
            intro y hy
            change ‖(K (x - y) - K (x - c)) * u y‖ =
              ‖K (x - y) - K (x - c)‖ * ‖u y‖
            rw [norm_mul]

/-! The vector-measure/Lebesgue bridge for a complex kernel. The phase map
normalizes the density by its modulus, and continuity on weighted `L¹`
extends the indicator identity to every `L¹` input. -/
variable {α : Type} [MeasurableSpace α] {μ : Measure α}
private def kernelDensityPhaseMultiplierL1 (q : α → ℂ) (hq : MemLp q ∞ μ) (hqBound : ∀ᵐ x ∂μ, ‖q x‖ ≤ 1) : Lp ℂ 1 μ →L[ℝ] Lp ℂ 1 μ := by
  let φ (u : Lp ℂ 1 μ) : α → ℂ := q • (u : α → ℂ)
  have hφ (u : Lp ℂ 1 μ) : MemLp (φ u) 1 μ := by
    simpa only [φ] using (MemLp.smul (p := ∞) (q := 1) (r := 1) hq (Lp.memLp u))
  let f : Lp ℂ 1 μ →ₗ[ℝ] Lp ℂ 1 μ := {
    toFun := fun u => MemLp.toLp (φ u) (hφ u)
    map_add' := by
      intro u v
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp (hφ u), MemLp.coeFn_toLp (hφ v),
        MemLp.coeFn_toLp (hφ (u+v)), Lp.coeFn_add u v,
        Lp.coeFn_add (MemLp.toLp (φ u) (hφ u)) (MemLp.toLp (φ v) (hφ v))] with x h₁ h₂ h₃ h₄ h₅
      calc
        (MemLp.toLp (φ (u+v)) (hφ (u+v))) x = q x • (u+v) x := by simpa [φ, Pi.smul_apply] using h₃
        _ = q x • (u x + v x) := by simpa using congrArg (fun z : ℂ => q x • z) h₄
        _ = q x • u x + q x • v x := smul_add _ _ _
        _ = (MemLp.toLp (φ u) (hφ u)) x + (MemLp.toLp (φ v) (hφ v)) x := by
              have hh₁ : (MemLp.toLp (φ u) (hφ u)) x = q x • u x := by simpa [φ, Pi.smul_apply] using h₁
              have hh₂ : (MemLp.toLp (φ v) (hφ v)) x = q x • v x := by simpa [φ, Pi.smul_apply] using h₂
              rw [hh₁, hh₂]
        _ = (MemLp.toLp (φ u) (hφ u) + MemLp.toLp (φ v) (hφ v)) x := h₅.symm
    map_smul' := by
      intro r u
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp (hφ (r • u)), MemLp.coeFn_toLp (hφ u),
        Lp.coeFn_smul r u, Lp.coeFn_smul r (MemLp.toLp (φ u) (hφ u))] with x h₁ h₂ h₃ h₄
      calc
        (MemLp.toLp (φ (r • u)) (hφ (r • u))) x = q x • (r • u) x := by simpa [φ, Pi.smul_apply] using h₁
        _ = q x • (r • u x) := by simpa using congrArg (fun z : ℂ => q x • z) h₃
        _ = r • (q x • u x) := (smul_comm r (q x) (u x)).symm
        _ = r • (MemLp.toLp (φ u) (hφ u)) x := by
              have hh₂ : (MemLp.toLp (φ u) (hφ u)) x = q x • u x := by simpa [φ, Pi.smul_apply] using h₂
              rw [hh₂]
        _ = (r • MemLp.toLp (φ u) (hφ u)) x := h₄.symm
  }
  have hbound (u : Lp ℂ 1 μ) : ‖f u‖ ≤ ‖u‖ := by
    have hh : ‖f u‖ ≤ 1 * ‖u‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul (f := f u) (g := u) (c := 1)
      filter_upwards [hqBound, MemLp.coeFn_toLp (hφ u)] with x hqx hx
      change ‖(MemLp.toLp (φ u) (hφ u)) x‖ ≤ 1 * ‖u x‖
      rw [hx]
      simpa [φ, Pi.smul_apply] using calc
        ‖q x • u x‖ = ‖q x‖ * ‖u x‖ := norm_smul _ _
        _ ≤ 1 * ‖u x‖ := by nlinarith [norm_nonneg (u x)]
    simpa using hh
  have hlip : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm]
    calc
      ‖f u - f v‖ = ‖f (u-v)‖ := by rw [map_sub]
      _ ≤ ‖u-v‖ := hbound _
      _ = 1 * dist u v := by simp [dist_eq_norm]
  exact ContinuousLinearMap.mk f hlip.continuous

private theorem kernelDensityPhaseMultiplierL1_coeFn (q : α → ℂ) (hq : MemLp q ∞ μ)
    (hqBound : ∀ᵐ x ∂μ, ‖q x‖ ≤ 1) (u : Lp ℂ 1 μ) :
    (kernelDensityPhaseMultiplierL1 q hq hqBound u : α → ℂ) =ᵐ[μ] fun x => q x * u x := by
  change (MemLp.toLp (q • (u : α → ℂ))
    (MemLp.smul (p := ∞) (q := 1) (r := 1) hq (Lp.memLp u)) : α → ℂ) =ᵐ[μ]
      fun x => q x * u x
  filter_upwards [MemLp.coeFn_toLp (MemLp.smul (p := ∞) (q := 1) (r := 1) hq (Lp.memLp u))]
    with x hx
  simpa [Pi.smul_apply, smul_eq_mul] using hx

variable {K : ℝ → ℂ}
private def kernelDensityWeight (K : ℝ → ℂ) (x : ℝ) : ℝ≥0 := ‖K x‖₊
private def kernelDensityPhase (K : ℝ → ℂ) (x : ℝ) : ℂ := K x / (kernelDensityWeight K x : ℂ)
/-- The total-variation density associated with a complex kernel. -/
def kernelVariationMeasure (K : ℝ → ℂ) : Measure ℝ :=
  volume.withDensity (fun x => (‖K x‖₊ : ℝ≥0∞))

private theorem kernelDensityWeight_eq_norm (K : ℝ → ℂ) (x : ℝ) : (kernelDensityWeight K x : ℝ) = ‖K x‖ := by simp [kernelDensityWeight]
private theorem kernelDensityPhase_mul_weight (K : ℝ → ℂ) (x : ℝ) : kernelDensityPhase K x * (kernelDensityWeight K x : ℂ) = K x := by
  by_cases h : K x = 0
  · simp [kernelDensityPhase, kernelDensityWeight, h]
  · have hn : (kernelDensityWeight K x : ℂ) ≠ 0 := by
      rw [show (kernelDensityWeight K x : ℂ) = (‖K x‖ : ℂ) by simp [kernelDensityWeight]]
      exact_mod_cast (norm_ne_zero_iff.mpr h)
    simp [kernelDensityPhase, hn]

private theorem kernelDensityPhase_norm_le (K : ℝ → ℂ) (x : ℝ) : ‖kernelDensityPhase K x‖ ≤ 1 := by
  by_cases h : K x = 0
  · simp [kernelDensityPhase, kernelDensityWeight, h]
  · have hd : ‖(kernelDensityWeight K x : ℂ)‖ = ‖K x‖ := by simp [kernelDensityWeight]
    rw [kernelDensityPhase, norm_div, hd]
    exact le_of_eq (div_self (ne_of_gt (norm_pos_iff.mpr h)))

private theorem kernelDensityPhase_measurable (K : ℝ → ℂ) (hK : Continuous K) : Measurable (kernelDensityPhase K) := by
  unfold kernelDensityPhase kernelDensityWeight
  fun_prop

private theorem kernelDensityWeight_measurable (K : ℝ → ℂ) (hK : Continuous K) : Measurable (kernelDensityWeight K) := by
  unfold kernelDensityWeight
  fun_prop

theorem kernelVariationMeasure_isFinite {K : ℝ → ℂ} (hK : Integrable K volume) : IsFiniteMeasure (kernelVariationMeasure K) := by
  have hfi : (∫⁻ x, ‖K x‖ₑ ∂volume) ≠ ∞ := by
    simpa only [enorm_norm] using (hasFiniteIntegral_iff_enorm).mp hK.norm.2 |>.ne
  have hfi' : (∫⁻ x, (‖K x‖₊ : ℝ≥0∞) ∂volume) ≠ ∞ := by
    simpa only [enorm_eq_nnnorm] using hfi
  rw [kernelVariationMeasure]
  exact isFiniteMeasure_withDensity hfi'

private noncomputable def kernelDensityIntegralCLM (K : ℝ → ℂ) (hK : Continuous K) :
    Lp ℂ 1 (kernelVariationMeasure K) →L[ℝ] ℂ := by
  let q := kernelDensityPhase K
  have hqsm : Measurable q := by
    simpa [q] using kernelDensityPhase_measurable K hK
  have hq : MemLp q ∞ volume :=
    memLp_top_of_bound hqsm.aestronglyMeasurable 1
      (ae_of_all volume fun x => kernelDensityPhase_norm_le K x)
  have hqBound : ∀ᵐ x ∂volume, ‖q x‖ ≤ 1 :=
    ae_of_all volume fun x => kernelDensityPhase_norm_le K x
  let d := kernelDensityWeight K
  have hd : Measurable d := kernelDensityWeight_measurable K hK
  exact (L1.integralCLM (α := ℝ) (E := ℂ) (μ := volume)).comp
    ((kernelDensityPhaseMultiplierL1 q hq hqBound).comp
      (withDensitySMulLI volume hd).toContinuousLinearMap)

private theorem kernelDensityIntegralCLM_apply (K : ℝ → ℂ) (hK : Continuous K)
    (u : Lp ℂ 1 (kernelVariationMeasure K)) :
    kernelDensityIntegralCLM K hK u = ∫ x, K x * u x ∂volume := by
  let q := kernelDensityPhase K
  let d := kernelDensityWeight K
  change Lp ℂ 1 (volume.withDensity fun x => (kernelDensityWeight K x : ℝ≥0∞)) at u
  have hqsm : Measurable q := by simpa [q] using kernelDensityPhase_measurable K hK
  have hq : MemLp q ∞ volume :=
    memLp_top_of_bound hqsm.aestronglyMeasurable 1
      (ae_of_all volume fun x => kernelDensityPhase_norm_le K x)
  have hqBound : ∀ᵐ x ∂volume, ‖q x‖ ≤ 1 :=
    ae_of_all volume fun x => kernelDensityPhase_norm_le K x
  have hd : Measurable d := kernelDensityWeight_measurable K hK
  change L1.integralCLM
      (kernelDensityPhaseMultiplierL1 q hq hqBound (withDensitySMulLI volume hd u)) = _
  rw [← L1.integral_eq]
  rw [L1.integral_eq_integral]
  have hmul := kernelDensityPhaseMultiplierL1_coeFn q hq hqBound (withDensitySMulLI volume hd u)
  have hden : (withDensitySMulLI volume hd u : ℝ → ℂ) =ᵐ[volume]
      (fun x => d x • u x) := by
    rw [withDensitySMulLI_apply]
    exact (memL1_smul_of_L1_withDensity hd u).coeFn_toLp
  calc
    ∫ x, (kernelDensityPhaseMultiplierL1 q hq hqBound (withDensitySMulLI volume hd u)) x ∂volume =
        ∫ x, q x * (withDensitySMulLI volume hd u) x ∂volume := by
          apply integral_congr_ae
          exact hmul
    _ = ∫ x, K x * u x ∂volume := by
          apply integral_congr_ae
          filter_upwards [hden] with x hx
          calc
            q x * (withDensitySMulLI volume hd u) x = q x * (d x • u x) := by rw [hx]
            _ = K x * u x := by
              rw [show d x • u x = (d x : ℂ) * u x by simp [NNReal.smul_def], ← mul_assoc]
              exact congrArg (fun z : ℂ => z * u x) (kernelDensityPhase_mul_weight K x)



private theorem kernelDensity_vectorIntegral_indicator (K : ℝ → ℂ) (hKcont : Continuous K)
    (hKint : Integrable K volume) (c : ℂ) {s : Set ℝ}
    (hs : MeasurableSet s) (hρs : kernelVariationMeasure K s < ∞) :
    ∫ᵛ x, (Lp.simpleFunc.indicatorConst 1 hs hρs.ne c :
          Lp ℂ 1 (kernelVariationMeasure K)) x ∂[ContinuousLinearMap.mul ℝ ℂ; volume.withDensityᵥ K] =
      kernelDensityIntegralCLM K hKcont (Lp.simpleFunc.indicatorConst 1 hs hρs.ne c) := by
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure, kernelDensityWeight]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact kernelVariationMeasure_isFinite hKint
  let z : Lp ℂ 1 (kernelVariationMeasure K) := Lp.simpleFunc.indicatorConst 1 hs hρs.ne c
  have hinput : (z : ℝ → ℂ) =ᵐ[kernelVariationMeasure K] s.indicator (fun _ => c) := by
    simpa [z, Lp.simpleFunc.coe_indicatorConst] using
      (indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hρs.ne) (c := c))
  have hinputμ : (z : ℝ → ℂ) =ᵐ[μ.variation] s.indicator (fun _ => c) := by
    simpa [hvar] using hinput
  have hinputVol : ∀ᵐ x ∂volume,
      (kernelDensityWeight K x : ℝ≥0∞) ≠ 0 → z x = s.indicator (fun _ => c) x := by
    simpa [kernelVariationMeasure] using
      (ae_withDensity_iff (kernelDensityWeight_measurable K hKcont).coe_nnreal_ennreal).1 hinput
  have hleft : ∫ᵛ x, z x ∂[B; μ] = B c (μ s) := by
    calc
      ∫ᵛ x, z x ∂[B; μ] =
          ∫ᵛ x, s.indicator (fun _ => c) x ∂[B; μ] :=
            VectorMeasure.integral_congr_ae hinputμ
      _ = B c (μ s) := VectorMeasure.integral_indicator_const c hs
  have hright : kernelDensityIntegralCLM K hKcont z =
      (∫ x in s, K x ∂volume) * c := by
    rw [kernelDensityIntegralCLM_apply]
    calc
      ∫ x, K x * z x ∂volume =
          ∫ x, K x * s.indicator (fun _ => c) x ∂volume := by
            apply integral_congr_ae
            filter_upwards [hinputVol] with x hx
            by_cases hzero : (kernelDensityWeight K x : ℝ≥0∞) = 0
            · have hzero' : kernelDensityWeight K x = 0 := by exact_mod_cast hzero
              have hKzero : K x = 0 := by
                rw [← kernelDensityPhase_mul_weight K x]
                have hzeroC : (kernelDensityWeight K x : ℂ) = 0 := by exact_mod_cast hzero'
                simp [hzeroC]
              simp [hKzero]
            · exact congrArg (fun w : ℂ => K x * w) (hx hzero)
      _ = ∫ x in s, K x * c ∂volume := by
            have hind : (fun x : ℝ => K x * s.indicator (fun _ => c) x) =
                s.indicator (fun x => K x * c) := by
              funext x
              by_cases hx : x ∈ s <;> simp [Set.indicator, hx]
            rw [hind, integral_indicator hs]
      _ = (∫ x in s, K x ∂volume) * c := by
            rw [integral_mul_const]
  have hμs : μ s = ∫ x in s, K x ∂volume := withDensityᵥ_apply hKint hs
  have hB : B c (μ s) = (∫ x in s, K x ∂volume) * c := by
    dsimp [B]
    rw [hμs]
    simp [ContinuousLinearMap.mul_apply, mul_comm]
  simpa [z] using hleft.trans (hB.trans hright.symm)



set_option maxHeartbeats 800000 in
theorem kernelDensity_vectorIntegral_eq_integral (K : ℝ → ℂ) (hKcont : Continuous K)
    (hKint : Integrable K volume) (u : Lp ℂ 1 (kernelVariationMeasure K)) :
    ∫ᵛ x, u x ∂[ContinuousLinearMap.mul ℝ ℂ; volume.withDensityᵥ K] =
      ∫ x, K x * u x ∂volume := by
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  let R := kernelDensityIntegralCLM K hKcont
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure, kernelDensityWeight]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact kernelVariationMeasure_isFinite hKint
  have hleftCont : Continuous (fun v : Lp ℂ 1 (kernelVariationMeasure K) =>
      ∫ᵛ x, v x ∂[B; μ]) := by
    rw [← hvar]
    simpa only [VectorMeasure.integral_eq_setToFun] using
      (continuous_setToFun (dominatedFinMeasAdditive_cbmApplyMeasure μ B))
  have hclosed : IsClosed {v : Lp ℂ 1 (kernelVariationMeasure K) |
      ∫ᵛ x, v x ∂[B; μ] = R v} := isClosed_eq hleftCont R.continuous
  have hbase : ∀ (c : ℂ) {s : Set ℝ} (hs : MeasurableSet s)
      (hρs : kernelVariationMeasure K s < ∞),
      ∫ᵛ x, (Lp.simpleFunc.indicatorConst 1 hs hρs.ne c :
          Lp ℂ 1 (kernelVariationMeasure K)) x ∂[B; μ] =
        R (Lp.simpleFunc.indicatorConst 1 hs hρs.ne c) := by
    intro c s hs hρs
    simpa [μ, B, R] using kernelDensity_vectorIntegral_indicator K hKcont hKint c hs hρs
  have hadd : ∀ ⦃f g : ℝ → ℂ⦄, ∀ hf : MemLp f 1 (kernelVariationMeasure K),
      ∀ hg : MemLp g 1 (kernelVariationMeasure K), Disjoint (Function.support f) (Function.support g) →
        (∫ᵛ x, (hf.toLp f) x ∂[B; μ] = R (hf.toLp f)) →
        (∫ᵛ x, (hg.toLp g) x ∂[B; μ] = R (hg.toLp g)) →
        (∫ᵛ x, (hf.toLp f + hg.toLp g) x ∂[B; μ] =
          R (hf.toLp f + hg.toLp g)) := by
    intro f g hf hg _hdisj hPf hPg
    have hfρ : Integrable f (kernelVariationMeasure K) := memLp_one_iff_integrable.mp hf
    have hgρ : Integrable g (kernelVariationMeasure K) := memLp_one_iff_integrable.mp hg
    have hfμ : μ.Integrable f := by
      change Integrable f μ.variation
      simpa [hvar] using hfρ
    have hgμ : μ.Integrable g := by
      change Integrable g μ.variation
      simpa [hvar] using hgρ
    have hfg : (hf.toLp f + hg.toLp g : Lp ℂ 1 (kernelVariationMeasure K)) =ᵐ[kernelVariationMeasure K]
        fun x => f x + g x := by
      filter_upwards [Lp.coeFn_add (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
        with x hsum hfx hgx
      calc
        (hf.toLp f + hg.toLp g) x = (hf.toLp f) x + (hg.toLp g) x := hsum
        _ = f x + g x := by rw [hfx, hgx]
    have hfgμ : (hf.toLp f + hg.toLp g : Lp ℂ 1 (kernelVariationMeasure K)) =ᵐ[μ.variation]
        fun x => f x + g x := by simpa [hvar] using hfg
    calc
      ∫ᵛ x, (hf.toLp f + hg.toLp g) x ∂[B; μ] =
          ∫ᵛ x, f x + g x ∂[B; μ] := VectorMeasure.integral_congr_ae hfgμ
      _ = (∫ᵛ x, f x ∂[B; μ]) + ∫ᵛ x, g x ∂[B; μ] :=
          VectorMeasure.integral_add hfμ hgμ
      _ = (∫ᵛ x, (hf.toLp f) x ∂[B; μ]) +
          ∫ᵛ x, (hg.toLp g) x ∂[B; μ] := by
            have hF : ∫ᵛ x, f x ∂[B; μ] =
                ∫ᵛ x, (hf.toLp f) x ∂[B; μ] :=
              VectorMeasure.integral_congr_ae (by simpa [hvar] using hf.coeFn_toLp.symm)
            have hG : ∫ᵛ x, g x ∂[B; μ] =
                ∫ᵛ x, (hg.toLp g) x ∂[B; μ] :=
              VectorMeasure.integral_congr_ae (by simpa [hvar] using hg.coeFn_toLp.symm)
            exact congrArg₂ (fun a b : ℂ => a + b) hF hG
      _ = R (hf.toLp f) + R (hg.toLp g) := by rw [hPf, hPg]
      _ = R (hf.toLp f + hg.toLp g) := (R.map_add _ _).symm
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  have hrep : ∫ᵛ x, u x ∂[B; μ] = R u :=
    Lp.induction (p := 1) (μ := kernelVariationMeasure K) (by norm_num)
      (fun v => ∫ᵛ x, v x ∂[B; μ] = R v) hbase hadd hclosed u
  exact hrep.trans (kernelDensityIntegralCLM_apply K hKcont u)

theorem kernelDensity_vectorIntegral_eq_function
    (K : ℝ → ℂ) (hKcont : Continuous K) (hKint : Integrable K volume)
    (g : ℝ → ℂ) (hg : MemLp g 1 (kernelVariationMeasure K)) :
    ∫ᵛ y, g y ∂[ContinuousLinearMap.mul ℝ ℂ; volume.withDensityᵥ K] =
      ∫ y, K y * g y ∂volume := by
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact kernelVariationMeasure_isFinite hKint
  let z : Lp ℂ 1 (kernelVariationMeasure K) := hg.toLp g
  have hρ : (z : ℝ → ℂ) =ᵐ[μ.variation] g := by
    simpa [z, hvar] using hg.coeFn_toLp
  have hvol : ∀ᵐ y ∂volume,
      (kernelDensityWeight K y : ℝ≥0∞) ≠ 0 → z y = g y := by
    have htoWeight : (z : ℝ → ℂ) =ᵐ[volume.withDensity
        (fun y => (kernelDensityWeight K y : ℝ≥0∞))] g := by
      simpa [z, kernelVariationMeasure, kernelDensityWeight] using hg.coeFn_toLp
    exact (ae_withDensity_iff
      (kernelDensityWeight_measurable K hKcont).coe_nnreal_ennreal).1 htoWeight
  have hbridge := kernelDensity_vectorIntegral_eq_integral K hKcont hKint z
  calc
    ∫ᵛ y, g y ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
        ∫ᵛ y, z y ∂[ContinuousLinearMap.mul ℝ ℂ; μ] :=
          VectorMeasure.integral_congr_ae hρ.symm
    _ = ∫ y, K y * z y ∂volume := hbridge
    _ = ∫ y, K y * g y ∂volume := by
          apply integral_congr_ae
          filter_upwards [hvol] with y hy
          by_cases hzero : K y = 0
          · simp [hzero]
          · apply congrArg (fun w : ℂ => K y * w)
            apply hy
            intro hd
            simp [kernelDensityWeight, hzero] at hd

private theorem kernelDensity_translate_memLp_one
    (K : ℝ → ℂ) (hKcont : Continuous K) (m j : ℤ) (x : ℝ)
    (u : ℝ → ℂ) (hu₁ : MemLp u 1 volume)
    (hsupp : ∀ᵐ z ∂volume, z ∉ dyadicInterval m j → u z = 0) :
    MemLp (fun y => u (x-y)) 1 (kernelVariationMeasure K) := by
  classical
  let Q := dyadicInterval m j
  let a : ℝ := (j : ℝ) * (2 : ℝ) ^ m
  let b : ℝ := ((j + 1 : ℤ) : ℝ) * (2 : ℝ) ^ m
  let I : Set ℝ := Set.Icc (x-b) (x-a)
  have hQmeas : MeasurableSet Q := by
    dsimp [Q, dyadicInterval]
    exact measurableSet_Ico
  have hQI : ∀ y, x-y ∈ Q → y ∈ I := by
    intro y hy
    simp only [Q, dyadicInterval, Set.mem_Ico] at hy
    simp only [I, Set.mem_Icc]
    constructor <;> dsimp [a, b] at * <;> linarith
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image (hKcont.norm.continuousOn))
  let C' := max C 0
  let dcut : ℝ → ℝ := fun y =>
    if x-y ∈ Q then ‖K y‖ else 0
  have hshiftMeas : MeasurableSet {y : ℝ | x-y ∈ Q} :=
    hQmeas.preimage (by fun_prop)
  have hdmeas : Measurable dcut := by
    dsimp [dcut]
    exact Measurable.ite hshiftMeas hKcont.norm.measurable measurable_const
  have hdBound : ∀ y, ‖dcut y‖ ≤ C' := by
    intro y
    by_cases hy : x-y ∈ Q
    · have hyI : y ∈ I := hQI y hy
      have hKy : ‖K y‖ ≤ C' :=
        (hC _ ⟨y, hyI, rfl⟩).trans (le_max_left C 0)
      simpa [dcut, hy] using hKy
    · simp [dcut, hy, C', le_max_right]
  have hdLp : MemLp dcut ∞ volume :=
    memLp_top_of_bound hdmeas.aestronglyMeasurable C'
      (ae_of_all volume hdBound)
  have htransInt : Integrable (fun y => u (x-y)) volume :=
    (volume.measurePreserving_sub_left x).integrable_comp_of_integrable
      (memLp_one_iff_integrable.mp hu₁)
  have htransLp : MemLp (fun y => u (x-y)) 1 volume :=
    memLp_one_iff_integrable.mpr htransInt
  have hmulLp : MemLp (fun y => dcut y • u (x-y)) 1 volume :=
    MemLp.smul (p := ∞) (q := 1) (r := 1) hdLp htransLp
  have hshiftSupp : ∀ᵐ y ∂volume, x-y ∉ Q → u (x-y) = 0 :=
    (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hsupp
  have hcutEq : (fun y => dcut y • u (x-y)) =ᵐ[volume]
      fun y => (kernelDensityWeight K y : ℝ) • u (x-y) := by
    filter_upwards [hshiftSupp] with y hshiftSupp
    by_cases hy : x-y ∈ Q
    · simp [dcut, hy, kernelDensityWeight_eq_norm]
    · have hu0 : u (x-y) = 0 := hshiftSupp hy
      simp [dcut, hy, hu0]
  have hmulInt : Integrable
      (fun y => (kernelDensityWeight K y : ℝ) • u (x-y)) volume :=
    (memLp_one_iff_integrable.mp hmulLp).congr hcutEq
  have hρint : Integrable (fun y => u (x-y)) (kernelVariationMeasure K) := by
    change Integrable (fun y => u (x-y))
      (volume.withDensity (fun y => (kernelDensityWeight K y : ℝ≥0∞)))
    exact (integrable_withDensity_iff_integrable_smul
      (kernelDensityWeight_measurable K hKcont)).2 hmulInt
  exact memLp_one_iff_integrable.mpr hρint

/-- The `L²` convolution operator associated with an integrable complex
kernel density. -/
noncomputable def kernelConvolutionL2Operator
    (K : ℝ → ℂ) (hKint : Integrable K volume) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] Lp ℂ 2 (volume : Measure ℝ) := by
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact kernelVariationMeasure_isFinite hKint
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  exact lpComplexMeasureConvolutionCLM 2 (by norm_num) μ

private theorem lpComplexMeasureConvolution_ae_eq_kernelIntegral_of_supported
    (K : ℝ → ℂ) (hKcont : Continuous K) (hKint : Integrable K volume)
    (m j : ℤ) (u : ℝ → ℂ) (hu₁ : MemLp u 1 volume) (hu₂ : MemLp u 2 volume)
    (hsupp : ∀ z, z ∉ dyadicInterval m j → u z = 0) :
    (kernelConvolutionL2Operator K hKint (hu₂.toLp u) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y, K y * (hu₂.toLp u) (x-y) ∂volume := by
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  let F : Lp ℂ 2 volume := hu₂.toLp u
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact kernelVariationMeasure_isFinite hKint
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hFae : (F : ℝ → ℂ) =ᵐ[volume] u := by
    simpa [F] using hu₂.coeFn_toLp
  have hF₁ : MemLp (fun z : ℝ => F z) 1 volume :=
    (memLp_congr_ae hFae).mpr hu₁
  have hFsupp : ∀ᵐ z ∂volume, z ∉ dyadicInterval m j → F z = 0 := by
    filter_upwards [hFae] with z hzu
    intro hz
    rw [hzu]
    exact hsupp z hz
  have hraw := complexMeasureConvolution_ae_eq_raw_integral μ F
  have hpoint : (fun x : ℝ => complexMeasureConvolution μ (fun z => F z)
        (Lp.aestronglyMeasurable F) x) =ᵐ[volume]
      fun x => ∫ y, K y * F (x-y) ∂volume := by
    filter_upwards [hraw] with x hrawX
    calc
      complexMeasureConvolution μ (fun z => F z) (Lp.aestronglyMeasurable F) x =
          ∫ᵛ y, F (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hrawX
      _ = ∫ y, K y * F (x-y) ∂volume :=
        kernelDensity_vectorIntegral_eq_function K hKcont hKint _
          (kernelDensity_translate_memLp_one K hKcont m j x (fun z => F z) hF₁ hFsupp)
  have hLpRaw := lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution μ F
  change (lpComplexMeasureConvolution 2 μ F : ℝ → ℂ) =ᵐ[volume] _
  exact hLpRaw.trans hpoint

/-- On a smooth compactly supported input, the `L²` representative of
convolution by the complex density `K` agrees almost everywhere with the
ordinary Lebesgue convolution integral. -/
theorem lpComplexMeasureConvolution_ae_eq_kernelIntegral_of_smooth_compactSupport
    (K : ℝ → ℂ) (hKcont : Continuous K) (hKint : Integrable K volume)
    (f : ℝ → ℂ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f) :
    (lpComplexMeasureConvolution 2 (volume.withDensityᵥ K)
      ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y, K y * f (x-y) ∂volume := by
  have hfcont : Continuous f := hf.continuous
  have hf₂ : MemLp f 2 volume := hfcont.memLp_of_hasCompactSupport hfc
  let F : Lp ℂ 2 volume := hf₂.toLp f
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact kernelVariationMeasure_isFinite hKint
  have hraw := complexMeasureConvolution_ae_eq_raw_integral μ F
  have hcongr := rawComplexMeasureConvolution_ae_congr μ f (fun y => F y)
    hfcont.stronglyMeasurable (Lp.stronglyMeasurable F)
    (by simpa [F] using hf₂.coeFn_toLp.symm)
  have hpoint : (fun x : ℝ => complexMeasureConvolution μ (fun y => F y)
        (Lp.aestronglyMeasurable F) x) =ᵐ[volume]
      fun x => ∫ y, K y * f (x-y) ∂volume := by
    filter_upwards [hraw, hcongr] with x hrawX hcongrX
    calc
      complexMeasureConvolution μ (fun y => F y) (Lp.aestronglyMeasurable F) x =
          ∫ᵛ y, F (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hrawX
      _ = ∫ᵛ y, f (x-y) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := hcongrX.symm
      _ = ∫ y, K y * f (x-y) ∂volume :=
        kernelDensity_vectorIntegral_eq_function K hKcont hKint _ (by
          letI : IsFiniteMeasure (kernelVariationMeasure K) :=
            kernelVariationMeasure_isFinite hKint
          obtain ⟨C, hC⟩ := hfcont.bounded_above_of_compact_support hfc
          exact MemLp.of_bound
            ((hfcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
            C (ae_of_all _ fun y => hC (x-y)))
  exact (lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution μ F).trans hpoint

/-- The public kernel operator used in `lj:kernel-cz` has the ordinary
Lebesgue-convolution representative on every smooth compactly supported
input. -/
theorem kernelConvolutionL2Operator_ae_eq_kernelIntegral_of_smooth_compactSupport
    (K : ℝ → ℂ) (hKcont : Continuous K) (hKint : Integrable K volume)
    (f : ℝ → ℂ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f) :
    (kernelConvolutionL2Operator K hKint
      ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y, K y * f (x-y) ∂volume := by
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact kernelVariationMeasure_isFinite hKint
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  change (lpComplexMeasureConvolution 2 μ
      ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f) : ℝ → ℂ) =ᵐ[volume] _
  simpa [μ] using
    lpComplexMeasureConvolution_ae_eq_kernelIntegral_of_smooth_compactSupport
      K hKcont hKint f hf hfc

/-- The ordinary kernel convolution obeys the exact dyadic off-support
estimate required by lj:kernel-cz. The derivative bound is used pointwise
to dominate the cancelled integral by a reciprocal-square tail; integrating
the two tails gives 8B/9, hence the source constant B. -/
theorem kernelConvolutionL2Operator_weakCZOffSupportBound
    (K : ℝ → ℂ) (hKcont : Continuous K) (hKdiff : ∀ x, DifferentiableAt ℝ K x)
    (hKint : Integrable K volume) {B : ℝ}
    (hderiv : ∀ x ≠ 0, ‖deriv K x‖ ≤ B / |x| ^ 2) :
    weakCZOffSupportBound (kernelConvolutionL2Operator K hKint) B := by
  have hB : 0 ≤ B := convolution_kernel_derivative_constant_nonneg hderiv
  intro u m j hu₁ hu₂ hmean hsupp
  let Q : Set ℝ := dyadicInterval m j
  let ell : ℝ := (2 : ℝ) ^ m
  let c : ℝ := ((j : ℝ) + (1 / 2 : ℝ)) * ell
  let a : ℝ := 9 * ell / 2
  let E : Set ℝ := (dyadicNinefoldInterval m j)ᶜ
  let F : Lp ℂ 2 (volume : Measure ℝ) := hu₂.toLp u
  let T : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp ℂ 2 (volume : Measure ℝ) := kernelConvolutionL2Operator K hKint
  let mass : ℝ := ∫ z, ‖u z‖ ∂volume
  let R : ℝ → ℝ := fun x => |x - c| ^ (-2 : ℝ)
  let C : ℝ := 2 * B * ell * mass
  let G : ℝ → ℝ := fun x => C * R x
  have hell : 0 < ell := by dsimp [ell]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hQ : MeasurableSet Q := by
    dsimp [Q]
    exact measurableSet_Ico
  have hQeq : Q = Ico ((j : ℝ) * ell) (((j + 1 : ℤ) : ℝ) * ell) := by
    dsimp [Q, dyadicInterval, ell]
  have hstep : (((j + 1 : ℤ) : ℝ) * ell) = (j : ℝ) * ell + ell := by
    push_cast
    ring
  have hc : c = (j : ℝ) * ell + ell / 2 := by
    dsimp [c]
    ring
  have hNine : dyadicNinefoldInterval m j = Ico (c - a) (c + a) := by
    dsimp [dyadicNinefoldInterval, c, ell, a]
    push_cast
    congr 1 <;> ring
  have hE : E = Iio (c - a) ∪ Ici (c + a) := by
    dsimp [E]
    rw [hNine]
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Ico, Set.mem_union,
      Set.mem_Iio, Set.mem_Ici]
    constructor
    · intro hx
      by_cases hleft : x < c - a
      · exact Or.inl hleft
      · right
        by_contra hright
        apply hx
        exact ⟨le_of_not_gt hleft, lt_of_not_ge hright⟩
    · rintro (hleft | hright) hmem
      · exact (not_le_of_gt hleft) hmem.1
      · exact (not_lt_of_ge hright) hmem.2
  have hEmeas : MeasurableSet E := by
    dsimp [E]
    rw [hNine]
    exact measurableSet_Ico.compl
  have hyQ (y : ℝ) (hy : y ∈ Q) : |y - c| ≤ ell / 2 := by
    have hy' : (j : ℝ) * ell ≤ y ∧ y < (((j + 1 : ℤ) : ℝ) * ell) := by
      simpa [hQeq] using hy
    rw [abs_le]
    constructor
    · rw [hc]
      nlinarith [hy'.1]
    · rw [hc]
      nlinarith [hy'.2, hstep]
  have hfar (x : ℝ) (hx : x ∈ E) : a ≤ |x - c| := by
    have hxnot : x ∉ Ico (c - a) (c + a) := by
      have hx' : x ∉ dyadicNinefoldInterval m j := by
        simpa [E] using hx
      simpa [hNine] using hx'
    change ¬ (c - a ≤ x ∧ x < c + a) at hxnot
    by_cases hleft : x < c - a
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · have hright : c + a ≤ x := by
        by_contra hn
        apply hxnot
        exact ⟨le_of_not_gt hleft, lt_of_not_ge hn⟩
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hFae : (F : ℝ → ℂ) =ᵐ[volume] u := by
    simpa [F] using hu₂.coeFn_toLp
  have hF₁ : MemLp (fun z : ℝ => F z) 1 volume :=
    (memLp_congr_ae hFae).mpr hu₁
  have hFsupp : ∀ᵐ z ∂volume, z ∉ Q → F z = 0 := by
    filter_upwards [hFae] with z hzu
    intro hz
    rw [hzu]
    exact hsupp z (by simpa [Q] using hz)
  have hFsuppComp : ∀ᵐ z ∂volume, z ∈ Qᶜ → F z = 0 := by
    simpa [Set.mem_compl_iff] using hFsupp
  have hFsuppRestrict : ∀ᵐ z ∂(volume.restrict Qᶜ), F z = 0 :=
    (ae_restrict_iff' hQ.compl).2 hFsuppComp
  have hFint : Integrable (fun z : ℝ => F z) volume :=
    memLp_one_iff_integrable.mp hF₁
  have hFQint : IntegrableOn (fun z : ℝ => F z) Q volume := hFint.integrableOn
  have hFmean : ∫ z, F z ∂volume = 0 := by
    calc
      ∫ z, F z ∂volume = ∫ z, u z ∂volume := integral_congr_ae hFae
      _ = 0 := hmean
  have hFcompZero : ∫ z in Qᶜ, F z ∂volume = 0 := by
    calc
      ∫ z in Qᶜ, F z ∂volume = ∫ z in Qᶜ, (0 : ℂ) ∂volume :=
        integral_congr_ae hFsuppRestrict
      _ = 0 := by simp
  have hFQmean : ∫ z in Q, F z ∂volume = 0 := by
    rw [← integral_add_compl hQ hFint, hFcompZero, add_zero] at hFmean
    exact hFmean
  have hFNormInt : Integrable (fun z : ℝ => ‖F z‖) volume := hFint.norm
  have hFcompNormZero : ∫ z in Qᶜ, ‖F z‖ ∂volume = 0 := by
    have hz0 : ∀ᵐ z ∂(volume.restrict Qᶜ), ‖F z‖ = 0 := by
      filter_upwards [hFsuppRestrict] with z hzsup
      simp [hzsup]
    calc
      ∫ z in Qᶜ, ‖F z‖ ∂volume = ∫ z in Qᶜ, (0 : ℝ) ∂volume :=
        integral_congr_ae hz0
      _ = 0 := by simp
  have hFtotalNorm : ∫ z, ‖F z‖ ∂volume = ∫ z in Q, ‖F z‖ ∂volume := by
    rw [← integral_add_compl hQ hFNormInt, hFcompNormZero, add_zero]
  have hNormAE : (fun z : ℝ => ‖F z‖) =ᵐ[volume] fun z => ‖u z‖ :=
    hFae.mono fun z hz => congrArg norm hz
  have hmassEq : ∫ z in Q, ‖F z‖ ∂volume = mass := by
    calc
      ∫ z in Q, ‖F z‖ ∂volume = ∫ z, ‖F z‖ ∂volume := hFtotalNorm.symm
      _ = ∫ z, ‖u z‖ ∂volume := integral_congr_ae hNormAE
  have hmassNonneg : 0 ≤ mass := by
    dsimp [mass]
    exact integral_nonneg (fun z => norm_nonneg _)
  have hrep := lpComplexMeasureConvolution_ae_eq_kernelIntegral_of_supported
    K hKcont hKint m j u hu₁ hu₂ hsupp
  have hkernelBound (x : ℝ) (hxE : x ∈ E) :
      ‖∫ y, K y * F (x-y) ∂volume‖ ≤ C * R x := by
    have hfarx : a ≤ |x-c| := hfar x hxE
    have hrpos : 0 < |x-c| := lt_of_lt_of_le ha hfarx
    have hRnonneg : 0 ≤ R x := by
      dsimp [R]
      positivity
    let M : ℝ := 2 * B * ell * R x
    have hMnonneg : 0 ≤ M := by dsimp [M]; positivity
    have hdiffBound (y : ℝ) (hy : y ∈ Q) :
        ‖K (x-y) - K (x-c)‖ ≤ M := by
      have hycenter := hyQ y hy
      have hcoeff : 4 * B * |y-c| ≤ 2 * B * ell := by
        nlinarith [mul_le_mul_of_nonneg_left hycenter (show 0 ≤ 4 * B by positivity)]
      have hpoint := convolution_kernel_difference_centered_pointwise
        hKdiff hB hell hderiv hycenter hfarx
      calc
        ‖K (x-y) - K (x-c)‖ ≤ 4 * B * |y-c| * R x := hpoint
        _ ≤ 2 * B * ell * R x := mul_le_mul_of_nonneg_right hcoeff hRnonneg
        _ = M := rfl
    have hKdiffCont : Continuous (fun y : ℝ => K (x-y) - K (x-c)) := by
      exact (hKcont.comp (continuous_const.sub continuous_id)).sub continuous_const
    have hmajorInt : IntegrableOn (fun y : ℝ => M * ‖F y‖) Q volume :=
      (hFNormInt.const_mul M).integrableOn
    have hdiffInt : IntegrableOn
        (fun y : ℝ => (K (x-y) - K (x-c)) * F y) Q volume := by
      apply hmajorInt.mono'
        (hKdiffCont.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F)).restrict
      filter_upwards [ae_restrict_mem hQ] with y hy
      calc
        ‖(K (x-y) - K (x-c)) * F y‖ =
            ‖K (x-y) - K (x-c)‖ * ‖F y‖ := norm_mul _ _
        _ ≤ M * ‖F y‖ := mul_le_mul_of_nonneg_right (hdiffBound y hy) (norm_nonneg _)
    have hdiffNormInt : IntegrableOn
        (fun y : ℝ => ‖K (x-y) - K (x-c)‖ * ‖F y‖) Q volume := by
      apply hmajorInt.mono'
        (((hKdiffCont.norm.aestronglyMeasurable.mul
          (Lp.aestronglyMeasurable F).norm)).restrict)
      filter_upwards [ae_restrict_mem hQ] with y hy
      calc
        ‖‖K (x-y) - K (x-c)‖ * ‖F y‖‖ =
            ‖K (x-y) - K (x-c)‖ * ‖F y‖ := by
              rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        _ ≤ M * ‖F y‖ :=
          mul_le_mul_of_nonneg_right (hdiffBound y hy) (norm_nonneg _)
    have hconstInt : IntegrableOn (fun y : ℝ => K (x-c) * F y) Q volume :=
      hFQint.const_mul (K (x-c))
    have hsourceInt : IntegrableOn (fun y : ℝ => K (x-y) * F y) Q volume := by
      apply (hdiffInt.add hconstInt).congr_fun
      · intro y hy
        simp only [Pi.add_apply]
        ring
      · exact hQ
    have hsourceGlobal : Integrable (fun y : ℝ => K (x-y) * F y) volume := by
      have hindicator := hsourceInt.integrable_indicator hQ
      have hsourceAE : (fun y : ℝ => K (x-y) * F y) =ᵐ[volume]
          Q.indicator (fun y => K (x-y) * F y) := by
        filter_upwards [hFsupp] with y hy
        by_cases hQy : y ∈ Q
        · simp [hQy]
        · simp [hQy, hy hQy]
      exact hindicator.congr hsourceAE.symm
    have hsourceCompZero :
        ∫ y in Qᶜ, K (x-y) * F y ∂volume = 0 := by
      have hy0 : ∀ᵐ y ∂(volume.restrict Qᶜ), K (x-y) * F y = 0 := by
        filter_upwards [hFsuppRestrict] with y hy
        simp [hy]
      calc
        ∫ y in Qᶜ, K (x-y) * F y ∂volume =
            ∫ y in Qᶜ, (0 : ℂ) ∂volume := integral_congr_ae hy0
        _ = 0 := by simp
    have hsourceCell :
        ∫ y, K (x-y) * F y ∂volume =
          ∫ y in Q, K (x-y) * F y ∂volume := by
      rw [← integral_add_compl hQ hsourceGlobal, hsourceCompZero, add_zero]
    have hchange :
        ∫ y, K (x-y) * F y ∂volume = ∫ y, K y * F (x-y) ∂volume := by
      have h := (volume.measurePreserving_sub_left x).integral_comp
        (Homeomorph.subLeft x).measurableEmbedding
        (fun y : ℝ => K y * F (x-y))
      simpa [sub_sub_cancel] using h
    have hcancel := convolutionKernelOnCell_cancelledPointwiseBound
      (x := x) (c := c) hQ hsourceInt hFQint hFQmean
    have hcellEq :
        ∫ y, K y * F (x-y) ∂volume =
          ∫ y in Q, K (x-y) * F y ∂volume := hchange.symm.trans hsourceCell
    have hdiffIntegral :
        ∫ y in Q, ‖K (x-y) - K (x-c)‖ * ‖F y‖ ∂volume ≤
          M * ∫ y in Q, ‖F y‖ ∂volume := by
      calc
        ∫ y in Q, ‖K (x-y) - K (x-c)‖ * ‖F y‖ ∂volume ≤
            ∫ y in Q, M * ‖F y‖ ∂volume :=
          integral_mono_ae hdiffNormInt hmajorInt
            ((ae_restrict_mem hQ).mono fun y hy =>
              mul_le_mul_of_nonneg_right (hdiffBound y hy) (norm_nonneg _))
        _ = M * ∫ y in Q, ‖F y‖ ∂volume := by rw [integral_const_mul]
    calc
      ‖∫ y, K y * F (x-y) ∂volume‖ =
          ‖∫ y in Q, K (x-y) * F y ∂volume‖ := by rw [hcellEq]
      _ ≤ ∫ y in Q, ‖K (x-y) - K (x-c)‖ * ‖F y‖ ∂volume := hcancel
      _ ≤ M * ∫ y in Q, ‖F y‖ ∂volume := hdiffIntegral
      _ = C * R x := by
        rw [hmassEq]
        dsimp [M, C]
        ring
  have hboundAE : ∀ᵐ x ∂volume,
      x ∈ E → ‖(T F : ℝ → ℂ) x‖ ≤ G x := by
    filter_upwards [hrep] with x hrepX
    intro hxE
    rw [hrepX]
    exact hkernelBound x hxE
  have hRecip := reciprocalSquare_outer_integrable_and_integral
    (c := c) (a := a) ha
  have hRecipInt : IntegrableOn R E volume := by
    rw [hE]
    simpa [R] using hRecip.1
  have hRecipValue : ∫ x in E, R x ∂volume = 2 * a⁻¹ := by
    rw [hE]
    simpa [R] using hRecip.2
  have hGint : IntegrableOn G E volume := by
    change IntegrableOn (fun x => C * R x) E volume
    exact hRecipInt.const_mul C
  have hboundRestrict : ∀ᵐ x ∂(volume.restrict E),
      ‖(T F : ℝ → ℂ) x‖ ≤ G x := by
    exact (ae_restrict_iff' hEmeas).2 hboundAE
  have hTnormAES : AEStronglyMeasurable
      (fun x : ℝ => ‖(T F : Lp ℂ 2 volume) x‖) (volume.restrict E) :=
    (Lp.aestronglyMeasurable (T F)).norm.restrict
  have hboundNormRestrict : ∀ᵐ x ∂(volume.restrict E),
      ‖‖(T F : Lp ℂ 2 volume) x‖‖ ≤ G x := by
    filter_upwards [hboundRestrict] with x hx
    rw [Real.norm_of_nonneg (norm_nonneg ((T F : Lp ℂ 2 volume) x))]
    exact hx
  have hTnormInt : IntegrableOn
      (fun x : ℝ => ‖(T F : Lp ℂ 2 volume) x‖) E volume := by
    exact hGint.mono' hTnormAES hboundNormRestrict
  refine ⟨hTnormInt, ?_⟩
  calc
    ∫ x in E, ‖(T F : Lp ℂ 2 volume) x‖ ∂volume ≤
        ∫ x in E, G x ∂volume := integral_mono_ae hTnormInt hGint hboundRestrict
    _ = C * (2 * a⁻¹) := by
      change ∫ x in E, C * R x ∂volume = _
      rw [integral_const_mul, hRecipValue]
    _ = (8 / 9) * B * mass := by
      dsimp [C, a]
      field_simp
      <;> ring
    _ ≤ B * ∫ x, ‖u x‖ ∂volume := by
      dsimp [mass]
      nlinarith [mul_nonneg hB hmassNonneg]

/-- The adjoint convolution kernel `star (K (-x))` inherits the same
integrability and derivative constants as `K`. This records the exact
adjoint-kernel fact used by the proof of `lj:kernel-cz`. -/
theorem convolutionAdjointKernel_data
    (K : ℝ → ℂ) (hKint : Integrable K volume)
    (hKdiff : ∀ x, DifferentiableAt ℝ K x) {B : ℝ}
    (hderiv : ∀ x ≠ 0, ‖deriv K x‖ ≤ B / |x| ^ 2) :
    let Kstar : ℝ → ℂ := fun x => star (K (-x))
    Integrable Kstar volume ∧
      (∀ x, DifferentiableAt ℝ Kstar x) ∧
      (∀ x ≠ 0, ‖deriv Kstar x‖ ≤ B / |x| ^ 2) := by
  dsimp
  have hKmem : MemLp K 1 volume := memLp_one_iff_integrable.mpr hKint
  have hKnegMem : MemLp (fun x : ℝ => K (-x)) 1 volume :=
    hKmem.comp_measurePreserving (Measure.measurePreserving_neg volume)
  have hKstarMem : MemLp (fun x : ℝ => star (K (-x))) 1 volume := hKnegMem.star
  have hKstarInt : Integrable (fun x : ℝ => star (K (-x))) volume :=
    memLp_one_iff_integrable.mp hKstarMem
  have hKstarDiff : ∀ x, DifferentiableAt ℝ (fun y : ℝ => star (K (-y))) x := by
    intro x
    exact (hKdiff (-x)).comp x (hasDerivAt_neg x).differentiableAt |>.star
  refine ⟨hKstarInt, hKstarDiff, ?_⟩
  intro x hx
  have hchain : deriv (fun y : ℝ => star (K (-y))) x = star (-deriv K (-x)) := by
    rw [deriv.star, deriv_comp_neg]
  change ‖deriv (fun y : ℝ => star (K (-y))) x‖ ≤ B / |x| ^ 2
  calc
    ‖deriv (fun y : ℝ => star (K (-y))) x‖ =
        ‖star (-deriv K (-x))‖ := congrArg norm hchain
    _ = ‖deriv K (-x)‖ := by simp
    _ ≤ B / |x| ^ 2 := by simpa [abs_neg] using hderiv (-x) (neg_ne_zero.mpr hx)

/-- The reflected-conjugate kernel has the exact off-support estimate used
for the adjoint in `lj:kernel-cz`. -/
theorem convolutionAdjointKernel_weakCZOffSupportBound
    (K : ℝ → ℂ) (hKint : Integrable K volume)
    (hKdiff : ∀ x, DifferentiableAt ℝ K x) {B : ℝ}
    (hderiv : ∀ x ≠ 0, ‖deriv K x‖ ≤ B / |x| ^ 2) :
    ∃ hKstarInt : Integrable (fun x : ℝ => star (K (-x))) volume,
      weakCZOffSupportBound
        (kernelConvolutionL2Operator (fun x => star (K (-x))) hKstarInt) B := by
  have hdata := convolutionAdjointKernel_data K hKint hKdiff hderiv
  dsimp at hdata
  obtain ⟨hKstarInt, hKstarDiff, hKstarDeriv⟩ := hdata
  have hKstarCont : Continuous (fun x : ℝ => star (K (-x))) :=
    continuous_iff_continuousAt.mpr (fun x => (hKstarDiff x).continuousAt)
  exact ⟨hKstarInt,
    kernelConvolutionL2Operator_weakCZOffSupportBound
      (fun x => star (K (-x))) hKstarCont hKstarDiff hKstarInt hKstarDeriv⟩

private theorem kernelDensity_complexMeasureFourier_eq_integral
    (K : ℝ → ℂ) (hKcont : Continuous K) (hKint : Integrable K volume)
    (ξ : ℝ) :
    complexMeasureFourier (volume.withDensityᵥ K) ξ =
      ∫ y, K y * (Real.fourierChar (-(y * ξ)) : ℂ) ∂volume := by
  let phase : ℝ → ℂ := fun y => (Real.fourierChar (-(y * ξ)) : ℂ)
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact kernelVariationMeasure_isFinite hKint
  letI : IsFiniteMeasure (kernelVariationMeasure K) :=
    kernelVariationMeasure_isFinite hKint
  have hphaseSm : StronglyMeasurable phase := by
    dsimp [phase]
    fun_prop
  have hphaseBound : ∀ y, ‖phase y‖ ≤ 1 := by
    intro y
    simp [phase]
  have hphaseMem : MemLp phase 1 (kernelVariationMeasure K) :=
    MemLp.of_bound hphaseSm.aestronglyMeasurable 1
      (ae_of_all _ hphaseBound)
  change ∫ᵛ y, phase y ∂[ContinuousLinearMap.mul ℝ ℂ; μ] = _
  simpa [phase, μ] using
    (kernelDensity_vectorIntegral_eq_function K hKcont hKint phase hphaseMem)

private theorem kernelDensity_complexMeasureFourier_reflectedConj
    (K : ℝ → ℂ) (hKcont : Continuous K) (hKint : Integrable K volume)
    (Kstar : ℝ → ℂ) (hKstarcont : Continuous Kstar)
    (hKstarint : Integrable Kstar volume)
    (hKstar : ∀ x, Kstar x = star (K (-x))) (ξ : ℝ) :
    complexMeasureFourier (volume.withDensityᵥ Kstar) ξ =
      star (complexMeasureFourier (volume.withDensityᵥ K) ξ) := by
  let phase : ℝ → ℂ := fun y => (Real.fourierChar (-(y * ξ)) : ℂ)
  have hphaseNeg (y : ℝ) : phase (-y) = star (phase y) := by
    dsimp [phase]
    rw [Real.fourierChar_apply, Real.fourierChar_apply]
    change Complex.exp
        (↑(2 * Real.pi * (-((-y) * ξ))) * Complex.I) =
      star (Complex.exp (↑(2 * Real.pi * (-(y * ξ))) * Complex.I))
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_neg, map_ofNat]
    push_cast
    ring
  rw [kernelDensity_complexMeasureFourier_eq_integral Kstar hKstarcont hKstarint ξ,
    kernelDensity_complexMeasureFourier_eq_integral K hKcont hKint ξ]
  calc
    ∫ y, Kstar y * phase y ∂volume =
        ∫ y, Kstar (-y) * phase (-y) ∂volume := by
      have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
      simpa only [neg_neg] using hmp.integral_comp
        (Homeomorph.neg ℝ).measurableEmbedding
        (fun y : ℝ => Kstar (-y) * phase (-y))
    _ = ∫ y, star (K y) * star (phase y) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hKstar (-y), hphaseNeg y]
      simp only [neg_neg]
    _ = star (∫ y, K y * phase y ∂volume) := by
      have hstarIntegral :
          (∫ y, star (K y * phase y) ∂volume) =
            star (∫ y, K y * phase y ∂volume) := by
        simpa [Complex.star_def] using
          (integral_conj (f := fun y : ℝ => K y * phase y))
      rw [← hstarIntegral]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [star_mul]
      exact mul_comm _ _

private theorem inner_realLpMultiplier_adjoint_pair
    (M Mstar : Lp ℂ ∞ (volume : Measure ℝ))
    (hMstar : (Mstar : ℝ → ℂ) =ᵐ[volume]
      fun ξ => star ((M : ℝ → ℂ) ξ))
    (F G : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ (realLpMultiplier M F) G =
      inner ℂ F (realLpMultiplier Mstar G) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_realLpMultiplier M F,
      coeFn_realLpMultiplier Mstar G, hMstar] with ξ hMF hMstarG hstar
  rw [hMF, hMstarG, hstar]
  change inner ℂ ((M : ℝ → ℂ) ξ * F ξ) (G ξ) =
    inner ℂ (F ξ) (star ((M : ℝ → ℂ) ξ) * G ξ)
  rw [← smul_eq_mul, ← smul_eq_mul]
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]

private theorem l2_real_inner_eq_re_complex_inner
    (F G : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℝ F G = RCLike.re (inner ℂ F G) := by
  letI : InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  have hinnerInt : Integrable
      (fun x : ℝ => inner ℂ (F x) (G x)) volume :=
    MeasureTheory.L2.integrable_inner F G
  calc
    inner ℝ F G = ∫ x, inner ℝ (F x) (G x) ∂volume :=
      MeasureTheory.L2.inner_def _ _
    _ = ∫ x, RCLike.re (inner ℂ (F x) (G x)) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact real_inner_eq_re_inner ℂ (F x) (G x)
    _ = RCLike.re (∫ x, inner ℂ (F x) (G x) ∂volume) :=
      integral_re hinnerInt
    _ = RCLike.re (inner ℂ F G) := by rw [MeasureTheory.L2.inner_def]

private theorem kernelConvolutionL2Operator_adjointPairing
    (K Kstar : ℝ → ℂ) (hKcont : Continuous K)
    (hKint : Integrable K volume) (hKstarcont : Continuous Kstar)
    (hKstarint : Integrable Kstar volume)
    (hKstar : ∀ x, Kstar x = star (K (-x))) :
    ∀ (F G : Lp ℂ 2 (volume : Measure ℝ)),
      (∫ x, inner ℝ
        ((kernelConvolutionL2Operator K hKint F : Lp ℂ 2 volume) x)
        (G x) ∂volume) =
      ∫ x, inner ℝ (F x)
        ((kernelConvolutionL2Operator Kstar hKstarint G : Lp ℂ 2 volume) x)
        ∂volume := by
  let μ : ComplexMeasure ℝ := volume.withDensityᵥ K
  let μstar : ComplexMeasure ℝ := volume.withDensityᵥ Kstar
  have hvar : μ.variation = kernelVariationMeasure K := by
    dsimp [μ, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKint]
    congr 1
  have hvarstar : μstar.variation = kernelVariationMeasure Kstar := by
    dsimp [μstar, kernelVariationMeasure]
    rw [Measure.variation_withDensityᵥ hKstarint]
    congr 1
  letI : IsFiniteMeasure μ.variation := by
    rw [hvar]
    exact kernelVariationMeasure_isFinite hKint
  letI : IsFiniteMeasure μstar.variation := by
    rw [hvarstar]
    exact kernelVariationMeasure_isFinite hKstarint
  letI : IsFiniteMeasure (kernelVariationMeasure K) :=
    kernelVariationMeasure_isFinite hKint
  letI : IsFiniteMeasure (kernelVariationMeasure Kstar) :=
    kernelVariationMeasure_isFinite hKstarint
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let T : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp ℂ 2 (volume : Measure ℝ) := kernelConvolutionL2Operator K hKint
  let S : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp ℂ 2 (volume : Measure ℝ) := kernelConvolutionL2Operator Kstar hKstarint
  have hfourierT (F : Lp ℂ 2 (volume : Measure ℝ)) :
      realFourierTransformL2 (T F) =
        realLpMultiplier (complexMeasureFourierLpTop μ)
          (realFourierTransformL2 F) := by
    change realFourierTransformL2 (lpComplexMeasureConvolution 2 μ F) = _
    exact fourier_lpComplexMeasureConvolution μ F
  have hfourierS (G : Lp ℂ 2 (volume : Measure ℝ)) :
      realFourierTransformL2 (S G) =
        realLpMultiplier (complexMeasureFourierLpTop μstar)
          (realFourierTransformL2 G) := by
    change realFourierTransformL2 (lpComplexMeasureConvolution 2 μstar G) = _
    exact fourier_lpComplexMeasureConvolution μstar G
  have hmultiplier :
      (complexMeasureFourierLpTop μstar : ℝ → ℂ) =ᵐ[volume]
        fun ξ => star ((complexMeasureFourierLpTop μ : ℝ → ℂ) ξ) := by
    filter_upwards [coeFn_complexMeasureFourierLpTop μstar,
      coeFn_complexMeasureFourierLpTop μ] with ξ hstar h
    rw [hstar, h]
    exact kernelDensity_complexMeasureFourier_reflectedConj
      K hKcont hKint Kstar hKstarcont hKstarint hKstar ξ
  have hcomplex (F G : Lp ℂ 2 (volume : Measure ℝ)) :
      inner ℂ (T F) G = inner ℂ F (S G) := by
    calc
      inner ℂ (T F) G =
          inner ℂ (realFourierTransformL2 (T F))
            (realFourierTransformL2 G) :=
        (realFourierTransformL2.inner_map_map (T F) G).symm
      _ = inner ℂ
          (realLpMultiplier (complexMeasureFourierLpTop μ)
            (realFourierTransformL2 F)) (realFourierTransformL2 G) := by
          rw [hfourierT]
      _ = inner ℂ (realFourierTransformL2 F)
          (realLpMultiplier (complexMeasureFourierLpTop μstar)
            (realFourierTransformL2 G)) :=
          inner_realLpMultiplier_adjoint_pair _ _ hmultiplier _ _
      _ = inner ℂ (realFourierTransformL2 F)
          (realFourierTransformL2 (S G)) := by rw [← hfourierS]
      _ = inner ℂ F (S G) := realFourierTransformL2.inner_map_map F (S G)
  letI : InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  intro F G
  calc
    (∫ x, inner ℝ ((T F : Lp ℂ 2 volume) x) (G x) ∂volume) =
        inner ℝ (T F) G := (MeasureTheory.L2.inner_def _ _).symm
    _ = RCLike.re (inner ℂ (T F) G) :=
      l2_real_inner_eq_re_complex_inner (T F) G
    _ = RCLike.re (inner ℂ F (S G)) := congrArg RCLike.re (hcomplex F G)
    _ = inner ℝ F (S G) :=
      (l2_real_inner_eq_re_complex_inner F (S G)).symm
    _ = ∫ x, inner ℝ (F x) ((S G : Lp ℂ 2 volume) x) ∂volume :=
      MeasureTheory.L2.inner_def _ _

private theorem kernelConvolutionL2Operator_reflected_isAdjoint
    (K Kstar : ℝ → ℂ) (hKcont : Continuous K)
    (hKint : Integrable K volume) (hKstarcont : Continuous Kstar)
    (hKstarint : Integrable Kstar volume)
    (hKstar : ∀ x, Kstar x = star (K (-x))) :
    let T : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ]
        Lp ℂ 2 (volume : Measure ℝ) := kernelConvolutionL2Operator K hKint
    let S : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ]
        Lp ℂ 2 (volume : Measure ℝ) := kernelConvolutionL2Operator Kstar hKstarint
    S = T.adjoint := by
  let T : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp ℂ 2 (volume : Measure ℝ) := kernelConvolutionL2Operator K hKint
  let S : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp ℂ 2 (volume : Measure ℝ) := kernelConvolutionL2Operator Kstar hKstarint
  letI : InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  have hpair := kernelConvolutionL2Operator_adjointPairing K Kstar
    hKcont hKint hKstarcont hKstarint hKstar
  change S = T.adjoint
  apply ContinuousLinearMap.ext
  intro G
  apply ext_inner_left ℝ
  intro F
  calc
    inner ℝ F (S G) =
        ∫ x, inner ℝ (F x) ((S G : Lp ℂ 2 volume) x) ∂volume :=
      (MeasureTheory.L2.inner_def _ _).symm
    _ = ∫ x, inner ℝ ((T F : Lp ℂ 2 volume) x) (G x) ∂volume :=
      (hpair F G).symm
    _ = inner ℝ (T F) G := MeasureTheory.L2.inner_def _ _
    _ = inner ℝ F (T.adjoint G) :=
      (ContinuousLinearMap.adjoint_inner_right T F G).symm

/-- The exact real-line smooth-kernel criterion `lj:kernel-cz`.  The operator
in the hypothesis is the checked `L²` convolution operator associated with
the kernel density; its action agrees with ordinary Lebesgue convolution on
smooth compactly supported inputs.  The conclusion includes the strong
`Lᵖ` extension, its source constant, and agreement with the given `L²`
operator on `Lᵖ ∩ L²`. -/
theorem convolutionCZBound
    (K : ℝ → ℂ) (hKsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) K)
    (hKint : Integrable K volume) {A B : ℝ}
    (hT : ‖kernelConvolutionL2Operator K hKint‖ ≤ A)
    (hderiv : ∀ x ≠ 0, ‖deriv K x‖ ≤ B / |x| ^ 2)
    (p : ℝ) (hp₁ : 1 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
    ∃ U : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
        Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      (∀ f, ‖U f‖ ≤ weakTypeFromOffSupportStrongConstant p A B * ‖f‖) ∧
      (∀ (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
        (hf₂ : MemLp (f : ℝ → ℂ) 2 volume),
        (U f : ℝ → ℂ) =ᵐ[volume]
          (kernelConvolutionL2Operator K hKint
            (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ)) := by
  let hKcont : Continuous K := hKsmooth.continuous
  have hKdiff : ∀ x, DifferentiableAt ℝ K x := by
    intro x
    exact (hKsmooth.differentiable (by norm_num)).differentiableAt
  let Kstar : ℝ → ℂ := fun x => star (K (-x))
  have hstarData := convolutionAdjointKernel_data K hKint hKdiff hderiv
  dsimp [Kstar] at hstarData
  obtain ⟨hKstarint, hKstardiff, hKstarderiv⟩ := hstarData
  have hKstarcont : Continuous Kstar :=
    continuous_iff_continuousAt.mpr (fun x => (hKstardiff x).continuousAt)
  let T : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp ℂ 2 (volume : Measure ℝ) := kernelConvolutionL2Operator K hKint
  let S : Lp ℂ 2 (volume : Measure ℝ) →L[ℝ]
      Lp ℂ 2 (volume : Measure ℝ) := kernelConvolutionL2Operator Kstar hKstarint
  have hOffT : weakCZOffSupportBound T B := by
    simpa [T] using kernelConvolutionL2Operator_weakCZOffSupportBound
      K hKcont hKdiff hKint hderiv
  have hOffS : weakCZOffSupportBound S B := by
    simpa [S] using kernelConvolutionL2Operator_weakCZOffSupportBound
      Kstar hKstarcont hKstardiff hKstarint hKstarderiv
  have hPair := kernelConvolutionL2Operator_adjointPairing
    K Kstar hKcont hKint hKstarcont hKstarint (by
      intro x
      rfl)
  letI : InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure ℝ)) :=
    MeasureTheory.L2.innerProductSpace
  have hSadj : S = T.adjoint := by
    simpa [T, S] using kernelConvolutionL2Operator_reflected_isAdjoint
      K Kstar hKcont hKint hKstarcont hKstarint (by
        intro x
        rfl)
  have hSnorm : ‖S‖ ≤ A := by
    calc
      ‖S‖ = ‖T.adjoint‖ := congrArg norm hSadj
      _ = ‖T‖ := ContinuousLinearMap.adjoint.norm_map T
      _ ≤ A := hT
  exact weakTypeFromOffSupport_extension_agrees_on_Lp_inter_L2
    T hT hOffT S hPair hSnorm hOffS p hp₁

/-- Uniform finite-family form of `lj:kernel-cz`: each kernel in the family
has the same `Lᵖ` bound whenever it has the common `L²` and derivative
constants. -/
theorem convolutionCZBound_finiteFamily
    {ι : Type*} [Fintype ι] (K : ι → ℝ → ℂ)
    (hKsmooth : ∀ i : ι, ContDiff ℝ (↑(⊤ : ℕ∞)) (K i))
    (hKint : ∀ i : ι, Integrable (K i) volume) {A B p : ℝ}
    (hT : ∀ i : ι, ‖kernelConvolutionL2Operator (K i) (hKint i)‖ ≤ A)
    (hderiv : ∀ (i : ι) x, x ≠ 0 →
      ‖deriv (K i) x‖ ≤ B / |x| ^ 2)
    (hp₁ : 1 < p) :
    ∀ i : ι, letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr hp₁.le⟩
      ∃ U : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →L[ℝ]
          Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
        (∀ f, ‖U f‖ ≤ weakTypeFromOffSupportStrongConstant p A B * ‖f‖) ∧
        (∀ (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
          (hf₂ : MemLp (f : ℝ → ℂ) 2 volume),
          (U f : ℝ → ℂ) =ᵐ[volume]
            (kernelConvolutionL2Operator (K i) (hKint i)
              (hf₂.toLp (f : ℝ → ℂ)) : ℝ → ℂ)) := by
  intro i
  obtain ⟨U, hbound, hagree⟩ := convolutionCZBound
    (K i) (hKsmooth i) (hKint i) (hT i) (hderiv i) p hp₁
  exact ⟨U, hbound, hagree⟩

#print axioms convolution_kernel_derivative_constant_nonneg
#print axioms kernelConvolutionL2Operator_weakCZOffSupportBound
#print axioms kernelConvolutionL2Operator_reflected_isAdjoint
#print axioms convolutionCZBound
#print axioms convolutionCZBound_finiteFamily

end

end FractionalPrimes.Literature.JSW

end
