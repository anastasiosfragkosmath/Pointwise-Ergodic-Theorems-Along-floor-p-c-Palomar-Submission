module

public import FractionalPrimes.Literature.Multiplier.Data
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# First pointwise kernel estimate for `lp:dyadic-kernel`

This module isolates the low-frequency pointwise estimate for the real
inverse-transform variable. The full decay estimate is to be obtained by
combining this compact-support bound with two integrations by parts.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open Set MeasureTheory
open Filter
open scoped ContDiff FourierTransform

noncomputable section

/-- The dyadic scale `t_j = 2^{-j}`. -/
def dyadicScale (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ j

theorem dyadicScale_pos (j : ℕ) : 0 < dyadicScale j := by
  unfold dyadicScale
  positivity

theorem dyadicScale_le_one (j : ℕ) : dyadicScale j ≤ 1 := by
  unfold dyadicScale
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- The exact annular cutoff `ψ(ξ/t_j) - ψ(2ξ/t_j)`. -/
def dyadicCutoffFactor (j : ℕ) (ξ : ℝ) : ℝ :=
  ψ (ξ / dyadicScale j) - ψ ((2 * ξ) / dyadicScale j)

/-- The exact dyadic symbol piece `m_j` from the approved blueprint. -/
def dyadicSymbolPiece {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D)
    (j : ℕ) (ξ : ℝ) : ℂ :=
  m ξ * (dyadicCutoffFactor j ξ : ℂ)

/-- The open part of the fundamental interval away from the singular frequency. -/
def dyadicOpenPunctured : Set ℝ :=
  Set.Ioo (-(1 / 2 : ℝ)) 0 ∪ Set.Ioo 0 (1 / 2 : ℝ)

theorem dyadicOpenPunctured_subset_puncturedTorusLift :
    dyadicOpenPunctured ⊆ puncturedTorusLift := by
  intro ξ hξ
  change ξ ∉ Set.range (fun n : ℤ => (n : ℝ))
  intro hξint
  rcases hξint with ⟨z, hz⟩
  rcases hξ with hξ | hξ
  · have hleft : -(1 / 2 : ℝ) < ξ := hξ.1
    have hright : ξ < 0 := hξ.2
    have hleft' : (-1 : ℝ) < ξ := by linarith
    have hzleft : (-1 : ℤ) < z := by
      apply_mod_cast (by simpa [hz] using hleft' : (-1 : ℝ) < (z : ℝ))
    have hzright : z < 0 := by
      apply_mod_cast (by simpa [hz] using hright : (z : ℝ) < 0)
    omega
  · have hleft : 0 < ξ := hξ.1
    have hright : ξ < 1 / 2 := hξ.2
    have hright' : ξ < (1 : ℝ) := by linarith
    have hzleft : 0 < z := by
      apply_mod_cast (by simpa [hz] using hleft : 0 < (z : ℝ))
    have hzright : z < 1 := by
      apply_mod_cast (by simpa [hz] using hright' : (z : ℝ) < 1)
    omega

theorem isOpen_dyadicOpenPunctured : IsOpen dyadicOpenPunctured :=
  isOpen_Ioo.union isOpen_Ioo

theorem dyadicCutoffFactor_contDiff (j : ℕ) :
    ContDiff ℝ 2 (dyadicCutoffFactor j) := by
  have hψ : ContDiff ℝ 2 ψ := ψ_contDiff.of_le (by norm_num)
  have hfirst : ContDiff ℝ 2 (fun ξ : ℝ => ξ / dyadicScale j) := by fun_prop
  have hsecond : ContDiff ℝ 2 (fun ξ : ℝ => (2 * ξ) / dyadicScale j) := by
    fun_prop
  change ContDiff ℝ 2 (fun ξ : ℝ =>
    ψ (ξ / dyadicScale j) - ψ ((2 * ξ) / dyadicScale j))
  exact (hψ.comp hfirst).sub (hψ.comp hsecond)

theorem dyadicCutoffFactor_hasDerivAt (j : ℕ) (ξ : ℝ) :
    HasDerivAt (dyadicCutoffFactor j)
      (deriv ψ (ξ / dyadicScale j) * (1 / dyadicScale j) -
        deriv ψ ((2 * ξ) / dyadicScale j) * (2 / dyadicScale j)) ξ := by
  have hfirst : HasDerivAt (fun y : ℝ => y / dyadicScale j)
      (1 / dyadicScale j) ξ := by
    simpa using (hasDerivAt_id ξ).div_const (dyadicScale j)
  have hsecond : HasDerivAt (fun y : ℝ => (2 * y) / dyadicScale j)
      (2 / dyadicScale j) ξ := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_id ξ).mul_const (2 / dyadicScale j)
  have hψfirstAt : ContDiffAt ℝ 1 ψ (ξ / dyadicScale j) :=
    (ψ_contDiff.contDiffAt (x := ξ / dyadicScale j)).of_le (by norm_num)
  have hψfirst : HasDerivAt ψ (deriv ψ (ξ / dyadicScale j))
      (ξ / dyadicScale j) := by
    exact hψfirstAt.differentiableAt_one.hasDerivAt
  have hψsecondAt : ContDiffAt ℝ 1 ψ ((2 * ξ) / dyadicScale j) :=
    (ψ_contDiff.contDiffAt (x := (2 * ξ) / dyadicScale j)).of_le (by norm_num)
  have hψsecond : HasDerivAt ψ
      (deriv ψ ((2 * ξ) / dyadicScale j)) ((2 * ξ) / dyadicScale j) := by
    exact hψsecondAt.differentiableAt_one.hasDerivAt
  have hcompFirst := hψfirst.comp ξ hfirst
  have hcompSecond := hψsecond.comp ξ hsecond
  have hsub := hcompFirst.sub hcompSecond
  change HasDerivAt (fun y : ℝ =>
    ψ (y / dyadicScale j) - ψ ((2 * y) / dyadicScale j))
    (deriv ψ (ξ / dyadicScale j) * (1 / dyadicScale j) -
      deriv ψ ((2 * ξ) / dyadicScale j) * (2 / dyadicScale j)) ξ
  exact hsub

theorem deriv_dyadicCutoffFactor (j : ℕ) (ξ : ℝ) :
    deriv (dyadicCutoffFactor j) ξ =
      deriv ψ (ξ / dyadicScale j) * (1 / dyadicScale j) -
        deriv ψ ((2 * ξ) / dyadicScale j) * (2 / dyadicScale j) :=
  (dyadicCutoffFactor_hasDerivAt j ξ).deriv

theorem norm_deriv_dyadicCutoffFactor_le (j : ℕ) (ξ : ℝ) :
    ‖deriv (dyadicCutoffFactor j) ξ‖ ≤ 3 * B / dyadicScale j := by
  have ht := dyadicScale_pos j
  have hB₁ : ψDerivSup ≤ B := by
    unfold B
    linarith [ψSecondDerivSup_nonneg]
  have hderiv₁ : ‖deriv ψ (ξ / dyadicScale j)‖ ≤ B :=
    (norm_deriv_ψ_le_sup _).trans hB₁
  have hderiv₂ : ‖deriv ψ ((2 * ξ) / dyadicScale j)‖ ≤ B :=
    (norm_deriv_ψ_le_sup _).trans hB₁
  have hscale₁ : ‖(1 / dyadicScale j : ℝ)‖ = 1 / dyadicScale j := by
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr ht)]
  have hscale₂ : ‖(2 / dyadicScale j : ℝ)‖ = 2 / dyadicScale j := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) ht)]
  rw [deriv_dyadicCutoffFactor]
  calc
    ‖deriv ψ (ξ / dyadicScale j) * (1 / dyadicScale j) -
        deriv ψ ((2 * ξ) / dyadicScale j) * (2 / dyadicScale j)‖ ≤
        ‖deriv ψ (ξ / dyadicScale j) * (1 / dyadicScale j)‖ +
          ‖deriv ψ ((2 * ξ) / dyadicScale j) * (2 / dyadicScale j)‖ := norm_sub_le _ _
    _ = ‖deriv ψ (ξ / dyadicScale j)‖ * (1 / dyadicScale j) +
        ‖deriv ψ ((2 * ξ) / dyadicScale j)‖ * (2 / dyadicScale j) := by
      rw [norm_mul, norm_mul, hscale₁, hscale₂]
    _ ≤ B * (1 / dyadicScale j) + B * (2 / dyadicScale j) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hderiv₁ (by positivity))
        (mul_le_mul_of_nonneg_right hderiv₂ (by positivity))
    _ = 3 * B / dyadicScale j := by ring

theorem iteratedDeriv_two_dyadicCutoffFactor (j : ℕ) (ξ : ℝ) :
    iteratedDeriv 2 (dyadicCutoffFactor j) ξ =
      iteratedDeriv 2 ψ (ξ / dyadicScale j) *
          (1 / dyadicScale j) * (1 / dyadicScale j) -
        iteratedDeriv 2 ψ ((2 * ξ) / dyadicScale j) *
          (2 / dyadicScale j) * (2 / dyadicScale j) := by
  have ht := dyadicScale_pos j
  have hfirst : HasDerivAt (fun y : ℝ => y / dyadicScale j)
      (1 / dyadicScale j) ξ := by
    simpa using (hasDerivAt_id ξ).div_const (dyadicScale j)
  have hsecond : HasDerivAt (fun y : ℝ => (2 * y) / dyadicScale j)
      (2 / dyadicScale j) ξ := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_id ξ).mul_const (2 / dyadicScale j)
  have hψ'cont : ContDiff ℝ 1 (deriv ψ) := by
    exact (contDiff_infty_iff_deriv.mp ψ_contDiff).2.of_le (by norm_num)
  have hψfirstAt : ContDiffAt ℝ 1 (deriv ψ) (ξ / dyadicScale j) := by
    exact hψ'cont.contDiffAt
  have hψfirst : HasDerivAt (deriv ψ)
      (iteratedDeriv 2 ψ (ξ / dyadicScale j)) (ξ / dyadicScale j) := by
    have h := hψfirstAt.differentiableAt_one.hasDerivAt
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using h
  have hψsecondAt : ContDiffAt ℝ 1 (deriv ψ) ((2 * ξ) / dyadicScale j) := by
    exact hψ'cont.contDiffAt
  have hψsecond : HasDerivAt (deriv ψ)
      (iteratedDeriv 2 ψ ((2 * ξ) / dyadicScale j)) ((2 * ξ) / dyadicScale j) := by
    have h := hψsecondAt.differentiableAt_one.hasDerivAt
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using h
  have htermFirst := (hψfirst.comp ξ hfirst).const_mul (1 / dyadicScale j)
  have htermSecond := (hψsecond.comp ξ hsecond).const_mul (2 / dyadicScale j)
  have hsub := htermFirst.sub htermSecond
  have hfun : deriv (dyadicCutoffFactor j) =
      ((fun y : ℝ => (1 / dyadicScale j) *
          (deriv ψ ∘ fun z : ℝ => z / dyadicScale j) y) -
        (fun y : ℝ => (2 / dyadicScale j) *
          (deriv ψ ∘ fun z : ℝ => (2 * z) / dyadicScale j) y)) := by
    funext y
    rw [deriv_dyadicCutoffFactor]
    simp only [Function.comp_apply, Pi.sub_apply]
    have harg₁ : y / dyadicScale j = (dyadicScale j)⁻¹ * y := by
      rw [div_eq_mul_inv, mul_comm]
    have harg₂ : (2 * y) / dyadicScale j =
        (dyadicScale j)⁻¹ * y * 2 := by
      rw [div_eq_mul_inv]
      ring
    rw [harg₁, harg₂]
    ring_nf
  have hderiv := hsub.deriv
  have hresult : deriv (deriv (dyadicCutoffFactor j)) ξ =
      iteratedDeriv 2 ψ (ξ / dyadicScale j) * (1 / dyadicScale j) *
          (1 / dyadicScale j) -
        iteratedDeriv 2 ψ ((2 * ξ) / dyadicScale j) * (2 / dyadicScale j) *
          (2 / dyadicScale j) := by
    rw [hfun]
    convert hderiv using 1 <;> ring_nf
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using hresult

theorem norm_iteratedDeriv_two_dyadicCutoffFactor_le (j : ℕ) (ξ : ℝ) :
    ‖iteratedDeriv 2 (dyadicCutoffFactor j) ξ‖ ≤
      5 * B / dyadicScale j ^ 2 := by
  have ht := dyadicScale_pos j
  have hB : ψSecondDerivSup ≤ B := by
    unfold B
    linarith [ψDerivSup_nonneg]
  have hderiv₁ : ‖iteratedDeriv 2 ψ (ξ / dyadicScale j)‖ ≤ B :=
    (norm_iteratedDeriv_two_ψ_le_sup _).trans hB
  have hderiv₂ : ‖iteratedDeriv 2 ψ ((2 * ξ) / dyadicScale j)‖ ≤ B :=
    (norm_iteratedDeriv_two_ψ_le_sup _).trans hB
  have hscale₁ : 0 ≤ (1 / dyadicScale j) * (1 / dyadicScale j) :=
    mul_nonneg (le_of_lt (one_div_pos.mpr ht)) (le_of_lt (one_div_pos.mpr ht))
  have hscale₂ : 0 ≤ (2 / dyadicScale j) * (2 / dyadicScale j) :=
    mul_nonneg (le_of_lt (div_pos (by norm_num) ht))
      (le_of_lt (div_pos (by norm_num) ht))
  have hnormScale₁ : ‖(1 / dyadicScale j : ℝ)‖ = 1 / dyadicScale j := by
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by norm_num), abs_of_pos ht]
  have hnormScale₂ : ‖(2 / dyadicScale j : ℝ)‖ = 2 / dyadicScale j := by
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by norm_num), abs_of_pos ht]
  have hnormTerm₁ :
      ‖iteratedDeriv 2 ψ (ξ / dyadicScale j) *
          (1 / dyadicScale j) * (1 / dyadicScale j)‖ =
        ‖iteratedDeriv 2 ψ (ξ / dyadicScale j)‖ *
          ((1 / dyadicScale j) * (1 / dyadicScale j)) := by
    calc
      _ = ‖iteratedDeriv 2 ψ (ξ / dyadicScale j)‖ *
          ‖(1 / dyadicScale j : ℝ)‖ * ‖(1 / dyadicScale j : ℝ)‖ := by
        rw [norm_mul, norm_mul]
      _ = ‖iteratedDeriv 2 ψ (ξ / dyadicScale j)‖ *
          ((1 / dyadicScale j) * (1 / dyadicScale j)) := by
        rw [hnormScale₁]
        ring
  have hnormTerm₂ :
      ‖iteratedDeriv 2 ψ ((2 * ξ) / dyadicScale j) *
          (2 / dyadicScale j) * (2 / dyadicScale j)‖ =
        ‖iteratedDeriv 2 ψ ((2 * ξ) / dyadicScale j)‖ *
          ((2 / dyadicScale j) * (2 / dyadicScale j)) := by
    calc
      _ = ‖iteratedDeriv 2 ψ ((2 * ξ) / dyadicScale j)‖ *
          ‖(2 / dyadicScale j : ℝ)‖ * ‖(2 / dyadicScale j : ℝ)‖ := by
        rw [norm_mul, norm_mul]
      _ = ‖iteratedDeriv 2 ψ ((2 * ξ) / dyadicScale j)‖ *
          ((2 / dyadicScale j) * (2 / dyadicScale j)) := by
        rw [hnormScale₂]
        ring
  have hcoeff₁ : (1 / dyadicScale j) * (1 / dyadicScale j) =
      1 / dyadicScale j ^ 2 := by field_simp [ne_of_gt ht]
  have hcoeff₂ : (2 / dyadicScale j) * (2 / dyadicScale j) =
      4 / dyadicScale j ^ 2 := by field_simp [ne_of_gt ht]; norm_num
  rw [iteratedDeriv_two_dyadicCutoffFactor]
  calc
    ‖iteratedDeriv 2 ψ (ξ / dyadicScale j) *
        (1 / dyadicScale j) * (1 / dyadicScale j) -
      iteratedDeriv 2 ψ ((2 * ξ) / dyadicScale j) *
        (2 / dyadicScale j) * (2 / dyadicScale j)‖ ≤
        ‖iteratedDeriv 2 ψ (ξ / dyadicScale j)‖ *
          ((1 / dyadicScale j) * (1 / dyadicScale j)) +
        ‖iteratedDeriv 2 ψ ((2 * ξ) / dyadicScale j)‖ *
          ((2 / dyadicScale j) * (2 / dyadicScale j)) := by
      calc
        _ ≤ ‖iteratedDeriv 2 ψ (ξ / dyadicScale j) *
              (1 / dyadicScale j) * (1 / dyadicScale j)‖ +
            ‖iteratedDeriv 2 ψ ((2 * ξ) / dyadicScale j) *
              (2 / dyadicScale j) * (2 / dyadicScale j)‖ := norm_sub_le _ _
        _ = _ := by rw [hnormTerm₁, hnormTerm₂]
    _ ≤ B * ((1 / dyadicScale j) * (1 / dyadicScale j)) +
        B * ((2 / dyadicScale j) * (2 / dyadicScale j)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hderiv₁ hscale₁)
        (mul_le_mul_of_nonneg_right hderiv₂ hscale₂)
    _ = 5 * B / dyadicScale j ^ 2 := by rw [hcoeff₁, hcoeff₂]; ring

theorem hasDerivAt_dyadicComplexCutoff (j : ℕ) (ξ : ℝ) :
    HasDerivAt (fun y : ℝ => (dyadicCutoffFactor j y : ℂ))
      (Complex.ofReal (deriv (dyadicCutoffFactor j) ξ)) ξ := by
  have hcont : ContDiff ℝ 1 (dyadicCutoffFactor j) :=
    (dyadicCutoffFactor_contDiff j).of_le (by norm_num)
  exact hcont.contDiffAt.differentiableAt_one.hasDerivAt.ofReal_comp

theorem deriv_dyadicComplexCutoff (j : ℕ) (ξ : ℝ) :
    deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ =
      Complex.ofReal (deriv (dyadicCutoffFactor j) ξ) :=
  (hasDerivAt_dyadicComplexCutoff j ξ).deriv

theorem iteratedDeriv_two_dyadicComplexCutoff (j : ℕ) (ξ : ℝ) :
    iteratedDeriv 2 (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ =
      Complex.ofReal (iteratedDeriv 2 (dyadicCutoffFactor j) ξ) := by
  have hderivFun : deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) =
      fun y => Complex.ofReal (deriv (dyadicCutoffFactor j) y) := by
    funext y
    exact deriv_dyadicComplexCutoff j y
  have hcont : ContDiff ℝ 1 (deriv (dyadicCutoffFactor j)) := by
    simpa using (dyadicCutoffFactor_contDiff j).deriv'
  have hsecond : HasDerivAt (deriv (dyadicCutoffFactor j))
      (iteratedDeriv 2 (dyadicCutoffFactor j) ξ) ξ := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using
      hcont.contDiffAt.differentiableAt_one.hasDerivAt
  have hcomplex := hsecond.ofReal_comp
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderivFun]
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using hcomplex.deriv

theorem norm_deriv_dyadicComplexCutoff_le (j : ℕ) (ξ : ℝ) :
    ‖deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ ≤
      3 * B / dyadicScale j := by
  rw [deriv_dyadicComplexCutoff j ξ]
  simpa using norm_deriv_dyadicCutoffFactor_le j ξ

theorem norm_iteratedDeriv_two_dyadicComplexCutoff_le (j : ℕ) (ξ : ℝ) :
    ‖iteratedDeriv 2 (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ ≤
      5 * B / dyadicScale j ^ 2 := by
  rw [iteratedDeriv_two_dyadicComplexCutoff j ξ]
  simpa using norm_iteratedDeriv_two_dyadicCutoffFactor_le j ξ

theorem dyadicSymbolData_derivative_bounds {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (ξ : ℝ)
    (hinner : dyadicScale j / 16 ≤ |ξ|)
    (houter : |ξ| ≤ dyadicScale j / 4) :
    ‖m ξ‖ ≤ D ∧ ‖deriv m ξ‖ ≤ 16 * D / dyadicScale j ∧
      ‖iteratedDeriv 2 m ξ‖ ≤ 256 * D / dyadicScale j ^ 2 := by
  have ht := dyadicScale_pos j
  have ht₁ := dyadicScale_le_one j
  have hinnerPos : 0 < dyadicScale j / 16 := div_pos (dyadicScale_pos j) (by norm_num)
  have hξpos : 0 < |ξ| := lt_of_lt_of_le hinnerPos hinner
  have hξhalf : |ξ| < 1 / 2 := by nlinarith [houter, ht₁]
  have hbound := h.weightedDerivativeBound ξ hξpos hξhalf
  have hfirstNonneg : 0 ≤ ‖ξ * deriv m ξ‖ := norm_nonneg _
  have hsecondNonneg : 0 ≤ ‖ξ ^ 2 * iteratedDeriv 2 m ξ‖ := norm_nonneg _
  have hm : ‖m ξ‖ ≤ D := by nlinarith [hbound, hfirstNonneg, hsecondNonneg]
  have hfirstWeighted : ‖ξ * deriv m ξ‖ ≤ D := by
    nlinarith [hbound, norm_nonneg (m ξ), hsecondNonneg]
  have hfirstAbs : |ξ| * ‖deriv m ξ‖ ≤ D := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hfirstWeighted
    exact hfirstWeighted
  have hlow₁ : dyadicScale j / 16 ≤ |ξ| := hinner
  have hfirstScaled := mul_le_mul_of_nonneg_right hlow₁
    (norm_nonneg (deriv m ξ))
  have hfirstSmall : dyadicScale j / 16 * ‖deriv m ξ‖ ≤ D :=
    hfirstScaled.trans hfirstAbs
  have hderiv : ‖deriv m ξ‖ ≤ 16 * D / dyadicScale j := by
    apply (le_div_iff₀ ht).2
    nlinarith [hfirstSmall]
  have hsecondWeighted : ‖ξ ^ 2 * iteratedDeriv 2 m ξ‖ ≤ D := by
    nlinarith [hbound, norm_nonneg (m ξ), hfirstNonneg]
  have hsecondAbs : |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ D := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at hsecondWeighted
    exact hsecondWeighted
  have hlowSq : (dyadicScale j / 16) ^ 2 ≤ |ξ| ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hlow₁ (abs_nonneg ξ)
    have h₂ := mul_le_mul_of_nonneg_left hlow₁ (by positivity :
      0 ≤ dyadicScale j / 16)
    nlinarith
  have hsecondScaled := mul_le_mul_of_nonneg_right hlowSq
    (norm_nonneg (iteratedDeriv 2 m ξ))
  have hsecondSmall : (dyadicScale j / 16) ^ 2 *
      ‖iteratedDeriv 2 m ξ‖ ≤ D := hsecondScaled.trans hsecondAbs
  have hsecond : ‖iteratedDeriv 2 m ξ‖ ≤ 256 * D / dyadicScale j ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).2
    nlinarith [hsecondSmall]
  exact ⟨hm, hderiv, hsecond⟩

theorem dyadicSymbolPiece_deriv_formula {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (ξ : ℝ)
    (hinner : dyadicScale j / 16 ≤ |ξ|)
    (houter : |ξ| ≤ dyadicScale j / 4) :
    deriv (dyadicSymbolPiece h j) ξ =
      deriv m ξ * (dyadicCutoffFactor j ξ : ℂ) +
        m ξ * deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ := by
  have hinnerPos : 0 < dyadicScale j / 16 := div_pos (dyadicScale_pos j) (by norm_num)
  have hξpos : 0 < |ξ| := lt_of_lt_of_le hinnerPos hinner
  have hξhalf : |ξ| < 1 / 2 := by
    have ht := dyadicScale_le_one j
    nlinarith [houter]
  have hξ0 : ξ ≠ 0 := by
    intro hzero
    subst ξ
    simp at hξpos
  have hξU : ξ ∈ dyadicOpenPunctured := by
    rcases lt_or_gt_of_ne hξ0 with hneg | hpos
    · simp only [dyadicOpenPunctured, Set.mem_union, Set.mem_Ioo]
      left
      exact ⟨by rw [abs_lt] at hξhalf; linarith, hneg⟩
    · simp only [dyadicOpenPunctured, Set.mem_union, Set.mem_Ioo]
      right
      exact ⟨hpos, by rw [abs_lt] at hξhalf; linarith⟩
  have hm : ContDiffAt ℝ 1 m ξ :=
    ((h.smoothOnPuncturedTorus.mono
      dyadicOpenPunctured_subset_puncturedTorusLift).contDiffAt
        (isOpen_dyadicOpenPunctured.mem_nhds hξU)).of_le (by norm_num)
  have hη : ContDiffAt ℝ 1
      (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ := by
    have hcut : ContDiffOn ℝ 2
        (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) dyadicOpenPunctured :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        (dyadicCutoffFactor_contDiff j).contDiffOn
    exact (hcut.contDiffAt
      (isOpen_dyadicOpenPunctured.mem_nhds hξU)).of_le (by norm_num)
  have hmul := iteratedDeriv_mul (n := 1) hm hη
  change iteratedDeriv 1
      (fun y : ℝ => m y * (dyadicCutoffFactor j y : ℂ)) ξ = _ at hmul
  change deriv (fun y : ℝ => m y * (dyadicCutoffFactor j y : ℂ)) ξ = _
  simpa [Finset.sum_range_succ, iteratedDeriv_one, iteratedDeriv_zero, add_comm] using hmul

theorem dyadicSymbolPiece_deriv_norm_le_on_annulus {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (ξ : ℝ)
    (hinner : dyadicScale j / 16 ≤ |ξ|)
    (houter : |ξ| ≤ dyadicScale j / 4) :
    ‖deriv (dyadicSymbolPiece h j) ξ‖ ≤ 19 * B * D / dyadicScale j := by
  have hformula := dyadicSymbolPiece_deriv_formula h j ξ hinner houter
  obtain ⟨hm, hm₁, _hm₂⟩ :=
    dyadicSymbolData_derivative_bounds h j ξ hinner houter
  have hcut : |dyadicCutoffFactor j ξ| ≤ 1 := by
    have hp₁ := ψ_nonneg (ξ / dyadicScale j)
    have hp₂ := ψ_nonneg ((2 * ξ) / dyadicScale j)
    have hq₁ := ψ_le_one (ξ / dyadicScale j)
    have hq₂ := ψ_le_one ((2 * ξ) / dyadicScale j)
    rw [dyadicCutoffFactor, abs_le]
    constructor <;> linarith
  have hcut₁ := norm_deriv_dyadicComplexCutoff_le j ξ
  have hB₁ : 1 ≤ B := by
    unfold B
    linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
  have hD := h.D_nonneg
  have ht := dyadicScale_pos j
  have hcutNonneg : 0 ≤ |dyadicCutoffFactor j ξ| := abs_nonneg _
  have hm₁Nonneg : 0 ≤ ‖deriv m ξ‖ := norm_nonneg _
  have hmNonneg : 0 ≤ ‖m ξ‖ := norm_nonneg _
  calc
    ‖deriv (dyadicSymbolPiece h j) ξ‖ =
        ‖deriv m ξ * (dyadicCutoffFactor j ξ : ℂ) +
          m ξ * deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ := by
      rw [hformula]
    _ ≤ ‖deriv m ξ * (dyadicCutoffFactor j ξ : ℂ)‖ +
        ‖m ξ * deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ := norm_add_le _ _
    _ = ‖deriv m ξ‖ * |dyadicCutoffFactor j ξ| +
        ‖m ξ‖ * ‖deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ := by
      simp [norm_mul, Complex.norm_real]
    _ ≤ 16 * D / dyadicScale j * 1 + D * (3 * B / dyadicScale j) := by
      apply add_le_add
      · calc
          ‖deriv m ξ‖ * |dyadicCutoffFactor j ξ| ≤
              (16 * D / dyadicScale j) * |dyadicCutoffFactor j ξ| :=
                mul_le_mul_of_nonneg_right hm₁ (by positivity)
          _ ≤ (16 * D / dyadicScale j) * 1 :=
                mul_le_mul_of_nonneg_left hcut (by positivity)
      · exact mul_le_mul hm (by simpa using hcut₁) (by positivity) (by positivity)
    _ ≤ 19 * B * D / dyadicScale j := by
      have hfirst : 16 * D / dyadicScale j ≤ 16 * B * D / dyadicScale j := by
        apply (div_le_div_iff₀ ht ht).2
        have hBD : 0 ≤ (B - 1) * D :=
          mul_nonneg (by linarith) hD
        nlinarith [mul_nonneg hBD ht.le]
      have hsecond : D * (3 * B / dyadicScale j) =
          3 * B * D / dyadicScale j := by ring
      calc
        16 * D / dyadicScale j * 1 + D * (3 * B / dyadicScale j) =
            16 * D / dyadicScale j + 3 * B * D / dyadicScale j := by
          rw [hsecond]
          ring
        _ ≤ 16 * B * D / dyadicScale j + 3 * B * D / dyadicScale j :=
          add_le_add hfirst (le_refl _)
        _ = 19 * B * D / dyadicScale j := by ring

theorem dyadicSymbolPiece_iteratedDeriv_two_formula {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (ξ : ℝ)
    (hinner : dyadicScale j / 16 ≤ |ξ|)
    (houter : |ξ| ≤ dyadicScale j / 4) :
    iteratedDeriv 2 (dyadicSymbolPiece h j) ξ =
      iteratedDeriv 2 m ξ * (dyadicCutoffFactor j ξ : ℂ) +
        2 * deriv m ξ * deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ +
        m ξ * iteratedDeriv 2
          (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ := by
  have hinnerPos : 0 < dyadicScale j / 16 := div_pos (dyadicScale_pos j) (by norm_num)
  have hξpos : 0 < |ξ| := lt_of_lt_of_le hinnerPos hinner
  have hξhalf : |ξ| < 1 / 2 := by
    have ht := dyadicScale_le_one j
    nlinarith [houter]
  have hξ0 : ξ ≠ 0 := by
    intro hzero
    subst ξ
    simp at hξpos
  have hξU : ξ ∈ dyadicOpenPunctured := by
    rcases lt_or_gt_of_ne hξ0 with hneg | hpos
    · simp only [dyadicOpenPunctured, Set.mem_union, Set.mem_Ioo]
      left
      exact ⟨by rw [abs_lt] at hξhalf; linarith, hneg⟩
    · simp only [dyadicOpenPunctured, Set.mem_union, Set.mem_Ioo]
      right
      exact ⟨hpos, by rw [abs_lt] at hξhalf; linarith⟩
  have hm : ContDiffAt ℝ 2 m ξ :=
    (h.smoothOnPuncturedTorus.mono
      dyadicOpenPunctured_subset_puncturedTorusLift).contDiffAt
        (isOpen_dyadicOpenPunctured.mem_nhds hξU)
  have hη : ContDiffAt ℝ 2
      (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ := by
    have hcut : ContDiffOn ℝ 2
        (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) dyadicOpenPunctured :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        (dyadicCutoffFactor_contDiff j).contDiffOn
    exact hcut.contDiffAt (isOpen_dyadicOpenPunctured.mem_nhds hξU)
  have hmul := iteratedDeriv_mul (n := 2) hm hη
  change iteratedDeriv 2
      (fun y : ℝ => m y * (dyadicCutoffFactor j y : ℂ)) ξ = _ at hmul
  have hmul' : iteratedDeriv 2
      (fun y : ℝ => m y * (dyadicCutoffFactor j y : ℂ)) ξ =
      m ξ * iteratedDeriv 2 (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ +
        2 * deriv m ξ * deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ +
        iteratedDeriv 2 m ξ * (dyadicCutoffFactor j ξ : ℂ) := by
    simpa [Finset.sum_range_succ, iteratedDeriv_one, iteratedDeriv_zero] using hmul
  calc
    iteratedDeriv 2 (dyadicSymbolPiece h j) ξ =
        iteratedDeriv 2
          (fun y : ℝ => m y * (dyadicCutoffFactor j y : ℂ)) ξ := rfl
    _ = m ξ * iteratedDeriv 2
          (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ +
        2 * deriv m ξ * deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ +
        iteratedDeriv 2 m ξ * (dyadicCutoffFactor j ξ : ℂ) := hmul'
    _ = iteratedDeriv 2 m ξ * (dyadicCutoffFactor j ξ : ℂ) +
        2 * deriv m ξ * deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ +
        m ξ * iteratedDeriv 2
          (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ := by ring

theorem dyadicSymbolPiece_iteratedDeriv_two_norm_le_on_annulus {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (ξ : ℝ)
    (hinner : dyadicScale j / 16 ≤ |ξ|)
    (houter : |ξ| ≤ dyadicScale j / 4) :
    ‖iteratedDeriv 2 (dyadicSymbolPiece h j) ξ‖ ≤
      357 * B * D / dyadicScale j ^ 2 := by
  have hformula :=
    dyadicSymbolPiece_iteratedDeriv_two_formula h j ξ hinner houter
  obtain ⟨hm, hm₁, hm₂⟩ :=
    dyadicSymbolData_derivative_bounds h j ξ hinner houter
  have hcut : |dyadicCutoffFactor j ξ| ≤ 1 := by
    have hp₁ := ψ_nonneg (ξ / dyadicScale j)
    have hp₂ := ψ_nonneg ((2 * ξ) / dyadicScale j)
    have hq₁ := ψ_le_one (ξ / dyadicScale j)
    have hq₂ := ψ_le_one ((2 * ξ) / dyadicScale j)
    rw [dyadicCutoffFactor, abs_le]
    constructor <;> linarith
  have hcut₁ := norm_deriv_dyadicComplexCutoff_le j ξ
  have hcut₂ := norm_iteratedDeriv_two_dyadicComplexCutoff_le j ξ
  have hB₁ : 1 ≤ B := by
    unfold B
    linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
  have hD := h.D_nonneg
  have ht := dyadicScale_pos j
  calc
    ‖iteratedDeriv 2 (dyadicSymbolPiece h j) ξ‖ =
        ‖iteratedDeriv 2 m ξ * (dyadicCutoffFactor j ξ : ℂ) +
          2 * deriv m ξ * deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ +
          m ξ * iteratedDeriv 2
            (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ := by
      rw [hformula]
    _ ≤ ‖iteratedDeriv 2 m ξ * (dyadicCutoffFactor j ξ : ℂ) +
          2 * deriv m ξ * deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ +
          ‖m ξ * iteratedDeriv 2
            (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ := norm_add_le _ _
    _ ≤ ‖iteratedDeriv 2 m ξ * (dyadicCutoffFactor j ξ : ℂ)‖ +
          ‖2 * deriv m ξ * deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ +
          ‖m ξ * iteratedDeriv 2
            (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 256 * D / dyadicScale j ^ 2 * 1 +
          2 * (16 * D / dyadicScale j) * (3 * B / dyadicScale j) +
          D * (5 * B / dyadicScale j ^ 2) := by
      have hnorm₁ : ‖iteratedDeriv 2 m ξ * (dyadicCutoffFactor j ξ : ℂ)‖ =
          ‖iteratedDeriv 2 m ξ‖ * |dyadicCutoffFactor j ξ| := by
        simp [norm_mul, Complex.norm_real]
      have hnorm₂ : ‖2 * deriv m ξ *
          deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ =
          2 * ‖deriv m ξ‖ *
            ‖deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ := by
        simp [norm_mul, Complex.norm_real]
      rw [hnorm₁, hnorm₂, norm_mul]
      have hDerivData :=
        dyadicSymbolData_derivative_bounds h j ξ hinner houter
      rcases hDerivData with ⟨hm', hm'₁, hm'₂⟩
      have hcutNonneg : 0 ≤ |dyadicCutoffFactor j ξ| := abs_nonneg _
      have hfirst : ‖iteratedDeriv 2 m ξ‖ * |dyadicCutoffFactor j ξ| ≤
          256 * D / dyadicScale j ^ 2 * 1 := by
        calc
          ‖iteratedDeriv 2 m ξ‖ * |dyadicCutoffFactor j ξ| ≤
              (256 * D / dyadicScale j ^ 2) * |dyadicCutoffFactor j ξ| :=
                mul_le_mul_of_nonneg_right hm'₂ hcutNonneg
          _ ≤ (256 * D / dyadicScale j ^ 2) * 1 :=
                mul_le_mul_of_nonneg_left hcut (by positivity)
      have hmiddle : 2 * ‖deriv m ξ‖ *
          ‖deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ ≤
          2 * (16 * D / dyadicScale j) * (3 * B / dyadicScale j) := by
        have hprod : ‖deriv m ξ‖ *
            ‖deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ ≤
            (16 * D / dyadicScale j) * (3 * B / dyadicScale j) :=
          mul_le_mul hm'₁ hcut₁ (norm_nonneg _) (by positivity)
        calc
          2 * ‖deriv m ξ‖ *
              ‖deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ =
              2 * (‖deriv m ξ‖ *
                ‖deriv (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖) := by ring
          _ ≤ 2 * ((16 * D / dyadicScale j) * (3 * B / dyadicScale j)) :=
                mul_le_mul_of_nonneg_left hprod (by norm_num)
          _ = 2 * (16 * D / dyadicScale j) * (3 * B / dyadicScale j) := by ring
      have hlast : ‖m ξ‖ *
          ‖iteratedDeriv 2 (fun y : ℝ => (dyadicCutoffFactor j y : ℂ)) ξ‖ ≤
          D * (5 * B / dyadicScale j ^ 2) :=
        mul_le_mul hm' hcut₂ (norm_nonneg _) (by positivity)
      exact add_le_add (add_le_add hfirst hmiddle) hlast
    _ ≤ 357 * B * D / dyadicScale j ^ 2 := by
      have hBD : 0 ≤ (B - 1) * D := mul_nonneg (by linarith) hD
      have hBDt : 0 ≤ (B - 1) * D * dyadicScale j ^ 2 :=
        mul_nonneg hBD (sq_nonneg (dyadicScale j))
      have hfirst : 256 * D / dyadicScale j ^ 2 ≤
          256 * B * D / dyadicScale j ^ 2 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos ht) (sq_pos_of_pos ht)).2
        nlinarith [hBDt]
      have hsecond : 2 * (16 * D / dyadicScale j) * (3 * B / dyadicScale j) =
          96 * B * D / dyadicScale j ^ 2 := by
        field_simp
        ring
      have hthird : D * (5 * B / dyadicScale j ^ 2) =
          5 * B * D / dyadicScale j ^ 2 := by ring
      calc
        256 * D / dyadicScale j ^ 2 * 1 +
            2 * (16 * D / dyadicScale j) * (3 * B / dyadicScale j) +
            D * (5 * B / dyadicScale j ^ 2) =
            256 * D / dyadicScale j ^ 2 +
              96 * B * D / dyadicScale j ^ 2 +
              5 * B * D / dyadicScale j ^ 2 := by rw [hsecond, hthird]; ring
        _ ≤ 256 * B * D / dyadicScale j ^ 2 +
              96 * B * D / dyadicScale j ^ 2 +
              5 * B * D / dyadicScale j ^ 2 :=
          add_le_add (add_le_add hfirst (le_refl _)) (le_refl _)
        _ = 357 * B * D / dyadicScale j ^ 2 := by ring

/-- The positive-sign real inverse Fourier phase `e^{2π i x ξ}`. -/
def dyadicInversePhase (x ξ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)

theorem norm_dyadicInversePhase (x ξ : ℝ) : ‖dyadicInversePhase x ξ‖ = 1 := by
  simp [dyadicInversePhase, Complex.norm_exp]

/-- The inverse-transform integrand, with the kernel variable `x : ℝ`. -/
def dyadicKernelIntegrand {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x ξ : ℝ) : ℂ :=
  dyadicSymbolPiece h j ξ * dyadicInversePhase x ξ

/-- The real inverse transform of the `j`-th dyadic piece. -/
def dyadicKernelPiece {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x : ℝ) : ℂ :=
  ∫ ξ : ℝ, dyadicKernelIntegrand h j x ξ

theorem dyadicKernelPiece_eq_fourierInv {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x : ℝ) :
    dyadicKernelPiece h j x = 𝓕⁻ (dyadicSymbolPiece h j) x := by
  rw [dyadicKernelPiece, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [dyadicKernelIntegrand, dyadicInversePhase, Circle.smul_def]
  have hphase : Complex.exp
      (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) =
      Complex.exp (↑(2 * Real.pi * x * ξ) * Complex.I) := by
    congr 1
    congr 1
    simp
    ring
  rw [← hphase]
  exact mul_comm _ _

theorem dyadicKernelPiece_eq_fourier_neg {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x : ℝ) :
    dyadicKernelPiece h j x = 𝓕 (dyadicSymbolPiece h j) (-x) := by
  rw [dyadicKernelPiece_eq_fourierInv, Real.fourierInv_eq_fourier_neg]

theorem dyadicCutoffFactor_eq_zero_of_abs_le_lower (j : ℕ) (ξ : ℝ)
    (hξ : |ξ| ≤ dyadicScale j / 16) : dyadicCutoffFactor j ξ = 0 := by
  have ht := dyadicScale_pos j
  have hfirst : |ξ / dyadicScale j| ≤ 1 / 8 := by
    rw [abs_div, abs_of_pos ht]
    apply (div_le_iff₀ ht).2
    linarith
  have hsecond : |(2 * ξ) / dyadicScale j| ≤ 1 / 8 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)), abs_of_pos ht]
    apply (div_le_iff₀ ht).2
    nlinarith
  rw [dyadicCutoffFactor, ψ_eq_one_of_abs_le _ hfirst,
    ψ_eq_one_of_abs_le _ hsecond]
  ring

theorem dyadicCutoffFactor_eq_zero_of_upper_le_abs (j : ℕ) (ξ : ℝ)
    (hξ : dyadicScale j / 4 ≤ |ξ|) : dyadicCutoffFactor j ξ = 0 := by
  have ht := dyadicScale_pos j
  have hfirst : 3 / 16 ≤ |ξ / dyadicScale j| := by
    rw [abs_div, abs_of_pos ht]
    apply (le_div_iff₀ ht).2
    nlinarith
  have hsecond : 3 / 16 ≤ |(2 * ξ) / dyadicScale j| := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)), abs_of_pos ht]
    apply (le_div_iff₀ ht).2
    nlinarith
  have hfirst_zero : ψ (ξ / dyadicScale j) = 0 := by
    by_contra hn
    have hmem : ξ / dyadicScale j ∈ Function.support ψ := by
      change ψ (ξ / dyadicScale j) ≠ 0
      exact hn
    rw [support_ψ] at hmem
    have hball := Metric.mem_ball.mp hmem
    rw [Real.dist_eq] at hball
    simp only [sub_zero] at hball
    linarith
  have hsecond_zero : ψ ((2 * ξ) / dyadicScale j) = 0 := by
    by_contra hn
    have hmem : (2 * ξ) / dyadicScale j ∈ Function.support ψ := by
      change ψ ((2 * ξ) / dyadicScale j) ≠ 0
      exact hn
    rw [support_ψ] at hmem
    have hball := Metric.mem_ball.mp hmem
    rw [Real.dist_eq] at hball
    simp only [sub_zero] at hball
    linarith
  simp [dyadicCutoffFactor, hfirst_zero, hsecond_zero]

theorem dyadicCutoffFactor_abs_le_one (j : ℕ) (ξ : ℝ) :
    |dyadicCutoffFactor j ξ| ≤ 1 := by
  have h₁ := ψ_nonneg (ξ / dyadicScale j)
  have h₂ := ψ_nonneg ((2 * ξ) / dyadicScale j)
  have h₃ := ψ_le_one (ξ / dyadicScale j)
  have h₄ := ψ_le_one ((2 * ξ) / dyadicScale j)
  rw [dyadicCutoffFactor, abs_le]
  constructor <;> linarith

/-- Nonzero dyadic pieces lie in the approved annulus
`t_j/16 ≤ |ξ| ≤ t_j/4`, hence away from zero and within `|ξ|<1/2`. -/
theorem dyadicSymbolPiece_support_annulus {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (ξ : ℝ)
    (hξ : dyadicSymbolPiece h j ξ ≠ 0) :
    dyadicScale j / 16 < |ξ| ∧ |ξ| < dyadicScale j / 4 := by
  have hη : dyadicCutoffFactor j ξ ≠ 0 := by
    intro hzero
    simp [dyadicSymbolPiece, hzero] at hξ
  constructor
  · by_contra hnot
    have hlow : |ξ| ≤ dyadicScale j / 16 := le_of_not_gt hnot
    exact hη (dyadicCutoffFactor_eq_zero_of_abs_le_lower j ξ hlow)
  · by_contra hnot
    have hupp : dyadicScale j / 4 ≤ |ξ| := le_of_not_gt hnot
    exact hη (dyadicCutoffFactor_eq_zero_of_upper_le_abs j ξ hupp)

/-- The closed annulus containing the topological support of a dyadic piece. -/
def dyadicClosedAnnulus (j : ℕ) : Set ℝ :=
  {ξ | dyadicScale j / 16 ≤ |ξ| ∧ |ξ| ≤ dyadicScale j / 4}

theorem isClosed_dyadicClosedAnnulus (j : ℕ) : IsClosed (dyadicClosedAnnulus j) := by
  have hlower : IsClosed {ξ : ℝ | dyadicScale j / 16 ≤ |ξ|} :=
    isClosed_le continuous_const continuous_abs
  have hupper : IsClosed {ξ : ℝ | |ξ| ≤ dyadicScale j / 4} :=
    isClosed_le continuous_abs continuous_const
  exact hlower.inter hupper

theorem dyadicSymbolPiece_tsupport_annulus {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    tsupport (dyadicSymbolPiece h j) ⊆ dyadicClosedAnnulus j := by
  apply closure_minimal ?_ (isClosed_dyadicClosedAnnulus j)
  intro ξ hξ
  have hξ' : dyadicSymbolPiece h j ξ ≠ 0 := by
    simpa [Function.mem_support] using hξ
  obtain ⟨hlower, hupper⟩ := dyadicSymbolPiece_support_annulus h j ξ hξ'
  exact ⟨hlower.le, hupper.le⟩

theorem dyadicSymbolPiece_support_Icc {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    Function.support (dyadicSymbolPiece h j) ⊆
      Set.Icc (-(dyadicScale j / 4)) (dyadicScale j / 4) := by
  intro ξ hξ
  have hξ' : dyadicSymbolPiece h j ξ ≠ 0 := by
    simpa [Function.mem_support] using hξ
  obtain ⟨_, hupper⟩ := dyadicSymbolPiece_support_annulus h j ξ hξ'
  exact abs_le.mp hupper.le

theorem dyadicSymbolPiece_deriv_support_annulus {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    Function.support (deriv (dyadicSymbolPiece h j)) ⊆
      dyadicClosedAnnulus j := by
  calc
    Function.support (deriv (dyadicSymbolPiece h j)) ⊆
        tsupport (dyadicSymbolPiece h j) := support_deriv_subset
    _ ⊆ dyadicClosedAnnulus j := dyadicSymbolPiece_tsupport_annulus h j

theorem dyadicSymbolPiece_iteratedDeriv_two_support_annulus
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (j : ℕ) :
    Function.support (iteratedDeriv 2 (dyadicSymbolPiece h j)) ⊆
      dyadicClosedAnnulus j := by
  have hs : Function.support (iteratedDeriv 2 (dyadicSymbolPiece h j)) ⊆
      tsupport (dyadicSymbolPiece h j) := by
    simp only [iteratedDeriv_succ, iteratedDeriv_one]
    exact support_deriv_subset.trans tsupport_deriv_subset
  exact hs.trans (dyadicSymbolPiece_tsupport_annulus h j)

theorem dyadicSymbolPiece_deriv_norm_le {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (ξ : ℝ) :
    ‖deriv (dyadicSymbolPiece h j) ξ‖ ≤ 19 * B * D / dyadicScale j := by
  by_cases hξ : ξ ∈ dyadicClosedAnnulus j
  · have hξ' : dyadicScale j / 16 ≤ |ξ| ∧ |ξ| ≤ dyadicScale j / 4 := hξ
    exact dyadicSymbolPiece_deriv_norm_le_on_annulus h j ξ hξ'.1 hξ'.2
  · have hξts : ξ ∉ tsupport (dyadicSymbolPiece h j) := by
      intro hts
      exact hξ (dyadicSymbolPiece_tsupport_annulus h j hts)
    rw [deriv_of_notMem_tsupport hξts]
    have hnonneg : 0 ≤ 19 * B * D / dyadicScale j := by
      have ht := dyadicScale_pos j
      have hB : 0 ≤ B := by unfold B; linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) h.D_nonneg) ht.le
    simpa using hnonneg

theorem dyadicSymbolPiece_iteratedDeriv_two_norm_le {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (ξ : ℝ) :
    ‖iteratedDeriv 2 (dyadicSymbolPiece h j) ξ‖ ≤
      357 * B * D / dyadicScale j ^ 2 := by
  by_cases hξ : ξ ∈ dyadicClosedAnnulus j
  · have hξ' : dyadicScale j / 16 ≤ |ξ| ∧ |ξ| ≤ dyadicScale j / 4 := hξ
    exact dyadicSymbolPiece_iteratedDeriv_two_norm_le_on_annulus h j ξ hξ'.1 hξ'.2
  · have hξts : ξ ∉ tsupport (deriv (dyadicSymbolPiece h j)) := by
      intro hts
      have hts' := tsupport_deriv_subset hts
      exact hξ (dyadicSymbolPiece_tsupport_annulus h j hts')
    have hzero : deriv (deriv (dyadicSymbolPiece h j)) ξ = 0 :=
      deriv_of_notMem_tsupport hξts
    rw [show iteratedDeriv 2 (dyadicSymbolPiece h j) ξ =
        deriv (deriv (dyadicSymbolPiece h j)) ξ by simp [iteratedDeriv_succ, iteratedDeriv_one],
      hzero]
    have ht := dyadicScale_pos j
    have hB : 0 ≤ B := by unfold B; linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
    have hnonneg : 0 ≤ 357 * B * D / dyadicScale j ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) h.D_nonneg)
        (sq_nonneg (dyadicScale j))
    simpa using hnonneg

/-- The exact dyadic symbol piece has a globally C² zero extension. The
vanishing cutoff removes the singularity at the origin and the seam. -/
theorem dyadicSymbolPiece_contDiff {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    ContDiff ℝ 2 (dyadicSymbolPiece h j) := by
  apply contDiffOn_univ.1
  intro ξ _
  by_cases hξ : ξ ∈ dyadicOpenPunctured
  · have hU : dyadicOpenPunctured ⊆ puncturedTorusLift :=
      dyadicOpenPunctured_subset_puncturedTorusLift
    have hm : ContDiffOn ℝ 2 m dyadicOpenPunctured :=
      h.smoothOnPuncturedTorus.mono hU
    have hcut : ContDiffOn ℝ 2 (fun ξ : ℝ =>
        (dyadicCutoffFactor j ξ : ℂ)) dyadicOpenPunctured :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        (dyadicCutoffFactor_contDiff j).contDiffOn
    have hp : ContDiffOn ℝ 2 (dyadicSymbolPiece h j) dyadicOpenPunctured := by
      unfold dyadicSymbolPiece
      exact hm.mul hcut
    exact hp.contDiffAt (isOpen_dyadicOpenPunctured.mem_nhds hξ)
  · have hzero : dyadicSymbolPiece h j =ᶠ[nhds ξ] fun _ => 0 := by
      by_cases hξ0 : ξ = 0
      · subst ξ
        have ht := dyadicScale_pos j
        have hrad : 0 < dyadicScale j / 16 := by positivity
        filter_upwards [Metric.ball_mem_nhds 0 hrad] with y hy
        have hyabs : |y| ≤ dyadicScale j / 16 := by
          rw [Metric.mem_ball, Real.dist_eq] at hy
          simpa using hy.le
        have hcutzero := dyadicCutoffFactor_eq_zero_of_abs_le_lower j y hyabs
        simp [dyadicSymbolPiece, hcutzero]
      · have houter : 1 / 2 ≤ |ξ| := by
          by_contra hn
          have hsmall : |ξ| < 1 / 2 := lt_of_not_ge hn
          rcases lt_or_gt_of_ne hξ0 with hneg | hpos
          · have hmem : ξ ∈ dyadicOpenPunctured := by
              simp only [dyadicOpenPunctured, Set.mem_union, Set.mem_Ioo]
              exact Or.inl ⟨by rw [abs_lt] at hsmall; linarith, hneg⟩
            exact hξ hmem
          · have hmem : ξ ∈ dyadicOpenPunctured := by
              simp only [dyadicOpenPunctured, Set.mem_union, Set.mem_Ioo]
              exact Or.inr ⟨hpos, by rw [abs_lt] at hsmall; linarith⟩
            exact hξ hmem
        have hrad : 0 < (1 / 8 : ℝ) := by norm_num
        filter_upwards [Metric.ball_mem_nhds ξ hrad] with y hy
        have hdist : |y - ξ| < 1 / 8 := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hy
        have htriangle : |ξ| ≤ |y| + |y - ξ| := by
          calc
            |ξ| = |y + (ξ - y)| := by congr 1 <;> ring
            _ ≤ |y| + |ξ - y| := abs_add_le y (ξ - y)
            _ = |y| + |y - ξ| := by
              rw [show ξ - y = -(y - ξ) by ring, abs_neg]
        have hyouter : dyadicScale j / 4 ≤ |y| := by
          have ht := dyadicScale_le_one j
          nlinarith [houter, hdist, htriangle]
        have hcutzero := dyadicCutoffFactor_eq_zero_of_upper_le_abs j y hyouter
        simp [dyadicSymbolPiece, hcutzero]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hzero

theorem dyadicSymbolPiece_hasCompactSupport {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    HasCompactSupport (dyadicSymbolPiece h j) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (dyadicSymbolPiece_support_Icc h j)

theorem dyadicSymbolPiece_iteratedDeriv_two_integrable {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    Integrable (fun ξ : ℝ => iteratedDeriv 2 (dyadicSymbolPiece h j) ξ) := by
  have hcont : Continuous (fun ξ : ℝ => iteratedDeriv 2 (dyadicSymbolPiece h j) ξ) :=
    (dyadicSymbolPiece_contDiff h j).continuous_iteratedDeriv 2 (by norm_num)
  have hcompact : HasCompactSupport
      (fun ξ : ℝ => iteratedDeriv 2 (dyadicSymbolPiece h j) ξ) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      (dyadicSymbolPiece_hasCompactSupport h j).deriv.deriv
  exact hcont.integrable_of_hasCompactSupport hcompact

theorem dyadicSymbolPiece_iteratedDeriv_integrable {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j n : ℕ) (hn : n ≤ 2) :
    Integrable (fun ξ : ℝ => iteratedDeriv n (dyadicSymbolPiece h j) ξ) := by
  have hcont := dyadicSymbolPiece_contDiff h j
  have hcompact := dyadicSymbolPiece_hasCompactSupport h j
  interval_cases n
  · simpa only [iteratedDeriv_zero] using hcont.continuous.integrable_of_hasCompactSupport hcompact
  · simpa only [iteratedDeriv_one] using
      (hcont.continuous_iteratedDeriv 1 (by norm_num)).integrable_of_hasCompactSupport
        (by simpa only [iteratedDeriv_one] using hcompact.deriv)
  · exact dyadicSymbolPiece_iteratedDeriv_two_integrable h j

theorem dyadicSymbolPiece_iteratedDeriv_two_l1_le {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) :
    ∫ ξ : ℝ, ‖iteratedDeriv 2 (dyadicSymbolPiece h j) ξ‖ ≤
      357 * B * D / (2 * dyadicScale j) := by
  let t := dyadicScale j
  let q : ℝ → ℝ := fun ξ => ‖iteratedDeriv 2 (dyadicSymbolPiece h j) ξ‖
  let s : Set ℝ := Set.Icc (-(t / 4)) (t / 4)
  have ht : 0 < t := dyadicScale_pos j
  have hqcont : Continuous q := by
    dsimp [q]
    exact ((dyadicSymbolPiece_contDiff h j).continuous_iteratedDeriv 2 (by norm_num)).norm
  have hqsupport : Function.support q ⊆ s := by
    intro ξ hξ
    have hξ' : iteratedDeriv 2 (dyadicSymbolPiece h j) ξ ≠ 0 := by
      simpa [q, Function.mem_support] using hξ
    have hξ'' : ξ ∈ Function.support (iteratedDeriv 2 (dyadicSymbolPiece h j)) := by
      change iteratedDeriv 2 (dyadicSymbolPiece h j) ξ ≠ 0
      exact hξ'
    have hAnn := dyadicSymbolPiece_iteratedDeriv_two_support_annulus h j hξ''
    have hupper : |ξ| ≤ t / 4 := by
      simpa [dyadicClosedAnnulus, t] using hAnn.2
    exact abs_le.mp hupper
  have hqcompact : HasCompactSupport q :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hqsupport
  have hqint : Integrable q := hqcont.integrable_of_hasCompactSupport hqcompact
  have hqintSet : IntegrableOn q s volume := hqint.integrableOn
  have hfinite : volume s ≠ ⊤ := by
    dsimp [s]
    exact isCompact_Icc.measure_lt_top.ne
  have hq_indicator : q = s.indicator q := by
    funext ξ
    by_cases hξ : ξ ∈ s
    · simp [hξ]
    · have hzero : q ξ = 0 := by
        by_contra hqξ
        have hqmem : ξ ∈ Function.support q := by
          change q ξ ≠ 0
          exact hqξ
        exact hξ (hqsupport hqmem)
      simp [hξ, hzero]
  calc
    ∫ ξ : ℝ, q ξ = ∫ ξ : ℝ, s.indicator q ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      exact congrFun hq_indicator ξ
    _ = ∫ ξ in s, q ξ ∂volume := integral_indicator (by
      dsimp [s]
      exact measurableSet_Icc)
    _ ≤ ∫ ξ in s, 357 * B * D / t ^ 2 ∂volume := by
      apply setIntegral_mono_on hqintSet (integrableOn_const hfinite) (by
        dsimp [s]
        exact measurableSet_Icc)
      intro ξ hξ
      exact dyadicSymbolPiece_iteratedDeriv_two_norm_le h j ξ
    _ = (357 * B * D / t ^ 2) * (t / 2) := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc]
      have hwidth : t / 4 - -(t / 4) = t / 2 := by ring
      rw [hwidth, ENNReal.toReal_ofReal (by positivity)]
      ring
    _ = 357 * B * D / (2 * dyadicScale j) := by
      dsimp [t]
      field_simp

theorem dyadicSymbolPiece_norm_le {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (ξ : ℝ) :
    ‖dyadicSymbolPiece h j ξ‖ ≤ D := by
  have hD := h.D_nonneg
  by_cases hp : dyadicSymbolPiece h j ξ = 0
  · simp [hp, hD]
  · obtain ⟨hlow, hupp⟩ := dyadicSymbolPiece_support_annulus h j ξ hp
    have hξpos : 0 < |ξ| := by
      have ht := dyadicScale_pos j
      exact lt_of_le_of_lt (by positivity) hlow
    have hξhalf : |ξ| < 1 / 2 := by
      have ht := dyadicScale_le_one j
      nlinarith [hupp]
    have hmBound := h.weightedDerivativeBound ξ hξpos hξhalf
    have hmNonneg : 0 ≤ ‖m ξ‖ := norm_nonneg _
    have heta := dyadicCutoffFactor_abs_le_one j ξ
    calc
      ‖dyadicSymbolPiece h j ξ‖ = ‖m ξ‖ * |dyadicCutoffFactor j ξ| := by
        simp [dyadicSymbolPiece, norm_mul, Complex.norm_real]
      _ ≤ ‖m ξ‖ * 1 := mul_le_mul_of_nonneg_left heta hmNonneg
      _ ≤ D := by nlinarith [norm_nonneg (ξ * deriv m ξ),
        norm_nonneg (ξ ^ 2 * iteratedDeriv 2 m ξ)]

theorem dyadicKernelIntegrand_support_subset {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x : ℝ) :
    Function.support (dyadicKernelIntegrand h j x) ⊆
      Set.Icc (-(dyadicScale j / 4)) (dyadicScale j / 4) := by
  intro ξ hξ
  have hnonzero : dyadicKernelIntegrand h j x ξ ≠ 0 := by
    change dyadicKernelIntegrand h j x ξ ≠ 0 at hξ
    exact hξ
  have hp : dyadicSymbolPiece h j ξ ≠ 0 := by
    intro hp
    simp [dyadicKernelIntegrand, hp] at hnonzero
  obtain ⟨_, hupp⟩ := dyadicSymbolPiece_support_annulus h j ξ hp
  exact abs_le.mp (le_of_lt hupp)

theorem dyadicKernelIntegrand_measurable {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x : ℝ) :
    Measurable (dyadicKernelIntegrand h j x) := by
  have heta : Measurable (dyadicCutoffFactor j) := by
    have hψ : Continuous ψ := ψ_contDiff.continuous
    have hfirst : Continuous (fun ξ : ℝ => ξ / dyadicScale j) := by fun_prop
    have hsecond : Continuous (fun ξ : ℝ => (2 * ξ) / dyadicScale j) := by
      fun_prop
    change Measurable (fun ξ : ℝ =>
      ψ (ξ / dyadicScale j) - ψ ((2 * ξ) / dyadicScale j))
    exact (hψ.measurable.comp hfirst.measurable).sub
      (hψ.measurable.comp hsecond.measurable)
  have hpiece : Measurable (dyadicSymbolPiece h j) := by
    unfold dyadicSymbolPiece
    exact h.measurable.mul (Complex.continuous_ofReal.measurable.comp heta)
  have hphase : Continuous (dyadicInversePhase x) := by
    unfold dyadicInversePhase
    fun_prop
  exact hpiece.mul hphase.measurable

theorem dyadicKernelIntegrand_norm_le {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x ξ : ℝ) :
    ‖dyadicKernelIntegrand h j x ξ‖ ≤ D := by
  have hD := h.D_nonneg
  rw [dyadicKernelIntegrand, norm_mul, norm_dyadicInversePhase, mul_one]
  exact dyadicSymbolPiece_norm_le h j ξ

theorem dyadicKernelIntegrand_integrable {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x : ℝ) :
    Integrable (dyadicKernelIntegrand h j x) := by
  let s := Set.Icc (-(dyadicScale j / 4)) (dyadicScale j / 4)
  have hsupp : Function.support (dyadicKernelIntegrand h j x) ⊆ s :=
    dyadicKernelIntegrand_support_subset h j x
  have hmeas := (dyadicKernelIntegrand_measurable h j x).aestronglyMeasurable
    (μ := volume)
  have hbounded : ∀ᵐ ξ ∂(volume.restrict s),
      ‖dyadicKernelIntegrand h j x ξ‖ ≤ D := by
    filter_upwards with ξ
    exact dyadicKernelIntegrand_norm_le h j x ξ
  have hfinite : volume s ≠ ⊤ := by
    dsimp [s]
    exact isCompact_Icc.measure_lt_top.ne
  have hOn : IntegrableOn (dyadicKernelIntegrand h j x) s volume :=
    Measure.integrableOn_of_bounded hfinite hmeas (M := D) hbounded
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hOn

theorem norm_dyadicKernelPiece_le_l1 {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x : ℝ) :
    ‖dyadicKernelPiece h j x‖ ≤
      ∫ ξ : ℝ, ‖dyadicKernelIntegrand h j x ξ‖ := by
  exact norm_integral_le_integral_norm _

/-- The compact-support pointwise estimate, stated in the exact `AD` form
on the low-frequency region `t_j |x| ≤ 1`. -/
theorem dyadicKernelPiece_bound_of_small_frequency {m : ℝ → ℂ} {D : ℝ}
    (h : SymbolData m D) (j : ℕ) (x : ℝ)
    (hx : dyadicScale j * |x| ≤ 1) :
    ‖dyadicKernelPiece h j x‖ ≤
      A * D * dyadicScale j / (1 + dyadicScale j * |x|) ^ 2 := by
  let t := dyadicScale j
  have ht : 0 < t := dyadicScale_pos j
  have hD := h.D_nonneg
  have hfinite : volume (Set.Icc (-(t / 4)) (t / 4)) ≠ ⊤ := by
    exact isCompact_Icc.measure_lt_top.ne
  have hsupp := dyadicKernelIntegrand_support_subset h j x
  have hF := dyadicKernelIntegrand_integrable h j x
  have hnormSupport : Function.support (fun ξ : ℝ =>
      ‖dyadicKernelIntegrand h j x ξ‖) ⊆ Set.Icc (-(t / 4)) (t / 4) := by
    intro ξ hξ
    change ‖dyadicKernelIntegrand h j x ξ‖ ≠ 0 at hξ
    have hn : dyadicKernelIntegrand h j x ξ ≠ 0 := by
      intro hz
      exact hξ (by simp [hz])
    have hIcc := hsupp hn
    simpa [t, dyadicScale] using hIcc
  have hnormfun : (fun ξ : ℝ => ‖dyadicKernelIntegrand h j x ξ‖) =
      (Set.Icc (-(t / 4)) (t / 4)).indicator
        (fun ξ => ‖dyadicKernelIntegrand h j x ξ‖) := by
    funext ξ
    by_cases hξ : ξ ∈ Set.Icc (-(t / 4)) (t / 4)
    · simp [hξ]
    · have hzero : dyadicKernelIntegrand h j x ξ = 0 := by
        by_contra hn
        have hn' : ‖dyadicKernelIntegrand h j x ξ‖ ≠ 0 := by
          intro hz
          exact hn (norm_eq_zero.mp hz)
        exact hξ (hnormSupport hn')
      simp [hξ, hzero]
  have hnormInt : Integrable (fun ξ : ℝ =>
      ‖dyadicKernelIntegrand h j x ξ‖) := hF.norm
  have hnormIntSet : IntegrableOn (fun ξ : ℝ =>
      ‖dyadicKernelIntegrand h j x ξ‖) (Set.Icc (-(t / 4)) (t / 4)) volume :=
    hnormInt.integrableOn
  calc
    ‖dyadicKernelPiece h j x‖ ≤
        ∫ ξ : ℝ, ‖dyadicKernelIntegrand h j x ξ‖ :=
      norm_dyadicKernelPiece_le_l1 h j x
    _ = ∫ ξ in Set.Icc (-(t / 4)) (t / 4),
        ‖dyadicKernelIntegrand h j x ξ‖ ∂volume := by
      calc
        ∫ ξ : ℝ, ‖dyadicKernelIntegrand h j x ξ‖ =
            ∫ ξ : ℝ, (Set.Icc (-(t / 4)) (t / 4)).indicator
              (fun ξ => ‖dyadicKernelIntegrand h j x ξ‖) ξ := by
          apply integral_congr_ae
          filter_upwards with ξ
          exact congrFun hnormfun ξ
        _ = ∫ ξ in Set.Icc (-(t / 4)) (t / 4),
            ‖dyadicKernelIntegrand h j x ξ‖ ∂volume :=
          integral_indicator measurableSet_Icc
    _ ≤ ∫ ξ in Set.Icc (-(t / 4)) (t / 4), D ∂volume := by
      apply setIntegral_mono_on
        hnormIntSet (integrableOn_const hfinite) measurableSet_Icc
      intro ξ hξ
      exact dyadicKernelIntegrand_norm_le h j x ξ
    _ = D * (t / 2) := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc]
      have hdiff : t / 4 - -(t / 4) = t / 2 := by ring
      rw [hdiff, ENNReal.toReal_ofReal (by positivity)]
      ring
    _ ≤ A * D * t / (1 + t * |x|) ^ 2 := by
      have hA : 2 ≤ A := by
        have hB : 1 ≤ B := by
          unfold B
          linarith [ψDerivSup_nonneg, ψSecondDerivSup_nonneg]
        unfold A
        norm_num
        nlinarith [hB]
      have hx' : t * |x| ≤ 1 := by simpa [t] using hx
      have hu : 0 ≤ t * |x| := mul_nonneg ht.le (abs_nonneg x)
      have huSq : (t * |x|) ^ 2 ≤ 1 := by
        have hmul := mul_le_mul_of_nonneg_left hx' hu
        nlinarith
      have hden : (1 + t * |x|) ^ 2 ≤ 4 := by nlinarith [hx', hu, huSq]
      have hdenpos : 0 < (1 + t * |x|) ^ 2 := by positivity
      apply (le_div_iff₀ hdenpos).2
      have hH : 0 ≤ D * t := mul_nonneg hD ht.le
      have hmul : D * (t / 2) * (1 + t * |x|) ^ 2 ≤
          D * (t / 2) * 4 :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      have hA' : 2 * (D * t) ≤ A * (D * t) :=
        mul_le_mul_of_nonneg_right hA hH
      nlinarith [hmul, hA']

end

end FractionalPrimes.Literature.Multiplier
