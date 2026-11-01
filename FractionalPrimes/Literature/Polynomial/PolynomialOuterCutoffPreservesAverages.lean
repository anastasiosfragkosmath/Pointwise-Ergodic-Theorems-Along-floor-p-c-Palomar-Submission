module

public import FractionalPrimes.Chebyshev
public import FractionalPrimes.Literature.Polynomial.MellinWindowData
public import FractionalPrimes.Literature.Polynomial.PolynomialSmoothMeanDecay
public import Mathlib.Data.Int.ModEq

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open scoped BigOperators

noncomputable section

/-- The source coefficient `f(n) ζ(n/X) 1_{n ≡ a (q)}` for either of the
integer-indexed arithmetic weights in `lup:outer-cutoff`. -/
noncomputable def outerCutoffResidueCoefficient
    (f : ℤ → ℝ) (X : ℝ) (q : ℕ) (a : ℤ) (n : ℕ) : ℂ :=
  ((f (n : ℤ) * polynomialOuterCutoff ((n : ℝ) / X) : ℝ) : ℂ) *
    if Int.ModEq (q : ℤ) (n : ℤ) a then 1 else 0

private theorem outerCutoff_logX_ge_one {X : ℝ} (hX : 3 ≤ X) :
    1 ≤ Real.log X := by
  have hXpos : 0 < X := by linarith
  apply (Real.le_log_iff_exp_le hXpos).2
  exact Real.exp_one_lt_three.le.trans hX

private theorem outerCutoff_log_three_mul_le_two_logX {X : ℝ}
    (hX : 3 ≤ X) : Real.log (3 * X) ≤ 2 * Real.log X := by
  have hXpos : 0 < X := by linarith
  have hlog3 : Real.log 3 ≤ Real.log X :=
    Real.log_le_log (by norm_num) hX
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hXpos.ne']
  linarith

theorem outerCutoffResidueCoefficient_support
    (f : ℤ → ℝ) (X : ℝ) (q : ℕ) (a : ℤ)
    (hX : 3 ≤ X) :
    ∀ n, 0 < n → outerCutoffResidueCoefficient f X q a n ≠ 0 →
      X / 2 < (n : ℝ) ∧ (n : ℝ) < 3 * X := by
  intro n hn hcoeff
  by_cases hmod : Int.ModEq (q : ℤ) (n : ℤ) a
  · have hcut : polynomialOuterCutoff ((n : ℝ) / X) ≠ 0 := by
      intro hz
      apply hcoeff
      simp [outerCutoffResidueCoefficient, hmod, hz]
    have hcutSupport := polynomialOuterCutoff_support_subset
      (by simpa [Function.mem_support] using hcut)
    have hXpos : 0 < X := by linarith
    have hmul : ((n : ℝ) / X) * X = (n : ℝ) := by
      field_simp
    constructor
    · nlinarith [hcutSupport.1]
    · nlinarith [hcutSupport.2]
  · simp [outerCutoffResidueCoefficient, hmod] at hcoeff

theorem outerCutoffArithmeticWeight_abs_le
    (f : ℤ → ℝ) (X : ℝ) (n : ℕ)
    (hX : 3 ≤ X)
    (hf : f = paperLambda ∨ f = fun n => (paperMu n : ℝ))
    (hn : 0 < n)
    (hcut : polynomialOuterCutoff ((n : ℝ) / X) ≠ 0) :
    |f (n : ℤ)| ≤ 2 * Real.log X := by
  have hXpos : 0 < X := by linarith
  have hsupport := polynomialOuterCutoff_support_subset
    (by simpa [Function.mem_support] using hcut)
  have hmul : ((n : ℝ) / X) * X = (n : ℝ) := by field_simp
  have hnupper : (n : ℝ) < 3 * X := by nlinarith [hsupport.2]
  have hnZ : 1 ≤ (n : ℤ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogX : 1 ≤ Real.log X := outerCutoff_logX_ge_one hX
  rcases hf with hfLambda | hfMu
  · rw [hfLambda]
    have hb := paperLambda_bounds hnZ
    have hnreal : ((n : ℤ) : ℝ) = (n : ℝ) := by norm_cast
    rw [hnreal] at hb
    have hnlog : Real.log (n : ℝ) ≤ Real.log (3 * X) :=
      Real.log_le_log (by exact_mod_cast hn) hnupper.le
    have hlogupper := outerCutoff_log_three_mul_le_two_logX hX
    have hnonneg : 0 ≤ paperLambda (n : ℤ) := hb.1
    rw [abs_of_nonneg hnonneg]
    exact hb.2.trans (hnlog.trans hlogupper)
  · rw [hfMu]
    have hmu := paperMu_abs_le_one hnZ
    have hmuReal : |(paperMu (n : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hmu
    exact hmuReal.trans (by nlinarith [hlogX])

theorem outerCutoffResidueCoefficient_bound
    (f : ℤ → ℝ) (X : ℝ) (q : ℕ) (a : ℤ)
    (hX : 3 ≤ X)
    (hf : f = paperLambda ∨ f = fun n => (paperMu n : ℝ)) :
    ∀ n, 0 < n → ‖outerCutoffResidueCoefficient f X q a n‖ ≤
      2 * Real.log X := by
  intro n hn
  have hlogXnonneg : 0 ≤ Real.log X := by
    linarith [outerCutoff_logX_ge_one hX]
  by_cases hmod : Int.ModEq (q : ℤ) (n : ℤ) a
  · by_cases hcutZero : polynomialOuterCutoff ((n : ℝ) / X) = 0
    · simp [outerCutoffResidueCoefficient, hmod, hcutZero]
      exact hlogXnonneg
    · have hfbound := outerCutoffArithmeticWeight_abs_le f X n hX hf hn hcutZero
      have hcutNonneg := polynomialOuterCutoff_nonneg ((n : ℝ) / X)
      have hcutle := polynomialOuterCutoff_le_one ((n : ℝ) / X)
      have hnorm : ‖outerCutoffResidueCoefficient f X q a n‖ =
          |f (n : ℤ)| * polynomialOuterCutoff ((n : ℝ) / X) := by
        simp [outerCutoffResidueCoefficient, hmod, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hcutNonneg]
      rw [hnorm]
      calc
        |f (n : ℤ)| * polynomialOuterCutoff ((n : ℝ) / X) ≤
            |f (n : ℤ)| * 1 :=
          mul_le_mul_of_nonneg_left hcutle (abs_nonneg _)
        _ = |f (n : ℤ)| := mul_one _
        _ ≤ 2 * Real.log X := hfbound
  · simp [outerCutoffResidueCoefficient, hmod]
    exact hlogXnonneg

/-- The exact Mellin-window instance for the residue-restricted Möbius or
von Mangoldt coefficients after applying the fixed outer cutoff. -/
noncomputable def outerCutoffWindowData
    (rho : ℝ → ℝ) (X H : ℝ) (q : ℕ) (a : ℤ) (f : ℤ → ℝ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X) (_hq : 0 < q)
    (hf : f = paperLambda ∨ f = fun n => (paperMu n : ℝ)) :
    MellinWindowData :=
  mellinWindowData rho X H (2 * Real.log X)
    (outerCutoffResidueCoefficient f X q a)
    hX hH hHX (by have hlog := outerCutoff_logX_ge_one hX; positivity)
    (fun n hn ha =>
      let h := outerCutoffResidueCoefficient_support f X q a hX n hn ha
      ⟨h.1, h.2.le⟩)
    (outerCutoffResidueCoefficient_bound f X q a hX hf)

/-- The outer cutoff retains the exact source support and `2 log X` coefficient
bound, while its normalized Mellin-window mean is the original arithmetic
average over `(X,X+H]` in the chosen residue class. -/
theorem outerCutoffPreservesAverages
    (rho : ℝ → ℝ) (X H : ℝ) (q : ℕ) (a : ℤ) (f : ℤ → ℝ)
    (hX : 3 ≤ X) (hH : 0 < H) (hHX : H ≤ X) (hq : 0 < q)
    (hf : f = paperLambda ∨ f = fun n => (paperMu n : ℝ)) :
    (∀ n, 0 < n → outerCutoffResidueCoefficient f X q a n ≠ 0 →
      X / 2 < (n : ℝ) ∧ (n : ℝ) < 3 * X) ∧
    (∀ n, 0 < n → ‖outerCutoffResidueCoefficient f X q a n‖ ≤
      2 * Real.log X) ∧
    (outerCutoffWindowData rho X H q a f hX hH hHX hq hf).N_H =
      ((H⁻¹ : ℝ) : ℂ) *
        ∑ n ∈ (mellinWindowAverageIndices X H).filter
            (fun n : ℕ => Int.ModEq (q : ℤ) (n : ℤ) a),
          (f (n : ℤ) : ℂ) := by
  refine ⟨outerCutoffResidueCoefficient_support f X q a hX,
    outerCutoffResidueCoefficient_bound f X q a hX hf, ?_⟩
  classical
  let I := mellinWindowAverageIndices X H
  have hsum :
      (∑ n ∈ I, outerCutoffResidueCoefficient f X q a n) =
        ∑ n ∈ I.filter (fun n : ℕ => Int.ModEq (q : ℤ) (n : ℤ) a),
          (f (n : ℤ) : ℂ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have hnI : X < (n : ℝ) ∧ (n : ℝ) ≤ X + H := by
      apply (mellinIntervalIndices_mem_iff (by linarith [hX]) n).1
      simpa [I, mellinWindowAverageIndices] using hn
    have hXpos : 0 < X := by linarith
    have hnlo : 1 ≤ (n : ℝ) / X := by
      apply (le_div_iff₀ hXpos).2
      linarith [hnI.1]
    have hhi : (n : ℝ) / X ≤ 2 := by
      have hHX' : X + H ≤ 2 * X := by linarith
      apply (div_le_iff₀ hXpos).2
      exact hnI.2.trans hHX'
    have hcut : polynomialOuterCutoff ((n : ℝ) / X) = 1 :=
      polynomialOuterCutoff_eq_one hnlo hhi
    by_cases hmod : Int.ModEq (q : ℤ) (n : ℤ) a
    · simp [outerCutoffResidueCoefficient, hmod, hcut]
    · simp [outerCutoffResidueCoefficient, hmod]
  unfold outerCutoffWindowData
  change ((H⁻¹ : ℝ) : ℂ) *
      (∑ n ∈ I, outerCutoffResidueCoefficient f X q a n) = _
  rw [hsum]

#print axioms outerCutoffPreservesAverages

end

end FractionalPrimes.Literature.Polynomial
