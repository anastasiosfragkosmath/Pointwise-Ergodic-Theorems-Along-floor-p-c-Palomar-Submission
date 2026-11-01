module

public import FractionalPrimes.Literature.DirichletAdapter.SmoothLongFactorTailIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Exact conversion of the blueprint's two-sided frequency set integral. -/

@[expose] public section

open MeasureTheory intervalIntegral
open scoped Interval

namespace FractionalPrimes.Literature.DirichletAdapter

/-- The source set `W ≤ |t| ≤ U` is exactly the union of the two closed tails. -/
theorem smoothLongFactor_frequencyDomain_eq_twoTails
    (W U : ℝ) (hW : 0 < W) (hWU : W ≤ U) :
    {t : ℝ | W ≤ |t| ∧ |t| ≤ U} = Set.Icc (-U) (-W) ∪ Set.Icc W U := by
  ext t
  constructor
  · intro ht
    change W ≤ |t| ∧ |t| ≤ U at ht
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h] at ht
      change t ∈ Set.Icc (-U) (-W) ∨ t ∈ Set.Icc W U
      exact Or.inr ⟨ht.1, ht.2⟩
    · rw [abs_of_nonpos h] at ht
      change t ∈ Set.Icc (-U) (-W) ∨ t ∈ Set.Icc W U
      exact Or.inl ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro ht
    change t ∈ Set.Icc (-U) (-W) ∨ t ∈ Set.Icc W U at ht
    rcases ht with ht | ht
    · have htn : t ≤ 0 := by linarith [ht.2]
      change W ≤ |t| ∧ |t| ≤ U
      rw [abs_of_nonpos htn]
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · have htp : 0 ≤ t := by linarith [ht.1]
      change W ≤ |t| ∧ |t| ≤ U
      rw [abs_of_nonneg htp]
      exact ht

/-- Set integration on the exact frequency domain equals the two oriented
interval integrals used for the power-tail calculation. -/
theorem smoothLongFactor_frequencyDomain_integral_eq_twoTails
    (W U : ℝ) (hW : 0 < W) (hWU : W ≤ U)
    (f : ℝ → ℝ)
    (hneg : IntervalIntegrable f volume (-U) (-W))
    (hpos : IntervalIntegrable f volume W U) :
    (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U}, f t) =
      (∫ t in -U..-W, f t) + (∫ t in W..U, f t) := by
  have hUW : -U ≤ -W := neg_le_neg hWU
  have hdisj : Disjoint (Set.Icc (-U) (-W)) (Set.Icc W U) := by
    apply Set.disjoint_left.mpr
    intro t htneg htpos
    linarith [htneg.2, htpos.1]
  have hintNeg : IntegrableOn f (Set.Icc (-U) (-W)) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hUW).mp hneg
  have hintPos : IntegrableOn f (Set.Icc W U) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hWU).mp hpos
  rw [smoothLongFactor_frequencyDomain_eq_twoTails W U hW hWU,
    setIntegral_union hdisj measurableSet_Icc hintNeg hintPos,
    integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← integral_of_le hUW, ← integral_of_le hWU]

/-- Integrate a pointwise quadrature envelope over the paper's exact
two-sided frequency domain. -/
theorem smoothLongFactor_frequencyDomain_integral_le_envelope
    (W U δ C : ℝ) (j : ℕ)
    (hW : 0 < W) (hWU : W ≤ U) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hj : 2 ≤ j) (f : ℝ → ℝ)
    (hfneg : IntervalIntegrable f volume (-U) (-W))
    (hfpos : IntervalIntegrable f volume W U)
    (hbound : ∀ t, W ≤ |t| → |t| ≤ U →
      f t ≤ C * (|t| ^ (-(j : ℝ)) + δ)) :
    (∫ t in {t : ℝ | W ≤ |t| ∧ |t| ≤ U}, f t) ≤
      C * (2 * (W ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) + 2 * U * δ) := by
  let g : ℝ → ℝ := fun t => |t| ^ (-(j : ℝ)) + δ
  have hU : 0 < U := lt_of_lt_of_le hW hWU
  have hInt (a b : ℝ) (hzero : (0 : ℝ) ∉ [[a, b]]) :
      IntervalIntegrable g volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have htne : t ≠ 0 := by
      intro heq
      subst t
      exact hzero ht
    have habs : |t| ≠ 0 := abs_ne_zero.mpr htne
    exact (((Real.continuousAt_rpow_const |t| (-(j : ℝ))
      (Or.inl habs)).comp continuous_abs.continuousAt).add
        continuousAt_const).continuousWithinAt
  have hgneg : IntervalIntegrable g volume (-U) (-W) :=
    hInt (-U) (-W) (Set.notMem_uIcc_of_gt (by linarith) (by linarith))
  have hgpos : IntervalIntegrable g volume W U :=
    hInt W U (Set.notMem_uIcc_of_lt hW hU)
  have hneg := intervalIntegral.integral_mono_on (neg_le_neg hWU)
    hfneg (hgneg.const_mul C) (by
      intro t ht
      have htAbs : W ≤ |t| ∧ |t| ≤ U := by
        have htn : t ≤ 0 := by linarith [ht.2]
        rw [abs_of_nonpos htn]
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      exact hbound t htAbs.1 htAbs.2)
  have hpos := intervalIntegral.integral_mono_on hWU
    hfpos (hgpos.const_mul C) (by
      intro t ht
      have htp : 0 ≤ t := by linarith [ht.1]
      have htAbs : W ≤ |t| ∧ |t| ≤ U := by
        rw [abs_of_nonneg htp]
        exact ht
      exact hbound t htAbs.1 htAbs.2)
  rw [smoothLongFactor_frequencyDomain_integral_eq_twoTails W U hW hWU f
    hfneg hfpos]
  have htail := smoothLongFactor_twoTailPlusConstant_le W U δ j hW hWU hδ hj
  simp only [intervalIntegral.integral_const_mul] at hneg hpos
  calc
    (∫ t in -U..-W, f t) + (∫ t in W..U, f t) ≤
      C * ((∫ t in -U..-W, g t) + (∫ t in W..U, g t)) := by
        rw [mul_add]
        exact add_le_add hneg hpos
    _ ≤ C * (2 * (W ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) + 2 * U * δ) := by
      exact mul_le_mul_of_nonneg_left htail hC

#print axioms smoothLongFactor_frequencyDomain_eq_twoTails
#print axioms smoothLongFactor_frequencyDomain_integral_eq_twoTails
#print axioms smoothLongFactor_frequencyDomain_integral_le_envelope

end FractionalPrimes.Literature.DirichletAdapter

end
