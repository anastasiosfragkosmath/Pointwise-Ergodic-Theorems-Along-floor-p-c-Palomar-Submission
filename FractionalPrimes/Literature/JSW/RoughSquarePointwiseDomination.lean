module

public import FractionalPrimes.Literature.JSW.RoughSquareHilbertStage

/-! Pointwise scale domination for the maximal-stage improvement. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW

theorem roughSquare_all_scales_le_full_square
    {p : ℝ≥0∞} (v : ℤ → Lp ℂ p (volume : Measure ℝ))
    (hfinite : ∀ᵐ x ∂volume,
      (∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)) < ∞) :
    ∀ᵐ x ∂volume, ∀ k : ℤ, ‖(v k : ℝ → ℂ) x‖ ≤
      Real.sqrt ((∑' j : ℤ, ENNReal.ofReal (‖(v j : ℝ → ℂ) x‖^2)).toReal) := by
  filter_upwards [hfinite] with x hx
  intro k
  have ht : ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2) ≤
      ∑' j : ℤ, ENNReal.ofReal (‖(v j : ℝ → ℂ) x‖^2) :=
    ENNReal.le_tsum (f := fun j : ℤ => ENNReal.ofReal (‖(v j : ℝ → ℂ) x‖^2)) k
  have hr := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hx.ne).mpr ht
  rw [ENNReal.toReal_ofReal (sq_nonneg _)] at hr
  have hroot := Real.sqrt_le_sqrt hr
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hroot

#print axioms roughSquare_all_scales_le_full_square
end FractionalPrimes.Literature.JSW
end
