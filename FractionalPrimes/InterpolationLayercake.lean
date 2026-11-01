module

public import FractionalPrimes.Operators
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

@[expose] public section

/-!
# Layer-cake identity for discrete complex sequences

This file records the pinned Mathlib layer-cake theorem in the exact norm
notation used by the paper's counting-measure convolution.  It is an analytic
support lemma for the explicit proof of blueprint `lem:interpolation`.
-/

namespace FractionalPrimes

open MeasureTheory
open Filter
open Set
open scoped ENNReal

noncomputable section

/-- For every positive real exponent, the counting-measure `p`-moment of a
complex sequence equals the layer-cake integral of its strict superlevel
sets, with the exact derivative weight `p * t^(p-1)`. -/
theorem integerSequence_lintegral_enorm_rpow_eq_lintegral_meas_lt
    {p : ℝ} (hp : 0 < p) (f : ℤ → ℂ) :
    ∫⁻ k : ℤ, ‖f k‖ₑ ^ p ∂(Measure.count : Measure ℤ) =
      ENNReal.ofReal p *
        ∫⁻ t in Ioi (0 : ℝ),
          Measure.count {k : ℤ | t < ‖f k‖} * ENNReal.ofReal (t ^ (p - 1)) := by
  have h := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
    (Measure.count : Measure ℤ)
    (f := fun k : ℤ => ‖f k‖)
    (Eventually.of_forall fun k => norm_nonneg (f k))
    (measurable_of_countable _).aemeasurable hp
  calc
    ∫⁻ k : ℤ, ‖f k‖ₑ ^ p ∂(Measure.count : Measure ℤ) =
        ∫⁻ k : ℤ, ENNReal.ofReal (‖f k‖ ^ p) ∂(Measure.count : Measure ℤ) := by
          apply lintegral_congr_ae
          filter_upwards with k
          rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
    _ = ENNReal.ofReal p *
        ∫⁻ t in Ioi (0 : ℝ),
          Measure.count {k : ℤ | t < ‖f k‖} * ENNReal.ofReal (t ^ (p - 1)) := h

end

end FractionalPrimes
