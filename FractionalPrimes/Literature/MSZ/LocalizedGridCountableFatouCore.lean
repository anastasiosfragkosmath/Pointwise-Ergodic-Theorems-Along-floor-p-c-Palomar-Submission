module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.Basic
public import FractionalPrimes.Operators

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory Filter
open scoped ENNReal Topology

/-- Counting-measure Fatou passage for a pointwise-convergent sequence of
real-valued functions on the integers, with a uniform extended Lp bound. -/
theorem msz_counting_eLpNorm_le_of_pointwise_limit_core
    {p : ℝ≥0∞} (approximant : ℕ → ℤ → ℝ) (limit : ℤ → ℝ)
    (C : ℝ≥0∞)
    (hbound : ∀ J,
      eLpNorm (approximant J) p (Measure.count : Measure ℤ) ≤ C)
    (hpoint : ∀ x : ℤ,
      Tendsto (fun J : ℕ => approximant J x) atTop (𝓝 (limit x))) :
    eLpNorm limit p (Measure.count : Measure ℤ) ≤ C := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (Filter.Eventually.of_forall hbound)
    (fun J => (measurable_of_countable (approximant J)).aestronglyMeasurable)
    (measurable_of_countable limit).aestronglyMeasurable
  exact ae_count_int_iff_forall.mpr hpoint

end FractionalPrimes.Literature.MSZ

end

