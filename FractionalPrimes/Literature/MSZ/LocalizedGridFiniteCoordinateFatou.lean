module

public import FractionalPrimes.Literature.MSZ.LocalizedGridCountableFatouCore

@[expose] public section

namespace FractionalPrimes.Literature.MSZ

open MeasureTheory Filter
open scoped ENNReal Topology

/-! A finite-coordinate continuity adapter for the last Fatou passage in
`lm:finiteVariationEstimate`. The finite coordinate type is instantiated in
the application by the scale interval times the level-`l` increment indices. -/

/-- Coordinatewise convergence of finite complex vectors gives convergence of
their Euclidean square-function norm, so any uniform counting-measure
`eLpNorm` bound for the finite approximants passes to the limit. -/
theorem msz_counting_eLpNorm_finiteSquare_le_of_coordinatewise_limit
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞}
    (approximant : ℕ → ℤ → ι → ℂ) (limit : ℤ → ι → ℂ)
    (C : ℝ≥0∞)
    (hbound : ∀ J,
      eLpNorm
        (fun x : ℤ => Real.sqrt (∑ i : ι, ‖approximant J x i‖ ^ 2))
        p (Measure.count : Measure ℤ) ≤ C)
    (hcoordinate : ∀ i : ι, ∀ x : ℤ,
      Tendsto (fun J : ℕ => approximant J x i) atTop (𝓝 (limit x i))) :
    eLpNorm
      (fun x : ℤ => Real.sqrt (∑ i : ι, ‖limit x i‖ ^ 2))
      p (Measure.count : Measure ℤ) ≤ C := by
  have hSquareNorm :
      Continuous (fun v : ι → ℂ => Real.sqrt (∑ i : ι, ‖v i‖ ^ 2)) := by
    fun_prop
  refine msz_counting_eLpNorm_le_of_pointwise_limit_core
    (fun J x => Real.sqrt (∑ i : ι, ‖approximant J x i‖ ^ 2))
    (fun x => Real.sqrt (∑ i : ι, ‖limit x i‖ ^ 2)) C hbound ?_
  intro x
  have hcoordinateVector :
      Tendsto (fun J : ℕ => approximant J x) atTop (𝓝 (limit x)) :=
    tendsto_pi_nhds.mpr (fun i => hcoordinate i x)
  exact hSquareNorm.continuousAt.tendsto.comp hcoordinateVector

end FractionalPrimes.Literature.MSZ

end
