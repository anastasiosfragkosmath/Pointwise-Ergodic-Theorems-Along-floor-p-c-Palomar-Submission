module

public import FractionalPrimes.Literature.JSW.PositiveGeometricNuOfMaximal

/-! Restrict an all-integer-scale positive maximal bound to a finite
geometric family without changing its constant. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

/-- The all-scale positive maximal majorant used in `lj:positivity`.
The `+y` convention is the adjoint convolution convention in the
finite-vector energy pairing. -/
def GeometricAdjointMaximalBound
    (σ : Measure ℝ) (b q B : ℝ) : Prop :=
  ∀ g : ℝ → ℝ, MemLp g (ENNReal.ofReal q) volume →
    ∃ M : ℝ → ℝ,
      MemLp M (ENNReal.ofReal q) volume ∧
      (∀ x, 0 ≤ M x) ∧
      (∀ᵐ x ∂volume, ∀ k : ℤ,
        (∫ y, g (x + y) ∂Measure.map (fun y : ℝ => b ^ k * y) σ) ≤ M x) ∧
      lpNorm M (ENNReal.ofReal q) volume ≤
        B * lpNorm g (ENNReal.ofReal q) volume

/-- The same all-scale witness controls every selected finite list of
geometric scales, with no dependence on the list or its indexing map. -/
theorem geometricAdjointMaximalBound_finite
    {ι : Type*} [Fintype ι]
    {σ : Measure ℝ} {b q B : ℝ}
    (hMax : GeometricAdjointMaximalBound σ b q B)
    (κ : ι → ℤ) (g : ℝ → ℝ)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    ∃ M : ℝ → ℝ,
      MemLp M (ENNReal.ofReal q) volume ∧
      (∀ x, 0 ≤ M x) ∧
      (∀ᵐ x ∂volume, ∀ i,
        (∫ y, g (x + y) ∂Measure.map (fun y : ℝ => b ^ κ i * y) σ) ≤ M x) ∧
      lpNorm M (ENNReal.ofReal q) volume ≤
        B * lpNorm g (ENNReal.ofReal q) volume := by
  obtain ⟨M, hM, hnonneg, hdom, hnorm⟩ := hMax g hg
  refine ⟨M, hM, hnonneg, ?_, hnorm⟩
  filter_upwards [hdom] with x hx
  intro i
  exact hx (κ i)

#print axioms geometricAdjointMaximalBound_finite

end FractionalPrimes.Literature.JSW

end
