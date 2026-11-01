module

public import FractionalPrimes.Literature.JSW.PositiveGeometricNuReciprocalRegion

/-! The source reciprocal-region diagonal theorem on genuine `Lp` inputs. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- The finite-family reciprocal-region ν estimate in the exact `Lp`
format used by the localized-square bootstrap. -/
theorem geometricNuDiagonalLpBoundFromMaximal
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {b q₀ : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hb : 1 < b) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    {p : ℝ} (hp : 1 < p)
    (hregion : |p⁻¹ - (2 : ℝ)⁻¹| < (2 * q₀)⁻¹) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type*} [Fintype ι] (κ : ι → ℤ)
        (G : ι → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)),
        lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i : ι =>
          (localizedSquareNuLpConvolution hSupp p b hp (κ i) (G i) : ℝ → ℂ) x))
          (ENNReal.ofReal p) volume ≤
          C * lpNorm (fun x : ℝ => WithLp.toLp 2
            (fun i : ι => (G i : ℝ → ℂ) x))
            (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hbound⟩ :=
    geometricNuDiagonalBoundFromMaximal hSupp hb hq₀ hMax hp hregion
  refine ⟨C, hC, ?_⟩
  intro ι _ κ G
  let f : ι → ℝ → ℂ := fun i x => (G i : ℝ → ℂ) x
  have hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume := by
    intro i
    exact Lp.memLp (G i)
  have hstrong : ∀ i, StronglyMeasurable (f i) := by
    intro i
    exact Lp.stronglyMeasurable (G i)
  have h := hbound κ f hf hstrong
  simpa only [f, Lp.toLp_coeFn] using h

#print axioms geometricNuDiagonalLpBoundFromMaximal

end

end FractionalPrimes.Literature.JSW

end
