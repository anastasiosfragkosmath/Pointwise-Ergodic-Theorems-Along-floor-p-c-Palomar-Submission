module

public import FractionalPrimes.Literature.JSW.PositiveGeometricNuLpRegion
public import FractionalPrimes.Literature.JSW.LocalizedSquareDecay

/-! The conditional localized square estimate obtained from the source
geometric ν diagonal range. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- At any bootstrap stage with positive maximal bounds above `q₀`, the
localized ν square family has the exact product of the diagonal and
Littlewood--Paley constants throughout the approved reciprocal region. -/
theorem localizedSquareLpBoundFromMaximal
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {b q₀ : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hb : 1 < b) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    {p : ℝ} (hp : 1 < p)
    (hregion : |p⁻¹ - (2 : ℝ)⁻¹| < (2 * q₀)⁻¹) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (j : ℤ) (F : Finset ℤ)
        (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)),
        lpNorm (fun x : ℝ => WithLp.toLp 2
          (fun k : {k : ℤ // k ∈ F} =>
            (localizedSquareNuLpConvolution hSupp p b hp k.1
              (littlewoodPaleyProjectionLp hb hp (k.1 + j) f) : ℝ → ℂ) x))
          (ENNReal.ofReal p) volume ≤
        C * littlewoodPaleyUpperConstant p b
          (ne_of_gt (by linarith : 0 < b)) * ‖f‖ := by
  obtain ⟨C, hC, hdiag⟩ :=
    geometricNuDiagonalLpBoundFromMaximal hSupp hb hq₀ hMax hp hregion
  let B : NNReal := ⟨C, hC.le⟩
  refine ⟨C, hC, ?_⟩
  intro j F f
  have hdiag' : ∀ (F : Finset ℤ)
      (g : {k : ℤ // k ∈ F} →
        Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)),
      lpNorm (fun x : ℝ => WithLp.toLp 2 (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp p b hp k.1 (g k) : ℝ → ℂ) x))
        (ENNReal.ofReal p) volume ≤
      (B : ℝ) * lpNorm (fun x : ℝ => WithLp.toLp 2
        (fun k : {k : ℤ // k ∈ F} => (g k : ℝ → ℂ) x))
        (ENNReal.ofReal p) volume := by
    intro F g
    change lpNorm (fun x : ℝ => WithLp.toLp 2
      (fun k : {k : ℤ // k ∈ F} =>
        (localizedSquareNuLpConvolution hSupp p b hp k.1 (g k) : ℝ → ℂ) x))
      (ENNReal.ofReal p) volume ≤
      C * lpNorm (fun x : ℝ => WithLp.toLp 2
        (fun k : {k : ℤ // k ∈ F} => (g k : ℝ → ℂ) x))
        (ENNReal.ofReal p) volume
    exact hdiag (κ := fun k : {k : ℤ // k ∈ F} => k.1) g
  have hbound := localizedSquare_finite_lp_bound_of_diagonal
    hSupp hb hp B hdiag' j F f
  change _ ≤ C * littlewoodPaleyUpperConstant p b
    (ne_of_gt (by linarith : 0 < b)) * ‖f‖ at hbound
  exact hbound

#print axioms localizedSquareLpBoundFromMaximal

end

end FractionalPrimes.Literature.JSW

end
