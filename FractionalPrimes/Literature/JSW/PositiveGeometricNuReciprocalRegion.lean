module

public import FractionalPrimes.Literature.JSW.PositiveGeometricNuFromSigmaMaximal
public import FractionalPrimes.Literature.JSW.PositiveNuHilbertExponentBridge
public import FractionalPrimes.Literature.JSW.PositiveExponentCriterion

/-! The conditional geometric ν diagonal bound on the exact reciprocal
region used at each stage of the rough-square bootstrap. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FractionalPrimes.Literature.JSW

noncomputable section

/-- If the positive geometric σ maximal operator has a bound at every
exponent above `q₀`, the source geometric cancellation vector has a
uniform finite-family bound throughout the approved reciprocal region.
The constant may depend on `p` and the positive maximal bound, but not on
the finite family or its geometric scale choices. -/
theorem geometricNuDiagonalBoundFromMaximal
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {b q₀ : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hb : 1 < b) (hq₀ : 1 < q₀)
    (hMax : ∀ s : ℝ, q₀ < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    {p : ℝ} (hp : 1 < p)
    (hregion : |p⁻¹ - (2 : ℝ)⁻¹| < (2 * q₀)⁻¹) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type*} [Fintype ι] (κ : ι → ℤ) (f : ι → ℝ → ℂ)
        (hf : ∀ i, MemLp (f i) (ENNReal.ofReal p) volume)
        (hstrong : ∀ i, StronglyMeasurable (f i)),
        lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i : ι =>
          (localizedSquareNuLpConvolution hSupp p b hp (κ i)
            ((hf i).toLp (f i)) : ℝ → ℂ) x))
          (ENNReal.ofReal p) volume ≤
          C * lpNorm (fun x : ℝ => WithLp.toLp 2 (fun i => f i x))
            (ENNReal.ofReal p) volume := by
  by_cases hlow : p < 2
  · have hp0 : 0 < p := by linarith
    have hpm1 : 0 < p - 1 := by linarith
    have h2mp : 0 < 2 - p := by linarith
    have hs : q₀ < p / (2 - p) :=
      (lower_maximal_exponent_criterion hp hlow hq₀).2 hregion
    obtain ⟨B, hB, hMB⟩ := hMax (p / (2 - p)) hs
    let C₀ : ℝ := Real.sqrt B +
      Real.sqrt (geometricPsiMaximalConstant (p / (2 - p)))
    let C : ℝ := max 1 C₀
    have hCpos : 0 < C :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
    have hC₀le : C₀ ≤ C := le_max_right _ _
    have hpq : p.HolderConjugate (p / (p - 1)) := by
      refine ⟨?_, hp0, div_pos hp0 hpm1⟩
      field_simp
      ring
    have hq : 2 < p / (p - 1) := by
      apply (lt_div_iff₀ hpm1).2
      nlinarith
    have hqs : ((p / (p - 1)) / 2).HolderConjugate
        (p / (2 - p)) := by
      refine ⟨?_, div_pos (div_pos hp0 hpm1) (by norm_num),
        div_pos hp0 h2mp⟩
      field_simp
      ring
    refine ⟨C, hCpos, ?_⟩
    intro ι _ κ f hf hstrong
    have hbound := finiteGeometricNuVector_lower_of_sigmaMaximal
      hSupp hb hp hpq hq hqs hB hMB κ f hf hstrong
    exact hbound.trans (mul_le_mul_of_nonneg_right hC₀le lpNorm_nonneg)
  · by_cases heq : p = 2
    · subst p
      refine ⟨2, by norm_num, ?_⟩
      intro ι _ κ f hf hstrong
      exact finiteGeometricNuVector_two_ofReal_bound hSupp b κ f hf
    · have hhigh : 2 < p := lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm heq)
      have hp0 : 0 < p := by linarith
      have hpm2 : 0 < p - 2 := by linarith
      have hq : q₀ < p / (p - 2) :=
        (upper_maximal_exponent_criterion hhigh hq₀).2 hregion
      obtain ⟨B, hB, hMB⟩ := hMax (p / (p - 2)) hq
      let C₀ : ℝ := Real.sqrt B +
        Real.sqrt (geometricPsiMaximalConstant (p / (p - 2)))
      let C : ℝ := max 1 C₀
      have hCpos : 0 < C :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
      have hC₀le : C₀ ≤ C := le_max_right _ _
      have hpq : (p / 2).HolderConjugate (p / (p - 2)) := by
        refine ⟨?_, div_pos hp0 (by norm_num), div_pos hp0 hpm2⟩
        field_simp
        ring
      refine ⟨C, hCpos, ?_⟩
      intro ι _ κ f hf hstrong
      have hbound := finiteGeometricNuVector_upper_of_sigmaMaximal
        hSupp hb hhigh hpq hB hMB κ f hf hstrong
      exact hbound.trans (mul_le_mul_of_nonneg_right hC₀le lpNorm_nonneg)

#print axioms geometricNuDiagonalBoundFromMaximal

end

end FractionalPrimes.Literature.JSW

end
