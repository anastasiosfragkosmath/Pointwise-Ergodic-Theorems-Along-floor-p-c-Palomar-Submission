module

public import FractionalPrimes.Literature.JSW.RoughSquareEnergyIdentity

/-! The existing Hilbert estimate in the same source square representation
as the non-Hilbert bootstrap stages. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem roughSquareHilbertEnergy_finite
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ᵐ x ∂volume, initialSquareInfiniteConvolutionEnergy hSupp hσ b f x < ∞ := by
  have hm : Measurable (initialSquareInfiniteConvolutionEnergy hSupp hσ b f) := by
    apply Measurable.ennreal_tsum
    intro k
    exact ENNReal.continuous_ofReal.measurable.comp
      ((Lp.stronglyMeasurable (initialSquareNuConvolution hSupp hσ b k f)).measurable.norm.pow_const 2)
  exact ae_lt_top hm ((initialSquare_infinite_convolution_energy_bound
    hSupp hσ hb hβ f).trans_lt ENNReal.ofReal_lt_top).ne

private theorem roughSquare_full_hilbert_at
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P = 2)
    (f : Lp ℂ P (volume : Measure ℝ)) :
    let v : ℤ → Lp ℂ (P) (volume : Measure ℝ) :=
      fun k => geometricNuLpConvolutionAt hSupp P b k f
    (∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)) < ∞) ∧
    eLpNorm (fun x => Real.sqrt ((∑' k : ℤ,
      ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)).toReal)) P volume ≤
      ENNReal.ofReal (((2*Real.pi+2*|D|) *
        Real.sqrt (1/(1-b⁻¹^2)+1/(1-Real.rpow b (-2*β)))) * ‖f‖) := by
  subst P
  change (∀ᵐ x ∂volume, initialSquareInfiniteConvolutionEnergy hSupp hσ b f x < ∞) ∧
    eLpNorm (initialSquareConvolutionSquareFunction hSupp hσ b f) 2 volume ≤ _
  exact ⟨roughSquareHilbertEnergy_finite hSupp hσ hb hβ f,
    by simpa only [ENNReal.ofReal_ofNat] using
      initialSquare_square_function_L2_bound hSupp hσ hb hβ f⟩

theorem roughSquare_full_hilbert_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β)
    (f : Lp ℂ (ENNReal.ofReal (2 : ℝ)) (volume : Measure ℝ)) :
    let v : ℤ → Lp ℂ (ENNReal.ofReal (2 : ℝ)) (volume : Measure ℝ) :=
      fun k => localizedSquareNuLpConvolution hSupp 2 b (by norm_num) k f
    (∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)) < ∞) ∧
    eLpNorm (fun x => Real.sqrt ((∑' k : ℤ,
      ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)).toReal)) (ENNReal.ofReal 2) volume ≤
      ENNReal.ofReal (((2*Real.pi+2*|D|) *
        Real.sqrt (1/(1-b⁻¹^2)+1/(1-Real.rpow b (-2*β)))) * ‖f‖) := by
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have h := roughSquare_full_hilbert_at hSupp hσ hb hβ
    (P := ENNReal.ofReal (2 : ℝ)) (by norm_num) f
  simpa only [geometricNuLpConvolutionAt, localizedSquareNuLpConvolution] using h

theorem roughSquare_full_stage_bound_all
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq : 1 < q)
    (hMax : ∀ s : ℝ, q < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hp : 1 < p)
    (hr : |p⁻¹ - (2 : ℝ)⁻¹| < (2*q)⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      let v : ℤ → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
        fun k => localizedSquareNuLpConvolution hSupp p b hp k f
      (∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)) < ∞) ∧
      eLpNorm (fun x => Real.sqrt ((∑' k : ℤ,
        ENNReal.ofReal (‖(v k : ℝ → ℂ) x‖^2)).toReal))
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (K * ‖f‖) := by
  by_cases hp2 : p = 2
  · subst p
    refine ⟨(2*Real.pi+2*|D|) *
      Real.sqrt (1/(1-b⁻¹^2)+1/(1-Real.rpow b (-2*β))), ?_, ?_⟩
    · exact mul_nonneg (by nlinarith [Real.pi_pos, abs_nonneg D]) (Real.sqrt_nonneg _)
    · intro f
      exact roughSquare_full_hilbert_bound hSupp hσ hb hβ f
  · exact roughSquare_full_stage_bound hSupp hσ hb hβ hq hMax hp hp2 hr

#print axioms roughSquare_full_stage_bound_all
#print axioms roughSquareHilbertEnergy_finite
#print axioms roughSquare_full_hilbert_bound
end
end FractionalPrimes.Literature.JSW
end
