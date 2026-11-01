module

public import FractionalPrimes.Literature.JSW.RoughSquareSigmaDomination

/-! The checked smooth maximal comparison on the actual geometric Lp
representatives at arbitrary finite exponents. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

theorem geometricPsiLpConvolution_ae_eq_raw
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p)
    (k : ℤ) (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    (geometricPsiLpConvolution hSupp p b hp k f : ℝ → ℂ) =ᵐ[volume]
      complexMeasureConvolution
        (initialSquareDilateComplexMeasure (initialSquarePsiComplexMeasure σ) (b^k))
        (f : ℝ → ℂ) (Lp.aestronglyMeasurable f) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  letI : IsProbabilityMeasure (initialSquarePsiProbabilityMeasure σ) :=
    initialSquarePsiProbabilityMeasure_isProbability hSupp
  let μ := initialSquareSigmaComplexMeasure
    (Measure.map (fun y : ℝ => b^k*y) (initialSquarePsiProbabilityMeasure σ))
  letI : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    rw [initialSquareSigmaComplexMeasure_variation_eq]
    infer_instance
  have hm : μ = initialSquareDilateComplexMeasure (initialSquarePsiComplexMeasure σ) (b^k) :=
    initialSquarePsiComplexMeasure_map_eq_dilate hSupp (b^k) inferInstance inferInstance
  have h := lpComplexMeasureConvolution_ae_eq_complexMeasureConvolution_of_memLp hp μ f
    (f : ℝ → ℂ) (Lp.stronglyMeasurable f).measurable (Lp.memLp f) Filter.EventuallyEq.rfl
  change (geometricPsiLpConvolution hSupp p b hp k f : ℝ → ℂ) =ᵐ[volume]
    complexMeasureConvolution μ (f : ℝ → ℂ) (Lp.aestronglyMeasurable f) at h
  rw [hm] at h
  exact h

theorem roughSquare_psi_sup_le_lineMaximal
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p) (hb : 1 < b)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    ∀ᵐ x ∂volume,
      (⨆ k : ℤ, ENNReal.ofReal (‖(geometricPsiLpConvolution hSupp p b hp k f : ℝ → ℂ) x‖)) ≤
        ENNReal.ofReal (4 * lpNorm φ ∞ volume) * lineMaximal (f : ℝ → ℂ) x := by
  have hrep := ae_all_iff.mpr (fun k : ℤ =>
    geometricPsiLpConvolution_ae_eq_raw (b := b) hSupp hp k f)
  filter_upwards [hrep] with x hx
  apply iSup_le
  intro k
  rw [hx k]
  exact initialSquarePsiConvolution_maximal_bound_of_memLp hSupp hp
    (f : ℝ → ℂ) (Lp.memLp f) (b^k) (zpow_pos (by linarith) k) x

theorem roughSquare_sigma_sup_le_square_add_lineMaximal
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p) (hb : 1 < b)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (hfinite : ∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal
      (‖(localizedSquareNuLpConvolution hSupp p b hp k f : ℝ → ℂ) x‖^2)) < ∞) :
    ∀ᵐ x ∂volume,
      (⨆ k : ℤ, ENNReal.ofReal (‖(geometricSigmaLpConvolution σ p b hp k f : ℝ → ℂ) x‖)) ≤
      ENNReal.ofReal (Real.sqrt ((∑' j : ℤ, ENNReal.ofReal
        (‖(localizedSquareNuLpConvolution hSupp p b hp j f : ℝ → ℂ) x‖^2)).toReal)) +
        ENNReal.ofReal (4 * lpNorm φ ∞ volume) * lineMaximal (f : ℝ → ℂ) x := by
  filter_upwards [roughSquare_sigma_sup_domination hSupp hp f hfinite,
    roughSquare_psi_sup_le_lineMaximal hSupp hp hb f] with x hs hψ
  exact hs.trans (add_le_add le_rfl hψ)

theorem roughSquare_sigma_sup_finite
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p) (hb : 1 < b)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (hfinite : ∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal
      (‖(localizedSquareNuLpConvolution hSupp p b hp k f : ℝ → ℂ) x‖^2)) < ∞) :
    ∀ᵐ x ∂volume, (⨆ k : ℤ, ENNReal.ofReal
      (‖(geometricSigmaLpConvolution σ p b hp k f : ℝ → ℂ) x‖)) < ∞ := by
  filter_upwards [roughSquare_sigma_sup_le_square_add_lineMaximal hSupp hp hb f hfinite,
    lineMaximal_lt_top_ae_of_memLp hp (Lp.memLp f)] with x hx hline
  exact hx.trans_lt (ENNReal.add_lt_top.mpr
    ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hline⟩)

theorem roughSquare_sigma_sup_real_majorant
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p) (hb : 1 < b)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (hfinite : ∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal
      (‖(localizedSquareNuLpConvolution hSupp p b hp k f : ℝ → ℂ) x‖^2)) < ∞) :
    ∀ᵐ x ∂volume,
      (⨆ k : ℤ, ENNReal.ofReal (‖(geometricSigmaLpConvolution σ p b hp k f : ℝ → ℂ) x‖)).toReal ≤
      Real.sqrt ((∑' j : ℤ, ENNReal.ofReal
        (‖(localizedSquareNuLpConvolution hSupp p b hp j f : ℝ → ℂ) x‖^2)).toReal) +
      (4 * lpNorm φ ∞ volume) * lineMaximalReal (f : ℝ → ℂ) x := by
  filter_upwards [roughSquare_sigma_sup_le_square_add_lineMaximal hSupp hp hb f hfinite,
    lineMaximal_lt_top_ae_of_memLp hp (Lp.memLp f)] with x hx hline
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hline.ne⟩) hx
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hline.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) lpNorm_nonneg)] at h
  exact h

#print axioms roughSquare_sigma_sup_real_majorant
#print axioms roughSquare_sigma_sup_finite
#print axioms geometricPsiLpConvolution_ae_eq_raw
#print axioms roughSquare_psi_sup_le_lineMaximal
#print axioms roughSquare_sigma_sup_le_square_add_lineMaximal
end
end FractionalPrimes.Literature.JSW
end
