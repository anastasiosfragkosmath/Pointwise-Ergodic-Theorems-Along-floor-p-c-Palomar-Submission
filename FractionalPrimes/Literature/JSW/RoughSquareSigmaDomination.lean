module

public import FractionalPrimes.Literature.JSW.RoughSquarePointwiseDomination

/-! The source σ = ν + ψ pointwise comparison at arbitrary finite Lp. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def geometricSigmaLpConvolution
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (p b : ℝ) (hp : 1 < p)
    (k : ℤ) (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let μ := initialSquareSigmaComplexMeasure (Measure.map (fun y : ℝ => b^k*y) σ)
  letI : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    rw [initialSquareSigmaComplexMeasure_variation_eq]
    infer_instance
  exact lpComplexMeasureConvolution (ENNReal.ofReal p) μ f

def geometricPsiLpConvolution
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (p b : ℝ) (hp : 1 < p)
    (k : ℤ) (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  letI : IsProbabilityMeasure (initialSquarePsiProbabilityMeasure σ) :=
    initialSquarePsiProbabilityMeasure_isProbability hSupp
  let μ := initialSquareSigmaComplexMeasure
    (Measure.map (fun y : ℝ => b^k*y) (initialSquarePsiProbabilityMeasure σ))
  letI : IsFiniteMeasure μ.variation := by
    dsimp [μ]
    rw [initialSquareSigmaComplexMeasure_variation_eq]
    infer_instance
  exact lpComplexMeasureConvolution (ENNReal.ofReal p) μ f

theorem geometricSigmaLpConvolution_eq_nu_add_psi
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p)
    (k : ℤ) (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    geometricSigmaLpConvolution σ p b hp k f =
      localizedSquareNuLpConvolution hSupp p b hp k f +
        geometricPsiLpConvolution hSupp p b hp k f := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have h : localizedSquareNuLpConvolution hSupp p b hp k f =
      geometricSigmaLpConvolution σ p b hp k f -
        geometricPsiLpConvolution hSupp p b hp k f :=
    geometricNuLpConvolution_eq_positive_sub hSupp hp k f
  rw [h]
  abel

theorem roughSquare_sigma_scale_domination
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (hfinite : ∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal
      (‖(localizedSquareNuLpConvolution hSupp p b hp k f : ℝ → ℂ) x‖^2)) < ∞) :
    ∀ᵐ x ∂volume, ∀ k : ℤ,
      ‖(geometricSigmaLpConvolution σ p b hp k f : ℝ → ℂ) x‖ ≤
      Real.sqrt ((∑' j : ℤ, ENNReal.ofReal
        (‖(localizedSquareNuLpConvolution hSupp p b hp j f : ℝ → ℂ) x‖^2)).toReal) +
      ‖(geometricPsiLpConvolution hSupp p b hp k f : ℝ → ℂ) x‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hsplit : ∀ k : ℤ, ∀ᵐ x ∂volume,
      (geometricSigmaLpConvolution σ p b hp k f : ℝ → ℂ) x =
      (localizedSquareNuLpConvolution hSupp p b hp k f : ℝ → ℂ) x +
        (geometricPsiLpConvolution hSupp p b hp k f : ℝ → ℂ) x := by
    intro k
    have h := Lp.ext_iff.mp (geometricSigmaLpConvolution_eq_nu_add_psi (b := b) hSupp hp k f)
    exact h.trans (Lp.coeFn_add _ _)
  have hnu := roughSquare_all_scales_le_full_square
    (fun k => localizedSquareNuLpConvolution hSupp p b hp k f) hfinite
  filter_upwards [ae_all_iff.mpr hsplit, hnu] with x hs hn
  intro k
  rw [hs k]
  exact (norm_add_le _ _).trans (add_le_add (hn k) le_rfl)

theorem roughSquare_sigma_sup_domination
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p b : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (hfinite : ∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal
      (‖(localizedSquareNuLpConvolution hSupp p b hp k f : ℝ → ℂ) x‖^2)) < ∞) :
    ∀ᵐ x ∂volume,
      (⨆ k : ℤ, ENNReal.ofReal (‖(geometricSigmaLpConvolution σ p b hp k f : ℝ → ℂ) x‖)) ≤
      ENNReal.ofReal (Real.sqrt ((∑' j : ℤ, ENNReal.ofReal
        (‖(localizedSquareNuLpConvolution hSupp p b hp j f : ℝ → ℂ) x‖^2)).toReal)) +
      ⨆ k : ℤ, ENNReal.ofReal (‖(geometricPsiLpConvolution hSupp p b hp k f : ℝ → ℂ) x‖) := by
  filter_upwards [roughSquare_sigma_scale_domination hSupp hp f hfinite] with x hx
  apply iSup_le
  intro k
  exact (ENNReal.ofReal_le_ofReal (hx k)).trans
    (ENNReal.ofReal_add_le.trans (add_le_add le_rfl
      (le_iSup (fun j : ℤ => ENNReal.ofReal
        (‖(geometricPsiLpConvolution hSupp p b hp j f : ℝ → ℂ) x‖)) k)))

#print axioms roughSquare_sigma_sup_domination
#print axioms geometricSigmaLpConvolution_eq_nu_add_psi
#print axioms roughSquare_sigma_scale_domination
end
end FractionalPrimes.Literature.JSW
end
