module

public import FractionalPrimes.Literature.JSW.RoughSquarePsiDomination

/-! The exact square-plus-smooth maximal norm estimate. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def geometricNuSquareFunction
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p) (b : ℝ)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) (x : ℝ) : ℝ :=
  Real.sqrt ((∑' j : ℤ, ENNReal.ofReal
    (‖(localizedSquareNuLpConvolution hSupp p b hp j f : ℝ → ℂ) x‖^2)).toReal)

def geometricSigmaLpMaximalReal
    (σ : Measure ℝ) [IsProbabilityMeasure σ] {p : ℝ} (hp : 1 < p) (b : ℝ)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) (x : ℝ) : ℝ :=
  (⨆ k : ℤ, ENNReal.ofReal (‖(geometricSigmaLpConvolution σ p b hp k f : ℝ → ℂ) x‖)).toReal

theorem roughSquare_sigma_maximal_norm_of_square
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {p b K : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1) (hp : 1 < p) (hb : 1 < b) (hK : 0 ≤ K)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ))
    (hfinite : ∀ᵐ x ∂volume, (∑' k : ℤ, ENNReal.ofReal
      (‖(localizedSquareNuLpConvolution hSupp p b hp k f : ℝ → ℂ) x‖^2)) < ∞)
    (hSquare : eLpNorm (geometricNuSquareFunction hSupp hp b f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (K * ‖f‖)) :
    eLpNorm (geometricSigmaLpMaximalReal σ hp b f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (K + (4 * lpNorm φ ∞ volume) *
        ((6*p*2^(p-1)/(p-1))^(1/p))) * eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) volume := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let M := geometricSigmaLpMaximalReal σ hp b f
  let S := geometricNuSquareFunction hSupp hp b f
  let C : ℝ := 4 * lpNorm φ ∞ volume
  let H : ℝ := (6*p*2^(p-1)/(p-1))^(1/p)
  have hC : 0 ≤ C := mul_nonneg (by norm_num) lpNorm_nonneg
  have hH : 0 ≤ H := Real.rpow_nonneg (by
    have hp0 : 0 < p := by linarith
    have hd : 0 < p-1 := by linarith
    positivity) _
  have hM : Measurable M := by
    apply ENNReal.measurable_toReal.comp
    apply Measurable.iSup
    intro k
    exact ENNReal.continuous_ofReal.measurable.comp
      (Lp.stronglyMeasurable (geometricSigmaLpConvolution σ p b hp k f)).measurable.norm
  have hdom := roughSquare_sigma_sup_real_majorant hSupp hp hb f hfinite
  have hmono : eLpNorm M (ENNReal.ofReal p) volume ≤
      eLpNorm (S + C • lineMaximalReal (f : ℝ → ℂ)) (ENNReal.ofReal p) volume := by
    apply eLpNorm_mono_ae_real hM.aestronglyMeasurable
    filter_upwards [hdom] with x hx
    change ‖M x‖ ≤ _
    have hM0 : 0 ≤ M x := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hM0]
    exact hx
  have hinput : ENNReal.ofReal ‖f‖ = eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) volume := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp f).eLpNorm_ne_top]
  rw [ENNReal.ofReal_mul hK, hinput] at hSquare
  calc
    _ ≤ _ := hmono
    _ ≤ eLpNorm S (ENNReal.ofReal p) volume +
        eLpNorm (C • lineMaximalReal (f : ℝ → ℂ)) (ENNReal.ofReal p) volume := eLpNorm_add_le
          (ENNReal.one_le_ofReal.mpr hp.le)
    _ = eLpNorm S (ENNReal.ofReal p) volume +
        ENNReal.ofReal C * eLpNorm (lineMaximalReal (f : ℝ → ℂ)) (ENNReal.ofReal p) volume := by
      rw [eLpNorm_const_smul, Real.enorm_of_nonneg hC]
    _ ≤ ENNReal.ofReal K * eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) volume +
        ENNReal.ofReal C * (ENNReal.ofReal H * eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) volume) :=
      add_le_add hSquare (mul_le_mul_of_nonneg_left
        (lineMaximal_strongLp hp (Lp.memLp f)) (by positivity))
    _ = _ := by
      rw [← mul_assoc, ← add_mul, ← ENNReal.ofReal_mul hC,
        ← ENNReal.ofReal_add hK (mul_nonneg hC hH)]

theorem roughSquare_sigma_maximal_stage_norm
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β D b q p : ℝ}
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    (hσ : MeasureSplittingBounds σ β D) (hb : 1 < b) (hβ : 0 < β) (hq : 1 < q)
    (hMax : ∀ s : ℝ, q < s →
      ∃ B : ℝ, 0 ≤ B ∧ GeometricAdjointMaximalBound σ b s B)
    (hp : 1 < p) (hr : |p⁻¹ - (2 : ℝ)⁻¹| < (2*q)⁻¹) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
      eLpNorm (geometricSigmaLpMaximalReal σ hp b f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal B * eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) volume := by
  obtain ⟨K, hK, hfull⟩ := roughSquare_full_stage_bound_all hSupp hσ hb hβ hq hMax hp hr
  refine ⟨K + (4 * lpNorm φ ∞ volume) * ((6*p*2^(p-1)/(p-1))^(1/p)), ?_, ?_⟩
  · have hp0 : 0 < p := by linarith
    have hd : 0 < p-1 := by linarith
    apply add_nonneg hK
    apply mul_nonneg (mul_nonneg (by norm_num) lpNorm_nonneg)
    exact Real.rpow_nonneg (by positivity) _
  · intro f
    exact roughSquare_sigma_maximal_norm_of_square hSupp hp hb hK f
      (hfull f).1 (hfull f).2

#print axioms roughSquare_sigma_maximal_stage_norm
#print axioms roughSquare_sigma_maximal_norm_of_square
end
end FractionalPrimes.Literature.JSW
end
