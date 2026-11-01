module

public import FractionalPrimes.Literature.JSW.SmoothPsiL1Translation
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The exact inverse-scale L1 translation modulus of the actual smooth density. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FractionalPrimes.Literature.JSW
noncomputable section

def smoothPsiDilatedDensity
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (τ x : ℝ) : ℝ :=
  τ⁻¹*measureSplittingPsi σ (x/τ)

theorem smoothPsiDilatedDensity_L1_translation
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hSupp : σ.support ⊆ Set.Icc (-(1 : ℝ)) 1)
    {τ : ℝ} (hτ : 0 < τ) (y c : ℝ) :
    Integrable (fun x : ℝ => smoothPsiDilatedDensity σ τ (x-y)-
      smoothPsiDilatedDensity σ τ (x-c)) volume ∧
    lpNorm (fun x : ℝ => smoothPsiDilatedDensity σ τ (x-y)-
      smoothPsiDilatedDensity σ τ (x-c)) 1 volume ≤
      (|y-c|/τ)*lpNorm (deriv φ) 1 volume := by
  let G : ℝ → ℝ := fun z => measureSplittingPsi σ (z-y/τ)-measureSplittingPsi σ (z-c/τ)
  obtain ⟨hGint,hGbound⟩ := measureSplittingPsi_L1_translation hSupp (y/τ) (c/τ)
  have hscaled : Integrable (fun x : ℝ => τ⁻¹*G (τ⁻¹*x)) volume :=
    (hGint.comp_mul_left' (inv_ne_zero hτ.ne')).const_mul _
  have hfun : (fun x : ℝ => smoothPsiDilatedDensity σ τ (x-y)-
      smoothPsiDilatedDensity σ τ (x-c)) = fun x : ℝ => τ⁻¹*G (τ⁻¹*x) := by
    funext x
    dsimp [smoothPsiDilatedDensity, G]
    rw [show (x-y)/τ = τ⁻¹*x-y/τ by ring, show (x-c)/τ = τ⁻¹*x-c/τ by ring]
    ring
  have hnorm : lpNorm (fun x : ℝ => smoothPsiDilatedDensity σ τ (x-y)-
      smoothPsiDilatedDensity σ τ (x-c)) 1 volume = lpNorm G 1 volume := by
    rw [hfun, lpNorm_one_eq_integral_norm hscaled.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hGint.aestronglyMeasurable]
    simp only [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hτ]
    rw [integral_const_mul]
    have hcomp := Measure.integral_comp_mul_left (fun z : ℝ => |G z|) τ⁻¹
    simp only [inv_inv, abs_of_pos hτ, smul_eq_mul] at hcomp
    rw [hcomp]
    field_simp
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [G]
    rw [show (τ*z-y)/τ = z-y/τ by field_simp,
      show (τ*z-c)/τ = z-c/τ by field_simp]
  refine ⟨hfun ▸ hscaled, ?_⟩
  rw [hnorm]
  calc
    _ ≤ |y/τ-c/τ| * lpNorm (deriv φ) 1 volume := hGbound
    _ = _ := by rw [← sub_div, abs_div, abs_of_pos hτ]

#print axioms smoothPsiDilatedDensity_L1_translation
end
end FractionalPrimes.Literature.JSW
end
