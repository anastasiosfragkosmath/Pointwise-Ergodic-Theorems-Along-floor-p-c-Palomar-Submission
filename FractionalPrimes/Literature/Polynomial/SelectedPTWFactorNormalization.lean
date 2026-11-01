module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedDyadicPTWSourceAssembly
public import FractionalPrimes.Literature.Twisted.PTWDivisorLogarithmicBounds
public import Mathlib.Tactic
@[expose] public section
noncomputable section
namespace FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity

/-- Literal factor/allocation normalization in the source PTW integral bound. -/
theorem selectedPTWFactorNormalization
    {X a : ℝ} (hX : 3 ≤ X) {d : ℕ} (hd : 0 < d)
    (hdlog : (d : ℝ) ≤ (Real.log X) ^ a) :
    (divisorFunction 3 ⟨d, hd⟩ : ℝ) / (d : ℝ) *
        (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
          selectedPTWFactorScale X d) ≤
      ((2 : ℝ) ^ 36 * divisorSubpowerConstant 60 (1 / 1000 : ℝ) *
        divisorSubpowerConstant 3 (1 / 1000 : ℝ)) *
          (Real.log X) ^ (3 + a / 500) := by
  let L := Real.log X
  let τ : ℝ := divisorFunction 2 ⟨d, hd⟩
  have hL : 0 < L := Real.log_pos (by linarith [hX])
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hlog : Real.log (8 * X) ≤ 4 * L := by
    have hp : (8 : ℝ) ≤ X ^ 3 := by
      calc
        8 ≤ (3 : ℝ) ^ 3 := by norm_num
        _ ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
    have harg : 8 * X ≤ X ^ 4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ X) (sub_nonneg.mpr hp)]
    have h := Real.log_le_log (by positivity : 0 < 8 * X) harg
    simpa [Real.log_pow, L] using h
  have hscale : selectedPTWFactorScale X d ≤ (2 : ℝ) ^ 12 * L * τ ^ 20 := by
    unfold selectedPTWFactorScale
    rw [divisorCoefficient_eq_divisorFunction 2 d hd]
    calc
      _ ≤ (2 : ℝ) ^ 10 * (4 * L) * τ ^ 20 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
      _ = _ := by ring
  have hscale0 : 0 ≤ selectedPTWFactorScale X d := by
    unfold selectedPTWFactorScale
    have : 0 ≤ Real.log (8 * X) := Real.log_nonneg (by linarith [hX])
    positivity
  have hcube : selectedPTWFactorScale X d * selectedPTWFactorScale X d *
      selectedPTWFactorScale X d ≤ (2 : ℝ) ^ 36 * L ^ 3 * τ ^ 60 := by
    calc
      _ = selectedPTWFactorScale X d ^ 3 := by ring
      _ ≤ ((2 : ℝ) ^ 12 * L * τ ^ 20) ^ 3 := pow_le_pow_left₀ hscale0 hscale 3
      _ = _ := by ring
  have hdiv := selectedPTWDivisorProductLogarithmicBound hL hd hdlog
  calc
    _ ≤ (divisorFunction 3 ⟨d, hd⟩ : ℝ) / (d : ℝ) *
        ((2 : ℝ) ^ 36 * L ^ 3 * τ ^ 60) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = ((2 : ℝ) ^ 36 * L ^ 3) *
        (τ ^ 60 * ((divisorFunction 3 ⟨d, hd⟩ : ℝ) / (d : ℝ))) := by ring
    _ ≤ ((2 : ℝ) ^ 36 * L ^ 3) *
        ((divisorSubpowerConstant 60 (1 / 1000 : ℝ) *
          divisorSubpowerConstant 3 (1 / 1000 : ℝ)) * L ^ (a / 500)) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = _ := by
      rw [show L ^ 3 = L ^ (3 : ℝ) by norm_cast]
      rw [show ((2 : ℝ) ^ 36 * L ^ (3 : ℝ)) *
          ((divisorSubpowerConstant 60 (1 / 1000 : ℝ) *
            divisorSubpowerConstant 3 (1 / 1000 : ℝ)) * L ^ (a / 500)) =
          ((2 : ℝ) ^ 36 * divisorSubpowerConstant 60 (1 / 1000 : ℝ) *
            divisorSubpowerConstant 3 (1 / 1000 : ℝ)) *
              (L ^ (3 : ℝ) * L ^ (a / 500)) by ring]
      rw [← Real.rpow_add hL]

#print axioms selectedPTWFactorNormalization
end FractionalPrimes.Literature.DirichletMean
end
