module

public import FractionalPrimes.Literature.DirichletAdapter.DPTypeILogarithmicAbsorption
public import FractionalPrimes.Literature.DirichletAdapter.DPIImajScalarAbsorption

@[expose] public section
namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Uniformity
noncomputable section

/-- The exact numerical budget shared by the two source DP component branches.
The analytic constants remain explicit, and the `A+22` IImaj saving pays
for the possible scalar logarithm and the residue tuples. -/
theorem dpBranchLogarithmicAbsorption
    {X W A B D η K₁ K₂ c : ℝ} {j k : ℕ}
    (hX : 1 ≤ X) (hL : 1 ≤ Real.log X)
    (hA : 0 < A) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hW : W = (Real.log X) ^ D)
    (hD : A + 22 ≤ D * ((j : ℝ) - 1))
    (hjη : 8 ≤ (j : ℝ) * η)
    (hlarge : 2 * Real.log (logAbsorptionM 1 (A + 22)) ≤ Real.log X)
    (hk : k ≤ 1) (hc : |c| ≤ (2 : ℝ) ^ 10) :
    max
      (K₁ * Real.sqrt X * Real.log X *
        (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)))
      (K₂ * Real.sqrt X *
        (‖(c : ℂ) * (((4 * Real.log X) ^ k : ℝ) : ℂ)‖ *
          (Real.log X) ^ (20 * B) *
          (Real.log X) ^ (-(A + 22 + 20 * B)))) ≤
      (2 * K₁ + (2 : ℝ) ^ 12 * K₂) * Real.sqrt X *
        (Real.log X) ^ (-(A + 21)) := by
  have hXpos : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hT := dpTypeILogarithmicAbsorption hX hL (by linarith : 0 < A + 21)
    hW (by linarith : (A + 21) + 1 ≤ D * ((j : ℝ) - 1)) hjη
    (by simpa only [show (A + 21) + 1 = A + 22 by ring] using hlarge)
  have hI := dpIImajScalarAbsorption (A := A) (B := B) hL hk hc
  have hleft :
      K₁ * Real.sqrt X * Real.log X *
          (W ^ (1 - (j : ℝ)) + X ^ (1 - (j : ℝ) * η / 4)) ≤
        (2 * K₁ + (2 : ℝ) ^ 12 * K₂) * Real.sqrt X *
          (Real.log X) ^ (-(A + 21)) := by
    have hmul := mul_le_mul_of_nonneg_left hT (mul_nonneg hK₁ hXpos)
    have hpow : 0 ≤ (Real.log X) ^ (-(A + 21)) := by positivity
    nlinarith [mul_nonneg hK₂ hXpos]
  have hright :
      K₂ * Real.sqrt X *
          (‖(c : ℂ) * (((4 * Real.log X) ^ k : ℝ) : ℂ)‖ *
            (Real.log X) ^ (20 * B) *
            (Real.log X) ^ (-(A + 22 + 20 * B))) ≤
        (2 * K₁ + (2 : ℝ) ^ 12 * K₂) * Real.sqrt X *
          (Real.log X) ^ (-(A + 21)) := by
    have hmul := mul_le_mul_of_nonneg_left hI (mul_nonneg hK₂ hXpos)
    have hpow : 0 ≤ (Real.log X) ^ (-(A + 21)) := by positivity
    nlinarith [mul_nonneg hK₁ hXpos]
  exact max_le hleft hright

#print axioms dpBranchLogarithmicAbsorption
end
end FractionalPrimes.Literature.DirichletAdapter
