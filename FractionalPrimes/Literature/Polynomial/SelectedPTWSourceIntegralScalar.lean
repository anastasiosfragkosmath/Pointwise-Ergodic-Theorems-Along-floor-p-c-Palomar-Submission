module
public import FractionalPrimes.Literature.Uniformity.ArithmeticGroupingConstants
public import FractionalPrimes.Literature.Polynomial.SelectedPTWFactorNormalization
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWTransferAssembly
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWRetainedBlocks
@[expose] public section
noncomputable section
namespace FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- The exact `C₁` of the approved restricted-twist deduction. -/
def selectedPTWSourceIntegralConstant : ℝ :=
  (2 : ℝ) ^ (37 + selectedMobiusPTWLogExponent) *
    (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
    (2 * decompositionC) ^ (3 / 2 : ℝ) *
    (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 *
    divisorSubpowerConstant 60 (1 / 1000 : ℝ) *
    divisorSubpowerConstant 3 (1 / 1000 : ℝ)

theorem selectedPTWSourceIntegralScalar_le
    {X a : ℝ} (hX : 3 ≤ X) {d : ℕ} (hd : 0 < d)
    (hdlog : (d : ℝ) ≤ (Real.log X) ^ a) :
    (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 *
      ((divisorFunction 3 ⟨d, hd⟩ : ℝ) *
        (selectedPTWFactorScale X d * selectedPTWFactorScale X d *
          selectedPTWFactorScale X d) *
        (2 * (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
          (2 * decompositionC) ^ (3 / 2 : ℝ) *
          (2 * Real.log X) ^ selectedMobiusPTWLogExponent *
          Real.sqrt X / (d : ℝ) * (Real.log X) ^ (-5 * a / 4))) ≤
      selectedPTWSourceIntegralConstant * Real.sqrt X *
        (Real.log X) ^ selectedMobiusPTWSourceIntegralExponent a := by
  let L := Real.log X
  let B := selectedMobiusPTWLogExponent
  let F := selectedPTWFactorScale X d
  let K := (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 *
    (2 * (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
      (2 * decompositionC) ^ (3 / 2 : ℝ))
  have hL : 0 < L := Real.log_pos (by linarith [hX])
  have hC : 0 ≤ decompositionC := by unfold decompositionC; positivity
  have hJ : 0 ≤ J 20 := by unfold J FractionalPrimes.Literature.DirichletMean.K; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hnorm := selectedPTWFactorNormalization hX hd hdlog
  have hscale :
      ((divisorFunction 3 ⟨d, hd⟩ : ℝ) / (d : ℝ) * (F * F * F)) *
        (K * (2 * L) ^ B * Real.sqrt X * L ^ (-5 * a / 4)) ≤
      (((2 : ℝ) ^ 36 * divisorSubpowerConstant 60 (1 / 1000 : ℝ) *
        divisorSubpowerConstant 3 (1 / 1000 : ℝ)) * L ^ (3 + a / 500)) *
        (K * (2 * L) ^ B * Real.sqrt X * L ^ (-5 * a / 4)) :=
    mul_le_mul_of_nonneg_right hnorm (by positivity)
  have hp : L ^ (3 + a / 500) * L ^ (B : ℝ) * L ^ (-5 * a / 4) =
      L ^ selectedMobiusPTWSourceIntegralExponent a := by
    rw [← Real.rpow_add hL, ← Real.rpow_add hL]
    congr 1
    dsimp [selectedMobiusPTWSourceIntegralExponent, B]
    ring
  calc
    _ = ((divisorFunction 3 ⟨d, hd⟩ : ℝ) / (d : ℝ) * (F * F * F)) *
        (K * (2 * L) ^ B * Real.sqrt X * L ^ (-5 * a / 4)) := by dsimp [K, F, B, L]; ring
    _ ≤ _ := hscale
    _ = _ := by
      rw [mul_pow, ← Real.rpow_natCast L B]
      unfold selectedPTWSourceIntegralConstant
      rw [pow_add]
      dsimp [K, B, L] at hp ⊢
      linear_combination (2 : ℝ) ^ 37 *
        (2 : ℝ) ^ selectedMobiusPTWLogExponent *
        (J 20 * (2 : ℝ) ^ (3 * (2 ^ 20 + 1))) *
        (2 * decompositionC) ^ (3 / 2 : ℝ) *
        (selectedMobiusPTWDyadicBlockCount decompositionC : ℝ) ^ 3 *
        divisorSubpowerConstant 60 (1 / 1000 : ℝ) *
        divisorSubpowerConstant 3 (1 / 1000 : ℝ) * Real.sqrt X * hp

#print axioms selectedPTWSourceIntegralScalar_le
end FractionalPrimes.Literature.DirichletMean
end
