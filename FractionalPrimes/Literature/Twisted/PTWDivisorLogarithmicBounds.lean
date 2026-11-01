module
public import FractionalPrimes.Literature.Twisted.DivisorCoefficientPowerBound
public import FractionalPrimes.Literature.Twisted.DivisorSubpowerExplicit
public import Mathlib.Tactic
@[expose] public section
namespace FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
noncomputable section

/-- The explicit divisor subpower bound at a modulus bounded by a logarithmic
power. No large-X threshold beyond positivity of the logarithm is used. -/
theorem divisorSubpower_logarithmic
    {L a ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    {k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (hdlog : (d : ℝ) ≤ L ^ a) :
    (divisorFunction 2 ⟨d, hd⟩ : ℝ) ^ k ≤
      divisorSubpowerConstant k ε * L ^ (a * ε) := by
  have hsub := divisorSubpowerExplicit hk hε (⟨d, hd⟩ : PositiveInteger)
  have hp : (d : ℝ) ^ ε ≤ L ^ (a * ε) := by
    calc
      _ ≤ (L ^ a) ^ ε := Real.rpow_le_rpow (by positivity) hdlog hε.le
      _ = _ := (Real.rpow_mul hL.le a ε).symm
  exact hsub.trans (mul_le_mul_of_nonneg_left hp (by
    unfold divisorSubpowerConstant
    positivity))

/-- The two exact divisor losses in the source restricted-twist argument:
sixty ordinary divisor factors, and the normalized three-fold allocation count. -/
theorem selectedPTWDivisorLogarithmicBounds
    {L a : ℝ} (hL : 0 < L) {d : ℕ} (hd : 0 < d)
    (hdlog : (d : ℝ) ≤ L ^ a) :
    (divisorFunction 2 ⟨d, hd⟩ : ℝ) ^ 60 ≤
      divisorSubpowerConstant 60 (1 / 1000 : ℝ) * L ^ (a / 1000) ∧
    (divisorFunction 3 ⟨d, hd⟩ : ℝ) / (d : ℝ) ≤
      divisorSubpowerConstant 3 (1 / 1000 : ℝ) * L ^ (a / 1000) := by
  have hsixty := divisorSubpower_logarithmic hL
    (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num : 0 < 60) hd hdlog
  have hthree := divisorSubpower_logarithmic hL
    (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num : 0 < 3) hd hdlog
  have hnat : divisorFunction 3 ⟨d, hd⟩ ≤ divisorFunction 2 ⟨d, hd⟩ ^ 3 := by
    simpa only [divisorCoefficient_eq_divisorFunction 3 d hd,
      divisorCoefficient_eq_divisorFunction 2 d hd] using
      divisorCoefficient_succ_le_two_pow 2 d hd
  have hcast : (divisorFunction 3 ⟨d, hd⟩ : ℝ) ≤
      (divisorFunction 2 ⟨d, hd⟩ : ℝ) ^ 3 := by exact_mod_cast hnat
  constructor
  · simpa only [show a * (1 / 1000 : ℝ) = a / 1000 by ring] using hsixty
  · have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    calc
      _ ≤ (divisorFunction 3 ⟨d, hd⟩ : ℝ) :=
        div_le_self (by positivity) hdR
      _ ≤ (divisorFunction 2 ⟨d, hd⟩ : ℝ) ^ 3 := hcast
      _ ≤ _ := by
        simpa only [show a * (1 / 1000 : ℝ) = a / 1000 by ring] using hthree

/-- Combined divisor normalization with the exact `a/500` source exponent. -/
theorem selectedPTWDivisorProductLogarithmicBound
    {L a : ℝ} (hL : 0 < L) {d : ℕ} (hd : 0 < d)
    (hdlog : (d : ℝ) ≤ L ^ a) :
    (divisorFunction 2 ⟨d, hd⟩ : ℝ) ^ 60 *
        ((divisorFunction 3 ⟨d, hd⟩ : ℝ) / (d : ℝ)) ≤
      (divisorSubpowerConstant 60 (1 / 1000 : ℝ) *
        divisorSubpowerConstant 3 (1 / 1000 : ℝ)) * L ^ (a / 500) := by
  have h := selectedPTWDivisorLogarithmicBounds hL hd hdlog
  calc
    _ ≤ (divisorSubpowerConstant 60 (1 / 1000 : ℝ) * L ^ (a / 1000)) *
        (divisorSubpowerConstant 3 (1 / 1000 : ℝ) * L ^ (a / 1000)) := by
      apply mul_le_mul h.1 h.2 (by positivity)
      unfold divisorSubpowerConstant
      positivity
    _ = _ := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hL]
      congr 2
      ring

#print axioms selectedPTWDivisorProductLogarithmicBound
#print axioms divisorSubpower_logarithmic
#print axioms selectedPTWDivisorLogarithmicBounds
end
end FractionalPrimes.Literature.Twisted
