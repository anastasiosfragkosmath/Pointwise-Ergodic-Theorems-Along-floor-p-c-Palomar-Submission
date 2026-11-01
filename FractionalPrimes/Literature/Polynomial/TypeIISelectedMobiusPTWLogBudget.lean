module

public import FractionalPrimes.Literature.Polynomial.DirichletMeanConstants
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! The final scalar logarithmic budget in the conditional Möbius PTW
argument. The exact source threshold makes both long-prefix powers at most
`(log X)^(-a)`; the absolute-transfer constant is retained verbatim. -/

@[expose] public section

namespace FractionalPrimes.Literature.DirichletMean

/-- The logarithmic exponent after expanding the three `Z₂₀` factors. -/
def selectedMobiusPTWLogExponent : ℕ :=
  b 20 + 3 + 3 * (2 ^ 20 - 1)

/-- The component-mass exponent in the approved Möbius PTW threshold. -/
def selectedMobiusPTWComponentExponent : ℕ := 2 ^ 180 + 1

/-- The exact threshold exponent `a_*` in the approved restricted-twist
deduction. -/
def selectedMobiusPTWThreshold : ℕ :=
  max (max (selectedMobiusPTWComponentExponent + 2)
      (16 * (selectedMobiusPTWLogExponent + 10))) 2

/-- The long-prefix constant after the source absolute-transfer step. -/
def selectedMobiusPTWLongPrefixConstant
    (a M₁ K₀ C₁ : ℝ) : ℝ :=
  max 1 ((2 : ℝ) ^ 36 * (1 + M₁) *
    (K₀ + (1 + 10 * a) * C₁))

/-- With the exact source `a_*`, both logarithmic error exponents in the
large-prefix estimate are at most `-a`. -/
theorem selectedMobiusPTW_logPowerBudget
    {a L : ℝ} (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (hL : 1 ≤ L) :
    L ^ ((selectedMobiusPTWComponentExponent : ℝ) - 20 * a) ≤ L ^ (-a) ∧
      L ^ ((selectedMobiusPTWLogExponent : ℝ) + 4 -
        5 * a / 4 + a / 500) ≤ L ^ (-a) := by
  have hbetaNat : selectedMobiusPTWComponentExponent + 2 ≤
      selectedMobiusPTWThreshold := by
    exact le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hB0Nat : 16 * (selectedMobiusPTWLogExponent + 10) ≤
      selectedMobiusPTWThreshold := by
    exact le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hbeta : (selectedMobiusPTWComponentExponent : ℝ) + 2 ≤ a := by
    have hbetaR : (selectedMobiusPTWComponentExponent : ℝ) + 2 ≤
        (selectedMobiusPTWThreshold : ℝ) := by
      norm_cast
    exact hbetaR.trans ha
  have hB0 : 16 * ((selectedMobiusPTWLogExponent : ℝ) + 10) ≤ a := by
    have hB0R :
        16 * ((selectedMobiusPTWLogExponent : ℝ) + 10) ≤
          (selectedMobiusPTWThreshold : ℝ) := by
      norm_cast
    exact hB0R.trans ha
  have hB0nonneg : 0 ≤ (selectedMobiusPTWLogExponent : ℝ) := by
    exact_mod_cast Nat.zero_le selectedMobiusPTWLogExponent
  have hExp₁ :
      (selectedMobiusPTWComponentExponent : ℝ) - 20 * a ≤ -a := by
    linarith
  have hslack :
      (selectedMobiusPTWLogExponent : ℝ) + 4 ≤
        (1 / 4 - 1 / 500 : ℝ) * a := by
    nlinarith [hB0, hB0nonneg]
  have hExp₂ :
      (selectedMobiusPTWLogExponent : ℝ) + 4 -
        5 * a / 4 + a / 500 ≤ -a := by
    linarith
  exact ⟨Real.rpow_le_rpow_of_exponent_le hL hExp₁,
    Real.rpow_le_rpow_of_exponent_le hL hExp₂⟩

#print axioms selectedMobiusPTW_logPowerBudget

/-- The source absolute-transfer scalar is bounded by the exact long-prefix
constant times `(log X)^(-a)`. This lemma absorbs only the approved powers;
all earlier factors, including the original divisor and allocation costs,
remain in the inputs `K₀` and `C₁`. -/
theorem selectedMobiusPTW_longPrefixScalarBound
    {a L M₁ K₀ C₁ : ℝ}
    (haThreshold : (selectedMobiusPTWThreshold : ℝ) ≤ a)
    (hL : 1 ≤ L)
    (hM₁ : 0 ≤ M₁) (hK₀ : 0 ≤ K₀) (hC₁ : 0 ≤ C₁) :
    (2 : ℝ) ^ 36 * (1 + M₁) *
        (K₀ * L ^ ((selectedMobiusPTWComponentExponent : ℝ) - 20 * a) +
          (1 + 10 * a) * C₁ *
            L ^ ((selectedMobiusPTWLogExponent : ℝ) + 4 -
              5 * a / 4 + a / 500)) ≤
      selectedMobiusPTWLongPrefixConstant a M₁ K₀ C₁ * L ^ (-a) := by
  have h2nat : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
  have h2 : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast h2nat
  have ha : 2 ≤ a := h2.trans haThreshold
  have hpower := selectedMobiusPTW_logPowerBudget haThreshold hL
  have hcoef : 0 ≤ 1 + 10 * a := by linarith
  have hpref : 0 ≤ (2 : ℝ) ^ 36 * (1 + M₁) := by positivity
  have hsum :
      K₀ * L ^ ((selectedMobiusPTWComponentExponent : ℝ) - 20 * a) +
        (1 + 10 * a) * C₁ *
          L ^ ((selectedMobiusPTWLogExponent : ℝ) + 4 -
            5 * a / 4 + a / 500) ≤
        (K₀ + (1 + 10 * a) * C₁) * L ^ (-a) := by
    calc
      _ ≤ K₀ * L ^ (-a) + (1 + 10 * a) * C₁ * L ^ (-a) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hpower.1 hK₀)
          (mul_le_mul_of_nonneg_left hpower.2
            (mul_nonneg hcoef hC₁))
      _ = _ := by ring
  have hcoef' :
      (2 : ℝ) ^ 36 * (1 + M₁) *
          (K₀ + (1 + 10 * a) * C₁) ≤
        selectedMobiusPTWLongPrefixConstant a M₁ K₀ C₁ :=
    le_max_right _ _
  have hLnonneg : 0 ≤ L := by linarith
  have hLpow : 0 ≤ L ^ (-a) := Real.rpow_nonneg hLnonneg _
  calc
    _ ≤ (2 : ℝ) ^ 36 * (1 + M₁) *
          ((K₀ + (1 + 10 * a) * C₁) * L ^ (-a)) :=
      mul_le_mul_of_nonneg_left hsum hpref
    _ = ((2 : ℝ) ^ 36 * (1 + M₁) *
          (K₀ + (1 + 10 * a) * C₁)) * L ^ (-a) := by ring
    _ ≤ selectedMobiusPTWLongPrefixConstant a M₁ K₀ C₁ *
          L ^ (-a) :=
      mul_le_mul_of_nonneg_right hcoef' hLpow

#print axioms selectedMobiusPTW_longPrefixScalarBound

end FractionalPrimes.Literature.DirichletMean

end
