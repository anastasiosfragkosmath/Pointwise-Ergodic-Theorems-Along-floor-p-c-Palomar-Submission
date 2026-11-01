module
public import FractionalPrimes.Literature.Polynomial.TypeIISelectedMobiusPTWLogBudget
public import FractionalPrimes.Literature.Twisted.PrefixTwistRange
public import Mathlib.Tactic
@[expose] public section
namespace FractionalPrimes.Literature.DirichletMean
open FractionalPrimes.Literature.Twisted

/-- The exact approved threshold supplies the elementary conditions used by
the prefix mass theorem; no larger threshold exponent is chosen. -/
theorem selectedPTWSourceThreshold_facts
    {a : ℝ} (ha : (selectedMobiusPTWThreshold : ℝ) ≤ a) :
    (1 : ℝ) ≤ selectedMobiusPTWThreshold ∧ 2 ≤ a ∧
      (prefixTwistBeta : ℝ) < a := by
  have htwo : 2 ≤ selectedMobiusPTWThreshold := Nat.le_max_right _ _
  have htwoR : (2 : ℝ) ≤ selectedMobiusPTWThreshold := by exact_mod_cast htwo
  have hbeta : selectedMobiusPTWComponentExponent + 2 ≤ selectedMobiusPTWThreshold :=
    (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
  have hbetaR : (selectedMobiusPTWComponentExponent : ℝ) + 2 ≤
      (selectedMobiusPTWThreshold : ℝ) := by exact_mod_cast hbeta
  have heq : prefixTwistBeta = selectedMobiusPTWComponentExponent := rfl
  rw [heq]
  exact ⟨by linarith, htwoR.trans ha, by linarith⟩

/-- The paper's upper short-interval endpoint implies the base-length bound
used internally by the Mellin and local-mass data constructors. -/
theorem selectedPTWSourceLength_le_base
    {X H η : ℝ} (hX : 1 ≤ X) (hη : 0 ≤ η)
    (hH : H ≤ X ^ (1 - η)) : H ≤ X := by
  calc
    H ≤ X ^ (1 - η) := hH
    _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    _ = X := Real.rpow_one X

#print axioms selectedPTWSourceThreshold_facts
#print axioms selectedPTWSourceLength_le_base
end FractionalPrimes.Literature.DirichletMean
end
