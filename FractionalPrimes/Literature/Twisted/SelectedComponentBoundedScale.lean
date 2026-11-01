module
public import FractionalPrimes.Literature.Twisted.SelectedComponentMass
public import FractionalPrimes.Literature.Twisted.SmallDivisorDomination
public import Mathlib.Tactic
@[expose] public section
namespace FractionalPrimes.Literature.Twisted
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

 theorem divisorCoefficient_two_le_self (n : ℕ) : divisorCoefficient 2 n ≤ n := by
  rw [divisorCoefficient_two_eq_cardDivisors]
  exact Nat.card_divisors_le_self n

/-- The literal bounded-scale coefficient constant in the source PTW proof. -/
noncomputable def selectedComponentBoundedScaleConstant (X₀ : ℝ) : ℝ :=
  (2 : ℝ) ^ 10 * Real.log (8 * X₀) * (2 * X₀) ^ 20

 theorem divisorComponentBoundedScale
    {X X₀ : ℝ} (hX : 3 ≤ X) (hXX₀ : X ≤ X₀)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * X₀) :
    (2 : ℝ) ^ 10 * Real.log (8 * X) * (divisorCoefficient 2 n : ℝ) ^ 20 ≤
      selectedComponentBoundedScaleConstant X₀ := by
  have hXpos : 0 < X := by linarith
  have hlog : Real.log (8 * X) ≤ Real.log (8 * X₀) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (8 * X₀) := Real.log_nonneg (by linarith)
  have hdiv : (divisorCoefficient 2 n : ℝ) ≤ 2 * X₀ := by
    exact (by exact_mod_cast divisorCoefficient_two_le_self n :
      (divisorCoefficient 2 n : ℝ) ≤ (n : ℝ)).trans hn
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hlog (by positivity))
    (pow_le_pow_left₀ (by positivity) hdiv 20)
    (by positivity) (mul_nonneg (by positivity) hlog0)

 theorem mobiusDyadicComponent_abs_le_boundedScale
    {X X₀ : ℝ} (hX : 3 ≤ X) (hXX₀ : X ≤ X₀)
    (ν : MobiusDyadicLabel X) {n : ℕ} (hn : 0 < n)
    (hnX₀ : (n : ℝ) ≤ 2 * X₀) :
    |mobiusDyadicComponent (dyadicMobiusCutoff X) ν n| ≤
      selectedComponentBoundedScaleConstant X₀ :=
  (mobiusDyadicComponent_abs_le_divisorTwenty hX ν n hn).trans
    (divisorComponentBoundedScale hX hXX₀ hnX₀)

 theorem vonMangoldtDyadicComponent_abs_le_boundedScale
    {X X₀ : ℝ} (hX : 3 ≤ X) (hXX₀ : X ≤ X₀)
    (ν : VonMangoldtDyadicLabel X) {n : ℕ} (hn : 0 < n)
    (hnX₀ : (n : ℝ) ≤ 2 * X₀) :
    |vonMangoldtDyadicComponent (dyadicMobiusCutoff X) ν n| ≤
      selectedComponentBoundedScaleConstant X₀ :=
  (vonMangoldtDyadicComponent_abs_le_divisorTwenty hX ν n hn).trans
    (divisorComponentBoundedScale hX hXX₀ hnX₀)

#print axioms divisorCoefficient_two_le_self
#print axioms mobiusDyadicComponent_abs_le_boundedScale
#print axioms vonMangoldtDyadicComponent_abs_le_boundedScale
end FractionalPrimes.Literature.Twisted
end
