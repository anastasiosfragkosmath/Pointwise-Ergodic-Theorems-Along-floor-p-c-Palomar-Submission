module

public import FractionalPrimes.Literature.Multiplier.WeakStrongInterpolation

/-!
# Conjugate exponent arithmetic for the upper multiplier range

For `p > 2`, the conjugate exponent `q = p / (p - 1)` lies in the range
of the checked low-exponent multiplier theorem. This file records the exact
exponent and constant identities used to transfer that estimate.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

theorem multiplierConjugateExponent_gt_one {p : ℝ} (hp : 2 < p) :
    1 < p / (p - 1) := by
  have hpden : 0 < p - 1 := by linarith
  have hq : p / (p - 1) = 1 + 1 / (p - 1) := by
    field_simp [ne_of_gt hpden]
    <;> ring
  rw [hq]
  have hpos : 0 < 1 / (p - 1) := one_div_pos.mpr hpden
  linarith

theorem multiplierConjugateExponent_lt_two {p : ℝ} (hp : 2 < p) :
    p / (p - 1) < 2 := by
  have hpden : 0 < p - 1 := by linarith
  rw [div_lt_iff₀ hpden]
  nlinarith

theorem multiplierConjugateExponent_holderConjugate {p : ℝ} (hp : 2 < p) :
    p.HolderConjugate (p / (p - 1)) := by
  have hp1 : 1 < p := by linarith
  simpa [Real.conjExponent] using
    (Real.HolderConjugate.conjExponent hp1)

theorem multiplierConjugateExponent_reciprocal {p : ℝ} (hp : 2 < p) :
    1 / (p / (p - 1)) = (p - 1) / p := by
  have hp0 : 0 < p := by linarith
  have hpden : 0 < p - 1 := by linarith
  field_simp [ne_of_gt hp0, ne_of_gt hpden]
  <;> ring

private theorem weakStrongInterpolation_conjugateCoefficient_eq
    {p : ℝ} (hp : 2 < p) :
    2 * W * (p / (p - 1)) / ((p / (p - 1)) - 1) +
        4 * (p / (p - 1)) / (2 - (p / (p - 1))) =
      2 * W * p + 4 * p / (p - 2) := by
  have hpden : 0 < p - 1 := by linarith
  have hpden2 : 0 < p - 2 := by linarith
  have hqsub : p / (p - 1) - 1 = 1 / (p - 1) := by
    field_simp [ne_of_gt hpden]
    <;> ring
  have h2subq : 2 - p / (p - 1) = (p - 2) / (p - 1) := by
    field_simp [ne_of_gt hpden]
    <;> ring
  have hratio₁ : (p / (p - 1)) / ((p / (p - 1)) - 1) = p := by
    rw [hqsub]
    field_simp [ne_of_gt hpden]
    <;> ring
  have hratio₂ : (p / (p - 1)) / (2 - (p / (p - 1))) = p / (p - 2) := by
    rw [h2subq]
    field_simp [ne_of_gt hpden, ne_of_gt hpden2]
    <;> ring
  calc
    2 * W * (p / (p - 1)) / ((p / (p - 1)) - 1) +
        4 * (p / (p - 1)) / (2 - (p / (p - 1))) =
      2 * W * ((p / (p - 1)) / ((p / (p - 1)) - 1)) +
        4 * ((p / (p - 1)) / (2 - (p / (p - 1)))) := by ring
    _ = 2 * W * p + 4 * p / (p - 2) := by
      rw [hratio₁, hratio₂]
      ring

/-- The low-range interpolation coefficient evaluated at `p/(p-1)` is
exactly the blueprint's high-range constant `C_{p/(p-1)}`. -/
theorem weakStrongInterpolation_conjugateConstant_eq {p : ℝ} (hp : 2 < p) :
    (2 * W * (p / (p - 1)) / ((p / (p - 1)) - 1) +
        4 * (p / (p - 1)) / (2 - (p / (p - 1)))) ^
          (1 / (p / (p - 1))) =
      (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) := by
  rw [weakStrongInterpolation_conjugateCoefficient_eq hp,
    multiplierConjugateExponent_reciprocal hp]

end FractionalPrimes.Literature.Multiplier
