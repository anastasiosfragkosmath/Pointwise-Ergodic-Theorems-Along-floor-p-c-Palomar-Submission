module

public import FractionalPrimes.InterpolationPowerOptimization

@[expose] public section

/-!
# Exact exponent and constant conventions for `lem:interpolation`

These definitions mirror the piecewise constants and minimum exponent in the
approved interpolation lemma, so the three checked operator branches can be
assembled without changing its statement.
-/

namespace FractionalPrimes

noncomputable section

/-- The exponent `β_p = min(2/p, 2-2/p)` from the approved lemma. -/
def interpolationBeta (p : ℝ) : ℝ := min (2 / p) (2 - 2 / p)

/-- The lower-range constant `C_p` for `1<p<2`. -/
noncomputable def interpolationLowerConstant (p : ℝ) : ℝ :=
  (4 * p / (2 - p) + 2 * p / (p - 1)) ^ (1 / p)

/-- The exact piecewise constant in the approved interpolation lemma:
`C₂=1`, and `C_p=C_{p'}` above 2. -/
noncomputable def interpolationConstant (p : ℝ) : ℝ :=
  if p < 2 then interpolationLowerConstant p
  else if p = 2 then 1
  else interpolationLowerConstant (p / (p - 1))

theorem interpolationBeta_eq_lower {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    interpolationBeta p = 2 - 2 / p := by
  unfold interpolationBeta
  apply min_eq_right
  have hp0 : 0 < p := by linarith
  apply (le_div_iff₀ hp0).2
  have hmul : (2 - 2 / p) * p = 2 * p - 2 := by
    field_simp [ne_of_gt hp0]
  rw [hmul]
  linarith

theorem interpolationBeta_eq_upper {p : ℝ} (hp : 2 < p) :
    interpolationBeta p = 2 / p := by
  unfold interpolationBeta
  apply min_eq_left
  have hp0 : 0 < p := by linarith
  apply (div_le_iff₀ hp0).2
  have hmul : (2 - 2 / p) * p = 2 * p - 2 := by
    field_simp [ne_of_gt hp0]
  rw [hmul]
  linarith

/-- The conjugate exponent used in the upper branch lies in the lower range,
and its powers translate to the paper's `p>2` powers. -/
theorem interpolation_dual_exponent_identities {p : ℝ} (hp : 2 < p) :
    1 < p / (p - 1) ∧ p / (p - 1) < 2 ∧
      2 / (p / (p - 1)) - 1 = 1 - 2 / p ∧
      2 - 2 / (p / (p - 1)) = 2 / p := by
  have hp0 : 0 < p := by linarith
  have hden : 0 < p - 1 := by linarith
  have hq1 : 1 < p / (p - 1) := by
    apply (lt_div_iff₀ hden).2
    linarith
  have hq2 : p / (p - 1) < 2 := by
    apply (div_lt_iff₀ hden).2
    linarith
  have hpow1 : 2 / (p / (p - 1)) - 1 = 1 - 2 / p := by
    field_simp [ne_of_gt hp0, ne_of_gt hden]
    ring
  have hpow2 : 2 - 2 / (p / (p - 1)) = 2 / p := by
    field_simp [ne_of_gt hp0, ne_of_gt hden]
    ring
  exact ⟨hq1, hq2, hpow1, hpow2⟩

end

end FractionalPrimes
