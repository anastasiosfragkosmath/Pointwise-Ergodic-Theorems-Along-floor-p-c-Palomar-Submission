module

public import FractionalPrimes.Literature.JSW.PositiveGeometricNuLowerBound

/-! Exact exponent arithmetic in the `lj:positivity` maximal criterion. -/

@[expose] public section

namespace FractionalPrimes.Literature.JSW

/-- Above the Hilbert exponent, the maximal exponent threshold is exactly
the right half of the approved reciprocal-exponent region. -/
theorem upper_maximal_exponent_criterion
    {p q₀ : ℝ} (hp : 2 < p) (hq₀ : 1 < q₀) :
    q₀ < p / (p - 2) ↔
      |p⁻¹ - (2 : ℝ)⁻¹| < (2 * q₀)⁻¹ := by
  have hp0 : 0 < p := by linarith
  have hpm2 : 0 < p - 2 := by linarith
  have hq0 : 0 < q₀ := by linarith
  have htwoq : 0 < 2 * q₀ := by positivity
  have hpinv : p⁻¹ < (2 : ℝ)⁻¹ :=
    (inv_lt_inv₀ hp0 (by norm_num)).2 hp
  rw [abs_of_neg (sub_neg.mpr hpinv)]
  constructor
  · intro h
    have hmul : q₀ * (p - 2) < p := (lt_div_iff₀ hpm2).mp h
    field_simp
    nlinarith [hmul]
  · intro h
    apply (lt_div_iff₀ hpm2).2
    have hdiff : (2 : ℝ)⁻¹ - p⁻¹ < (2 * q₀)⁻¹ := by
      nlinarith [h]
    field_simp at hdiff
    nlinarith

#print axioms upper_maximal_exponent_criterion

/-- Below the Hilbert exponent, the same maximal threshold is the left
half of the reciprocal-exponent region. -/
theorem lower_maximal_exponent_criterion
    {p q₀ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hq₀ : 1 < q₀) :
    q₀ < p / (2 - p) ↔
      |p⁻¹ - (2 : ℝ)⁻¹| < (2 * q₀)⁻¹ := by
  have hp0 : 0 < p := by linarith
  have h2mp : 0 < 2 - p := by linarith
  have hq0 : 0 < q₀ := by linarith
  have htwoq : 0 < 2 * q₀ := by positivity
  have hpinv : (2 : ℝ)⁻¹ < p⁻¹ :=
    (inv_lt_inv₀ (by norm_num) hp0).2 hp2
  rw [abs_of_pos (sub_pos.mpr hpinv)]
  constructor
  · intro h
    have hmul : q₀ * (2 - p) < p := (lt_div_iff₀ h2mp).mp h
    field_simp
    nlinarith [hmul]
  · intro h
    apply (lt_div_iff₀ h2mp).2
    field_simp at h
    nlinarith [h]

#print axioms lower_maximal_exponent_criterion

end FractionalPrimes.Literature.JSW

end
