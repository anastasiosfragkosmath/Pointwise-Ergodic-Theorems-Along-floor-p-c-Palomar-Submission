module

public import FractionalPrimes.InterpolationExponents

/-! The exact logarithmic exponent choice in `er:operator-decay`. -/
@[expose] public section
namespace FractionalPrimes
noncomputable section

theorem interpolationBeta_pos {p : ℝ} (hp : 1 < p) :
    0 < interpolationBeta p := by
  have hp0 : 0 < p := by linarith
  unfold interpolationBeta
  refine lt_min (by positivity) ?_
  have h : 2 / p < 2 := (div_lt_iff₀ hp0).mpr (by linarith)
  linarith

theorem interpolationBeta_le_one {p : ℝ} (hp : 1 < p) :
    interpolationBeta p ≤ 1 := by
  have hp0 : 0 < p := by linarith
  unfold interpolationBeta
  by_cases h : p ≤ 2
  · apply (min_le_right _ _).trans
    have hdiv : 1 ≤ 2 / p := (le_div_iff₀ hp0).mpr (by linarith)
    linarith
  · apply (min_le_left _ _).trans
    exact (div_le_iff₀ hp0).mpr (by linarith)

theorem interpolationConstant_nonneg {p : ℝ} (hp : 1 < p) :
    0 ≤ interpolationConstant p := by
  rcases lt_trichotomy p 2 with hlo | heq | hhi
  · simp only [interpolationConstant, hlo, ite_true]
    unfold interpolationLowerConstant
    have hden : 0 < 2 - p := by linarith
    have hpden : 0 < p - 1 := by linarith
    have hp0 : 0 < p := by linarith
    positivity
  · subst p
    norm_num [interpolationConstant]
  · have hq1 := (interpolation_dual_exponent_identities hhi).1
    have hq2 := (interpolation_dual_exponent_identities hhi).2.1
    have hqden : 0 < p / (p - 1) - 1 := by linarith
    have hqtop : 0 < 2 - p / (p - 1) := by linarith
    simp only [interpolationConstant, not_lt_of_gt hhi, ne_of_gt hhi, ite_false]
    unfold interpolationLowerConstant
    positivity

/-- Choosing A=(D+1)/β absorbs the logarithmic endpoint loss exactly as in
the approved source proof. All coefficients are preserved. -/
theorem logarithmicInterpolationScalar
    {β D M C L : ℝ} (hβ : 0 < β) (hD : 0 < D)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hL : 1 ≤ L) :
    ((M + 1) * L) ^ (1 - β) *
        ((C + 1) * L ^ (-((D + 1) / β))) ^ β ≤
      ((M + 1) ^ (1 - β) * (C + 1) ^ β) * L ^ (-D) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [Real.mul_rpow (by positivity : 0 ≤ M + 1) hL0.le,
    Real.mul_rpow (by positivity : 0 ≤ C + 1) (Real.rpow_nonneg hL0.le _),
    ← Real.rpow_mul hL0.le]
  have hexp : (1 - β) + (-((D + 1) / β)) * β ≤ -D := by
    field_simp
    nlinarith
  calc
    _ = ((M + 1) ^ (1 - β) * (C + 1) ^ β) *
        L ^ ((1 - β) + (-((D + 1) / β)) * β) := by
      rw [Real.rpow_add hL0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL hexp) (by positivity)

#print axioms logarithmicInterpolationScalar
end
end FractionalPrimes
