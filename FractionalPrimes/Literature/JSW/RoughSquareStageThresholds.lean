module

public import FractionalPrimes.Literature.JSW.RoughSquareStageExponents
public import FractionalPrimes.Literature.JSW.PositiveExponentCriterion

/-! Exact finite-stage thresholds of the approved square bootstrap. -/
@[expose] public section
namespace FractionalPrimes.Literature.JSW
noncomputable section

def roughSquareThreshold (n : ℕ) : ℝ := (2 : ℝ)^(n+1) / ((2 : ℝ)^(n+1)-1)

theorem roughSquareThreshold_one_lt (n : ℕ) : 1 < roughSquareThreshold n := by
  have h : 1 < (2 : ℝ)^(n+1) := one_lt_pow₀ (by norm_num) (by omega)
  unfold roughSquareThreshold
  exact (lt_div_iff₀ (by linarith : 0 < (2 : ℝ)^(n+1)-1)).2 (by linarith)

@[simp] theorem roughSquareThreshold_zero : roughSquareThreshold 0 = 2 := by
  norm_num [roughSquareThreshold]

private theorem roughSquareLower_ratio {a : ℝ} (ha : 1 < a) :
    2*a/(2*a-1) = 2*(a/(a-1))/(a/(a-1)+1) := by
  have h0 : a-1 ≠ 0 := by linarith
  have h1 : 2*a-1 ≠ 0 := by linarith
  have h2 : a/(a-1)+1 ≠ 0 := by
    have : 0 < a/(a-1) := div_pos (by linarith) (by linarith)
    linarith
  field_simp [h0, h1, h2]
  ring

theorem roughSquareThreshold_succ (n : ℕ) :
    roughSquareThreshold (n+1) = roughSquareLower (roughSquareThreshold n) := by
  have h : 1 < (2 : ℝ)^(n+1) := one_lt_pow₀ (by norm_num) (by omega)
  unfold roughSquareThreshold roughSquareLower
  rw [pow_succ]
  simpa only [mul_comm] using roughSquareLower_ratio h

theorem roughSquareThreshold_eventually_below {p : ℝ} (hp : 1 < p) :
    ∃ n : ℕ, roughSquareThreshold n < p := by
  obtain ⟨n, hn⟩ := add_one_pow_unbounded_of_pos (p/(p-1)) (show (0 : ℝ) < 1 by norm_num)
  norm_num only [one_add_one_eq_two] at hn
  have hp0 : 0 < p-1 := by linarith
  have hpow : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
  have hlarge : p < (p-1) * (2 : ℝ)^(n+1) := by
    have hmul := (div_lt_iff₀ hp0).mp hn
    rw [pow_succ]
    nlinarith
  have hden : 0 < (2 : ℝ)^(n+1)-1 := by
    have := one_lt_pow₀ (show (1 : ℝ) < 2 by norm_num) (show n+1 ≠ 0 by omega)
    linarith
  refine ⟨n, ?_⟩
  exact (div_lt_iff₀ hden).2 (by nlinarith)

theorem roughSquareThreshold_region_of_lower
    {p q : ℝ} (hq : 1 < q) (hp : 1 < p) (hp2 : p < 2)
    (hlo : roughSquareLower q < p) :
    |p⁻¹ - (2 : ℝ)⁻¹| < (2*q)⁻¹ := by
  apply (lower_maximal_exponent_criterion hp hp2 hq).1
  apply (lt_div_iff₀ (by linarith : 0 < 2-p)).2
  have h := (div_lt_iff₀ (by linarith : 0 < q+1)).1 hlo
  nlinarith

theorem roughSquareThreshold_exists_region {p : ℝ} (hp : 1 < p) :
    ∃ n : ℕ, |p⁻¹ - (2 : ℝ)⁻¹| < (2*roughSquareThreshold n)⁻¹ := by
  by_cases hlow : p < 2
  · have hs : 1 < p/(2-p) := (lt_div_iff₀ (by linarith)).2 (by linarith)
    obtain ⟨n, hn⟩ := roughSquareThreshold_eventually_below hs
    exact ⟨n, (lower_maximal_exponent_criterion hp hlow (roughSquareThreshold_one_lt n)).1 hn⟩
  · by_cases heq : p = 2
    · subst p
      refine ⟨0, ?_⟩
      norm_num
    · have hhigh : 2 < p := by rcases lt_or_gt_of_ne heq with h | h <;> linarith
      have hs : 1 < p/(p-2) := (lt_div_iff₀ (by linarith)).2 (by linarith)
      obtain ⟨n, hn⟩ := roughSquareThreshold_eventually_below hs
      exact ⟨n, (upper_maximal_exponent_criterion hhigh (roughSquareThreshold_one_lt n)).1 hn⟩

#print axioms roughSquareThreshold_succ
#print axioms roughSquareThreshold_exists_region
end
end FractionalPrimes.Literature.JSW
end
