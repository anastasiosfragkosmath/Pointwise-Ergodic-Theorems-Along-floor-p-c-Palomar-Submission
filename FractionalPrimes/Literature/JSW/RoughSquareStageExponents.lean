module

public import Mathlib

/-! Exact exponent arithmetic for the finite stages of the approved
`lj:rough-square` bootstrap. -/

@[expose] public section

namespace FractionalPrimes.Literature.JSW

noncomputable def roughSquareLower (q : ℝ) : ℝ := 2 * q / (q + 1)
noncomputable def roughSquareUpper (q : ℝ) : ℝ := 2 * q / (q - 1)

/-- The blueprint's chosen auxiliary exponent remains in the open stage
interval and lies farther from `2` than the target exponent. -/
theorem roughSquareStage_auxiliaryExponent
    {q p : ℝ} (hq : 1 < q)
    (hlo : roughSquareLower q < p)
    (hhi : p < roughSquareUpper q)
    (hp : p ≠ 2) :
    ∃ u : ℝ,
      (if p < 2 then u = (roughSquareLower q + p) / 2 ∧
        roughSquareLower q < u ∧ u < p ∧ p < 2
       else u = (p + roughSquareUpper q) / 2 ∧
        2 < p ∧ p < u ∧ u < roughSquareUpper q) := by
  have hq1 : 0 < q + 1 := by linarith
  have hqm1 : 0 < q - 1 := by linarith
  have hL2 : roughSquareLower q < 2 := by
    unfold roughSquareLower
    apply (div_lt_iff₀ hq1).2
    nlinarith
  have h2U : 2 < roughSquareUpper q := by
    unfold roughSquareUpper
    apply (lt_div_iff₀ hqm1).2
    nlinarith
  split_ifs with hlow
  · refine ⟨(roughSquareLower q + p) / 2, ?_⟩
    constructor
    · rfl
    constructor
    · linarith
    constructor
    · linarith
    · exact hlow
  · have hhigh : 2 < p := lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm hp)
    refine ⟨(p + roughSquareUpper q) / 2, ?_⟩
    constructor
    · rfl
    constructor
    · exact hhigh
    constructor
    · linarith
    · linarith

private theorem interpolationWeight_of_strictBetween
    {a b c : ℝ} (h : (c < b ∧ b < a) ∨ (a < b ∧ b < c)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ b = θ * a + (1 - θ) * c := by
  let θ : ℝ := (b - c) / (a - c)
  have hac : a - c ≠ 0 := by
    rcases h with h | h
    · exact ne_of_gt (sub_pos.mpr (lt_trans h.1 h.2))
    · exact ne_of_lt (sub_neg.mpr (lt_trans h.1 h.2))
  have hθpos : 0 < θ := by
    rcases h with h | h
    · exact div_pos (sub_pos.mpr h.1) (sub_pos.mpr (lt_trans h.1 h.2))
    · exact div_pos_of_neg_of_neg (sub_neg.mpr h.2)
        (sub_neg.mpr (lt_trans h.1 h.2))
  have hθlt : θ < 1 := by
    rcases h with h | h
    · apply (div_lt_iff₀ (sub_pos.mpr (lt_trans h.1 h.2))).2
      linarith
    · apply (div_lt_iff_of_neg (sub_neg.mpr (lt_trans h.1 h.2))).2
      linarith
  refine ⟨θ, hθpos, hθlt, ?_⟩
  dsimp [θ]
  field_simp
  ring

/-- For the source choice of `u`, the reciprocal exponent of `p` is a
strict convex interpolation between those of `2` and `u`. -/
theorem roughSquareStage_interpolationWeight
    {p u : ℝ} (h : (u < p ∧ p < 2 ∧ 0 < u) ∨ (2 < p ∧ p < u)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      p⁻¹ = θ * (2 : ℝ)⁻¹ + (1 - θ) * u⁻¹ := by
  have hbetween :
      (u⁻¹ < p⁻¹ ∧ p⁻¹ < (2 : ℝ)⁻¹) ∨
      ((2 : ℝ)⁻¹ < p⁻¹ ∧ p⁻¹ < u⁻¹) := by
    rcases h with h | h
    · right
      have hp0 : 0 < p := lt_trans h.2.2 h.1
      constructor
      · exact (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) hp0).2 h.2.1
      · exact (inv_lt_inv₀ hp0 h.2.2).2 h.1
    · left
      have hp0 : 0 < p := by linarith
      have hu0 : 0 < u := by linarith
      constructor
      · exact (inv_lt_inv₀ hu0 hp0).2 h.2
      · exact (inv_lt_inv₀ hp0 (by norm_num : (0 : ℝ) < 2)).2 h.1
  exact interpolationWeight_of_strictBetween hbetween

#print axioms roughSquareStage_auxiliaryExponent
#print axioms roughSquareStage_interpolationWeight

end FractionalPrimes.Literature.JSW

end
