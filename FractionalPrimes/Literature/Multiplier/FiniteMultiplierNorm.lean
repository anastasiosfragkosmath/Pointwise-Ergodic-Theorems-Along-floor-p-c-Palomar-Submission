module

public import FractionalPrimes.FiniteSupportLpGeneral
public import FractionalPrimes.Literature.Multiplier.FiniteMultiplierCore

/-!
# Norm bounds for the finite-input multiplier map

This file identifies the input norm with its exact finite moment and records
the lower, central, and upper exponent bounds for the canonical finite-input
multiplier map. These are the uniform finite-domain bounds needed for the
dense extension.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open scoped ENNReal

noncomputable section

/-- The `ℓᵖ` norm of the canonical inclusion of a finitely supported
sequence is its exact finite `p`-moment. -/
theorem finiteSupportLpInclusion_norm
    {p : ℝ} (hp1 : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] (f : ℤ →₀ ℂ) :
    ‖finiteSupportLpInclusion (P := ENNReal.ofReal p) f‖ =
      (∑ k ∈ f.support, ‖f k‖ ^ p) ^ (1 / p) := by
  have hpReal : 0 < p := lt_trans zero_lt_one hp1
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpReal
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hPto : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal hpReal.le
  have hEq :
      finiteSupportLpInclusion (P := ENNReal.ofReal p) f =
        FractionalPrimes.finiteSupportSequenceLpGeneral hp0 hpTop Fact.out
          f.support (f : ℤ → ℂ) := by
    apply lp.ext
    funext k
    rw [finiteSupportLpInclusion_apply,
      FractionalPrimes.finiteSupportSequenceLpGeneral_apply
        hp0 hpTop Fact.out f.support (f : ℤ → ℂ) k]
    by_cases hk : k ∈ f.support
    · simp [hk]
    · have hfk : f k = 0 := by
        by_contra hne
        exact hk (Finsupp.mem_support_iff.mpr hne)
      simp [hk, hfk]
  rw [hEq, FractionalPrimes.finiteSupportSequenceLpGeneral_norm
    hp0 hpTop Fact.out f.support (f : ℤ → ℂ), hPto]

/-- Casting an `lp` vector across an equality of exponents preserves its
pointwise representative. -/
private theorem lp_cast_apply
    {p q : ℝ≥0∞} (hpq : p = q) (F : lp (fun _ : ℤ => ℂ) p) (k : ℤ) :
    (hpq ▸ F) k = F k := by
  cases hpq
  rfl

/-- Casting an `lp` vector across an equality of exponents preserves its
norm. -/
private theorem lp_cast_norm
    {p q : ℝ≥0∞} (hpq : p = q) (F : lp (fun _ : ℤ => ℂ) p) :
    ‖hpq ▸ F‖ = ‖F‖ := by
  cases hpq
  rfl

/-- For `1 < p < 2`, the canonical finite-input map obeys the blueprint's
lower-range constant times the exact input `ℓᵖ` norm. -/
theorem finiteMultiplierLpMap_norm_le_lower
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hD : 0 < D)
    (hp1 : 1 < p) (hp2 : p < 2)
    [Fact (1 ≤ ENNReal.ofReal p)] (f : ℤ →₀ ℂ) :
    ‖finiteMultiplierLpMap (p := p) h hp1 f‖ ≤
      (2 * W * p / (p - 1) + 4 * p / (2 - p)) ^ (1 / p) * D *
        ‖finiteSupportLpInclusion (P := ENNReal.ofReal p) f‖ := by
  obtain ⟨F, hF, hFnorm⟩ :=
    exists_TmL2_lp_of_finsupp h hD hp1 hp2 f
  have hFmap : F = finiteMultiplierLpMap (p := p) h hp1 f := by
    apply lp.ext
    funext k
    calc
      F k = TmL2 h (finiteSequenceL2 f) k := congrFun hF k
      _ = finiteMultiplierLpMap (p := p) h hp1 f k := by simp
  have hinput := finiteSupportLpInclusion_norm hp1 f
  calc
    ‖finiteMultiplierLpMap (p := p) h hp1 f‖ = ‖F‖ := by rw [← hFmap]
    _ ≤ (2 * W * p / (p - 1) + 4 * p / (2 - p)) ^ (1 / p) * D *
        (∑ k ∈ f.support, ‖f k‖ ^ p) ^ (1 / p) := hFnorm
    _ = (2 * W * p / (p - 1) + 4 * p / (2 - p)) ^ (1 / p) * D *
        ‖finiteSupportLpInclusion (P := ENNReal.ofReal p) f‖ := by rw [← hinput]

/-- At `p = 2`, the finite-input map obeys the direct multiplier bound with
constant exactly `D`. -/
theorem finiteMultiplierLpMap_norm_le_two
    {m : ℝ → ℂ} {D : ℝ} (h : SymbolData m D) (hp1 : 1 < (2 : ℝ))
    [Fact (1 ≤ ENNReal.ofReal (2 : ℝ))] (f : ℤ →₀ ℂ) :
    ‖finiteMultiplierLpMap (p := 2) h hp1 f‖ ≤
      D * ‖finiteSupportLpInclusion (P := ENNReal.ofReal (2 : ℝ)) f‖ := by
  have hP : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let F₂ : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞) :=
    hP ▸ finiteMultiplierLpMap (p := 2) h hp1 f
  let f₂ : lp (fun _ : ℤ => ℂ) (2 : ℝ≥0∞) :=
    hP ▸ finiteSupportLpInclusion (P := ENNReal.ofReal (2 : ℝ)) f
  have hF₂ : F₂ = TmL2 h (finiteSequenceL2 f) := by
    apply lp.ext
    funext k
    change (hP ▸ finiteMultiplierLpMap (p := 2) h hp1 f) k = _
    rw [lp_cast_apply hP]
    simp
  have hf₂ : f₂ = finiteSequenceL2 f := by
    apply lp.ext
    funext k
    change (hP ▸ finiteSupportLpInclusion
      (P := ENNReal.ofReal (2 : ℝ)) f) k = _
    rw [lp_cast_apply hP]
    simp
  have hinputNorm :
      ‖finiteSupportLpInclusion (P := ENNReal.ofReal (2 : ℝ)) f‖ =
        ‖finiteSequenceL2 f‖ := by
    calc
      _ = ‖f₂‖ := (lp_cast_norm hP _).symm
      _ = ‖finiteSequenceL2 f‖ := congrArg norm hf₂
  calc
    ‖finiteMultiplierLpMap (p := 2) h hp1 f‖ = ‖F₂‖ :=
      (lp_cast_norm hP _).symm
    _ = ‖TmL2 h (finiteSequenceL2 f)‖ := congrArg norm hF₂
    _ ≤ D * ‖finiteSequenceL2 f‖ := norm_TmL2_finiteSequenceL2_le h f
    _ = D * ‖finiteSupportLpInclusion (P := ENNReal.ofReal (2 : ℝ)) f‖ := by
      rw [hinputNorm]

/-- For `p > 2`, the canonical finite-input map obeys the blueprint's
upper-range constant times the exact input `ℓᵖ` norm. -/
theorem finiteMultiplierLpMap_norm_le_high
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hD : 0 < D)
    (hp2 : 2 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] (f : ℤ →₀ ℂ) :
    ‖finiteMultiplierLpMap (p := p) h (by linarith) f‖ ≤
      (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) * D *
        ‖finiteSupportLpInclusion (P := ENNReal.ofReal p) f‖ := by
  have hp1 : 1 < p := by linarith
  obtain ⟨F, hF, hFnorm⟩ :=
    exists_TmL2_lp_of_finsupp_high h hD hp2 f
  have hFmap : F = finiteMultiplierLpMap (p := p) h hp1 f := by
    apply lp.ext
    funext k
    calc
      F k = TmL2 h (finiteSequenceL2 f) k := congrFun hF k
      _ = finiteMultiplierLpMap (p := p) h hp1 f k := by simp
  have hinput := finiteSupportLpInclusion_norm hp1 f
  calc
    ‖finiteMultiplierLpMap (p := p) h hp1 f‖ = ‖F‖ := by rw [← hFmap]
    _ ≤ (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) * D *
        (∑ k ∈ f.support, ‖f k‖ ^ p) ^ (1 / p) := hFnorm
    _ = (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p) * D *
        ‖finiteSupportLpInclusion (P := ENNReal.ofReal p) f‖ := by rw [← hinput]

/-- The branchwise finite-input multiplier constant in the three exponent
ranges. -/
def finiteMultiplierLpNormConstant (p : ℝ) : ℝ :=
  if p < 2 then
    (2 * W * p / (p - 1) + 4 * p / (2 - p)) ^ (1 / p)
  else if p = 2 then 1
  else
    (2 * W * p + 4 * p / (p - 2)) ^ ((p - 1) / p)

/-- The branchwise interpolation constant is nonnegative on the full range
`p > 1`. -/
theorem finiteMultiplierLpNormConstant_nonneg {p : ℝ} (hp1 : 1 < p) :
    0 ≤ finiteMultiplierLpNormConstant p := by
  have hW : 0 ≤ W := by
    rw [W_eq, H₀_eq, A_eq]
    nlinarith [B_pos]
  unfold finiteMultiplierLpNormConstant
  split_ifs with hp2 hpEq
  · have hp0 : 0 < p := lt_trans zero_lt_one hp1
    have hpm1 : 0 < p - 1 := by linarith
    have h2mp : 0 < 2 - p := by linarith
    have hbase : 0 ≤ 2 * W * p / (p - 1) + 4 * p / (2 - p) := by
      positivity
    exact Real.rpow_nonneg hbase _
  · simp
  · have hp2 : 2 < p := by
      have hle : 2 ≤ p := le_of_not_gt hp2
      exact lt_of_le_of_ne hle (by
        intro hEq
        exact hpEq hEq.symm)
    have hp0 : 0 < p := lt_trans zero_lt_one hp1
    have h2mp : 0 < p - 2 := by linarith
    have hbase : 0 ≤ 2 * W * p + 4 * p / (p - 2) := by
      positivity
    exact Real.rpow_nonneg hbase _

/-- The canonical finite-input multiplier is bounded on `ℓᵖ` for every
`p > 1`, with the exact source-order constant in each branch. -/
theorem finiteMultiplierLpMap_norm_le
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hp1 : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] (f : ℤ →₀ ℂ) :
    ‖finiteMultiplierLpMap (p := p) h hp1 f‖ ≤
      finiteMultiplierLpNormConstant p * D *
        ‖finiteSupportLpInclusion (P := ENNReal.ofReal p) f‖ := by
  by_cases hDzero : D = 0
  · have hzero : TmL2 h (finiteSequenceL2 f) = 0 :=
      TmL2_eq_zero_of_D_eq_zero h hDzero (finiteSequenceL2 f)
    have hmapzero : finiteMultiplierLpMap (p := p) h hp1 f = 0 := by
      apply lp.ext
      funext k
      simp only [finiteMultiplierLpMap_apply]
      exact congrArg (fun u : lp (fun _ : ℤ => ℂ) 2 => u k) hzero
    rw [hmapzero, norm_zero, hDzero]
    simp
  · have hDpos : 0 < D := lt_of_le_of_ne h.D_nonneg (Ne.symm hDzero)
    rcases lt_trichotomy p 2 with hp2 | hp2 | hp2
    · simpa [finiteMultiplierLpNormConstant, hp2] using
        finiteMultiplierLpMap_norm_le_lower h hDpos hp1 hp2 f
    · subst p
      simpa [finiteMultiplierLpNormConstant] using
        finiteMultiplierLpMap_norm_le_two h (by norm_num)
          (f := f)
    · have hp1' : 1 < p := hp1
      simpa [finiteMultiplierLpNormConstant,
        not_lt_of_gt hp2, ne_of_gt hp2] using
        finiteMultiplierLpMap_norm_le_high h hDpos hp2 f

end

end FractionalPrimes.Literature.Multiplier
