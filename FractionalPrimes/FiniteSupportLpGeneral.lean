module

public import FractionalPrimes.FiniteSupportLpNorm
public import FractionalPrimes.GeneralDiscreteLpBridge

@[expose] public section

/-!
# Finite-support counting-measure `Lᵖ` and sequence `lp`

For every finite exponent `p ≥ 1`, this module constructs the exact
truncation `if k ∈ s then f k else 0` in both models.  The constructions keep
the pointwise representative and exact finite-sum norm formulas.
-/

namespace FractionalPrimes

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {p : ℝ≥0∞}

/-- A finitely supported complex sequence belongs to counting-measure `Lᵖ`
for every finite exponent `p ≥ 1`. -/
theorem finiteSupportMemLpGeneral
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (_hpOne : 1 ≤ p)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    MemLp (fun k : ℤ => if k ∈ s then f k else 0) p Measure.count := by
  rw [MeasureTheory.memLp_iff,
    eLpNorm_finiteSupport_eq_sum_rpow hp0 hpTop s f]
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  apply ENNReal.rpow_lt_top_of_nonneg
  · positivity
  · have hsum : (∑ k ∈ s, ‖f k‖ₑ ^ p.toReal) < ∞ := by
      apply ENNReal.sum_lt_top.2
      intro k hk
      exact ENNReal.rpow_lt_top_of_nonneg hp.le enorm_lt_top.ne
    exact hsum.ne

/-- The counting-measure `Lᵖ` class of the exact finite truncation. -/
noncomputable def finiteSupportCountLpGeneral
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hpOne : 1 ≤ p)
    (s : Finset ℤ) (f : ℤ → ℂ) : Lp ℂ p (Measure.count : Measure ℤ) :=
  (finiteSupportMemLpGeneral hp0 hpTop hpOne s f).toLp
    (fun k : ℤ => if k ∈ s then f k else 0)

/-- The counting `Lᵖ` constructor has the exact truncation as representative
at every integer. -/
theorem finiteSupportCountLpGeneral_apply
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hpOne : 1 ≤ p)
    (s : Finset ℤ) (f : ℤ → ℂ) (k : ℤ) :
    (finiteSupportCountLpGeneral hp0 hpTop hpOne s f : ℤ → ℂ) k =
      if k ∈ s then f k else 0 := by
  exact ae_count_int_iff_forall.mp
    (MemLp.coeFn_toLp (finiteSupportMemLpGeneral hp0 hpTop hpOne s f)) k

/-- Exact extended `Lᵖ` norm of the finite truncation. -/
theorem finiteSupportCountLpGeneral_eLpNorm
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hpOne : 1 ≤ p)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    eLpNorm (finiteSupportCountLpGeneral hp0 hpTop hpOne s f : ℤ → ℂ)
        p Measure.count =
      (∑ k ∈ s, ‖f k‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
  have hrep :
      (finiteSupportCountLpGeneral hp0 hpTop hpOne s f : ℤ → ℂ) =
        (fun k : ℤ => if k ∈ s then f k else 0) := by
    funext k
    exact finiteSupportCountLpGeneral_apply hp0 hpTop hpOne s f k
  rw [hrep]
  exact eLpNorm_finiteSupport_eq_sum_rpow hp0 hpTop s f

/-- The same finite truncation as a sequence-space `lp` vector, obtained via
the checked counting-measure bridge. -/
noncomputable def finiteSupportSequenceLpGeneral
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hpOne : 1 ≤ p)
    (s : Finset ℤ) (f : ℤ → ℂ) : lp (fun _ : ℤ => ℂ) p := by
  letI : Fact (1 ≤ p) := ⟨hpOne⟩
  exact countLpToGeneralLp hp0 hpTop
    (finiteSupportCountLpGeneral hp0 hpTop hpOne s f)

/-- The sequence-space constructor has the exact truncation at every
integer. -/
theorem finiteSupportSequenceLpGeneral_apply
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hpOne : 1 ≤ p)
    (s : Finset ℤ) (f : ℤ → ℂ) (k : ℤ) :
    finiteSupportSequenceLpGeneral hp0 hpTop hpOne s f k =
      if k ∈ s then f k else 0 := by
  haveI : Fact (1 ≤ p) := ⟨hpOne⟩
  rw [finiteSupportSequenceLpGeneral, countLpToGeneralLp_apply]
  exact finiteSupportCountLpGeneral_apply hp0 hpTop hpOne s f k

/-- Exact extended `Lᵖ` norm of the sequence-space representative. -/
theorem finiteSupportSequenceLpGeneral_eLpNorm
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hpOne : 1 ≤ p)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    eLpNorm (finiteSupportSequenceLpGeneral hp0 hpTop hpOne s f : ℤ → ℂ)
        p Measure.count =
      (∑ k ∈ s, ‖f k‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
  have hrep :
      (finiteSupportSequenceLpGeneral hp0 hpTop hpOne s f : ℤ → ℂ) =
        (fun k : ℤ => if k ∈ s then f k else 0) := by
    funext k
    exact finiteSupportSequenceLpGeneral_apply hp0 hpTop hpOne s f k
  rw [hrep]
  exact eLpNorm_finiteSupport_eq_sum_rpow hp0 hpTop s f

/-- The sequence `lp` norm is the exact finite `p`-moment formula. -/
theorem finiteSupportSequenceLpGeneral_norm
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hpOne : 1 ≤ p)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    ‖finiteSupportSequenceLpGeneral hp0 hpTop hpOne s f‖ =
      (∑ k ∈ s, ‖f k‖ ^ p.toReal) ^ (1 / p.toReal) := by
  haveI : Fact (1 ≤ p) := ⟨hpOne⟩
  rw [finiteSupportSequenceLpGeneral,
    countLpToGeneralLp_norm hp0 hpTop]
  rw [Lp.norm_def, finiteSupportCountLpGeneral_eLpNorm hp0 hpTop hpOne]
  have hsum_ne : ∀ k ∈ s, ‖f k‖ₑ ^ p.toReal ≠ ∞ := by
    intro k hk
    exact (ENNReal.rpow_lt_top_of_nonneg
      (ENNReal.toReal_pos hp0 hpTop).le enorm_lt_top.ne).ne
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_sum hsum_ne]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [← ENNReal.toReal_rpow, toReal_enorm]

/-- The counting-measure `Lᵖ` norm is the same exact finite `p`-moment. -/
theorem finiteSupportCountLpGeneral_norm
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hpOne : 1 ≤ p)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    ‖finiteSupportCountLpGeneral hp0 hpTop hpOne s f‖ =
      (∑ k ∈ s, ‖f k‖ ^ p.toReal) ^ (1 / p.toReal) := by
  haveI : Fact (1 ≤ p) := ⟨hpOne⟩
  rw [← countLpToGeneralLp_norm hp0 hpTop
    (finiteSupportCountLpGeneral hp0 hpTop hpOne s f)]
  exact finiteSupportSequenceLpGeneral_norm hp0 hpTop hpOne s f

end

end FractionalPrimes
