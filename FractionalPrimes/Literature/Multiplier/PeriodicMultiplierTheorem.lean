module

public import FractionalPrimes.Literature.Multiplier.FiniteMultiplierAgreement
public import FractionalPrimes.Literature.Multiplier.ConjugateExponent

/-!
# The periodic multiplier theorem

Package the bounded extension, its exact finite-input action, uniqueness, and
agreement with the Fourier-defined `ℓ²` multiplier on `ℓᵖ ∩ ℓ²`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Multiplier

open scoped ENNReal

noncomputable section

/-- The piecewise constant in the periodic multiplier theorem. For `p > 2`
the blueprint states the lower-range constant at `p/(p-1)`. -/
def periodicMultiplierConstant (p : ℝ) : ℝ :=
  if p < 2 then
    (2 * W * p / (p - 1) + 4 * p / (2 - p)) ^ (1 / p)
  else if p = 2 then
    1
  else
    finiteMultiplierLpNormConstant (p / (p - 1))

/-- The blueprint's high-range constant is the direct coefficient used by
the finite-input multiplier bound. -/
theorem periodicMultiplierConstant_eq_finiteMultiplierLpNormConstant
    {p : ℝ} (hp1 : 1 < p) :
    periodicMultiplierConstant p = finiteMultiplierLpNormConstant p := by
  by_cases hp2 : p < 2
  · simp [periodicMultiplierConstant, finiteMultiplierLpNormConstant, hp2]
  · by_cases hpEq : p = 2
    · subst p
      simp [periodicMultiplierConstant, finiteMultiplierLpNormConstant]
    · have hpHigh : 2 < p :=
        lt_of_le_of_ne (le_of_not_gt hp2) (Ne.symm hpEq)
      have hq2 : p / (p - 1) < 2 :=
        multiplierConjugateExponent_lt_two hpHigh
      simpa [periodicMultiplierConstant, finiteMultiplierLpNormConstant,
        hp2, hpEq, hq2] using
          weakStrongInterpolation_conjugateConstant_eq hpHigh

/-- The periodic multiplier contract: there is a unique continuous linear
extension to sequence `ℓᵖ`, with the blueprint's exact norm constant, which
agrees with the Fourier-defined `ℓ²` multiplier on `ℓᵖ ∩ ℓ²`. -/
theorem periodicMultiplier
    {m : ℝ → ℂ} {D p : ℝ} (h : SymbolData m D) (hp1 : 1 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1.le⟩
    ∃! T : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) →L[ℂ]
        lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      ‖T‖ ≤ periodicMultiplierConstant p * D ∧
      (∀ f : ℤ →₀ ℂ,
        T (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) =
          finiteMultiplierLpMap (p := p) h hp1 f) ∧
      (∀ F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
        ∀ u : lp (fun _ : ℤ => ℂ) 2,
          (F : ℤ → ℂ) = (u : ℤ → ℂ) →
            (T F : ℤ → ℂ) = (TmL2 h u : ℤ → ℂ)) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1.le⟩
  let e := finiteSupportLpInclusion (P := ENNReal.ofReal p)
  have hconstant := periodicMultiplierConstant_eq_finiteMultiplierLpNormConstant hp1
  refine ⟨finiteMultiplierLpExtension h hp1, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa only [hconstant] using
        finiteMultiplierLpExtension_opNorm_le h hp1
    · constructor
      · intro f
        exact finiteMultiplierLpExtension_apply_finite h hp1 f
      · intro F u hFU
        exact finiteMultiplierLpExtension_eq_TmL2_of_lp2 h hp1 F u hFU
  · intro T hT
    have hrestriction : T.toLinearMap.comp e =
        finiteMultiplierLpMap (p := p) h hp1 := by
      apply LinearMap.ext
      intro f
      exact hT.2.1 f
    exact (finiteMultiplierLpExtension_unique h hp1 T hrestriction).symm

end

end FractionalPrimes.Literature.Multiplier
