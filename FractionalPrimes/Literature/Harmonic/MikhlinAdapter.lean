module

public import FractionalPrimes.Literature.Multiplier.PeriodicMultiplierTheorem

/-!
# The harmonic periodic Mikhlin adapter (`ha:mikhlin`)

The harmonic corollary's bounded periodic (C^2) symbol assumptions are
packaged in the same real-line lift used by `SymbolData`. Measurability is
derived from smoothness off the integer translates of zero; it is not an
additional assumption. The source's smooth seam is represented by matching
the value and the first two derivatives at `-1/2` and `1/2`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Harmonic

open FractionalPrimes.Literature.Multiplier
open Set
open scoped ENNReal

noncomputable section

/-- The hypotheses of `ha:mikhlin` on a periodic lift to `ℝ`. The derivative
bound is written with complex norms, which are the absolute values appearing
in the source statement. -/
structure PeriodicMikhlinHypotheses (m : ℝ → ℂ) (D : ℝ) : Prop where
  bounded : ∃ C : ℝ, ∀ x : ℝ, ‖m x‖ ≤ C
  periodic : Function.Periodic m 1
  smoothOnPuncturedTorus : ContDiffOn ℝ 2 m puncturedTorusLift
  seamValue : m (-(1 / 2 : ℝ)) = m (1 / 2)
  seamFirstDerivative : deriv m (-(1 / 2 : ℝ)) = deriv m (1 / 2)
  seamSecondDerivative :
    iteratedDeriv 2 m (-(1 / 2 : ℝ)) = iteratedDeriv 2 m (1 / 2)
  weightedDerivativeBound : ∀ ξ : ℝ, 0 < |ξ| → |ξ| < 1 / 2 →
    ‖m ξ‖ + ‖ξ * deriv m ξ‖ + ‖ξ ^ 2 * iteratedDeriv 2 m ξ‖ ≤ D

/-- Smoothness away from the integer lattice makes an otherwise arbitrary
bounded periodic symbol measurable. This is the measure-theoretic content of
the source's punctured-torus (C^2) assumption. -/
theorem measurable_of_smoothOnPuncturedTorus {m : ℝ → ℂ}
    (hm : ContDiffOn ℝ 2 m puncturedTorusLift) : Measurable m := by
  let s : Set ℝ := Set.range fun n : ℤ => (n : ℝ)
  have hs : s.Countable := Set.countable_range _
  have hcont : ContinuousOn m sᶜ := by
    convert hm.continuousOn using 1
    ext x
    simp [s, puncturedTorusLift, eq_comm]
  have hdom : Continuous (sᶜ.domRestrict m) :=
    continuousOn_iff_continuous_domRestrict.mp hcont
  exact measurable_of_measurable_on_compl_countable s hs hdom.measurable

/-- Convert the source-facing hypotheses into the checked multiplier input.
Only the measurable field is constructed here; the remaining fields have
exactly the hypotheses recorded above. -/
theorem PeriodicMikhlinHypotheses.toSymbolData {m : ℝ → ℂ} {D : ℝ}
    (h : PeriodicMikhlinHypotheses m D) : SymbolData m D :=
  { measurable := measurable_of_smoothOnPuncturedTorus h.smoothOnPuncturedTorus
    bounded := h.bounded
    periodic := h.periodic
    smoothOnPuncturedTorus := h.smoothOnPuncturedTorus
    seamValue := h.seamValue
    seamFirstDerivative := h.seamFirstDerivative
    seamSecondDerivative := h.seamSecondDerivative
    weightedDerivativeBound := h.weightedDerivativeBound }

/-- The bounded periodic Mikhlin multiplier contract from `ha:mikhlin`.
This is the checked periodic-multiplier extension, with its exact finite-input
action and agreement with the Fourier-defined `ℓ²` multiplier. -/
theorem periodicMikhlinAdapter {m : ℝ → ℂ} {D p : ℝ}
    (h : PeriodicMikhlinHypotheses m D) (hp1 : 1 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1.le⟩
    ∃! T : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) →L[ℂ]
        lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      ‖T‖ ≤ periodicMultiplierConstant p * D ∧
      (∀ f : ℤ →₀ ℂ,
        T (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) =
          finiteMultiplierLpMap (p := p) h.toSymbolData hp1 f) ∧
      (∀ F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
        ∀ u : lp (fun _ : ℤ => ℂ) 2,
          (F : ℤ → ℂ) = (u : ℤ → ℂ) →
            (T F : ℤ → ℂ) = (TmL2 h.toSymbolData u : ℤ → ℂ)) := by
  simpa using periodicMultiplier h.toSymbolData hp1

end

end FractionalPrimes.Literature.Harmonic

namespace FractionalPrimes.External

open FractionalPrimes.Literature.Harmonic
open FractionalPrimes.Literature.Multiplier
open scoped ENNReal

/-- Source-index name for the periodic Mikhlin corollary of `lp:main`.
The multiplier and its finite-input/Fourier actions are fixed by the
checked periodic multiplier theorem. -/
theorem periodicMultiplier {m : ℝ → ℂ} {D p : ℝ}
    (h : PeriodicMikhlinHypotheses m D) (hp1 : 1 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1.le⟩
    ∃! T : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p) →L[ℂ]
        lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
      ‖T‖ ≤ periodicMultiplierConstant p * D ∧
      (∀ f : ℤ →₀ ℂ,
        T (finiteSupportLpInclusion (P := ENNReal.ofReal p) f) =
          finiteMultiplierLpMap (p := p) h.toSymbolData hp1 f) ∧
      (∀ F : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
        ∀ u : lp (fun _ : ℤ => ℂ) 2,
          (F : ℤ → ℂ) = (u : ℤ → ℂ) →
            (T F : ℤ → ℂ) = (TmL2 h.toSymbolData u : ℤ → ℂ)) := by
  exact periodicMikhlinAdapter h hp1

end FractionalPrimes.External

end
