module

public import FractionalPrimes.Literature.DirichletAdapter.DPLabelDepthLogBound
public import FractionalPrimes.Literature.DirichletAdapter.SmoothHeathBrownDPComponentAccumulation
public import Mathlib.Tactic

@[expose] public section
namespace FractionalPrimes.Literature.DirichletAdapter
open FractionalPrimes.Literature.Polynomial
open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics
noncomputable section

/-- Pay the exact retained-label count in either source expansion.
The pointwise component envelope `C` is supplied separately by the
checked analytic branch theorem. -/
theorem dpRetainedLabelEnvelopeSums_le
    {X T0 W C : ℝ} {q : ℕ} {a : ℤ}
    (hX : 3 ≤ X) (hC : 0 ≤ C)
    (hμ : ∀ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
      dirichletMeanEnvelopeOfA_X
        (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
          (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν))
        T0 W ≤ C)
    (hΛ : ∀ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
      dirichletMeanEnvelopeOfA_X
        (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
          (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν))
        T0 W ≤ C) :
    (∑ ν ∈ smoothHeathBrownMobiusRetainedLabels X,
      dirichletMeanEnvelopeOfA_X
        (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
          (smoothHeathBrownMobiusComponent (dyadicMobiusCutoff X) ν))
        T0 W) ≤ 10 * (8 * Real.log X) ^ 20 * C ∧
    (∑ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X,
      dirichletMeanEnvelopeOfA_X
        (smoothHeathBrownComponentOuterCutoffMellinPolynomial X q a
          (smoothHeathBrownVonMangoldtComponent (dyadicMobiusCutoff X) ν))
        T0 W) ≤ 10 * (8 * Real.log X) ^ 20 * C := by
  classical
  have hcards := smoothHeathBrownRetainedLabels_card_le_log_power hX
  constructor
  · calc
      _ ≤ ∑ ν ∈ smoothHeathBrownMobiusRetainedLabels X, C := by
        apply Finset.sum_le_sum
        intro ν hν
        exact hμ ν hν
      _ = ((smoothHeathBrownMobiusRetainedLabels X).card : ℝ) * C := by
        simp [Finset.sum_const, mul_comm]
      _ ≤ 10 * (8 * Real.log X) ^ 20 * C :=
        mul_le_mul_of_nonneg_right hcards.1 hC
  · calc
      _ ≤ ∑ ν ∈ smoothHeathBrownVonMangoldtRetainedLabels X, C := by
        apply Finset.sum_le_sum
        intro ν hν
        exact hΛ ν hν
      _ = ((smoothHeathBrownVonMangoldtRetainedLabels X).card : ℝ) * C := by
        simp [Finset.sum_const, mul_comm]
      _ ≤ 10 * (8 * Real.log X) ^ 20 * C :=
        mul_le_mul_of_nonneg_right hcards.2 hC

#print axioms dpRetainedLabelEnvelopeSums_le
end
end FractionalPrimes.Literature.DirichletAdapter
