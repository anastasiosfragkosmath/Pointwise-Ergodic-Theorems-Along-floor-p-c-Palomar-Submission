module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalP1Threshold
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalP3SourceInstantiation

/-!
# The positive-degree source correlation bound

The source case split in `conditionalIntegerSourceLargeCorrelation_refutes`
rules out a strict large-correlation witness once the P1-derived data are
available.  This module separates those data from the witness itself and
records the resulting exact non-strict bound.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open FractionalPrimes.Literature.Uniformity.Combinatorics

/-- For natural integer endpoints, the real-indexed interval sum is exactly
the paper's positive-integer block sum. -/
theorem realIntegerInterval_sum_eq_nat_Ioc
    {M : Type*} [AddCommMonoid M] (X H : ℕ) (f : ℤ → M) :
    (∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ), f n) =
      ∑ n ∈ Finset.Ioc X (X + H), f (n : ℤ) := by
  have hfloorX : Int.floor (X : ℝ) = (X : ℤ) := by norm_num
  have hfloorEnd : Int.floor ((X : ℝ) + (H : ℝ)) = ((X + H : ℕ) : ℤ) := by
    rw [← Nat.cast_add]
    norm_num
  have hinterval :
      realIntegerInterval (X : ℝ) (H : ℝ) =
        Finset.Ioc (X : ℤ) ((X + H : ℕ) : ℤ) := by
    ext n
    simp only [realIntegerInterval, Finset.mem_Ico, Finset.mem_Ioc,
      hfloorX, hfloorEnd]
    omega
  rw [hinterval]
  exact (cramerShortInterval_sum_nat_eq_int X H f).symm

/-- All of the exact source context for the positive-degree branch except
the strict large-correlation inequality.  The latter is the assertion to be
contradicted, so it is intentionally not an input field. -/
structure ConditionalIntegerSourceBoundData
    (d X H K c D E a b : ℕ) (A a₀ η δ Cpm Ctw Astar : ℝ)
    (P : Polynomial ℝ) (w : ℤ → ℂ) where
  hInv : arithmeticInverseTasksWithConstants d K c
  hd : 1 ≤ d
  hX : 3 ≤ X
  hA : 0 < A
  hη : 0 < η
  hηmax : η < 3 / 16
  hDsource : A + (b : ℝ) + 5 < (D : ℝ)
  hE : E = 2 * c * D + 3
  hEa : E < a
  hAgtDE : (D : ℝ) + (E : ℝ) + 3 < (a : ℝ)
  hAgtD : d + 3 < a
  ha₀ : a₀ = A + 2 * (E : ℝ) + 50 * (a : ℝ) + 3
  hL : 2 ≤ Real.log (X : ℝ)
  hδpos : 0 < δ
  hδsmall : δ < min (1 / 2) ((Real.log (X : ℝ))⁻¹)
  hδinv : δ⁻¹ = (Real.log (X : ℝ)) ^ (D : ℝ)
  hDelta : δ = (Real.log (X : ℝ)) ^ (-(D : ℝ))
  hDeltaType : δ ≤ decompositionDelta (X : ℝ)
  hThreshold : 4 * decompositionC <
    (Real.log (X : ℝ)) ^ ((D : ℝ) - A - (decompositionB : ℝ))
  hHlower : (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ)
  hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - η)
  hApp : 4 * cramerApproximationConstant (A + 2) (1 / 16 : ℝ) ≤
    (Real.log (X : ℝ)) ^ 2
  hLevel : Real.exp 26 ≤ (Real.log (X : ℝ)) ^ ((D : ℝ) - 4 / 5)
  hCtype : 1 ≤ decompositionC
  hScaleBudget :
    2 * (K : ℝ) * decompositionC * (Real.log (X : ℝ)) ^ (c * D) <
      (X : ℝ) ^ η
  hP : P.natDegree ≤ d
  hL3modulus : (d.factorial : ℝ) * (K : ℝ) ≤
    (Real.log (X : ℝ)) ^ 3
  hL3variation : (d.factorial : ℝ) *
    (1 + 2 * Real.pi * binomialVariationConstant d) * (K : ℝ) ≤
      (Real.log (X : ℝ)) ^ 3
  hL3q : (d.factorial : ℝ) * (K : ℝ) ≤ (Real.log (X : ℝ)) ^ 3
  hL3T : 2 * Real.pi * (d : ℝ) * (K : ℝ) ≤ (Real.log (X : ℝ)) ^ 3
  hL3tv : (d.factorial : ℝ) *
    (1 + 2 * Real.pi * ((d + 1 : ℕ) : ℝ)) * (K : ℝ) ^ 2 ≤
      (Real.log (X : ℝ)) ^ 3
  hLE : (Real.log (X : ℝ)) ^ E ≤ X
  hCpmPos : 0 < Cpm
  hCpmSmall : 2 * Cpm < (Real.log (X : ℝ)) ^ 2
  hMuPrefix :
    residuePrefixEnvelope X H (fun n => (paperMu n : ℂ))
        ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
      Cpm * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a₀)
  hCramerPrefix :
    residuePrefixEnvelope X H
        (fun n => (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
        ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
      Cpm * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a₀)
  hw : w = (fun n => (paperMu n : ℂ)) ∨
    w = (fun n => (paperLambda n : ℂ) -
      (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
  muPTWSelection : RestrictedPTWSelection X Astar (a : ℝ) η Ctw
    mobiusComplexPositiveFunction
  lambdaPTWSelection : RestrictedPTWSelection X Astar (a : ℝ) η Ctw
    vonMangoldtComplexPositiveFunction
  hCtwPos : 0 < Ctw
  hCtwSmall : Ctw < (Real.log (X : ℝ)) ^ 2

/-- Add a hypothetical strict correlation witness to the source data, giving
exactly the context consumed by the checked P2/P3 type case split. -/
def ConditionalIntegerSourceBoundData.toInverseContext
    {d X H K c D E a b : ℕ} {A a₀ η δ Cpm Ctw Astar : ℝ}
    {P : Polynomial ℝ} {w : ℤ → ℂ}
    (data : ConditionalIntegerSourceBoundData d X H K c D E a b
      A a₀ η δ Cpm Ctw Astar P w)
    (hLarge : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        w n * unitFrequencyPhase (P.eval (n : ℝ))‖) :
    ConditionalIntegerInverseContext d X H K c D E a b
      A a₀ η δ Cpm Ctw Astar P w := by
  exact {
    hInv := data.hInv
    hd := data.hd
    hX := data.hX
    hA := data.hA
    hη := data.hη
    hηmax := data.hηmax
    hDsource := data.hDsource
    hE := data.hE
    hEa := data.hEa
    hAgtDE := data.hAgtDE
    hAgtD := data.hAgtD
    ha₀ := data.ha₀
    hL := data.hL
    hδpos := data.hδpos
    hδsmall := data.hδsmall
    hδinv := data.hδinv
    hDelta := data.hDelta
    hDeltaType := data.hDeltaType
    hThreshold := data.hThreshold
    hHlower := data.hHlower
    hHupper := data.hHupper
    hApp := data.hApp
    hLevel := data.hLevel
    hCtype := data.hCtype
    hScaleBudget := data.hScaleBudget
    hP := data.hP
    hL3modulus := data.hL3modulus
    hL3variation := data.hL3variation
    hL3q := data.hL3q
    hL3T := data.hL3T
    hL3tv := data.hL3tv
    hLE := data.hLE
    hCpmPos := data.hCpmPos
    hCpmSmall := data.hCpmSmall
    hMuPrefix := data.hMuPrefix
    hCramerPrefix := data.hCramerPrefix
    hw := data.hw
    muPTWSelection := data.muPTWSelection
    lambdaPTWSelection := data.lambdaPTWSelection
    hCtwPos := data.hCtwPos
    hCtwSmall := data.hCtwSmall
    hLarge := hLarge
  }

/-- The exact source correlation bound for either arithmetic weight follows
from the checked case split, with all hypotheses stated independently of the
correlation being bounded. -/
theorem conditionalIntegerSourceCorrelation_le
    {d X H K c D E a b : ℕ} {A a₀ η δ Cpm Ctw Astar : ℝ}
    {P : Polynomial ℝ} {w : ℤ → ℂ}
    (data : ConditionalIntegerSourceBoundData d X H K c D E a b
      A a₀ η δ Cpm Ctw Astar P w) :
    ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
      w n * unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
        (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  apply le_of_not_gt
  intro hLarge
  exact conditionalIntegerSourceLargeCorrelation_refutes
    (data.toInverseContext hLarge)

/-- Assemble the two original arithmetic weights, retaining the source's
constant two on the large-X range. -/
theorem conditionalIntegerSourceTwoWeightCorrelation_le
    {d X H K c D E a b : ℕ} {A a₀ η δ Cpm Ctw Astar : ℝ}
    {P : Polynomial ℝ}
    (muData : ConditionalIntegerSourceBoundData d X H K c D E a b
      A a₀ η δ Cpm Ctw Astar P (fun n => (paperMu n : ℂ)))
    (lambdaData : ConditionalIntegerSourceBoundData d X H K c D E a b
      A a₀ η δ Cpm Ctw Astar P (fun n =>
        (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ))) :
    ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        (paperMu n : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ +
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        ((paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) *
          unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
        2 * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  have hMu := conditionalIntegerSourceCorrelation_le muData
  have hLambda := conditionalIntegerSourceCorrelation_le lambdaData
  calc
    _ ≤ (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) +
        (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) := add_le_add hMu hLambda
    _ = 2 * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by ring

/-- The source's natural-indexed short-block estimate with its exact constant
two, obtained from the real-integer interval case split by the endpoint
preserving sum adapter above. -/
theorem conditionalIntegerSourceNaturalTwoWeightCorrelation_le
    {d X H K c D E a b : ℕ} {A a₀ η δ Cpm Ctw Astar : ℝ}
    {P : Polynomial ℝ}
    (muData : ConditionalIntegerSourceBoundData d X H K c D E a b
      A a₀ η δ Cpm Ctw Astar P (fun n => (paperMu n : ℂ)))
    (lambdaData : ConditionalIntegerSourceBoundData d X H K c D E a b
      A a₀ η δ Cpm Ctw Astar P (fun n =>
        (paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ))) :
    ‖∑ n ∈ Finset.Ioc X (X + H),
        (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ +
      ‖∑ n ∈ Finset.Ioc X (X + H),
        ((paperLambda (n : ℤ) : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℂ)) *
          unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
        2 * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  have hMuSum :
      (∑ n ∈ Finset.Ioc X (X + H),
        (paperMu (n : ℤ) : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))) =
        ∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          (paperMu n : ℂ) * unitFrequencyPhase (P.eval (n : ℝ)) :=
    (realIntegerInterval_sum_eq_nat_Ioc X H
      (fun n : ℤ => (paperMu n : ℂ) *
        unitFrequencyPhase (P.eval (n : ℝ)))).symm
  have hLambdaSum :
      (∑ n ∈ Finset.Ioc X (X + H),
        ((paperLambda (n : ℤ) : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) (n : ℤ) : ℂ)) *
          unitFrequencyPhase (P.eval (n : ℝ))) =
        ∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          ((paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) *
            unitFrequencyPhase (P.eval (n : ℝ)) :=
    (realIntegerInterval_sum_eq_nat_Ioc X H
      (fun n : ℤ => ((paperLambda n : ℂ) -
        (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) *
          unitFrequencyPhase (P.eval (n : ℝ)))).symm
  rw [hMuSum, hLambdaSum]
  exact conditionalIntegerSourceTwoWeightCorrelation_le muData lambdaData

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.ConditionalIntegerSourceBoundData.toInverseContext
#print axioms FractionalPrimes.Literature.Polynomial.conditionalIntegerSourceCorrelation_le
#print axioms FractionalPrimes.Literature.Polynomial.conditionalIntegerSourceTwoWeightCorrelation_le
#print axioms FractionalPrimes.Literature.Polynomial.realIntegerInterval_sum_eq_nat_Ioc
#print axioms FractionalPrimes.Literature.Polynomial.conditionalIntegerSourceNaturalTwoWeightCorrelation_le
