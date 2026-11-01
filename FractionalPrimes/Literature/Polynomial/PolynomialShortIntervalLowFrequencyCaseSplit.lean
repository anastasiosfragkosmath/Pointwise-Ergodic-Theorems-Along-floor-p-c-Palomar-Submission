module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalLowFrequencyDecay
public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalPMAOneWeight

/-!
# Original-weight low-frequency contradiction

This is the low-frequency Type-II case in the conditional integer-centered
polynomial argument.  It applies the one-weight residue-prefix estimate to
the original weight and contradicts a strict large-correlation hypothesis.
The two original weights are exactly the Möbius weight and the centered
Cramér error from `polynomialMajorArcTask_oneWeightBounds`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes.Literature.Uniformity
open scoped BigOperators

/-- The source low-frequency branch is incompatible with a correlation
strictly larger than `H (log X)^(-A)`.  The two one-weight prefix bounds are
the same-constant estimates extracted from `polynomialMajorArcTask`; the
frequency variation is the exact `(X,X+H]` hypothesis of the preceding
low-frequency lemma. -/
theorem lowFrequencyTypeII_refutes_largeCorrelation
    (X H : ℕ) (A a₀ η : ℝ) (E a : ℕ) (T : ℝ) (q : ℕ)
    (g w : ℤ → ℂ) (C : ℝ)
    (hX : 3 ≤ X)
    (hη : 0 < η) (_hηmax : η < 3 / 16)
    (hHlower : (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ))
    (hHupper : (H : ℝ) ≤ (X : ℝ) ^ (1 - η))
    (hL : 2 ≤ Real.log (X : ℝ))
    (hA : 0 < A)
    (ha₀ : a₀ = A + 2 * (E : ℝ) + 50 * (a : ℝ) + 3)
    (_ha : 1 ≤ a) (hEa : E < a)
    (hCpos : 0 < C)
    (hCsmall : 2 * C < (Real.log (X : ℝ)) ^ 2)
    (hMuPrefix :
      residuePrefixEnvelope X H (fun n => (paperMu n : ℂ))
          ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
        C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a₀))
    (hCramerPrefix :
      residuePrefixEnvelope X H
          (fun n => (paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
          ((Real.log (X : ℝ)) ^ (a : ℝ)) ≤
        C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a₀))
    (hw : w = (fun n => (paperMu n : ℂ)) ∨
      w = (fun n => (paperLambda n : ℂ) -
        (paperShortBlockCramerWeight (X : ℝ) n : ℂ)))
    (hq : 0 < q) (hqBound : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ E)
    (hTlow : |T| < (X : ℝ) / (H : ℝ) *
      (Real.log (X : ℝ)) ^ (50 * a))
    (hTwisted :
      residueClassTotalVariation (logPhaseIntegerInterval (X : ℝ) (H : ℝ))
        (fun n => g n * archimedeanTwist (-T) (n : ℝ)) q hq ≤
          ENNReal.ofReal ((Real.log (X : ℝ)) ^ E))
    (hLarge : (H : ℝ) * (Real.log (X : ℝ)) ^ (-A) <
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ), w n * g n‖) :
    False := by
  have hXone : (1 : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hLengthExponent : 0 ≤ (5 / 8 : ℝ) + η := by positivity
  have hHoneReal : (1 : ℝ) ≤ (H : ℝ) := by
    calc
      1 ≤ (X : ℝ) ^ ((5 / 8 : ℝ) + η) := Real.one_le_rpow hXone hLengthExponent
      _ ≤ (H : ℝ) := hHlower
  have hHone : 1 ≤ H := by exact_mod_cast hHoneReal
  have hEtaExponent : 1 - η ≤ 1 := by linarith
  have hUpperPower : (X : ℝ) ^ (1 - η) ≤ (X : ℝ) := by
    calc
      (X : ℝ) ^ (1 - η) ≤ (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone hEtaExponent
      _ = (X : ℝ) := Real.rpow_one _
  have hHleX : H ≤ X := by
    exact_mod_cast (le_trans hHupper hUpperPower)
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hPrefix :
      residuePrefixEnvelope X H w ((Real.log (X : ℝ)) ^ a) ≤
        C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-a₀) := by
    rcases hw with hmu | hcr
    · subst w
      simpa only [← Real.rpow_natCast] using hMuPrefix
    · subst w
      simpa only [← Real.rpow_natCast] using hCramerPrefix
  have hVariation := lowFrequencyTypeII_residuePrefixBound
    X H E a (Real.log (X : ℝ)) T q hX hHone hHleX hL hEa hq hqBound
      hTlow g w hTwisted
  have hDecay := lowFrequencyTypeII_majorArcDecay
    A a₀ (Real.log (X : ℝ)) C (H : ℝ)
      (residuePrefixEnvelope X H w ((Real.log (X : ℝ)) ^ a))
      (‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ), w n * g n‖)
      E a hA hL hHpos ha₀ hCpos hCsmall hPrefix hVariation
  exact (lt_asymm hLarge hDecay).elim

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.lowFrequencyTypeII_refutes_largeCorrelation
