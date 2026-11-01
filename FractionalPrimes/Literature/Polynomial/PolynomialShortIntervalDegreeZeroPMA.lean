module

public import FractionalPrimes.Literature.Polynomial.PolynomialShortIntervalQOneAdapter
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Degree-zero branch of the conditional integer short-interval estimate

For a constant polynomial phase, each twisted sum has the same norm as its
untwisted full interval sum.  The modulus-one adapter places these two sums
inside the corresponding residue-prefix envelopes, so the source PMA bound
applies directly with its unchanged common constant.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open scoped BigOperators

/-- A polynomial of natDegree at most zero is constant, and multiplication by
its unit-frequency phase leaves the norm of any finite interval sum
unchanged. -/
theorem norm_interval_sum_mul_degreeZero_phase
    (X H : ℕ) (w : ℤ → ℂ) (P : Polynomial ℝ)
    (hP : P.natDegree ≤ 0) :
    ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        w n * unitFrequencyPhase (P.eval (n : ℝ))‖ =
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ), w n‖ := by
  classical
  have hnat : P.natDegree = 0 := by omega
  have hconst : P = Polynomial.C (P.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hnat
  have hphase (n : ℤ) :
      unitFrequencyPhase (P.eval (n : ℝ)) =
        unitFrequencyPhase (P.coeff 0) := by
    rw [hconst]
    simp
  have hsum :
      (∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        w n * unitFrequencyPhase (P.eval (n : ℝ))) =
      (∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ), w n) *
        unitFrequencyPhase (P.coeff 0) := by
    calc
      (∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          w n * unitFrequencyPhase (P.eval (n : ℝ))) =
        ∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          w n * unitFrequencyPhase (P.coeff 0) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [hphase]
      _ = (∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ), w n) *
          unitFrequencyPhase (P.coeff 0) := by rw [Finset.sum_mul]
  rw [hsum, norm_mul, norm_unitFrequencyPhase, mul_one]

/-- The exact degree-zero case of `lupo:conditional-integer`, proved from
the source PMA contract alone.  It retains the PMA constant and all source
interval hypotheses. -/
theorem degreeZeroIntegerUniformityOfPMA
    (hPMA : polynomialMajorArcTask)
    (A η : ℝ) (hA : 0 < A) (hη : 0 < η) (hηmax : η < 3 / 16) :
    ∃ C : ℝ, 0 < C ∧
      ∀ X H : ℕ, 3 ≤ X →
        (X : ℝ) ^ ((5 / 8 : ℝ) + η) ≤ (H : ℝ) →
        (H : ℝ) ≤ (X : ℝ) ^ (1 - η) →
        ∀ P : Polynomial ℝ, P.natDegree ≤ 0 →
          ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
              (paperMu n : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ +
            ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
              ((paperLambda n : ℂ) -
                (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) *
                  unitFrequencyPhase (P.eval (n : ℝ))‖ ≤
            C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    hPMA A 1 η hA (by norm_num) hη hηmax
  refine ⟨C, hC, ?_⟩
  intro X H hX hHlower hHupper P hP
  have hXreal : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three.le
  have hlogX : (1 : ℝ) ≤ Real.log (X : ℝ) := by
    exact le_trans hlog3 (Real.log_le_log (by norm_num) hXreal)
  have hPMA_bound := hbound X H hX hHlower hHupper
  have hPMA_bound' :
      residuePrefixEnvelope X H (fun n => (paperMu n : ℂ))
          (Real.log (X : ℝ)) +
        residuePrefixEnvelope X H
          (fun n => (paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
          (Real.log (X : ℝ)) ≤
        C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := by
    simpa using hPMA_bound
  have hmu := norm_interval_sum_mul_degreeZero_phase X H
    (fun n => (paperMu n : ℂ)) P hP
  have hlam := norm_interval_sum_mul_degreeZero_phase X H
    (fun n => (paperLambda n : ℂ) -
      (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) P hP
  calc
    ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        (paperMu n : ℂ) * unitFrequencyPhase (P.eval (n : ℝ))‖ +
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
        ((paperLambda n : ℂ) -
          (paperShortBlockCramerWeight (X : ℝ) n : ℂ)) *
            unitFrequencyPhase (P.eval (n : ℝ))‖ =
      ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          (paperMu n : ℂ)‖ +
        ‖∑ n ∈ realIntegerInterval (X : ℝ) (H : ℝ),
          ((paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))‖ := by
              rw [hmu, hlam]
    _ ≤ residuePrefixEnvelope X H (fun n => (paperMu n : ℂ))
          (Real.log (X : ℝ)) +
        residuePrefixEnvelope X H
          (fun n => (paperLambda n : ℂ) -
            (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
          (Real.log (X : ℝ)) := by
            exact add_le_add
              (norm_sum_interval_le_residuePrefixEnvelope X H
                (fun n => (paperMu n : ℂ)) (Real.log (X : ℝ)) hlogX)
              (norm_sum_interval_le_residuePrefixEnvelope X H
                (fun n => (paperLambda n : ℂ) -
                  (paperShortBlockCramerWeight (X : ℝ) n : ℂ))
                (Real.log (X : ℝ)) hlogX)
    _ ≤ C * (H : ℝ) * (Real.log (X : ℝ)) ^ (-A : ℝ) := hPMA_bound'

end FractionalPrimes.Literature.Polynomial

end

#print axioms FractionalPrimes.Literature.Polynomial.norm_interval_sum_mul_degreeZero_phase
#print axioms FractionalPrimes.Literature.Polynomial.degreeZeroIntegerUniformityOfPMA
