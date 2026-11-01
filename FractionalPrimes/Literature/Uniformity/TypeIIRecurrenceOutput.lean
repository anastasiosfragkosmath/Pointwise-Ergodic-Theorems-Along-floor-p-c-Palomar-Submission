module

public import FractionalPrimes.Literature.Uniformity.CoefficientRecurrenceToLogPhase

/-!
# The logarithmic-phase output of the Type-II coefficient recurrence

This is blueprint node `lu:inverse-ii-output`. The hypothesis is the
displayed coefficient recurrence with a specified `1 ≤ Q ≤ K`; the theorem
does not assume the arithmetic inverse task. The phase in its conclusion
is the original polynomial, evaluated at the original integer arguments.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The canonical centered coefficient expansion evaluates to the original
polynomial, with no change of the integer arguments. -/
theorem correctedCenteredRealPhase_canonical
    (d : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (X : ℤ) (t : ℝ) :
    correctedCenteredRealPhase d (X : ℝ)
        (fun j => (phaseCenteredAt P X).coeff j) t = P.eval t := by
  have heval := congrArg (fun R : Polynomial ℝ => R.eval (t - (X : ℝ)))
    (phaseCenteredAt_monomial_expansion P hP X)
  simpa [correctedCenteredRealPhase, Polynomial.eval_finsetSum,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_pow] using heval.symm

/-- Blueprint `lu:inverse-ii-output`, with the recurrence as the only
arithmetic hypothesis and all three approved output bounds. -/
theorem typeIIRecurrenceOutput
    (d : ℕ) (X H : ℤ) (P : Polynomial ℝ) (K : ℝ) (Q : ℕ)
    (hd : 1 ≤ d) (hX : 3 ≤ X) (hH : 2 ≤ H) (hHX : H ≤ X)
    (hP : P.natDegree ≤ d) (hQ : 1 ≤ Q) (hQK : (Q : ℝ) ≤ K)
    (hrec : ∀ j, 1 ≤ j → j ≤ d →
      realDistanceToIntegers
          ((Q : ℝ) * bilinearDerivativeCoefficient (X : ℝ)
            (fun i => (phaseCenteredAt P X).coeff i) j) ≤
        K * (X : ℝ) / (H : ℝ) ^ (j + 1)) :
    ∃ T : ℝ, ∃ q : ℕ, ∃ hq : 0 < q,
      (q : ℝ) ≤ (d.factorial : ℝ) * K ∧
      |T| ≤ 2 * Real.pi * (d : ℝ) * K *
        ((X : ℝ) / (H : ℝ)) ^ (d + 1) ∧
      residueClassTotalVariation (logPhaseIntegerInterval (X : ℝ) (H : ℝ))
          (fun n : ℤ => unitFrequencyPhase (P.eval (n : ℝ)) *
            archimedeanTwist (-T) (n : ℝ)) q hq ≤
        ENNReal.ofReal ((d.factorial : ℝ) * K *
          (1 + 2 * Real.pi * (d + 1 : ℕ) * K)) := by
  have hX0 : 0 ≤ X := by omega
  have hXnat : 1 ≤ X.toNat := by omega
  have hXcast : (X.toNat : ℝ) = (X : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hX0
  have hHr : (0 : ℝ) < (H : ℝ) := by
    have : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    linarith
  have hHXr : (H : ℝ) ≤ (X.toNat : ℝ) := by
    rw [hXcast]
    exact_mod_cast hHX
  have hQreal : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hK : 0 ≤ K := le_trans (by positivity : (0 : ℝ) ≤ Q) hQK
  have hterminal : (phaseCenteredAt P X).coeff (d + 1) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt (phaseCenteredAt_natDegree_le P hP X) (by omega)
  have hrec' : ∀ j, 1 ≤ j → j ≤ d →
      realDistanceToIntegers
          ((Q : ℝ) * bilinearDerivativeCoefficient (X.toNat : ℝ)
            (fun i => (phaseCenteredAt P X).coeff i) j) ≤
        K * (X.toNat : ℝ) / (H : ℝ) ^ (j + 1) := by
    simpa only [hXcast] using hrec
  obtain ⟨T, q, hq, hqeq, hT, hTV⟩ := coefficientRecurrenceToLogPhase
    d X.toNat Q (H : ℝ) K (fun i => (phaseCenteredAt P X).coeff i)
    hd hXnat hHr hHXr hQ hK hterminal hrec'
  have hdiv : K / (Q : ℝ) ≤ K := div_le_self hK hQreal
  have hqBound : (q : ℝ) ≤ (d.factorial : ℝ) * K := by
    rw [hqeq, Nat.cast_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hQK (Nat.cast_nonneg _)
  have hTBound : |T| ≤ 2 * Real.pi * (d : ℝ) * K *
      ((X : ℝ) / (H : ℝ)) ^ (d + 1) := by
    calc
      |T| ≤ (2 * Real.pi * (d : ℝ) * K / (Q : ℝ)) *
          ((X : ℝ) / (H : ℝ)) ^ (d + 1) := by
        simpa only [hXcast] using hT
      _ ≤ 2 * Real.pi * (d : ℝ) * K *
          ((X : ℝ) / (H : ℝ)) ^ (d + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hdiv (by positivity)
  have hconstant :
      (q : ℝ) * (1 + 2 * Real.pi * ((d + 1 : ℕ) * (K / (Q : ℝ)))) ≤
        (d.factorial : ℝ) * K * (1 + 2 * Real.pi * (d + 1 : ℕ) * K) := by
    have hfactor :
        1 + 2 * Real.pi * ((d + 1 : ℕ) * (K / (Q : ℝ))) ≤
          1 + 2 * Real.pi * (d + 1 : ℕ) * K := by
      calc
        _ = 1 + (2 * Real.pi * (d + 1 : ℕ)) * (K / (Q : ℝ)) := by ring
        _ ≤ 1 + (2 * Real.pi * (d + 1 : ℕ)) * K :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiv
            (by positivity : 0 ≤ 2 * Real.pi * (d + 1 : ℕ)))
    exact mul_le_mul hqBound hfactor (by positivity) (by positivity)
  refine ⟨T, q, hq, hqBound, hTBound, ?_⟩
  have hphase : (fun n : ℤ =>
      unitFrequencyPhase
          (correctedCenteredRealPhase d (X : ℝ)
            (fun i => (phaseCenteredAt P X).coeff i) (n : ℝ)) *
        archimedeanTwist (-T) (n : ℝ)) =
      (fun n : ℤ => unitFrequencyPhase (P.eval (n : ℝ)) *
        archimedeanTwist (-T) (n : ℝ)) := by
    funext n
    rw [correctedCenteredRealPhase_canonical d P hP X]
  rw [hXcast, hphase] at hTV
  exact hTV.trans (ENNReal.ofReal_le_ofReal hconstant)

end

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.correctedCenteredRealPhase_canonical
#print axioms FractionalPrimes.Literature.Uniformity.typeIIRecurrenceOutput
