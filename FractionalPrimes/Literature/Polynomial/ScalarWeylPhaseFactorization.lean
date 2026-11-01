module

public import FractionalPrimes.Literature.Polynomial.ScalarWeylTopTruncation
public import FractionalPrimes.Literature.Polynomial.ScalarWeyl

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open FractionalPrimes
open _root_.Polynomial

/-- Factor the phase of a degree-bounded polynomial into its low-degree
truncation and its prescribed top monomial. This is the input normalization
for the interval top-correction prefix lemma. -/
theorem scalarWeyl_topTruncationPhase_factorization
    (d : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (n : ℤ) :
    unitFrequencyPhase (P.eval (n : ℝ)) =
      unitFrequencyPhase
          ((scalarWeyl_topMonomialTruncation d P).eval (n : ℝ)) *
        unitFrequencyPhase (P.coeff d * (n : ℝ) ^ d) := by
  let Plo := scalarWeyl_topMonomialTruncation d P
  have hspec := scalarWeyl_topMonomialTruncation_spec d P hP
  have hdecomp : P = Plo + Polynomial.C (P.coeff d) * Polynomial.X ^ d := by
    simpa [Plo] using hspec.2.2.2
  have heval : P.eval (n : ℝ) =
      Plo.eval (n : ℝ) + P.coeff d * (n : ℝ) ^ d := by
    calc
      P.eval (n : ℝ) =
          (Plo + Polynomial.C (P.coeff d) * Polynomial.X ^ d).eval
            (n : ℝ) :=
        congrArg (fun Q : Polynomial ℝ => Q.eval (n : ℝ)) hdecomp
      _ = Plo.eval (n : ℝ) + P.coeff d * (n : ℝ) ^ d := by
        rw [Polynomial.eval_add, Polynomial.eval_C_mul,
          Polynomial.eval_X_pow]
  rw [heval, unitFrequencyPhase_add]

end FractionalPrimes.Literature.Polynomial
