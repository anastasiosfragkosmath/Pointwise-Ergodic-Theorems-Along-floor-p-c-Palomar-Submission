module

public import FractionalPrimes.Literature.Uniformity.BinomialPhaseVariation

/-!
# A small binomial multiple has controlled variation

Blueprint `lu:small-binomial-tv`. The nearest-integer rational part and
the small error use exactly the Newton coefficients of the original
polynomial. The final modulus is `r*d!`.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open FractionalPrimes.Literature.Polynomial

noncomputable section

/-- Scalar multiplication commutes with the exact Newton coefficients. -/
theorem binomialPolynomialCoefficient_const_mul
    (d : ℕ) (a : ℝ) (P : Polynomial ℝ) (M : ℤ) (j : ℕ) :
    binomialPolynomialCoefficient d (Polynomial.C a * P) M j =
      a * binomialPolynomialCoefficient d P M j := by
  rw [binomialPolynomialCoefficient_eq_iteratedForwardDifference,
    binomialPolynomialCoefficient_eq_iteratedForwardDifference]
  rw [congrFun (iteratedPolynomialForwardDifference_eval_eq_fwdDiff j
      (Polynomial.C a * P)) (M : ℝ),
    congrFun (iteratedPolynomialForwardDifference_eval_eq_fwdDiff j P) (M : ℝ)]
  have heval : (Polynomial.C a * P).eval = a • P.eval := by
    funext t
    simp [smul_eq_mul]
  rw [heval, fwdDiff_iter_const_smul]
  simp [smul_eq_mul]

/-- Each nonconstant coefficient is controlled by the exact finite
maximum defining the approved seminorm. -/
theorem binomialCoefficientNorm_controls_coefficient
    (d : ℕ) (hd : 1 ≤ d) (P : Polynomial ℝ) (M : ℤ) (H B : ℝ)
    (hnorm : binomialCoefficientNorm d P M H ≤ B)
    (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d) :
    H ^ j * realDistanceToIntegers (binomialPolynomialCoefficient d P M j) ≤ B := by
  unfold binomialCoefficientNorm polynomialBinomialCoefficientNorm at hnorm
  rw [dite_eq_left hd] at hnorm
  exact (Finset.le_sup'
    (fun k => H ^ k * realDistanceToIntegers (polynomialBinomialCoefficient d P M k))
    (Finset.mem_Icc.mpr ⟨hj, hjd⟩)).trans hnorm

/-- Rational part of the Newton coefficients. The constant coefficient is
left unchanged, precisely as in the source construction. -/
def smallBinomialRationalCoefficient (r : ℕ) (c : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then c 0 else (Int.floor ((r : ℝ) * c j + 1 / 2) : ℝ) / (r : ℝ)

def smallBinomialErrorCoefficient (r : ℕ) (c : ℕ → ℝ) (j : ℕ) : ℝ :=
  c j - smallBinomialRationalCoefficient r c j

theorem smallBinomialRationalCoefficient_integral_multiple
    (r : ℕ) (hr : 1 ≤ r) (c : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) :
    ∃ k : ℤ, (r : ℝ) * smallBinomialRationalCoefficient r c j = (k : ℝ) := by
  refine ⟨Int.floor ((r : ℝ) * c j + 1 / 2), ?_⟩
  simp only [smallBinomialRationalCoefficient, ite_eq_right (by omega : j ≠ 0)]
  field_simp

theorem smallBinomialErrorCoefficient_abs
    (r : ℕ) (hr : 1 ≤ r) (c : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) :
    |smallBinomialErrorCoefficient r c j| =
      realDistanceToIntegers ((r : ℝ) * c j) / (r : ℝ) := by
  have hrpos : (0 : ℝ) < r := by positivity
  have heq : c j - (Int.floor ((r : ℝ) * c j + 1 / 2) : ℝ) / (r : ℝ) =
      ((r : ℝ) * c j - (Int.floor ((r : ℝ) * c j + 1 / 2) : ℝ)) / (r : ℝ) := by
    field_simp
  simp only [smallBinomialErrorCoefficient, smallBinomialRationalCoefficient,
    ite_eq_right (by omega : j ≠ 0), heq, abs_div, abs_of_pos hrpos]
  rw [realDistanceToIntegers_eq_abs_centered, centeredFrequency]

theorem smallBinomialErrorCoefficient_bound
    (d r : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (P : Polynomial ℝ) (M : ℤ) (H B : ℝ) (hH : 1 ≤ H)
    (hnorm : binomialCoefficientNorm d (Polynomial.C (r : ℝ) * P) M H ≤ B)
    (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d) :
    |smallBinomialErrorCoefficient r (binomialPolynomialCoefficient d P M) j| ≤
      (B / (r : ℝ)) / H ^ j := by
  have hrpos : (0 : ℝ) < r := by positivity
  have hHpos : 0 < H := by linarith
  have hc := binomialCoefficientNorm_controls_coefficient d hd
    (Polynomial.C (r : ℝ) * P) M H B hnorm j hj hjd
  rw [binomialPolynomialCoefficient_const_mul] at hc
  rw [smallBinomialErrorCoefficient_abs r hr _ j hj]
  have hdist : realDistanceToIntegers
      ((r : ℝ) * binomialPolynomialCoefficient d P M j) ≤ B / H ^ j :=
    (le_div_iff₀ (by positivity : 0 < H ^ j)).mpr (by simpa [mul_comm] using hc)
  calc
    _ ≤ (B / H ^ j) / (r : ℝ) := div_le_div_of_nonneg_right hdist hrpos.le
    _ = (B / (r : ℝ)) / H ^ j := by ring

/-- The exact small-binomial-multiple variation theorem, first in natural
positive-multiple coordinates. -/
theorem smallBinomialMultipleVariation_nat
    (d r : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (M : ℤ) (H B : ℝ)
    (hH : 1 ≤ H) (hB : 0 ≤ B)
    (hnorm : binomialCoefficientNorm d (Polynomial.C (r : ℝ) * P) M H ≤ B) :
    ∃ hperiod : 0 < r * d.factorial,
      residueClassTotalVariation (logPhaseIntegerInterval (M : ℝ) H)
          (fun n : ℤ => unitFrequencyPhase (P.eval n)) (r * d.factorial) hperiod ≤
        ENNReal.ofReal ((d.factorial : ℝ) *
          ((r : ℝ) + 2 * Real.pi * binomialVariationConstant d * B)) := by
  let c : ℕ → ℝ := binomialPolynomialCoefficient d P M
  let a : ℕ → ℝ := smallBinomialRationalCoefficient r c
  let s : ℕ → ℝ := smallBinomialErrorCoefficient r c
  have hrpos : (0 : ℝ) < r := by positivity
  have ha : ∀ j, 1 ≤ j → j ≤ d → ∃ k : ℤ, (r : ℝ) * a j = (k : ℝ) := by
    intro j hj hjd
    exact smallBinomialRationalCoefficient_integral_multiple r hr c j hj
  have hs : ∀ j, 1 ≤ j → j ≤ d → |s j| ≤ (B / (r : ℝ)) / H ^ j := by
    intro j hj hjd
    exact smallBinomialErrorCoefficient_bound d r hd hr P M H B hH hnorm j hj hjd
  have hadd (t : ℝ) :
      newtonRealPhase d M a t + newtonRealPhase d M s t =
        ∑ j ∈ Finset.range (d + 1), c j *
          (newtonBinomialPolynomial j).eval (t - (M : ℝ)) := by
    unfold newtonRealPhase
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [s, smallBinomialErrorCoefficient, a]
    ring
  have hphase : (fun n : ℤ => unitFrequencyPhase (P.eval n)) =
      (fun n : ℤ => unitFrequencyPhase
        (newtonRealPhase d M a n + newtonRealPhase d M s n)) := by
    funext n
    congr 1
    rw [hadd]
    simpa only [add_sub_cancel] using
      newtonPolynomialExpansion_eval d P hP M ((n : ℝ) - (M : ℝ))
  obtain ⟨hperiod, hTV⟩ := residueClassTotalVariation_rational_add_binomial_le
    d r M a s H (B / (r : ℝ)) hr hH (div_nonneg hB hrpos.le) ha hs
  refine ⟨hperiod, ?_⟩
  rw [hphase]
  have hconstant : ((r * d.factorial : ℕ) : ℝ) *
      (1 + 2 * Real.pi * (B / (r : ℝ)) * binomialVariationConstant d) =
        (d.factorial : ℝ) * ((r : ℝ) + 2 * Real.pi * binomialVariationConstant d * B) := by
    rw [Nat.cast_mul]
    field_simp [hrpos.ne']
  rw [hconstant] at hTV
  exact hTV

/-- Blueprint `lu:small-binomial-tv`, for the integer multiple returned by
the arithmetic inverse clauses. Positivity makes `r.toNat` exactly the
same integer in the residue-modulus domain. -/
theorem smallBinomialMultipleVariation
    (d : ℕ) (r : ℤ) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (M : ℤ) (H B : ℝ)
    (hH : 1 ≤ H) (hB : 0 ≤ B)
    (hnorm : binomialCoefficientNorm d (Polynomial.C (r : ℝ) * P) M H ≤ B) :
    ∃ hperiod : 0 < r.toNat * d.factorial,
      residueClassTotalVariation (logPhaseIntegerInterval (M : ℝ) H)
          (fun n : ℤ => unitFrequencyPhase (P.eval n)) (r.toNat * d.factorial) hperiod ≤
        ENNReal.ofReal ((d.factorial : ℝ) *
          ((r : ℝ) + 2 * Real.pi * binomialVariationConstant d * B)) := by
  have hrnat : 1 ≤ r.toNat := by omega
  have hrcast : (r.toNat : ℝ) = (r : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ r)
  have hnorm' : binomialCoefficientNorm d (Polynomial.C (r.toNat : ℝ) * P) M H ≤ B := by
    simpa only [hrcast] using hnorm
  obtain ⟨hperiod, hTV⟩ := smallBinomialMultipleVariation_nat
    d r.toNat hd hrnat P hP M H B hH hB hnorm'
  refine ⟨hperiod, ?_⟩
  simpa only [hrcast] using hTV

end

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.smallBinomialErrorCoefficient_bound
#print axioms FractionalPrimes.Literature.Uniformity.smallBinomialMultipleVariation
