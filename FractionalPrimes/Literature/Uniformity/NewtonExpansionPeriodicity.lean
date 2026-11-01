module

public import FractionalPrimes.Literature.Uniformity.BinomialCoefficientNorm
public import FractionalPrimes.Literature.Polynomial.AffineRecurrence
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Div

/-!
# Newton expansion and rational binomial periodicity

Blueprint `lu:newton-periodicity`. Mathlib supplies Gregory–Newton
summation and vanishing of polynomial differences above the degree.
The integer-period argument uses polynomial evaluation congruence on the
integer descending Pochhammer polynomial, including negative arguments.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Uniformity

open FractionalPrimes.Literature.Polynomial

noncomputable section

/-- The real binomial polynomial `t(t-1)...(t-j+1)/j!`. -/
def newtonBinomialPolynomial (j : ℕ) : Polynomial ℝ :=
  Polynomial.C (j.factorial : ℝ)⁻¹ * descPochhammer ℝ j

theorem newtonBinomialPolynomial_eval (j : ℕ) (t : ℝ) :
    (newtonBinomialPolynomial j).eval t =
      (∏ i ∈ Finset.range j, (t - (i : ℝ))) / (j.factorial : ℝ) := by
  simp only [newtonBinomialPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    descPochhammer_eval_eq_prod_range, div_eq_mul_inv]
  ring

@[simp]
theorem newtonBinomialPolynomial_eval_nat (j n : ℕ) :
    (newtonBinomialPolynomial j).eval (n : ℝ) = (n.choose j : ℝ) := by
  rw [Nat.cast_choose_eq_descPochhammer_div]
  simp [newtonBinomialPolynomial, div_eq_mul_inv, mul_comm]

/-- The project's polynomial difference and Mathlib's function difference
agree before any Newton expansion is used. -/
theorem iteratedPolynomialForwardDifference_eval_eq_fwdDiff
    (k : ℕ) (P : Polynomial ℝ) :
    (fun t : ℝ => (iteratedPolynomialForwardDifference k P).eval t) =
      (fwdDiff (1 : ℝ))^[k] P.eval := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
    rw [iteratedPolynomialForwardDifference, ih, Function.iterate_succ_apply]
    congr 1
    funext t
    simp [polynomialForwardDifference, fwdDiff, Polynomial.eval_comp]

/-- The exact Gregory–Newton formula at nonnegative integer shifts, with
the finite sum truncated to the approved degree bound. -/
theorem newtonExpansion_at_nat
    (d : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (M : ℤ) (n : ℕ) :
    P.eval ((M : ℝ) + (n : ℝ)) =
      ∑ j ∈ Finset.range (d + 1),
        binomialPolynomialCoefficient d P M j * (n.choose j : ℝ) := by
  have hformula := shift_eq_sum_fwdDiff_iter (1 : ℝ) P.eval n (M : ℝ)
  have hcoefficient (j : ℕ) :
      binomialPolynomialCoefficient d P M j =
        ((fwdDiff (1 : ℝ))^[j] P.eval) (M : ℝ) := by
    rw [binomialPolynomialCoefficient_eq_iteratedForwardDifference]
    exact congrFun (iteratedPolynomialForwardDifference_eval_eq_fwdDiff j P) _
  have hzero (j : ℕ) (hj : d < j) :
      binomialPolynomialCoefficient d P M j = 0 := by
    rw [hcoefficient, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
      (lt_of_le_of_lt hP hj)]
    rfl
  have hsum :
      (∑ j ∈ Finset.range (d + 1),
          binomialPolynomialCoefficient d P M j * (n.choose j : ℝ)) =
        ∑ j ∈ Finset.range (n + 1),
          binomialPolynomialCoefficient d P M j * (n.choose j : ℝ) := by
    rcases le_total d n with hdn | hnd
    · apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hnot
      have hdj : d < j := by
        simp only [Finset.mem_range] at hj hnot
        omega
      rw [hzero j hdj, zero_mul]
    · symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hnot
      have hnj : n < j := by
        simp only [Finset.mem_range] at hj hnot
        omega
      rw [Nat.choose_eq_zero_of_lt hnj, Nat.cast_zero, mul_zero]
  rw [hsum]
  simpa only [nsmul_eq_mul, mul_one, hcoefficient, mul_comm] using hformula

/-- Exact real-polynomial Newton expansion at an integer centre. -/
theorem newtonPolynomialExpansion
    (d : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (M : ℤ) :
    P.comp (Polynomial.C (M : ℝ) + Polynomial.X) =
      ∑ j ∈ Finset.range (d + 1),
        Polynomial.C (binomialPolynomialCoefficient d P M j) *
          newtonBinomialPolynomial j := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective
    (Nat.cast_injective (R := ℝ))).mono
  rintro t ⟨n, rfl⟩
  simpa only [Set.mem_ofPred_eq, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, newtonBinomialPolynomial_eval_nat] using
    newtonExpansion_at_nat d P hP M n

/-- Evaluation of the real Newton expansion, including negative real
shifts and degree zero. -/
theorem newtonPolynomialExpansion_eval
    (d : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (M : ℤ) (t : ℝ) :
    P.eval ((M : ℝ) + t) =
      ∑ j ∈ Finset.range (d + 1),
        binomialPolynomialCoefficient d P M j *
          (newtonBinomialPolynomial j).eval t := by
  have heval := congrArg (fun R : Polynomial ℝ => R.eval t)
    (newtonPolynomialExpansion d P hP M)
  simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_mul] using heval

/-- Shifting a degree-`j` binomial polynomial by `q*d!` changes it by an
integer multiple of `q`. Integer polynomial congruence avoids any sign
restriction on `z`. -/
theorem newtonBinomialPolynomial_integer_increment
    (d q j : ℕ) (hjd : j ≤ d) (z : ℤ) :
    ∃ k : ℤ,
      (newtonBinomialPolynomial j).eval ((z + (q * d.factorial : ℕ) : ℤ) : ℝ) -
        (newtonBinomialPolynomial j).eval (z : ℝ) = (q : ℝ) * (k : ℝ) := by
  have hdiv := Polynomial.sub_dvd_eval_sub
    (z + (q * d.factorial : ℕ)) z (descPochhammer ℤ j)
  have hdiv' : ((q * d.factorial : ℕ) : ℤ) ∣
      (descPochhammer ℤ j).eval (z + (q * d.factorial : ℕ)) -
        (descPochhammer ℤ j).eval z := by
    simpa only [add_sub_cancel_left] using hdiv
  obtain ⟨k, hk⟩ := hdiv'
  obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hjd
  refine ⟨(m : ℤ) * k, ?_⟩
  have hkreal :
      (descPochhammer ℝ j).eval ((z + (q * d.factorial : ℕ) : ℤ) : ℝ) -
        (descPochhammer ℝ j).eval (z : ℝ) =
          (q : ℝ) * (d.factorial : ℝ) * (k : ℝ) := by
    have hcast := congrArg (fun a : ℤ => (a : ℝ)) hk
    simpa only [Int.cast_sub, descPochhammer_eval_cast, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul] using hcast
  have hmreal : (d.factorial : ℝ) = (j.factorial : ℝ) * (m : ℝ) := by
    exact_mod_cast hm
  dsimp [newtonBinomialPolynomial]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Int.cast_mul]
  simp only [Nat.cast_mul] at hkreal
  rw [← mul_sub, hkreal, hmreal]
  have hjfact : (j.factorial : ℝ) ≠ 0 := by positivity
  simp only [Int.cast_natCast]
  field_simp [hjfact]

/-- A polynomial specified in Newton coordinates at the integer centre. -/
def newtonRealPhase (d : ℕ) (M : ℤ) (r : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), r j *
    (newtonBinomialPolynomial j).eval (t - (M : ℝ))

/-- Rational Newton coefficients with denominator `q` give an integer
increment at every integer, including negative integers and degree zero. -/
theorem newtonRealPhase_increment_int
    (d q : ℕ) (M : ℤ) (r : ℕ → ℝ)
    (hr : ∀ j, 1 ≤ j → j ≤ d → ∃ k : ℤ, (q : ℝ) * r j = (k : ℝ))
    (n : ℤ) :
    ∃ k : ℤ, newtonRealPhase d M r ((n + (q * d.factorial : ℕ) : ℤ) : ℝ) -
      newtonRealPhase d M r (n : ℝ) = (k : ℝ) := by
  classical
  let S := Finset.range (d + 1)
  let term : ℕ → ℝ := fun j => r j *
    ((newtonBinomialPolynomial j).eval
        (((n + (q * d.factorial : ℕ) : ℤ) : ℝ) - (M : ℝ)) -
      (newtonBinomialPolynomial j).eval ((n : ℝ) - (M : ℝ)))
  have hterm : ∀ j ∈ S, ∃ k : ℤ, term j = (k : ℝ) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      refine ⟨0, ?_⟩
      simp [term, newtonBinomialPolynomial, descPochhammer_zero]
    · have hj1 : 1 ≤ j := by omega
      have hjd : j ≤ d := by simpa [S] using Finset.mem_range.mp hj
      obtain ⟨a, ha⟩ := hr j hj1 hjd
      obtain ⟨b, hb⟩ := newtonBinomialPolynomial_integer_increment d q j hjd (n - M)
      have harg :
          (((n + (q * d.factorial : ℕ) : ℤ) : ℝ) - (M : ℝ)) =
            (((n - M + (q * d.factorial : ℕ) : ℤ)) : ℝ) := by push_cast; ring
      have hb' :
          (newtonBinomialPolynomial j).eval
              (((n + (q * d.factorial : ℕ) : ℤ) : ℝ) - (M : ℝ)) -
            (newtonBinomialPolynomial j).eval ((n : ℝ) - (M : ℝ)) =
              (q : ℝ) * (b : ℝ) := by
        simpa only [harg, Int.cast_sub] using hb
      refine ⟨a * b, ?_⟩
      dsimp [term]
      simp only [Nat.cast_mul] at hb'
      rw [hb', ← mul_assoc, mul_comm (r j) (q : ℝ), ha, Int.cast_mul]
  let k : ℕ → ℤ := fun j => if hj : j ∈ S then Classical.choose (hterm j hj) else 0
  refine ⟨∑ j ∈ S, k j, ?_⟩
  have hsum : (∑ j ∈ S, term j) = ((∑ j ∈ S, k j : ℤ) : ℝ) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [k, dite_eq_left hj] using Classical.choose_spec (hterm j hj)
  rw [← hsum]
  unfold newtonRealPhase
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [term]
  ring

/-- Exact `q*d!` periodicity of the rational Newton phase. -/
theorem newtonRationalPhase_periodic
    (d q : ℕ) (M : ℤ) (r : ℕ → ℝ) (_hq : 1 ≤ q)
    (hr : ∀ j, 1 ≤ j → j ≤ d → ∃ k : ℤ, (q : ℝ) * r j = (k : ℝ)) :
    Function.Periodic
      (fun n : ℤ => unitFrequencyPhase (newtonRealPhase d M r (n : ℝ)))
      ((q * d.factorial : ℕ) : ℤ) := by
  intro n
  obtain ⟨k, hk⟩ := newtonRealPhase_increment_int d q M r hr n
  have hphase : newtonRealPhase d M r ((n + (q * d.factorial : ℕ) : ℤ) : ℝ) =
      newtonRealPhase d M r (n : ℝ) + (k : ℝ) := by linarith
  change unitFrequencyPhase
      (newtonRealPhase d M r ((n + (q * d.factorial : ℕ) : ℤ) : ℝ)) = _
  rw [hphase, unitFrequencyPhase_add, unitFrequencyPhase_int, mul_one]

/-- The source's rational-periodicity statement for an original polynomial
`R`, under its displayed Newton expansion. -/
theorem newtonPolynomialPhase_periodic_of_expansion
    (d q : ℕ) (M : ℤ) (R : Polynomial ℝ) (r : ℕ → ℝ) (hq : 1 ≤ q)
    (hR : ∀ t : ℝ, R.eval ((M : ℝ) + t) =
      ∑ j ∈ Finset.range (d + 1), r j * (newtonBinomialPolynomial j).eval t)
    (hr : ∀ j, 1 ≤ j → j ≤ d → ∃ k : ℤ, (q : ℝ) * r j = (k : ℝ)) :
    Function.Periodic (fun n : ℤ => unitFrequencyPhase (R.eval (n : ℝ)))
      ((q * d.factorial : ℕ) : ℤ) := by
  have heq (n : ℤ) : R.eval (n : ℝ) = newtonRealPhase d M r (n : ℝ) := by
    simpa [newtonRealPhase] using hR ((n : ℝ) - (M : ℝ))
  intro n
  change unitFrequencyPhase (R.eval ((n + (q * d.factorial : ℕ) : ℤ) : ℝ)) =
    unitFrequencyPhase (R.eval (n : ℝ))
  rw [heq, heq]
  exact newtonRationalPhase_periodic d q M r hq hr n

/-- The complete source node: exact real Newton expansion and rational
integer-phase periodicity with period `q*d!`. -/
theorem newtonExpansionPeriodicity :
    (∀ (d : ℕ) (P : Polynomial ℝ), P.natDegree ≤ d →
      ∀ (M : ℤ) (t : ℝ), P.eval ((M : ℝ) + t) =
        ∑ j ∈ Finset.range (d + 1),
          binomialPolynomialCoefficient d P M j *
            (newtonBinomialPolynomial j).eval t) ∧
    (∀ (d q : ℕ) (M : ℤ) (R : Polynomial ℝ) (r : ℕ → ℝ), 1 ≤ q →
      (∀ t : ℝ, R.eval ((M : ℝ) + t) =
        ∑ j ∈ Finset.range (d + 1), r j * (newtonBinomialPolynomial j).eval t) →
      (∀ j, 1 ≤ j → j ≤ d → ∃ k : ℤ, (q : ℝ) * r j = (k : ℝ)) →
        Function.Periodic
          (fun n : ℤ => unitFrequencyPhase (R.eval (n : ℝ)))
          ((q * d.factorial : ℕ) : ℤ)) :=
  ⟨newtonPolynomialExpansion_eval, newtonPolynomialPhase_periodic_of_expansion⟩

end

end FractionalPrimes.Literature.Uniformity

#print axioms FractionalPrimes.Literature.Uniformity.newtonPolynomialExpansion
#print axioms FractionalPrimes.Literature.Uniformity.newtonPolynomialExpansion_eval
#print axioms FractionalPrimes.Literature.Uniformity.newtonExpansionPeriodicity
