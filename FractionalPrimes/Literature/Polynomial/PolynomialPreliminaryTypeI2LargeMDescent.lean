module

public import FractionalPrimes.Literature.Polynomial.PolynomialPreliminaryTypeI2LargeM
public import FractionalPrimes.Literature.Polynomial.PolynomialIntegerCompositionError

/-!
# Large-scale Type-I₂ coefficient descent

This module specializes the generic integer-polynomial truncation lemmas to
the centered quadratic hyperbola product map.  It is kept separate from the
direction-selection assembly so both proof lanes can compile independently.
-/

@[expose] public section

namespace FractionalPrimes.Literature.Polynomial

open _root_.Polynomial

/-- Translation to monomial coordinates at an integer centre does not raise
the degree. -/
theorem phaseCenteredAt_natDegree_le
    {d : ℕ} (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (Y : ℤ) :
    (phaseCenteredAt P Y).natDegree ≤ d := by
  have hlinear :
      (Polynomial.C (Y : ℝ) + Polynomial.X).natDegree ≤ 1 := by
    rw [add_comm, Polynomial.natDegree_X_add_C]
  calc
    (phaseCenteredAt P Y).natDegree ≤
        P.natDegree *
          (Polynomial.C (Y : ℝ) + Polynomial.X).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ d * 1 := Nat.mul_le_mul hP hlinear
    _ = d := by simp

/-- Composing the phase centred at `Y` with the product coordinate centred
at `Y` recovers the original uncentred product phase exactly. -/
theorem phaseCenteredAt_comp_hyperbolaCenteredProductPolynomial
    (P : Polynomial ℝ) (m₀ n₀ q a Y : ℤ) :
    (phaseCenteredAt P Y).comp
        (hyperbolaCenteredProductPolynomial m₀ n₀ q a Y) =
      P.comp (hyperbolaProductPolynomial m₀ n₀ q a) := by
  rw [phaseCenteredAt, Polynomial.comp_assoc]
  congr 1
  simp [hyperbolaCenteredProductPolynomial]

/-- Exact degree-`d` monomial expansion of the phase centered at the integer
`Y`. -/
theorem phaseCenteredAt_monomial_expansion
    {d : ℕ} (P : Polynomial ℝ) (hP : P.natDegree ≤ d) (Y : ℤ) :
    P.comp (Polynomial.X + Polynomial.C (Y : ℝ)) =
      ∑ j ∈ Finset.range (d + 1),
        Polynomial.C ((phaseCenteredAt P Y).coeff j) * Polynomial.X ^ j := by
  have hcenter :
      P.comp (Polynomial.X + Polynomial.C (Y : ℝ)) =
        phaseCenteredAt P Y := by
    rw [phaseCenteredAt]
    congr 1
    exact add_comm _ _
  have hsum : phaseCenteredAt P Y =
      ∑ j ∈ Finset.range (d + 1),
        Polynomial.C ((phaseCenteredAt P Y).coeff j) * Polynomial.X ^ j := by
    calc
      phaseCenteredAt P Y =
          ∑ j ∈ Finset.range ((phaseCenteredAt P Y).natDegree + 1),
            Polynomial.C ((phaseCenteredAt P Y).coeff j) * Polynomial.X ^ j :=
        (phaseCenteredAt P Y).as_sum_range_C_mul_X_pow
      _ = ∑ j ∈ Finset.range (d + 1),
            Polynomial.C ((phaseCenteredAt P Y).coeff j) * Polynomial.X ^ j := by
        apply Finset.sum_subset
        · intro j hj
          exact Finset.mem_range.mpr
            (Nat.lt_of_lt_of_le (Finset.mem_range.mp hj)
              (Nat.add_le_add_right
                (phaseCenteredAt_natDegree_le P hP Y) 1))
        · intro j hj hnot
          have hjlarge : (phaseCenteredAt P Y).natDegree < j := by
            simp only [Finset.mem_range] at hj hnot
            omega
          simp [Polynomial.coeff_eq_zero_of_natDegree_lt hjlarge]
  exact hcenter.trans hsum

/-- Positive direction coordinates make the centered product map genuinely
quadratic. -/
theorem hyperbolaCenteredProductPolynomial_natDegree_eq_two
    (m₀ n₀ q a Y : ℤ) (hq : q ≠ 0) (ha : a ≠ 0) :
    (hyperbolaCenteredProductPolynomial m₀ n₀ q a Y).natDegree = 2 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (hyperbolaCenteredProductPolynomial_natDegree_le_two m₀ n₀ q a Y)
  rw [hyperbolaCenteredProductPolynomial_coeff_two]
  exact neg_ne_zero.mpr (mul_ne_zero (by exact_mod_cast hq) (by exact_mod_cast ha))

/-- The top coefficient of the truncated centered phase after composition
with the product map is the source's literal `(-qa)^l s α_l`. -/
theorem hyperbolaCenteredProductPolynomial_truncation_topCoefficient
    (p : Polynomial ℝ) (m₀ n₀ q a Y : ℤ)
    (l : ℕ) (hl : 1 ≤ l) (hq : q ≠ 0) (ha : a ≠ 0) (s : ℝ) :
    ((C s * polynomialCoefficientTruncation p l).comp
      (hyperbolaCenteredProductPolynomial m₀ n₀ q a Y)).coeff (2 * l) =
        (-((q : ℝ) * (a : ℝ))) ^ l * s * p.coeff l := by
  have h := polynomialCoefficientTruncation_comp_coeff_two_mul
    p (hyperbolaCenteredProductPolynomial m₀ n₀ q a Y) l hl
    (hyperbolaCenteredProductPolynomial_natDegree_eq_two
      m₀ n₀ q a Y hq ha) s
  rw [hyperbolaCenteredProductPolynomial_coeff_two] at h
  calc
    ((C s * polynomialCoefficientTruncation p l).comp
      (hyperbolaCenteredProductPolynomial m₀ n₀ q a Y)).coeff (2 * l) =
        s * p.coeff l * (-((q : ℝ) * (a : ℝ))) ^ l := h
    _ = (-((q : ℝ) * (a : ℝ))) ^ l * s * p.coeff l := by ring

/-- The sign of the quadratic leading coefficient disappears after taking
circle distance, giving precisely the positive product `(qa)^l` required by
the product-recurrence theorem. -/
theorem hyperbolaCenteredProductPolynomial_truncation_topDistance
    (p : Polynomial ℝ) (m₀ n₀ q a Y : ℤ)
    (l : ℕ) (hl : 1 ≤ l) (hq : q ≠ 0) (ha : a ≠ 0) (s : ℝ) :
    realDistanceToIntegers
        (((C s * polynomialCoefficientTruncation p l).comp
          (hyperbolaCenteredProductPolynomial m₀ n₀ q a Y)).coeff (2 * l)) =
      realDistanceToIntegers
        ((((q : ℝ) * (a : ℝ)) ^ l) * (s * p.coeff l)) := by
  rw [hyperbolaCenteredProductPolynomial_truncation_topCoefficient
    p m₀ n₀ q a Y l hl hq ha s]
  rw [show (-((q : ℝ) * (a : ℝ))) ^ l * s * p.coeff l =
      (-((q : ℝ) * (a : ℝ))) ^ l * (s * p.coeff l) by ring]
  exact realDistanceToIntegers_neg_pow_mul
    ((q : ℝ) * (a : ℝ)) (s * p.coeff l) l

/-- The source's full coefficient-error calculation for one centered
hyperbola product map.  The hypotheses are exactly the interval geometry,
the old composition error, and the already-controlled higher monomials; the
conclusion has the literal error `|k| B + d (2592 t²)^d U`. -/
theorem hyperbolaCenteredProductPolynomial_truncation_comp_error_le
    (p : Polynomial ℝ) (m₀ n₀ q a : ℤ)
    (K : ℕ) (hK : 36 ≤ K)
    (X H L t : ℝ) (hH : 1 ≤ H) (hL : 0 ≤ L) (ht : 1 ≤ t)
    (hLK : L ≤ t * (K : ℝ))
    (hstrip : ∀ n ∈ Finset.Icc 1 K,
      X < ((m₀ : ℝ) + (q : ℝ) * (n : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (n : ℝ)) ∧
      ((m₀ : ℝ) + (q : ℝ) * (n : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (n : ℝ)) ≤ X + H)
    {l d : ℕ} (hp : p.natDegree ≤ d) (hl : l ≤ d)
    (s v k : ℤ) (hsk : s = v * k)
    (U B : ℝ) (i : ℕ) (hU : 0 ≤ U)
    (horiginal :
      L ^ i * realDistanceToIntegers
        ((v : ℝ) *
          (p.comp (hyperbolaCenteredProductPolynomial
            m₀ n₀ q a (Int.floor X))).coeff i) ≤ B)
    (hhigh : ∀ j ∈ Finset.Ico (l + 1) (d + 1),
      H ^ j * realDistanceToIntegers ((s : ℝ) * p.coeff j) ≤ U) :
    L ^ i * realDistanceToIntegers
        (((C (s : ℝ) * polynomialCoefficientTruncation p l).comp
          (hyperbolaCenteredProductPolynomial
            m₀ n₀ q a (Int.floor X))).coeff i) ≤
      |(k : ℝ)| * B + (d : ℝ) * (2592 * t ^ 2) ^ d * U := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hA : 1 ≤ (2592 : ℝ) * t ^ 2 := by
    have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
    nlinarith
  have h := polynomialCoefficientTruncation_comp_error_le
    p (hyperbolaCenteredProductPolynomialInt
      m₀ n₀ q a (Int.floor X)) hp hl s v k hsk
    H L U (2592 * t ^ 2) B i hHpos hL hU hA
    (by
      simpa [hyperbolaCenteredProductPolynomial_map_intCast] using horiginal)
    hhigh
    (by
      intro j hj
      simpa [hyperbolaCenteredProductPolynomial_map_intCast] using
        (hyperbolaCenteredProductPolynomial_normalized_power_coefficientSum_le
          m₀ n₀ q a K hK X H L t hH hL ht hLK hstrip j))
  simpa [hyperbolaCenteredProductPolynomial_map_intCast] using h

/-- Under the descending-induction bounds `|k|,B ≤ U` and `U ≥ 1`, the
preceding exact coefficient error is absorbed by the source budget
`(1+d(2592t²)^d)U²`. -/
theorem hyperbolaCenteredProductPolynomial_truncation_comp_error_le_square
    (p : Polynomial ℝ) (m₀ n₀ q a : ℤ)
    (K : ℕ) (hK : 36 ≤ K)
    (X H L t : ℝ) (hH : 1 ≤ H) (hL : 0 ≤ L) (ht : 1 ≤ t)
    (hLK : L ≤ t * (K : ℝ))
    (hstrip : ∀ n ∈ Finset.Icc 1 K,
      X < ((m₀ : ℝ) + (q : ℝ) * (n : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (n : ℝ)) ∧
      ((m₀ : ℝ) + (q : ℝ) * (n : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (n : ℝ)) ≤ X + H)
    {l d : ℕ} (hp : p.natDegree ≤ d) (hl : l ≤ d)
    (s v k : ℤ) (hsk : s = v * k)
    (U B : ℝ) (i : ℕ) (hU : 1 ≤ U)
    (hkU : |(k : ℝ)| ≤ U) (hBU : B ≤ U)
    (horiginal :
      L ^ i * realDistanceToIntegers
        ((v : ℝ) *
          (p.comp (hyperbolaCenteredProductPolynomial
            m₀ n₀ q a (Int.floor X))).coeff i) ≤ B)
    (hhigh : ∀ j ∈ Finset.Ico (l + 1) (d + 1),
      H ^ j * realDistanceToIntegers ((s : ℝ) * p.coeff j) ≤ U) :
    L ^ i * realDistanceToIntegers
        (((C (s : ℝ) * polynomialCoefficientTruncation p l).comp
          (hyperbolaCenteredProductPolynomial
            m₀ n₀ q a (Int.floor X))).coeff i) ≤
      (1 + (d : ℝ) * (2592 * t ^ 2) ^ d) * U ^ 2 := by
  have hcoefficient :=
    hyperbolaCenteredProductPolynomial_truncation_comp_error_le
      p m₀ n₀ q a K hK X H L t hH hL ht hLK hstrip hp hl
      s v k hsk U B i (le_trans zero_le_one hU) horiginal hhigh
  have hB : 0 ≤ B := by
    have hleft : 0 ≤
        L ^ i * realDistanceToIntegers
          ((v : ℝ) *
            (p.comp (hyperbolaCenteredProductPolynomial
              m₀ n₀ q a (Int.floor X))).coeff i) :=
      mul_nonneg (pow_nonneg hL i) Metric.infDist_nonneg
    exact hleft.trans horiginal
  have habsorb := polynomialCoefficientTruncation_error_absorb
    d (2592 * t ^ 2) B U |(k : ℝ)|
    (by positivity) hB hU hkU hBU
  exact hcoefficient.trans habsorb

/-- Literal Type-I₂-budget form of the centered coefficient estimate used at
one step of the descending induction. -/
theorem hyperbolaCenteredProductPolynomial_truncation_comp_error_le_typeI2C
    (p : Polynomial ℝ) (m₀ n₀ q a : ℤ)
    (K : ℕ) (hK : 36 ≤ K)
    (X H L x : ℝ) (hH : 1 ≤ H) (hL : 0 ≤ L) (hx : 1 ≤ x)
    (hLK : L ≤ typeI2T x * (K : ℝ))
    (hstrip : ∀ n ∈ Finset.Icc 1 K,
      X < ((m₀ : ℝ) + (q : ℝ) * (n : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (n : ℝ)) ∧
      ((m₀ : ℝ) + (q : ℝ) * (n : ℝ)) *
          ((n₀ : ℝ) - (a : ℝ) * (n : ℝ)) ≤ X + H)
    {l d step : ℕ} (hp : p.natDegree ≤ d) (hl : l ≤ d)
    (s v quotient : ℤ) (hsq : s = v * quotient)
    (i : ℕ)
    (hW : 1 ≤ typeI2W d step x)
    (hquotient : |(quotient : ℝ)| ≤ typeI2W d step x)
    (hBW : typeI2B d x ≤ typeI2W d step x)
    (horiginal :
      L ^ i * realDistanceToIntegers
        ((v : ℝ) *
          (p.comp (hyperbolaCenteredProductPolynomial
            m₀ n₀ q a (Int.floor X))).coeff i) ≤ typeI2B d x)
    (hhigh : ∀ j ∈ Finset.Ico (l + 1) (d + 1),
      H ^ j * realDistanceToIntegers ((s : ℝ) * p.coeff j) ≤
        typeI2W d step x) :
    L ^ i * realDistanceToIntegers
        (((C (s : ℝ) * polynomialCoefficientTruncation p l).comp
          (hyperbolaCenteredProductPolynomial
            m₀ n₀ q a (Int.floor X))).coeff i) ≤
      typeI2C d x * typeI2W d step x ^ 2 := by
  have h :=
    hyperbolaCenteredProductPolynomial_truncation_comp_error_le_square
      p m₀ n₀ q a K hK X H L (typeI2T x) hH hL
      (typeI2T_ge_one x hx) hLK hstrip hp hl s v quotient hsq
      (typeI2W d step x) (typeI2B d x) i hW hquotient hBW
      horiginal hhigh
  simpa [typeI2C_eval] using h

end FractionalPrimes.Literature.Polynomial

#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_natDegree_eq_two
#print axioms FractionalPrimes.Literature.Polynomial.phaseCenteredAt_natDegree_le
#print axioms FractionalPrimes.Literature.Polynomial.phaseCenteredAt_comp_hyperbolaCenteredProductPolynomial
#print axioms FractionalPrimes.Literature.Polynomial.phaseCenteredAt_monomial_expansion
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_truncation_topCoefficient
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_truncation_topDistance
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_truncation_comp_error_le
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_truncation_comp_error_le_square
#print axioms FractionalPrimes.Literature.Polynomial.hyperbolaCenteredProductPolynomial_truncation_comp_error_le_typeI2C
